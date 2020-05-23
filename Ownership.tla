----------------------------- MODULE Ownership -----------------------------
EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANTS MAX_FUTURES, MAX_OPS, FUNCTIONS

ASSUME "main" \in FUNCTIONS

VARIABLES functionTable, systemState, programState, futures, nextFutureId

vars == <<functionTable, systemState, programState, futures, nextFutureId>>

----------------------------------------------------------------------------

OPS == {"op", "return"}

FutureValue == {"pending", "value", "pointer"}

FutureState == [
    value : FutureValue,
    fn : FUNCTIONS,
    args : SUBSET futures,
    program : Seq(OPS)
]


(***************************************************************************
  System State:
  
  * For each future, the system state stores the following information:
    - Its value, be it pending, some value, or pointer to some value in a
      distributed memory store.
    - The name of the function that will compute its value.
    - A list of futures as arguments to the function.
    - A sequence of operations to execute for the function.
  
  Program State:
  
  * For each future, the program state stores the set of futures that
    depend on this future for computation.
 ***************************************************************************)
 
Tup(S, n) == [1..n -> S]
SeqOf(set, n) == UNION {Tup(set, m) : m \in 0..n}

\* Valid programs must end with a return.
ValidPrograms == {Append(seq, "return") : seq \in SeqOf({"op"}, MAX_OPS)}
 
TypeInvariant ==
    LET definedFunctions == DOMAIN functionTable IN
    /\ definedFunctions \in SUBSET FUNCTIONS
    /\ functionTable \in [definedFunctions -> ValidPrograms]
    /\ \E futureSubset \in SUBSET futures :
        systemState \in [futureSubset -> FutureState]
    /\ programState \in [futures -> SUBSET futures]
    /\ Cardinality(futures) <= MAX_FUTURES
    /\ nextFutureId <= MAX_FUTURES


(***************************************************************************
  The initial state contains one function: "main".
 ***************************************************************************)
 
Init ==
    LET fn == "main" IN
    LET prog == <<"op", "return">> IN
    LET mainState == [value |-> "pending", fn |-> fn, args |-> {}, program |-> prog] IN
    /\ functionTable = [x \in {fn} |-> prog]
    /\ systemState = [x \in {0} |-> mainState]
    /\ programState = [x \in {0} |-> {}]
    /\ futures = {0}
    /\ nextFutureId = 1


(***************************************************************************
    Program Steps
 ***************************************************************************)

\* Invoke function f, create a new future x.
Call(scope, fn, args, newProg) ==
    LET x == nextFutureId IN
    LET prog == IF fn \in DOMAIN functionTable THEN functionTable[fn] ELSE newProg IN
    /\ x < MAX_FUTURES
    /\ scope \in DOMAIN programState
    /\ x \notin DOMAIN programState
    /\ x \notin programState[scope]
    /\ \A a \in args : a \in programState[scope]
    /\ functionTable' = [f \in {fn} |-> prog] @@ functionTable
    /\ futures' = futures \union {x}
    /\ nextFutureId' = x + 1
    /\ programState' =
        [y \in {x} |-> {}] @@ [programState EXCEPT ![scope] = programState[scope] \union {x}]
    /\ systemState' =
        LET state == [value |-> "pending", fn |-> fn, args |-> args, program |-> prog] IN
        [y \in {x} |-> state] @@ systemState
 
CallSomething ==
    \E scope \in futures :
    \E f \in FUNCTIONS \ {"main"} :
    \E args \in SUBSET programState[scope] :
    \E prog \in ValidPrograms:
    Call(scope, f, args, prog)

\* Get the value of x from the scope.
\* This does not change the system state.
Get(scope, x) ==
    /\ scope \in DOMAIN programState
    /\ x \in programState[scope]
    /\ x \in DOMAIN systemState
    /\ systemState[x].value /= "pending"
    /\ UNCHANGED vars

GetSomething ==
    \E scope \in futures :
    \E x \in programState[scope] :
    Get(scope, x)

\* Remove the dependency of x on the scope.
Delete(scope, x) ==
    /\ scope \in DOMAIN programState
    /\ x \in programState[scope]
    /\ programState' = [programState EXCEPT ![scope] = programState[scope] \ {x}]
    /\ UNCHANGED <<functionTable, systemState, futures, nextFutureId>>

DeleteSomething ==
    \E scope \in futures :
    \E x \in programState[scope] :
    Delete(scope, x)

ProgramStep ==
    \/ CallSomething
    \/ GetSomething
    \/ DeleteSomething


(***************************************************************************
    System Steps
 ***************************************************************************)

\* Decide whether to execute a step for a scope: Only execute a program when
\* some future is waiting on its return value.
ShouldExecute(scope) ==
    /\ scope \in DOMAIN systemState
    /\ systemState[scope].value = "pending"
    /\ \E x \in futures : scope \in programState[x]

\* Execute a program and store the return value in system state.
ExecuteProgramReturnValue(scope, retVal) ==
    /\ ShouldExecute(scope)
    /\ Len(systemState[scope].program) >= 1
    /\ Head(systemState[scope].program) = "return"
    /\ \A a \in systemState[scope].args : systemState[a].value /= "pending"
    /\ programState' = [programState EXCEPT ![scope] = {}]  \* TODO: maybe remove it for all?
    /\ systemState' =
        LET t == systemState[scope] IN
        LET args_ == IF retVal = "value" THEN {} ELSE t.args IN
        LET t_ == [value |-> retVal, fn |-> t.fn, args |-> args_, program |-> <<>>] IN
        [systemState EXCEPT ![scope] = t_]
    /\ UNCHANGED <<functionTable, futures, nextFutureId>>

ExecuteSomeProgramReturnValue ==
    \E scope \in futures :
    \E retVal \in {"value", "pointer"} :
    ExecuteProgramReturnValue(scope, retVal)
 
\* Execute one step of a program.
ExecuteProgramOp(scope) ==
    /\ ShouldExecute(scope)
    /\ Len(systemState[scope].program) >= 1
    /\ Head(systemState[scope].program) /= "return"
    /\ \A a \in systemState[scope].args : systemState[a].value /= "pending"
    /\ programState' = [programState EXCEPT ![scope] = {}]
    /\ systemState' =
        LET ops == systemState[scope].program IN
        LET rest == SubSeq(ops, 2, Len(ops)) IN
        [systemState EXCEPT ![scope].program = rest]
    /\ UNCHANGED <<functionTable, futures, nextFutureId>>

ExecuteSomeProgramOp ==
    \E scope \in futures :
    ExecuteProgramOp(scope)

\* Decides if no one depends on x's value or x's lineage.
OutOfLineageScope(x) == ~(
    \/ \E y \in DOMAIN programState : x \in programState[y]  \* TODO: correct?
    \/ \E y \in DOMAIN systemState :
        /\ systemState[y].value \in {"pending", "pointer"}
        /\ x \in systemState[y].args
)

\* Remove x from both the programState and the systemState.
CollectLineage(x) ==
    /\ OutOfLineageScope(x)
    /\ futures' = futures \ {x}
    /\ programState' = [o \in futures' |-> programState[o]]
    /\ systemState' = [o \in futures' |-> systemState[o]]
    /\ UNCHANGED <<functionTable, nextFutureId>>

CollectSomeLineage ==
    \E x \in futures :
    CollectLineage(x)

\* Checks if no one depends on x's value.
OutOfScope(x) == ~(
    \/ \E y \in DOMAIN programState : x \in programState[y]
    \/ \E y \in DOMAIN systemState :
        /\ systemState[y].value = "pending"
        /\ x \in systemState[y].args
)

\* Remove x from the program state table.
CollectValue(x) ==
    /\ OutOfScope(x)
    /\ x /= 0  \* Don't collect main.
    /\ systemState[x].value = "pointer"
    /\ systemState' = 
        LET oldVal == systemState[x] IN
        [systemState
        EXCEPT ![x] = [value |-> "pending", fn |-> oldVal.fn,
            args |-> oldVal.args, program |-> functionTable[oldVal.fn]]]
    /\ UNCHANGED <<functionTable, programState, futures, nextFutureId>>

CollectSomeValue ==
    \E x \in futures :
    CollectValue(x)

SystemStep ==
    \/ ExecuteSomeProgramReturnValue
    \/ ExecuteSomeProgramOp
    \/ CollectSomeLineage
    \/ CollectSomeValue
 

(***************************************************************************
    Failures and Recovery
 ***************************************************************************)

\* A value gets lost in distributed memory store.
LoseValue(x) ==
    /\ systemState[x].value = "pointer"
    /\ systemState' = 
        LET oldVal == systemState[x] IN
        [systemState
        EXCEPT ![x] = [value |-> "pending", fn |-> oldVal.fn,
            args |-> oldVal.args, program |-> functionTable[oldVal.fn]]]
    /\ UNCHANGED <<functionTable, programState, futures, nextFutureId>>

LoseSomeValue ==
    \E x \in futures : LoseValue(x)

\* A task gets lost and respawned. This is an atomic step in this spec
\* because otherwise the LineageInScopeInvariant would be violated.
LoseAndRecoverTask(x) ==
    LET fn == systemState[x].fn IN
    LET args == systemState[x].args IN
    LET prog == functionTable[fn] IN
    /\ x /= 0
    /\ systemState' =
        LET state == [value |-> "pending", fn |-> fn, args |-> args, program |-> prog] IN
        [systemState EXCEPT ![x] = state] 
    /\ UNCHANGED <<functionTable, programState, futures, nextFutureId>>

LoseAndRecoverSomeTask ==
    \E x \in DOMAIN systemState : LoseAndRecoverTask(x)

FailureStep ==
    \/ LoseSomeValue
    \/ LoseAndRecoverSomeTask

(***************************************************************************
    Spec
 ***************************************************************************)

Next ==
    \/ ProgramStep
    \/ SystemStep
    \/ FailureStep

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProgramStep)
    /\ WF_vars(SystemStep)
    /\ WF_vars(FailureStep)


(***************************************************************************
    Invariants
 ***************************************************************************)

RECURSIVE LineageInScope(_)
LineageInScope(x) ==
    /\ x \in DOMAIN systemState
    /\ \/ systemState[x].value = "value"
       \/ \A arg \in systemState[x].args : LineageInScope(arg)

LineageInScopeInvariant ==
    \A scope \in futures :
    \A x \in programState[scope] :
    LineageInScope(x)

SafetyInvariant ==
    /\ LineageInScopeInvariant


(***************************************************************************
    Temporal Properties
 ***************************************************************************)

LivenessProperty ==
    <>[](
        \A scope \in futures :
        \A x \in programState[scope] :
        systemState[x].value /= "pending"
    )


=============================================================================
\* Modification History
\* Last modified Sat May 23 15:20:32 PDT 2020 by lsf
\* Created Sat Apr 18 17:04:27 PDT 2020 by lsf
