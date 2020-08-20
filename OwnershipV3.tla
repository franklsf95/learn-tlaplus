---------------------------- MODULE OwnershipV3 ----------------------------
EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANTS MAX_CHILDREN, MAX_CALL_DEPTH

VARIABLES taskTable, schedulerInbox, taskInbox

vars == <<taskTable, schedulerInbox, taskInbox>>

----------------------------------------------------------------------------

MULTIPLIER == 100

Task == 0..(MULTIPLIER ^ MAX_CALL_DEPTH)

FutureValue == {"pending", "value", "pointer", "collected"}

IsValueReady(x) ==
    x \notin {"pending", "collected"}

Operation == {"CALL", "GET", "DELETE", "RETURN", "IDLE", "TERMINATED"}

CALL(x, args) == <<"CALL", x, args>>

GET(x) == <<"GET", x>>

DELETE(x) == <<"DELETE", x>>

RETURN == <<"RETURN">>

IDLE == <<"IDLE">>

TERMINATED == <<"TERMINATED">>

Instruction == Operation \X Seq(Task)

TaskSpec == [
    owner : Task,
    future : Task,
    args : SUBSET Task
]

FutureState == [
    inScope: BOOLEAN,
    valueGotten: BOOLEAN,
    value: FutureValue,
    taskSpec: TaskSpec
]

TaskState == [
    owner: Task,
    executedSteps: Seq(Instruction),
    nextStep: Instruction,
    nextChildId: Task,
    children: [SUBSET Task -> FutureState]
]

IsTerminated(taskState) ==
    taskState.nextStep[1] = "TERMINATED"

Globalize(scope, x) ==
    scope * MULTIPLIER + x


(***************************************************************************
  Type Invariants
 ***************************************************************************)

\* Ownership Table: [Task -> TaskState]
TaskTableTypeOK ==
    \A t \in DOMAIN taskTable :
    /\ t \in Task
\*    /\ taskTable[t] \in TaskState

SchedulerInboxTypeOK ==
    \* Scheduler's Inbox is a sequence of TaskSpec.
    schedulerInbox \in Seq(TaskSpec)

\* Each owner's inbox is a sequence of TaskSpec.
TaskInboxTypeOK ==
    \A t \in DOMAIN taskInbox :
    /\ t \in Task
    /\ taskInbox[t] \in Seq(TaskSpec)
 
TypeOK ==
    /\ TaskTableTypeOK
    /\ SchedulerInboxTypeOK
    /\ TaskInboxTypeOK


(***************************************************************************
  The initial state contains one function: "main".
 ***************************************************************************)
 
NewTaskState(owner) ==
    [owner |-> owner, executedSteps |-> <<>>, nextStep |-> IDLE, nextChildId |-> 1, children |-> <<>>]

Init ==
    /\ taskTable = [x \in {0} |-> NewTaskState(0)]
    /\ schedulerInbox = <<>>
    /\ taskInbox = [x \in {0} |-> <<>>]


(***************************************************************************
    Executing Program Steps
 ***************************************************************************)

\* Add the instruction into "executed steps" and reset the next instruction
\* to be IDLE.
FinishExecuting(taskState) ==
    LET executedSteps_== Append(taskState.executedSteps, taskState.nextStep) IN
    [[taskState EXCEPT !.executedSteps = executedSteps_] EXCEPT !.nextStep = IDLE]

\* Call a function, creating a new future and adding it to the ownership table.
\* Then send the task to the scheduler's queue for scheduling.
\* (Task Creation Step 1)
CallAndSchedule(scope, taskState, inst) ==
    LET x == Globalize(scope, inst[2]) IN
    LET args == inst[3] IN
    LET task == [owner |-> scope, future |-> x, args |-> args] IN
    /\ x \notin DOMAIN taskTable
    /\ x \notin DOMAIN taskTable[scope].children
    /\ schedulerInbox' =
        Append(schedulerInbox, task)
    /\ taskTable' =
       LET child == [inScope |-> TRUE, valueGotten |-> FALSE, value |-> "pending", taskSpec |-> task] IN
       LET children_ == [y \in {x} |-> child] @@ taskState.children IN
       LET taskState_ == [FinishExecuting(taskState) EXCEPT !.children = children_] IN
       [taskTable EXCEPT ![scope] = taskState_]
    /\ UNCHANGED <<taskInbox>>

\* Wait on a future for its task to finish, and get its value.
Get(scope, taskState, inst) ==
    LET x == inst[2] IN
    LET entry == taskState.children[x] IN
    /\ entry.inScope
    /\ ~entry.valueGotten
    /\ entry.value /= "pending"
    /\ taskTable' =
        LET futureState_ == [entry EXCEPT !.valueGotten = TRUE] IN
        LET taskState_ == [FinishExecuting(taskState) EXCEPT !.children[x] = futureState_] IN
        [taskTable EXCEPT ![scope] = taskState_]
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

\* Remove a future from current scope. This does not remove its task spec.
Delete(scope, taskState, inst) ==
    LET x == inst[2] IN
    /\ taskTable' =
        LET futureState_ == [taskTable[scope].children[x] EXCEPT !.inScope = FALSE] IN
        LET taskState_ == [FinishExecuting(taskState) EXCEPT !.children[x] = futureState_] IN
        [taskTable EXCEPT ![scope] = taskState_]
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

\* Finish execution. Return the value to its owner.
\* TODO: set all of its children's "inScope" flags to false.
Return(scope, taskState) ==
    \E retVal \in {"value", "pointer"} :
    LET owner == taskTable[scope].owner IN
    /\ LET taskTable_ ==
        [y \in {scope} |-> [FinishExecuting(taskState) EXCEPT !.nextStep = TERMINATED]]
        @@ taskTable
       IN
        taskTable' =
        \* owner = scope is a special case for the main function (0).
        IF owner \notin DOMAIN taskTable \/ owner = scope THEN taskTable_ ELSE
        LET ownerState == taskTable[owner] IN
\*        IF scope \notin DOMAIN ownerState.children THEN taskTable_ ELSE
        [y \in {owner} |-> [ownerState EXCEPT !.children[scope].value = retVal]]
        @@ taskTable_
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

ExecuteProgramStep(scope, taskState) ==
    LET inst == taskState.nextStep IN
    LET op == Head(inst) IN
    CASE op = "CALL" -> CallAndSchedule(scope, taskState, inst)
      [] op = "GET" -> Get(scope, taskState, inst)
      [] op = "DELETE" -> Delete(scope, taskState, inst)
      [] op = "RETURN" -> Return(scope, taskState)
      [] OTHER -> FALSE

ExecuteSomeProgramStep ==
    \E scope \in DOMAIN taskTable :
    LET taskState == taskTable[scope] IN
    /\ taskState.nextStep[1] \notin {"IDLE", "TERMINATED"}
    /\ ExecuteProgramStep(scope, taskState)

(***************************************************************************
    Submitting Program Steps
 ***************************************************************************)
 
\* Generate all possible instructions given a task state.
PossibleNextSteps(scope, taskState) ==
    LET children == DOMAIN taskState.children IN
    LET inScopes == {x \in children : taskState.children[x].inScope} IN
    UNION {
        IF
        \/ taskState.nextChildId >= MAX_CHILDREN
        \/ scope >= MULTIPLIER ^ (MAX_CALL_DEPTH - 1)
        THEN {}
        ELSE
        LET x == taskState.nextChildId IN
        \* CALL with any set of arguments.
        { CALL(x, args) : args \in SUBSET inScopes },
        
        \* GET anything that has not been gotten yet.
        { GET(x) : x \in {x \in inScopes : ~taskState.children[x].valueGotten} },
        
        \* DELETE anything that is in scope.
        { DELETE(x) : x \in inScopes },
        
        \* RETURN.
        { RETURN }
    }

\* Submit a program step according to the current task state.
SubmitProgramStep(scope, taskState) ==
    \E inst \in PossibleNextSteps(scope, taskState) :
    /\ taskTable' = 
       LET taskState_ == IF inst[1] = "CALL"
         THEN [taskState EXCEPT !.nextChildId = taskState.nextChildId + 1]
         ELSE taskState IN
       [y \in {scope} |-> [taskState_ EXCEPT !.nextStep = inst]]
       @@ taskTable
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

SubmitSomeProgramStep ==
    \E scope \in DOMAIN taskTable :
    LET taskState == taskTable[scope] IN
    /\ taskState.nextStep[1] = "IDLE"
    /\ SubmitProgramStep(scope, taskState)

ProgramStep ==
    \/ ExecuteSomeProgramStep
    \/ SubmitSomeProgramStep

(***************************************************************************
    System Steps: Task Creation
 ***************************************************************************)

\* Task Creation Step 2:
\* Scheduler takes a task from its queue and schedule it.
\* In the real system this involves allocating a worker location to the task.
\* In this spec it is simply sending the owner a message "SCHEDULED".
\* TODO: CAN SCHEDULER FAIL? simulate "cannot schedule".
ScheduleTask ==
    /\ Len(schedulerInbox) > 0
    /\ schedulerInbox' = Tail(schedulerInbox)
    /\ LET task == Head(schedulerInbox) IN
       LET owner == task.owner IN
       taskInbox' = [taskInbox EXCEPT ![owner] = Append(taskInbox[owner], task)]
    /\ UNCHANGED <<taskTable>>

\* Task Creation Step 3:
\* Owner takes a task from its "scheduled" queue and launch it,
\* provided that all of its arguments are ready.
\* TODO: and when someone is depending on it??
LaunchTask(scope) ==
    LET ownerQueue == taskInbox[scope] IN
    LET task == Head(ownerQueue) IN
    /\ \A a \in task.args : IsValueReady(taskTable[scope].children[a].value)
    /\ taskTable' =
       [y \in {task.future} |-> NewTaskState(task.owner)] @@ taskTable
    /\ taskInbox' =
       [y \in {task.future} |-> <<>>] @@ [taskInbox EXCEPT ![scope] = Tail(ownerQueue)]
    /\ UNCHANGED <<schedulerInbox>>

LaunchSomeTask ==
    \E scope \in DOMAIN taskInbox :
    /\ Len(taskInbox[scope]) > 0
    /\ LaunchTask(scope)

(***************************************************************************
    System Steps: Garbage Collection
 ***************************************************************************)

\* Collect the task state when it is terminated and when its children is empty.
CollectTaskState(scope) ==
    LET taskState == taskTable[scope] IN
    /\ IsTerminated(taskState)
    /\ Cardinality(DOMAIN taskState.children) = 0
    /\ taskTable' =
       [y \in DOMAIN taskTable \ {scope} |-> taskTable[y]]
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

CollectSomeTaskState ==
    \E x \in DOMAIN taskTable :
    CollectTaskState(x)

\* Decides if no one depends on x's value or x's lineage.
OutOfLineageScope(scope, x) ==
    LET taskState == taskTable[scope] IN
    LET children == taskState.children IN
    ~(
        \* Do not collect lineage of a task that hasn't returned yet.
        \/ children[x].value = "pending"
        \/ children[x].inScope
        \/ \E y \in DOMAIN children :
           LET futureState == children[y] IN
           /\ x \in futureState.taskSpec.args
           /\ futureState.value \in {"pending", "pointer", "collected"}
    )

\* Remove x's entry from its owner's task table entry.
CollectLineage(scope, x) ==
    /\ OutOfLineageScope(scope, x)
    /\ taskTable' =
       LET taskState == taskTable[scope] IN
       LET children == taskState.children IN
       LET children_ == [y \in DOMAIN children \ {x} |-> children[y]] IN
       LET taskState_ == [taskState EXCEPT !.children = children_] IN
       [y \in {scope} |-> taskState_] @@ taskTable
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

CollectSomeLineage ==
    \E scope \in DOMAIN taskTable :
    \E x \in DOMAIN taskTable[scope].children :
    CollectLineage(scope, x)

\* Checks if no one depends on x's value.
OutOfScope(scope, x) == 
    LET taskState == taskTable[scope] IN
    LET children == taskState.children IN
    ~(
        \/ children[x].inScope
        \/ \E y \in DOMAIN children :
           LET futureState == children[y] IN
           /\ futureState.value = "pending"
           /\ x \in futureState.taskSpec.args
    )

\* Garbage-collect x's value from the ownership table if no other future depends on it.
CollectValue(scope, x) ==
    LET taskState == taskTable[scope] IN
    LET children == taskState.children IN
    /\ OutOfScope(scope, x)
    /\ children[x].value = "pointer"
    /\ taskTable' =
       LET children_ == [y \in {x} |-> [children[x] EXCEPT !.value = "collected"]] @@ children IN
       LET taskState_ == [taskState EXCEPT !.children = children_] IN
       [y \in {scope} |-> taskState_] @@ taskTable
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

CollectSomeValue ==
    \E scope \in DOMAIN taskTable :
    \E x \in DOMAIN taskTable[scope].children :
    CollectValue(scope, x)

SystemStep ==
    \/ ScheduleTask
    \/ LaunchSomeTask
    \/ CollectSomeTaskState
    \/ CollectSomeLineage
    \/ CollectSomeValue


(***************************************************************************
    Failures and Recovery
 ***************************************************************************)

\* TODO: what to do when this happens? Who triggers respawning of the task?
\* A value gets lost in distributed memory store.
LoseValue(scope, x) ==
    LET taskState == taskTable[scope] IN
    /\ taskState.children[x].value = "pointer"
    /\ taskTable' =
        [y \in {scope} |-> [taskState EXCEPT !.children[x].value = "pending"]]
        @@ taskTable
    /\ UNCHANGED <<schedulerInbox, taskInbox>>

LoseSomeValue ==
    \E scope \in DOMAIN taskTable :
    \E x \in DOMAIN taskTable[scope].children :
    LoseValue(scope, x)

\* A task gets lost and respawned. This is an atomic step in this spec
\* because otherwise the LineageInScopeInvariant would be violated.
\* All descendants of this task also gets respawned due to fate-sharing.
\*LoseAndRecoverTask(x) ==
\*    /\ x /= 0
\*    /\ systemState' = RespawnTasks(systemState, <<x>>)
\*    /\ UNCHANGED <<functionTable, programState, futures, nextFutureId>>
\*
\*LoseAndRecoverSomeTask ==
\*    \E x \in DOMAIN systemState : LoseAndRecoverTask(x)

FailureStep ==
    \/ LoseSomeValue
\*    \/ LoseAndRecoverSomeTask


(***************************************************************************
    Spec
 ***************************************************************************)

Next ==
    \/ ProgramStep
    \/ SystemStep
\*    \/ FailureStep

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProgramStep)
    /\ WF_vars(SystemStep)
\*    /\ WF_vars(FailureStep)


(***************************************************************************
    Invariants
 ***************************************************************************)

RECURSIVE LineageInScope(_, _)
LineageInScope(scope, x) ==
    LET table == taskTable[scope].children IN
    /\ x \in DOMAIN table
    /\ \/ table[x].value = "value"
       \/ \A arg \in table[x].taskSpec.args : LineageInScope(scope, arg)

LineageInScopeInvariant ==
    \A scope \in DOMAIN taskTable :
    \A x \in DOMAIN taskTable[scope].children :
    LineageInScope(scope, x)

SafetyInvariant ==
    /\ LineageInScopeInvariant


(***************************************************************************
    Temporal Properties
 ***************************************************************************)
 
AllTasksFulfilled ==
    \A scope \in DOMAIN taskTable :
    \A x \in DOMAIN taskTable[scope].children :
    taskTable[scope].children[x].value /= "pending"

SchedulerInboxEmpty ==
    Len(schedulerInbox) = 0

taskInboxEmpty ==
    \A scope \in DOMAIN taskInbox :
    Len(taskInbox[scope]) = 0

\* TODO: check that taskTable eventually becomes empty?
LivenessProperty ==
    <>[](
        /\ AllTasksFulfilled
        /\ SchedulerInboxEmpty
        /\ taskInboxEmpty
    )


=============================================================================
\* Modification History
\* Last modified Thu Aug 13 15:25:09 PDT 2020 by lsf
\* Created Mon Aug 10 17:23:49 PDT 2020 by lsf
