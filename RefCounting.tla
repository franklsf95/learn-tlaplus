---------------------------- MODULE RefCounting ----------------------------
(***************************************************************************
  Variables are predefined.
  Variables can hold references to other variables.
  Variables can be deleted if they are not referenced by anything.
 ***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS VARS

VARIABLES refHolders, formerRefHolders, deleted

vars == <<refHolders, formerRefHolders, deleted>>
-----------------------------------------------------------------------------

TypeOK ==
    /\ refHolders \in [VARS -> SUBSET VARS]
    /\ formerRefHolders \in [VARS -> SUBSET VARS]
    /\ deleted \subseteq VARS

Init ==
    /\ refHolders = [v \in VARS |-> {}]
    /\ formerRefHolders = [v \in VARS |-> {}]
    /\ deleted = {}
-----------------------------------------------------------------------------

\* p holds a reference onto c
AddRef(p, c) ==
    /\ p /= c
    /\ ~(p \in deleted)
    /\ ~(c \in deleted)
    /\ ~(p \in refHolders[c])
    /\ ~(p \in formerRefHolders[c])
    /\ refHolders' = [refHolders EXCEPT ![c] = refHolders[c] \union {p}]
    /\ UNCHANGED <<deleted, formerRefHolders>>

\* p removes its reference of c
RemoveRef(p, c) ==
    /\ p /= c
    /\ ~(p \in deleted)
    /\ ~(c \in deleted)
    /\ p \in refHolders[c]
    /\ refHolders' = [refHolders EXCEPT ![c] = refHolders[c] \ {p}]
    /\ formerRefHolders' = [formerRefHolders EXCEPT ![c] = formerRefHolders[c] \union {p}]
    /\ UNCHANGED <<deleted>>

Delete(v) ==
    /\ refHolders[v] = {}
    /\ refHolders' = [c \in VARS |-> IF v \in refHolders[c] THEN refHolders[c] \ {v} ELSE refHolders[c]]
    /\ deleted' = deleted \union {v}
    /\ UNCHANGED <<formerRefHolders>>

AddRefAny == \E p \in VARS : \E c \in VARS : AddRef(p, c)

RemoveRefAny == \E p \in VARS : \E c \in VARS : RemoveRef(p, c)

DeleteAny == \E v \in VARS : Delete(v)

Next ==
    \/ AddRefAny
    \/ RemoveRefAny
    \/ DeleteAny

Spec == Init /\ [][Next]_vars /\ WF_vars(DeleteAny)

-----------------------------------------------------------------------------
(***************************************************************************
  Property to Check: Eventually all variables will be deleted.
  But this is not true, because this spec permits retain cycles.
 ***************************************************************************)
EventuallyAllDeleted == <>[](deleted = VARS)

Properties ==
    /\ EventuallyAllDeleted

=============================================================================
\* Modification History
\* Last modified Thu Apr 09 00:45:19 PDT 2020 by lsf
\* Created Wed Apr 08 13:46:16 PDT 2020 by lsf
