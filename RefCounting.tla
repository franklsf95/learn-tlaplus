---------------------------- MODULE RefCounting ----------------------------
(***************************************************************************
  At each step, one of the following actions can happen:
  - An object gets created.
  - An object takes a reference of another object.
  - An object releases its reference of another object.
  - An object gets deleted, if no other object references it.

  Temporal property to check:
  - Eventually all objects should be deleted (garbage-collected).

  The model checker should fail by detecting a retain cycle situation.
 ***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS MAX_OBJS

VARIABLES nextObjectId, objects, deletedObjects, refHolders, formerRefHolders

vars == <<nextObjectId, objects, deletedObjects, refHolders, formerRefHolders>>
-----------------------------------------------------------------------------

TypeOK ==
    /\ nextObjectId \in Int
    /\ nextObjectId <= MAX_OBJS + 1
    /\ refHolders \in [objects -> SUBSET objects]
    /\ formerRefHolders \in [objects -> SUBSET (objects \union deletedObjects)]
    /\ deletedObjects \intersect objects = {}
    /\ Cardinality(objects) <= MAX_OBJS
    /\ Cardinality(deletedObjects) <= MAX_OBJS
    /\ Cardinality(objects \union deletedObjects) <= MAX_OBJS

Init ==
    /\ nextObjectId = 1
    /\ objects = {}
    /\ deletedObjects = {}
    /\ refHolders = [v \in {} |-> {}]
    /\ formerRefHolders = [v \in {} |-> {}]
-----------------------------------------------------------------------------

\* Create a new object
CreateObject ==
    /\ Cardinality(objects \union deletedObjects) < MAX_OBJS
    /\ objects' = objects \union {nextObjectId}
    /\ refHolders' = [v \in objects' |-> IF v \in objects THEN refHolders[v] ELSE {}]
    /\ formerRefHolders' = [v \in objects' |-> IF v \in objects THEN formerRefHolders[v] ELSE {}]
    /\ nextObjectId' = nextObjectId + 1
    /\ UNCHANGED <<deletedObjects>>

\* Let p hold a reference onto c
AddRef(p, c) ==
    /\ p /= c
    /\ p \notin refHolders[c]
    /\ p \notin formerRefHolders[c]
    /\ refHolders' = [refHolders EXCEPT ![c] = refHolders[c] \union {p}]
    /\ UNCHANGED <<nextObjectId, objects, deletedObjects, formerRefHolders>>

\* Remove p's reference of c
RemoveRef(p, c) ==
    /\ p /= c
    /\ p \in refHolders[c]
    /\ refHolders' = [refHolders EXCEPT ![c] = refHolders[c] \ {p}]
    /\ formerRefHolders' = [formerRefHolders EXCEPT ![c] = formerRefHolders[c] \union {p}]
    /\ UNCHANGED <<nextObjectId, objects, deletedObjects>>

\* If v is not referenced by anyone, delete it, and remove its reference to anything.
Delete(v) ==
    /\ refHolders[v] = {}
    /\ objects' = objects \ {v}
    /\ deletedObjects' = deletedObjects \union {v}
    /\ refHolders' = [c \in objects' |-> IF v \in refHolders[c] THEN refHolders[c] \ {v} ELSE refHolders[c]]
    /\ formerRefHolders' = [c \in objects' |-> IF v \in refHolders[c] THEN formerRefHolders[c] \union {v} ELSE formerRefHolders[c]]
    /\ UNCHANGED <<nextObjectId>>

AddRefAny == \E p \in objects : \E c \in objects : AddRef(p, c)

RemoveRefAny == \E p \in objects : \E c \in objects : RemoveRef(p, c)

DeleteAny == \E v \in objects : Delete(v)

Next ==
    \/ CreateObject
    \/ AddRefAny
    \/ RemoveRefAny
    \/ DeleteAny

Spec == Init /\ [][Next]_vars /\ WF_vars(DeleteAny)

-----------------------------------------------------------------------------
(***************************************************************************
  Property to Check: Eventually all variables will be deleted.
  But this is not true, because this spec permits retain cycles.
 ***************************************************************************)
EventuallyAllDeleted == <>[](objects = {} /\ deletedObjects /= {})

Properties ==
    /\ EventuallyAllDeleted

=============================================================================
\* Modification History
\* Last modified Sun Apr 19 22:40:11 PDT 2020 by lsf
\* Created Wed Apr 08 13:46:16 PDT 2020 by lsf
