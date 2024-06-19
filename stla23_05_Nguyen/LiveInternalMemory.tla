------------------------ MODULE LiveInternalMemory --------------------------

(***************************************************************************)
(* This module defines LISpec to be specification ISpec of module          *)
(* InternalMemory enhanced with the liveness condition described in the    *)
(* subsection "The Liveness Requirement" of the section "The Memory        *)
(* Specification".                                                         *)
(***************************************************************************)

EXTENDS InternalMemory

vars == <<memInt, mem, ctl, buf>>
  (*************************************************************************)
  (* The tuple of all variables.                                           *)
  (*************************************************************************)
  
Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))
Liveness2 == \A p \in Proc : WF_vars(Do(p) \/ Rsp(p))
  (*************************************************************************)
  (* The two versions of the liveness condition defined in the book.       *)
  (*************************************************************************)
  
LISpec == ISpec /\ Liveness2
  (*************************************************************************)
  (* The spec with liveness.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* The following property asserts that, whenever any processor p has       *)
(* issued a request, so ctl[p] = "req", then a response eventually occurs, *)
(* setting ctl[p] to "rdy".                                                *)
(***************************************************************************)

LivenessProperty == 
   \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")
(*a/ LivenessProperty == 
   \A p \in Proc : (ctl[p] = "rdy") ~> (ctl[p] = "busy") )
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem asserts that specification LISpec satisfies       *)
(* property LivenessProperty.  The accompanying configuration file has TLC *)
(* check this theorem.                                                     *)
(***************************************************************************)
THEOREM ISpec => LivenessProperty
(* b/ change THEOREM ISpec => LivenessProperty    *)


(***************************************************************************)
(* The operator Send is used in specifications in conjuncts of the form    *)
(*                                                                         *)
(* (+)  Send(p, d, memInt, memInt')                                        *)
(*                                                                         *)
(* to specify the new value of memInt.  For TLC to handle such a           *)
(* conjunct, the definition of Send must make (+) equal something of the   *)
(* form                                                                    *)
(*                                                                         *)
(*   memInt' = ...                                                         *)
(*                                                                         *)
(* (A similar observation holds for Reply.)  We define Send so that (+)    *)
(* equals                                                                  *)
(*                                                                         *)
(*   memInt' = <<p, d>>                                                    *)
(*                                                                         *)
(* If we were doing serious model checking, we might try to reduce         *)
(* the state space by letting the value of memInt remain constant,         *)
(* so we would define Send so that (+) equals                              *)
(*                                                                         *)
(*   memInt' = memInt.                                                     *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

(***************************************************************************)
(* We define MCInitMemInt, the set of initial values of memInt, to contain *)
(* the single element <<p, NoVal>>, for an arbitrary processor p.          *)
(***************************************************************************)
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}
=============================================================================
