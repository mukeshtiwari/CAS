Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.
Require Import CAS.coq.sg.minset_lift.

Section Theory.
Variable S  : Type. 
Variable rS : brel S.

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S.
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 

(*Definition bop_minset_union : binary_op (finite_set S)
  := bop_full_reduce (uop_minset rS lteS) (bop_union rS).

*) 
Definition sltr_distributive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition sltr_not_distributive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition sltr_distributive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_distributive S L r add ltr) + (sltr_not_distributive S L r add ltr). 
 
Definition sltr_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition sltr_not_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition sltr_absorptive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_absorptive S L r add ltr) + (sltr_not_absorptive S L r add ltr). 


Definition sltr_strictly_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), (bop_not_is_id S r add s) -> ((r s (add s (ltr l s)) = true) * (r s (add s (ltr l s)) = false)).

Definition sltr_not_strictly_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  (bop_not_is_id S r add s) * ((r s (add s (ltr l s)) = false)  +  (r s (add s (ltr l s)) = true)) end }. 

Definition sltr_strictly_absorptive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_strictly_absorptive S L r add ltr) + (sltr_not_strictly_absorptive S L r add ltr). 
  

End Theory.

Section ACAS.

Record ltr_proofs (S L : Type) (eqS : brel S) (eqL : brel L) (ltr : L -> (S -> S)) := 
{
  A_ltr_congruence          : ltr_congruence L S eqL eqS ltr
; A_ltr_is_right_d          : ltr_is_right_decidable L S eqS ltr
; A_ltr_exists_id_d         : ltr_exists_id_decidable L S eqS ltr
; A_ltr_left_cancellative_d : ltr_left_cancellative_decidable L S eqS ltr
}.

Record A_sltr_CI (S L : Type) :=
{
  A_sltr_CI_carrier      : A_eqv S
; A_sltr_CI_label        : A_eqv L
; A_sltr_CI_plus         : binary_op S                                               
; A_sltr_CI_trans        : left_transform L S (* L -> (S -> S) *)
; A_sltr_CI_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_sltr_CI_carrier) A_sltr_CI_plus                                 
; A_sltr_CI_trans_proofs : ltr_proofs S L (A_eqv_eq S A_sltr_CI_carrier) (A_eqv_eq L A_sltr_CI_label)  A_sltr_CI_trans
; A_sltr_CI_proofs       : sltr_proofs S L (A_eqv_eq S A_sltr_CI_carrier) A_sltr_CI_plus A_sltr_CI_trans                                  
; A_sltr_CI_ast          : cas_ast 
}.
  


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  