Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts. 
Require Import CAS.coq.po.from_sg_left. 

Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq. 
Variable trnS : brel_transitive S eq. 


Variable plus     : binary_op S.
Variable times     : binary_op S.

Variable congP : bop_congruence S eq plus.
Variable assoP : bop_associative S eq plus.
Variable idemP : bop_idempotent S eq plus.
Variable commP : bop_commutative S eq plus.

Variable congT : bop_congruence S eq times.

Variable LD : bop_left_distributive S eq plus times.
Variable RD : bop_right_distributive S eq plus times. 

Definition lte := brel_lte_left eq plus.

Notation "a [=] b"   := (eq a b = true)          (at level 15).
Notation "a [+] b"   := (plus a b)          (at level 15).
Notation "a [*] b"   := (times a b)          (at level 15).       


Lemma os_from_bs_left_left_monotone : os_left_monotone S lte times.
Proof. intros a b c. compute. intro A. 
       assert (B := LD a b c).
       assert (C : (a [*] b) [=] (a [*] (b [+] c))).
          apply (congT _ _ _ _ (refS a) A). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        


Lemma os_from_bs_left_right_monotone : os_right_monotone S lte times.
Proof. intros a b c. compute. intro A. 
       assert (B := RD a b c).
       assert (C : (b [*] a) [=] ((b [+] c) [*] a)).
          apply (congT _ _ _ _ A (refS a)). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_left_strictly_monotone : os_left_strictly_monotone S lte times.   
Proof. intros a b c. compute. intros A B. split.
       apply os_from_bs_left_left_monotone; auto. 
       assert (C := LD a b c).
       assert (D := commP b c).
       assert (E := trnS _ _ _ A D).
       apply symS in A. 
       assert (F := congT _ _ _ _ (refS a) A). apply symS in F.
       assert (G := trnS _ _ _ F C). 
End Theory.

Section ACAS.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  