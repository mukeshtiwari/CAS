Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.
Require Import CAS.coq.theory.reduction.classical.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.minset_union.
Require Import CAS.coq.sg.minset_lift.

Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S.
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 
(*Variable lteAntiSym : brel_antisymmetric S rS lteS. *)

Variable bS : binary_op S.
Variable assoc_bS : bop_associative S rS bS. 
Variable cong_bS : bop_congruence S rS bS.
Notation "a [=] b"   := (rS a b = true)          (at level 15).
Notation "a [!=] b"  := (rS a b = false)          (at level 15).
Notation "a [=S] b"  := (brel_set rS a b = true)         (at level 15).
Notation "a [=MS] b" := (brel_minset rS lteS a b = true)        (at level 15).

Notation "a [in] b"  := (in_set rS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set rS b a = false)   (at level 15).
Notation "a [<=] b"  := (lteS a b = true)        (at level 15).
Notation "a [!<=] b" := (lteS a b = false)       (at level 15).
Notation "a [!<] b"  := (not_below rS lteS b a =true)       (at level 15).

Notation  "a [U] b"     := (bop_union rS a b) (at level 15).
Notation  "a [msl] b"   := (bop_minset_lift S rS lteS bS a b) (at level 15).
Notation  "a [msu] b"   := (bop_minset_union S rS lteS a b) (at level 15).
Notation  "a [lift] b"  := (bop_lift rS bS a b) (at level 15).

Notation "[ms] a"       := (uop_minset rS lteS a) (at level 15).

(* try to follow this

  (X [msl] (Y [msu] Z)) 
= [ms] (X [lift] ([ms] (Y [U] Z)))
= [ms] (X [lift] (Y [U] Z))
= [ms] ((X [lift] Y) [U] (X [lift] Z))
= [ms] ((X [lift] Y) [U] (X [lift] Z))
= [ms] ((X [lift] Y) [U] ms(X [lift] Z))
= [ms] (([ms] (X [lift] Y)) [U] ([ms] (X [lift] Z)))

= ((X [msl] Y) [msu] (X [msl] Z)) 

*) 

Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.

Lemma equiv_1 (X Y Z : finite_set S) :
  (X [msl] (Y [msu] Z)) [=S] ((X [msl] Y) [msu] (X [msl] Z)).
Proof.
  assert (H1 : (X [msl] (Y [msu] Z)) [=S] ([ms] (X [lift] [ms] (Y [U] Z)))).
     unfold bop_minset_lift. unfold bop_full_reduce.
     unfold bop_minset_union. unfold bop_full_reduce.
     admit. 
  
  assert (H2 : (([ms] (X [lift] [ms] (Y [U] Z))) [=S] ([ms] (X [lift] ([ms] (Y [U] Z)))))).  admit.               

  assert (H3 : (([ms] (X [lift] ([ms] (Y [U] Z)))) [=S] ([ms] (X [lift] (Y [U] Z))))). admit.

  assert (H4 : (([ms] (X [lift] (Y [U] Z))) [=S] ([ms] ((X [lift] Y) [U] (X [lift] Z))))). admit.

  assert (H5 : (([ms] ((X [lift] Y) [U] (X [lift] Z))) [=S] ([ms] ((X [lift] Y) [U] (X [lift] Z))))). admit.

  assert (H6 : (([ms] ((X [lift] Y) [U] (X [lift] Z))) [=S] ([ms] ((X [lift] Y) [U] (X [lift] Z))))). admit.

  assert (H7 : (([ms] ((X [lift] Y) [U] (X [lift] Z))) [=S] ([ms] ((X [lift] Y) [U] [ms] (X [lift] Z))))). admit.

  assert (H8 : (([ms] ((X [lift] Y) [U] [ms](X [lift] Z))) [=S] ([ms] (([ms] (X [lift] Y)) [U] ([ms] (X [lift] Z)))))). admit.

  assert (H9 : (([ms] (([ms] (X [lift] Y)) [U] ([ms] (X [lift] Z)))) [=S] ((X [msl] Y) [msu] (X [msl] Z)))). admit.                    

  assert (C2 := set_transitive _ _ _ H1 H2). 
  assert (C3 := set_transitive _ _ _ C2 H3).
  assert (C4 := set_transitive _ _ _ C3 H4).
  assert (C5 := set_transitive _ _ _ C4 H5).
  assert (C6 := set_transitive _ _ _ C5 H6).  
  assert (C7 := set_transitive _ _ _ C6 H7).
  assert (C8 := set_transitive _ _ _ C7 H8).
  assert (C9 := set_transitive _ _ _ C8 H9).

  exact C9. 
Admitted. 

Lemma equiv_2 (X Y Z : finite_set S) :
  ((Y [msu] Z) [msl] X) [=S] ((Y [msl] X) [msu] (Z [msl] X)).
Admitted. 

Lemma ld_inclusion_left 
   (X Y Z : finite_set S) 
   (s : S) 
   (H1 : s [in] uop_minset rS lteS (X [msl] (Y [msu] Z))) : 
  s [in] uop_minset rS lteS ((X [msl] Y) [msu] (X [msl] Z)). 
Admitted. 

Lemma ld_inclusion_right 
   (X Y Z : finite_set S) 
   (s : S) 
   (H1 : s [in] uop_minset rS lteS ((X [msl] Y) [msu] (X [msl] Z))): 
  s [in] uop_minset rS lteS (X [msl] (Y [msu] Z)). 
Admitted. 


Lemma rd_inclusion_left 
   (X Y Z : finite_set S) 
   (s : S) 
   (H1 : s [in] uop_minset rS lteS ((Y [msu] Z) [msl] X)) : 
   s [in] uop_minset rS lteS ((Y [msl] X) [msu] (Z [msl] X)). 
Admitted. 

Lemma rd_inclusion_right 
   (X Y Z : finite_set S) 
   (s : S)
   (H1 : s [in] uop_minset rS lteS ((Y [msl] X) [msu] (Z [msl] X))): 
  s [in] uop_minset rS lteS ((Y [msu] Z) [msl] X). 
Admitted. 


Lemma bop_minset_union_lift_left_distributive : 
        bop_left_distributive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. unfold bop_left_distributive. 
       intros X Y Z. 
       apply brel_minset_intro; auto.
       intro s. split; intro H1.
          apply ld_inclusion_left; auto. 
          apply ld_inclusion_right; auto.
Qed.           


Lemma bop_minset_union_lift_right_distributive : 
        bop_right_distributive (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS). 
Proof. unfold bop_right_distributive. 
       intros X Y Z. 
       apply brel_minset_intro; auto.
       intro s. split; intro H1.
          apply rd_inclusion_left; auto. 
          apply rd_inclusion_right; auto.
Qed.           




End Theory.

Section ACAS.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  