Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.conjunction. 
Require Import CAS.theory.brel.complement. 
Require Import CAS.theory.facts. 

Section Rlte.

Variable S : Type.
Variable r : brel S.
Variable b : binary_op S.

Variable symS : brel_symmetric S r.
Variable refS : brel_reflexive S r.
Variable tranS : brel_transitive S r.

Variable assS : bop_associative S r b.
Variable b_cong : bop_congruence S r b. 

Notation "x == y"  := (r x y = true)              (at level 30).
Notation "x != y"  := (r x y = false)             (at level 15).
Notation "x <<= y" := (brel_rlte r b x y = true)  (at level 15).
Notation "x !<= y" := (brel_rlte r b x y = false) (at level 15).
Notation "x @ y"   := (b x y)                     (at level 15).


Lemma brel_rlte_reflexive : bop_idempotent S r b -> brel_reflexive S (brel_rlte r b). 
Proof. intros idemS s. assert(id := idemS s). apply symS. assumption. Defined. 

Lemma brel_rlte_congruence : ∀ (r1 : brel S) (r2 : brel S),
       brel_congruence S r1 r2 -> 
       bop_congruence S r1 b -> 
         brel_congruence S r1 (brel_rlte r2 b). 
Proof. unfold brel_congruence, bop_congruence, brel_rlte. 
       intros r1 r2 r_cong cong s t u v H1 H2. 
       assert (H3 := cong _ _ _ _ H1 H2). 
       assert (H4 := r_cong _ _ _ _ H2 H3). 
       assumption. 
Defined. 


(*
   s <= t    -> t <= u    -> s <= u
   t = s + t -> u = t + u -> u = s + u
   u = t + u = ((s + t) + u) = (s + (t + u)) = s + u
*) 
Lemma brel_rlte_transitive : brel_transitive S (brel_rlte r b). 
Proof. intros s t u H1 H2. 
       assert (fact1 : r u (b (b s t) u ) = true). 
          assert (C := b_cong _ _ _ _ H1 (refS u)). 
          apply (tranS _ _ _ H2 C). 
       assert (fact2 : r u (b s (b t u)) = true).
          assert (A := assS s t u). 
          apply (tranS _ _ _ fact1 A). 
       assert (fact3 : r u (b s u) = true). 
          assert (C := b_cong _ _ _ _ (refS s) H2). apply symS in C. 
          apply (tranS _ _ _ fact2 C). 
       assumption. 
Defined. 


Lemma brel_rlte_antisymmetric : bop_commutative S r b -> brel_antisymmetric S r (brel_rlte r b). 
Proof. intros commS s t H1 H2. 
       assert (fact1 := commS t s). 
       assert (fact2 := tranS _ _ _ H2 fact1). apply symS in H1. 
       apply (tranS _ _ _ fact2 H1). 
Defined. 

Lemma brel_rlte_total : bop_commutative S r b -> bop_selective S r b -> brel_total S (brel_rlte r b). 
Proof. intros commS selS s t. 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       destruct (selS s t) as [Q | Q]. 
          right. apply symS in Q. apply (tranS _ _ _ Q fact1). 
          left. apply symS. assumption. 
Defined. 

Lemma brel_rlte_not_total : bop_commutative S r b -> bop_not_selective S r b -> brel_not_total S (brel_rlte r b). 
Proof. intros commS [ [s t] P]. 
       exists (s, t). 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       destruct P as [P1 P2]. 
       split. 
          apply (brel_symmetric_implies_dual _ _ symS) in P2. assumption. 
          assert(fact2 := brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 P1).
          apply (brel_symmetric_implies_dual _ _ symS) in fact2. assumption. 
Defined. 

Definition brel_rlte_total_decide : 
     bop_commutative S r b -> bop_selective_decidable S r b -> brel_total_decidable S (brel_rlte r b)
:= λ commS d, 
   match d with 
   | inl selS     => inl _ (brel_rlte_total commS selS)
   | inr not_selS => inr _ (brel_rlte_not_total commS not_selS) 
   end. 

Lemma brel_rlte_exists_top : bop_exists_ann S r b -> brel_exists_top S (brel_rlte r b). 
Proof.  intros [t P]. exists t. intro s. destruct (P s) as [L R]. compute. apply symS. assumption. Defined. 


Lemma brel_rlte_not_exists_top : bop_commutative S r b -> bop_not_exists_ann S r b -> brel_not_exists_top S (brel_rlte r b). 
Proof.  intros commS P s. exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           assert (fact1 := commS s w). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 F).
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
Defined. 

Definition brel_rlte_exists_top_decide : 
     bop_commutative S r b -> bop_exists_ann_decidable S r b -> brel_exists_top_decidable S (brel_rlte r b)
:= λ commS d, 
   match d with 
   | inl idS     => inl _ (brel_rlte_exists_top idS)
   | inr no_annS => inr _ (brel_rlte_not_exists_top commS no_annS) 
   end. 


Lemma brel_rlte_exists_bottom : bop_exists_id S r b -> brel_exists_bottom S (brel_rlte r b). 
Proof.  intros [t P]. exists t. intro s. destruct (P s) as [L R]. compute. apply symS. assumption. Defined. 

Lemma brel_rlte_not_exists_bottom : 
             bop_commutative S r b -> bop_not_exists_id S r b -> brel_not_exists_bottom S (brel_rlte r b). 
Proof.  intros commS P s. exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
           assert (fact1 := commS w s). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 F).
Defined. 

Definition brel_rlte_exists_bottom_decide : 
     bop_commutative S r b -> bop_exists_id_decidable S r b -> brel_exists_bottom_decidable S (brel_rlte r b)
:= λ commS d, 
   match d with 
   | inl annS   => inl _ (brel_rlte_exists_bottom annS)
   | inr no_idS => inr _ (brel_rlte_not_exists_bottom commS no_idS) 
   end. 

End Rlte.


