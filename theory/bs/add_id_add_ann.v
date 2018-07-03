Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties. 

Section AddIdAnn.

  Variable S : Type.
  Variable r : brel S.
  Variable c : cas_constant.
  Variable b1 b2 : binary_op S.

  Variable wS : S. 
  Variable refS : brel_reflexive S r. 
  Variable symS : brel_symmetric S r.

Notation "a <+> b"    := (brel_add_constant b a) (at level 15).
Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).


Lemma bops_add_id_add_ann_id_equals_ann : bops_id_equals_ann (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).   
Proof. unfold bops_id_equals_ann. 
       assert (is_id : bop_is_id (with_constant S) (c <+> r) (c [+id] b1) (inl c)). 
           intros [c' | s ]; compute; auto. 
       assert (is_ann : bop_is_ann (with_constant S) (c <+> r) (c [+ann] b2) (inl c)). 
           intros [c' | s ]; compute; auto. 
       exists (inl _ c). split; assumption. 
Defined. 

Lemma bops_add_id_add_ann_ann_equals_id :    
      bops_id_equals_ann S r b2 b1 -> 
           bops_id_equals_ann (with_constant S) (c <+> r) (c [+ann] b2) (c [+id] b1).
Proof. unfold bops_id_equals_ann. 
       intros [i [Pi Pa]].
       assert (is_id : bop_is_id (with_constant S) (c <+> r) (c [+ann] b2) (inr i)). 
           intros [c' | s ]; compute; auto. 
       assert (is_ann : bop_is_ann (with_constant S) (c <+> r) (c [+id] b1) (inr i)). 
           intros [c' | s ]; compute; auto. 
       exists (inr _ i). split; assumption. 
Defined. 


Lemma bops_add_id_add_ann_not_ann_equals_id :    
      bops_not_id_equals_ann S r b2 b1 -> 
           bops_not_id_equals_ann (with_constant S) (c <+> r) (c [+ann] b2) (c [+id] b1) .
Proof. unfold bops_not_id_equals_ann. 
       intros H [ci | s'].
       destruct (H wS) as [ [s' [P | Q] ] | [s' [P | Q] ] ]. 
       left. exists (inr _ s'). compute. left. reflexivity. 
       left. exists (inr _ s'). compute. left. reflexivity. 
       right. exists (inr _ s'). compute. left. reflexivity.
       right. exists (inr _ s'). compute. left. reflexivity.
       destruct (H s') as [ [s'' [P | Q] ] | [s'' [P | Q] ] ]. 
       left. exists (inr _ s''). compute. rewrite P. left. reflexivity. 
       left. exists (inr _ s''). compute. rewrite Q. right. reflexivity. 
       right. exists (inr _ s''). compute. rewrite P. left. reflexivity.
       right. exists (inr _ s''). compute. rewrite Q. right. reflexivity.
Defined. 


Lemma bops_add_id_add_ann_left_distributive  :
     bop_left_distributive S r b1 b2 ->   
        bop_left_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_distributive  : 
     bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 [s2 s3]] nldS]. 
       exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 

Lemma bops_add_id_add_ann_right_distributive  : 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_distributive  : 
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 [s2 s3]] nldS]. exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 
       

(* left left *) 
Lemma bops_add_id_add_ann_left_left_absorptive  : 
     bops_left_left_absorptive S r b1 b2 -> 
        bops_left_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2). 
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_left_absorptive : 
     bops_not_left_left_absorptive S r b1 b2 -> 
        bops_not_left_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

(* left right *) 
Lemma bops_add_id_add_ann_left_right_absorptive  : 
     bops_left_right_absorptive S r b1 b2 -> 
        bops_left_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_right_absorptive : 
     bops_not_left_right_absorptive S r b1 b2 -> 
        bops_not_left_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right left *) 
Lemma bops_add_id_add_ann_right_left_absorptive  : 
     bops_right_left_absorptive S r b1 b2 -> 
        bops_right_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_left_absorptive : 
     bops_not_right_left_absorptive S r b1 b2 -> 
        bops_not_right_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right right *) 
Lemma bops_add_id_add_ann_right_right_absorptive  : 
     bops_right_right_absorptive S r b1 b2 -> 
        bops_right_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_right_absorptive : 
     bops_not_right_right_absorptive S r b1 b2 -> 
        bops_not_right_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

(* experiment 

Lemma bops_add_id_add_ann_left_left_dependent_distributive  : 
     bops_left_left_dependent_distributive S r b1 b2 -> 
        bops_left_left_dependent_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; intro H; auto. Qed.
*) 

(* Decide *)

Definition bops_add_zero_left_distributive_decide : 
     bop_left_distributive_decidable S r b1 b2 -> 
         bop_left_distributive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_distributive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_distributive nldS)
   end. 

Definition bops_add_zero_right_distributive_decide : 
     bop_right_distributive_decidable S r b1 b2 -> 
        bop_right_distributive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_distributive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_distributive nldS)
   end. 


Definition bops_add_zero_left_left_absorptive_decide : 
     bops_left_left_absorptive_decidable S r b1 b2 -> 
        bops_left_left_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_left_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_left_absorptive nldS)
   end. 

Definition bops_add_zero_left_right_absorptive_decide : 
     bops_left_right_absorptive_decidable S r b1 b2 -> 
        bops_left_right_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_right_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_right_absorptive nldS)
   end. 


Definition bops_add_zero_right_left_absorptive_decide : 
     bops_right_left_absorptive_decidable S r b1 b2 -> 
        bops_right_left_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_left_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_left_absorptive nldS)
   end. 

Definition bops_add_zero_right_right_absorptive_decide : 
     bops_right_right_absorptive_decidable S r b1 b2 -> 
        bops_right_right_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_right_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_right_absorptive nldS)
   end.


Definition bops_add_zero_ann_equals_id_decide :
     bops_id_equals_ann_decidable S r b2 b1 -> 
        bops_id_equals_ann_decidable (with_constant S) (c <+> r) (c [+ann] b2) (c [+id] b1)
:= λ dS, 
   match dS with 
   | inl pS  => inl _ (bops_add_id_add_ann_ann_equals_id pS)
   | inr npS => inr _ (bops_add_id_add_ann_not_ann_equals_id npS)
   end. 


End AddIdAnn.