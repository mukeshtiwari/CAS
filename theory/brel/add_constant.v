Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop.
Require Import CAS.theory.brel_properties. 

Section AddConstant. 

Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable wS : S. 
Variable conS : brel_congruence S rS rS.
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

Notation "a <+> b"  := (brel_add_constant b a) (at level 15).

Lemma brel_add_constant_congruence : 
       brel_congruence S rS rS → brel_congruence (with_constant S) (c <+> rS) (c <+> rS). 
Proof. unfold brel_congruence. 
     intros congS [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto. 
     discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
Qed. 




(*
Lemma brel_add_constant_witness : (brel_witness S rS) → brel_witness (with_constant S) (c <+> rS). 
Proof. intros [s Ps]. exists (inr _ s). simpl. rewrite Ps. reflexivity. Defined. 

Lemma brel_add_constant_negate : (brel_witness S rS) → brel_negate (with_constant S) (c <+> rS). 
Proof. intros [s Ps]. exists (λ (d : with_constant S), match d with | inl _ => inr _ s  | inr _ => inl S c end).
       induction s0; simpl; auto. 
Defined. 

Definition brel_add_constant_nontrivial : (brel_nontrivial S rS) → brel_nontrivial (with_constant S) (c <+> rS)
:= λ ntS, 
   let wS := brel_nontrivial_witness S rS ntS in 
     {| 
        brel_nontrivial_witness  := brel_add_constant_witness wS
      ; brel_nontrivial_negate   := brel_add_constant_negate wS
     |} .
 *)

Lemma brel_add_constant_not_trivial : brel_not_trivial (with_constant S) (c <+> rS)
                                                       (λ (d : with_constant S), match d with | inl _ => inr _ wS  | inr _ => inl S c end). 
Proof. intro s. induction s; simpl; auto. Qed. 


Lemma brel_add_constant_reflexive : brel_reflexive (with_constant S) (c <+> rS). 
Proof. intros [a | b]; simpl. reflexivity. apply refS. Qed. 

Lemma brel_add_constant_symmetric : brel_symmetric (with_constant S) (c <+> rS). 
Proof.  intros [c1 | s1] [c2 | s2]; simpl; intro H; auto. Qed. 

Lemma brel_add_constant_transitive : brel_transitive (with_constant S) (c <+> rS). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros H1 H2; auto. discriminate. apply (tranS _ _ _ H1 H2). Qed. 

Lemma brel_add_constant_rep_correct : ∀ (rep : unary_op S), brel_rep_correct S rS rep →
                                       brel_rep_correct (with_constant S) (c <+> rS) (uop_with_constant rep).
Proof. intros rep P [a | b]. simpl. reflexivity. simpl. apply P. Qed. 

Lemma brel_add_constant_rep_idempotent : ∀ (rep : unary_op S), brel_rep_idempotent S rS rep →
                                       brel_rep_idempotent (with_constant S) (c <+> rS) (uop_with_constant rep).
Proof. intros rep P [a | b]; simpl. reflexivity. apply P. Qed. 

End AddConstant. 

