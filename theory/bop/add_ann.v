Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties.

Section AddAnn. 

Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable bS : binary_op S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable refS : brel_reflexive S rS.
Variable congS : bop_congruence S rS bS.
(* Variable assS : bop_associative S rS bS. *) 

Notation "a <+> b"  := (brel_add_constant b a) (at level 15).
Notation "a [+] b"  := (bop_add_ann b a)       (at level 15).

Lemma bop_add_ann_congruence : bop_congruence (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl; intros H1 H2;auto. Qed. 

Lemma bop_add_ann_associative : bop_associative S rS bS -> bop_associative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros assS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; auto. Qed. 

Lemma bop_add_ann_idempotent : bop_idempotent S rS bS → bop_idempotent (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros idemS [s1 | t1]; simpl; auto. Qed. 

Lemma bop_add_ann_not_idempotent : bop_not_idempotent S rS bS → bop_not_idempotent (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [s P]. exists (inr _ s). simpl. assumption. Defined. 

Lemma bop_add_ann_commutative : bop_commutative S rS bS → bop_commutative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros commS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_commutative : bop_not_commutative S rS bS → bop_not_commutative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t); simpl. assumption. Defined. 

Lemma bop_add_ann_selective : bop_selective S rS bS → bop_selective (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros selS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_selective : bop_not_selective S rS bS → bop_not_selective (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s1 s2] P]. exists (inr _ s1, inr _ s2). simpl. assumption. Defined. 

Lemma bop_add_ann_exists_ann : bop_exists_ann (with_constant S ) (c <+> rS) (c [+] bS).
Proof. exists (inl S c). intros [a | b]; compute; auto. Defined. 

Lemma bop_add_ann_exists_id : bop_exists_id S rS bS -> bop_exists_id (with_constant S ) (c <+> rS) (c [+] bS).
Proof. intros [annS pS]. exists (inr _ annS). intros [s | t]; compute; auto. Defined. 

Lemma bop_add_ann_not_exists_id : bop_not_exists_id S rS bS -> bop_not_exists_id (with_constant S ) (c <+> rS) (c [+] bS).
Proof. intros naS. intros [x | x]. exists (inr _ wS). compute; auto. destruct (naS x) as [y D].  exists (inr _ y). compute. exact D. Defined. 

Lemma bop_add_ann_not_is_left : bop_not_is_left (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. exists (inr _ wS, inl _ c). simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_is_right : bop_not_is_right (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. exists (inl _ c, inr _ wS). simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_left_cancellative : bop_not_left_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))); simpl. destruct (Pf wS) as [L _]. split; auto. Defined. 

Lemma bop_add_ann_not_right_cancellative : bop_not_right_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))); simpl. destruct (Pf wS) as [L _]. split; auto. Defined. 

Lemma bop_add_ann_not_left_constant : bop_not_left_constant (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inr _ wS, (inr _ wS, inl _ c)); simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_right_constant : bop_not_right_constant (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inr _ wS, (inr _ wS, inl _ c)); simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_anti_left : bop_not_anti_left (with_constant S) (c <+> rS) (c [+] bS).
Proof. unfold bop_not_anti_left. exists (inl c, inr wS); simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_anti_right : bop_not_anti_right (with_constant S) (c <+> rS) (c [+] bS).
Proof. unfold bop_not_anti_right. exists (inl c, inr wS); simpl. reflexivity.  Defined.

(* Decide *)

Definition bop_add_ann_idempotent_decide : 
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_ann_idempotent idemS)
   | inr not_idemS => inr _ (bop_add_ann_not_idempotent not_idemS)
   end.  

Definition bop_add_ann_commutative_decide : 
     bop_commutative_decidable S rS bS  → bop_commutative_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_ann_commutative commS)
   | inr not_commS => inr _ (bop_add_ann_not_commutative not_commS)
   end. 

Definition bop_add_ann_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_ann_selective selS)
   | inr not_selS   => inr _ (bop_add_ann_not_selective not_selS)
   end. 

Definition bop_add_ann_exists_id_decide : bop_exists_id_decidable S rS bS  →  bop_exists_id_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl eann  => inl _ (bop_add_ann_exists_id eann)
   | inr neann => inr _ (bop_add_ann_not_exists_id neann)
   end. 

End AddAnn. 