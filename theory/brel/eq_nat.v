Require Import Coq.Arith.Arith.     
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 

Open Scope nat. 

Lemma brel_nat_eq_S : ∀ s t : nat, brel_eq_nat (S s) (S t) = brel_eq_nat s t. 
Proof. unfold brel_eq_nat. induction s; induction t; compute; reflexivity. Qed. 

Lemma brel_nat_neq_S : ∀ s : nat, brel_eq_nat s (S s) = false. 
Proof. unfold brel_eq_nat. induction s. 
          compute; reflexivity. 
          rewrite brel_nat_eq_S. assumption. 
Qed. 

Lemma brel_eq_nat_reflexive : brel_reflexive nat brel_eq_nat. 
Proof. unfold brel_reflexive, brel_eq_nat. induction s; auto. Qed. 

Lemma brel_eq_nat_symmetric : brel_symmetric nat brel_eq_nat. 
Proof. unfold brel_symmetric, brel_eq_nat. 
       induction s; induction t; simpl; intros; auto. Qed. 

Lemma brel_eq_nat_transitive : brel_transitive nat brel_eq_nat. 
Proof. unfold brel_transitive, brel_eq_nat. 
       induction s; induction t; induction u; simpl; intros; auto.        
          discriminate. apply (IHs t u H H0).
Qed. 

Lemma brel_eq_nat_congruence : brel_congruence nat brel_eq_nat brel_eq_nat. 
Proof. unfold brel_congruence. 
       induction s; induction t; induction u; induction v; simpl; intros H Q; auto; discriminate.  
Qed. 

(*
Lemma brel_eq_nat_witness : brel_witness nat brel_eq_nat. 
Proof. unfold brel_witness, brel_eq_nat. exists 0; auto. Defined.

Lemma brel_eq_nat_negate : brel_negate nat brel_eq_nat. 
Proof. unfold brel_negate, brel_eq_nat. exists (S). intro s. split. 
          apply brel_nat_neq_S. 
          apply brel_symmetric_implies_dual. 
          apply brel_eq_nat_symmetric. 
          apply brel_nat_neq_S. 
Defined. 

Definition brel_eq_nat_nontrivial : brel_nontrivial nat brel_eq_nat
:= {| 
      brel_nontrivial_witness   := brel_eq_nat_witness
    ; brel_nontrivial_negate    := brel_eq_nat_negate
   |}. 
 *)


Lemma brel_eq_nat_not_trivial : brel_not_trivial nat brel_eq_nat S.
Proof. intro s. split. 
          apply brel_nat_neq_S. 
          apply brel_symmetric_implies_dual. 
          apply brel_eq_nat_symmetric. 
          apply brel_nat_neq_S. 
Defined. 

(* general lemmas *) 

Lemma beq_nat_to_prop  : ∀ s t: nat, beq_nat s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto; discriminate. Qed. 

Lemma injection_S_brel_eq_nat : ∀ s t : nat, brel_eq_nat s t = true -> brel_eq_nat (S s) (S t) = true. 
Proof. intros s t H. apply beq_nat_to_prop in H.  rewrite H. 
       apply brel_eq_nat_reflexive. 
Qed. 
