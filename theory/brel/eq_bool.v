Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 

Lemma eqb_bool_to_prop  : ∀ s t: bool, eqb s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto. Qed. 

Lemma brel_eq_bool_witness : brel_witness bool brel_eq_bool. 
Proof. unfold brel_witness, brel_eq_bool. exists true; auto. Defined.

Lemma brel_eq_bool_negate : brel_negate bool brel_eq_bool. 
Proof. unfold brel_negate, brel_eq_bool. exists (negb). induction s; auto. Defined.

Definition brel_eq_bool_nontrivial : brel_nontrivial bool brel_eq_bool
:= {| 
      brel_nontrivial_witness   := brel_eq_bool_witness
    ; brel_nontrivial_negate    := brel_eq_bool_negate
   |}. 

Lemma brel_eq_bool_reflexive : brel_reflexive bool brel_eq_bool. 
Proof. unfold brel_reflexive, brel_eq_bool. induction s; simpl; auto. 
Qed. 

Lemma brel_eq_bool_symmetric : brel_symmetric bool brel_eq_bool. 
Proof. unfold brel_symmetric, brel_eq_bool. 
       induction s; induction t; simpl; intros; auto. 
Qed. 

Lemma brel_eq_bool_transitive : brel_transitive bool brel_eq_bool. 
Proof. unfold brel_transitive, brel_eq_bool. 
       induction s; induction t; simpl; intros u H1 H2; destruct u; auto. 
Qed. 

Lemma brel_eq_bool_congruence : brel_congruence bool brel_eq_bool brel_eq_bool. 
Proof. induction s; induction t; induction u; induction v; intros H Q; auto. Qed. 

