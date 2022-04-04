Require Import Coq.Arith.Arith.     (* beq_nat *)

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.plus. 

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.


Section Compute.

Definition ltr_plus_one : ltr_type nat nat
    := λ l x,  bop_plus (S l) x. 

End Compute.  

Section Theory.  

Open Scope nat.   

Lemma ltr_plus_one_congruence: ltr_congruence nat nat brel_eq_nat brel_eq_nat ltr_plus_one. 
Proof. unfold ltr_congruence.
       intros l1 l2 s1 s2 H1 H2.
       unfold ltr_plus_one.
       apply bop_plus_congruence.
       + unfold brel_eq_nat. unfold Nat.eqb.
         fold (Nat.eqb l1 l2). unfold brel_eq_nat in H1. exact H1. 
       + exact H2.
Qed.

Lemma ltr_plus_one_left_cancellative: ltr_left_cancellative nat nat brel_eq_nat ltr_plus_one. 
Proof. intros l s1 s2 H. unfold ltr_plus_one. 
       assert (A := bop_plus_left_cancellative _ _ _ H).
       exact A.
Qed.


Lemma ltr_plus_one_not_left_constant : ltr_not_left_constant nat nat brel_eq_nat ltr_plus_one. 
Proof. unfold ltr_not_left_constant.
       exists (0, (0, S 0)). compute. 
       reflexivity. 
Defined. 


Lemma ltr_plus_one_not_is_right : ltr_not_is_right nat nat brel_eq_nat ltr_plus_one. 
Proof. unfold ltr_not_is_right.
       exists (0, 0). compute. 
       reflexivity. 
Defined.


Lemma ltr_plus_one_not_exists_id : ltr_not_exists_id nat nat brel_eq_nat ltr_plus_one. 
Proof. unfold ltr_not_exists_id.
       intro l.  unfold ltr_not_is_id, ltr_plus_one. 
       exists 0. compute.
       reflexivity. 
Defined.

Lemma ltr_plus_one_not_exists_ann : ltr_not_exists_ann nat nat brel_eq_nat ltr_plus_one. 
Proof. unfold ltr_not_exists_ann.
       intro s.  unfold ltr_not_is_ann, ltr_plus_one. 
       exists 0. unfold brel_eq_nat. unfold bop_plus.
Admitted. 



End Theory.

Section ACAS.


Definition ltr_plus_one_proofs : left_transform_proofs nat nat brel_eq_nat brel_eq_nat ltr_plus_one := 
{|
  A_left_transform_congruence          := ltr_plus_one_congruence 
; A_left_transform_is_right_d          := inr ltr_plus_one_not_is_right
; A_left_transform_left_constant_d     := inr ltr_plus_one_not_left_constant 
; A_left_transform_left_cancellative_d := inl ltr_plus_one_left_cancellative
|}.


Definition A_left_transform_plus_one : A_left_transform nat nat :=
{|
  A_left_transform_carrier      := A_eqv_nat 
; A_left_transform_label        := A_eqv_nat 
; A_left_transform_ltr          := ltr_plus_one 
; A_left_transform_exists_id_d  := inr ltr_plus_one_not_exists_id
; A_left_transform_exists_ann_d := inr ltr_plus_one_not_exists_ann 
; A_left_transform_proofs       := ltr_plus_one_proofs
; A_left_transform_ast          := Ast_ltr_plus_one
|}.

  
End ACAS. 


Section ACAS.

Open Scope nat.
  
Definition ltr_plus_one_certs : @left_transform_certificates nat nat := 
{|
  left_transform_congruence          := Assert_Ltr_Congruence 
; left_transform_is_right_d          := Certify_Ltr_Not_Is_Right (0, 0) 
; left_transform_left_constant_d     := Certify_Ltr_Not_Left_Constant (0, (0, S 0))
; left_transform_left_cancellative_d := Certify_Ltr_Left_Cancellative 
|}.


Definition left_transform_plus_one : @left_transform nat nat :=
{|
  left_transform_carrier      := eqv_eq_nat 
; left_transform_label        := eqv_eq_nat 
; left_transform_ltr          := ltr_plus_one 
; left_transform_exists_id_d  := Certify_Ltr_Not_Exists_Id
; left_transform_exists_ann_d := Certify_Ltr_Not_Exists_Ann 
; left_transform_certs        := ltr_plus_one_certs
; left_transform_ast          := Ast_ltr_plus_one
|}.
  
End ACAS. 


Section Verify.

Theorem correct_ltr_plus_one :
    left_transform_plus_one = A2C_left_transform nat nat A_left_transform_plus_one. 
Proof. compute. reflexivity. Qed. 

End Verify.   


