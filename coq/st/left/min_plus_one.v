Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min.       (* why am I using min_comm??? *) 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.bs.min_plus.

Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.

Section Theory.

Open Scope nat.

Definition bop_plus_one : binary_op nat :=
λ m n, bop_plus (bop_plus 1 m) n.   


(* (a + 1) + (b min c) = ((a + 1)  + b) min ((a + 1) + c) *) 
Lemma min_plus_one_slt_distributive :
  slt_distributive nat nat brel_eq_nat bop_min bop_plus_one. 
Proof. unfold slt_distributive. intros s t u.
       apply bop_min_plus_left_distributive. 
Qed.        

(* absorption *) 

Lemma min_plus_one_slt_absorptive : 
       slt_absorptive nat nat brel_eq_nat bop_min bop_plus_one. 
Proof. unfold slt_absorptive. intros s t. unfold bop_plus_one. 
       apply bops_min_plus_left_right_absorptive.
Qed. 


End Theory.

Section ACAS.
Open Scope nat.

 
Definition dioid_proofs_min_plus : dioid_proofs nat brel_eq_nat bop_min bop_plus := 
  {| 
     A_dioid_left_distributive      := bop_min_plus_left_distributive
   ; A_dioid_right_distributive     := bop_min_plus_right_distributive
   ; A_dioid_left_left_absorptive   := bops_min_plus_left_left_absorptive
   ; A_dioid_left_right_absorptive  := bops_min_plus_left_right_absorptive
  |}.


End ACAS.

Section MACAS.

Definition A_mcas_min_plus := A_BS_selective_cancellative_pre_dioid_with_one _ A_min_plus. 

End MACAS.
  
Section CAS.

Open Scope nat.

  Definition pann_tid_certs_min_plus : @pann_is_tid_certificates nat := 
{|
  pann_is_tid_plus_times_d := Id_Ann_Cert_None
; pann_is_tid_times_plus   := Assert_Exists_Id_Ann_Equal 0
|}. 



Definition dioid_certs_min_plus : @dioid_certificates nat := 
  {| 
     dioid_left_distributive      := Assert_Left_Distributive 
   ; dioid_right_distributive     := Assert_Right_Distributive 
   ; dioid_left_left_absorptive   := Assert_Left_Left_Absorptive 
   ; dioid_left_right_absorptive  := Assert_Left_Right_Absorptive 
  |}.


Definition min_plus : @selective_cancellative_pre_dioid_with_one nat := 
{|
  selective_cancellative_pre_dioid_with_one_eqv         := eqv_eq_nat 
; selective_cancellative_pre_dioid_with_one_plus        := bop_min
; selective_cancellative_pre_dioid_with_one_times       := bop_plus
; selective_cancellative_pre_dioid_with_one_plus_certs  := sg_CS_wa_certs sg_min
; selective_cancellative_pre_dioid_with_one_times_certs := sg_CK_certs_plus
; selective_cancellative_pre_dioid_with_one_id_ann_certs := pann_tid_certs_min_plus
; selective_cancellative_pre_dioid_with_one_certs       := dioid_certs_min_plus
; selective_cancellative_pre_dioid_with_one_ast         := Ast_min_plus
|}.

End CAS.

Section MCAS.

Definition mcas_min_plus := BS_selective_cancellative_pre_dioid_with_one min_plus. 

End MCAS.
  


Section Verify.

Theorem correct_min_plus : 
  min_plus = A2C_selective_cancellative_pre_dioid_with_one nat (A_min_plus). 
Proof. compute. reflexivity. Qed.


Theorem correct_mcas_min_plus : mcas_min_plus = A2C_mcas_bs nat A_mcas_min_plus.
Proof. compute. reflexivity. Qed. 


End Verify.   
