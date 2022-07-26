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
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.times.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.cast_up.
Section Theory.

Open Scope nat.   


(* 
   a * (b + c) = (a * b) + (a * c) 
*) 
Lemma bop_plus_times_left_distributive : 
        bop_left_distributive nat brel_eq_nat bop_plus bop_times.
Proof. 
    unfold bop_plus, bop_times, 
    bop_left_distributive.
    intros ? ? ?.
    rewrite Nat.mul_add_distr_l.
    unfold brel_eq_nat.
    apply Nat.eqb_refl.
Defined.
   

Lemma bop_plus_times_right_distributive : 
        bop_right_distributive nat brel_eq_nat bop_plus bop_times.
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_plus_congruence. 
       apply bop_times_commutative. 
       apply bop_plus_times_left_distributive. 
Defined.



(* absorption *) 

Lemma bops_plus_times_not_left_left_absorptive : 
        bops_not_left_left_absorptive nat brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 

Lemma bops_plus_times_not_left_right_absorptive : 
        bops_not_left_right_absorptive nat brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 

Lemma bops_plus_times_not_right_left_absorptive : 
        bops_not_right_left_absorptive nat brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 

Lemma bops_plus_times_not_right_right_absorptive : 
        bops_not_right_right_absorptive nat brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 

(* strict absorption *)
Lemma bops_plus_times_not_left_strictly_absorptive : 
  bops_not_left_strictly_absorptive nat 
    brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute.
  left. reflexivity.  Defined. 


Lemma bops_plus_times_not_right_strictly_absorptive : 
  bops_not_right_strictly_absorptive nat 
    brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute.
  left. reflexivity.  Defined. 




Lemma bop_plus_times_exists_id_ann_equal : bops_exists_id_ann_equal nat brel_eq_nat bop_plus bop_times.
Proof. exists 0. split. apply bop_plus_zero_is_id. apply bop_times_zero_is_ann. Defined. 

End Theory.

Section ACAS.

Open Scope nat.

Definition semiring_proofs_plus_times : semiring_proofs nat brel_eq_nat bop_plus bop_times := 
  {| 
     A_semiring_left_distributive       := bop_plus_times_left_distributive
   ; A_semiring_right_distributive      := bop_plus_times_right_distributive
   ; A_semiring_left_left_absorptive_d  := inr bops_plus_times_not_left_left_absorptive
   ; A_semiring_left_right_absorptive_d := inr bops_plus_times_not_left_right_absorptive
  |}.

Definition bop_plus_times_pid_is_tann_proofs : pid_is_tann_proofs nat brel_eq_nat bop_plus bop_times := 
{|
  A_pid_is_tann_plus_times   := bop_plus_times_exists_id_ann_equal
; A_pid_is_tann_times_plus_d := Id_Ann_Proof_Id_None _ _ _ _ (bop_times_exists_id, bop_plus_not_exists_ann)
|}.


Definition A_plus_times : A_semiring nat :=
{|
  A_semiring_eqv           := A_eqv_nat 
; A_semiring_plus          := bop_plus
; A_semiring_times         := bop_times 
; A_semiring_plus_proofs   := A_sg_C_proofs_plus
; A_semiring_times_proofs  := sg_proofs_times   
; A_semiring_id_ann_proofs := bop_plus_times_pid_is_tann_proofs
; A_semiring_proofs        := semiring_proofs_plus_times
; A_semiring_ast           := Ast_plus_times 
|}.

End ACAS.

Section MACAS.

Definition A_mcas_plus_times := A_BS_semiring _ A_plus_times. 

End MACAS.
  
Section CAS.

Open Scope nat.

Definition semiring_certs_plus_times : @semiring_certificates nat := 
  {| 
     semiring_left_distributive       := Assert_Left_Distributive
   ; semiring_right_distributive      := Assert_Right_Distributive
   ; semiring_left_left_absorptive_d  := Certify_Not_Left_Left_Absorptive (1, 1)
   ; semiring_left_right_absorptive_d := Certify_Not_Left_Right_Absorptive (1, 1)
  |}.

Definition bop_plus_times_pid_is_tann_certs : @pid_is_tann_certificates nat := 
{|
  pid_is_tann_plus_times   := Assert_Exists_Id_Ann_Equal 0
; pid_is_tann_times_plus_d := Id_Ann_Cert_Id_None 1
|}.

Definition plus_times : @semiring nat :=
{|
  semiring_eqv          := eqv_eq_nat 
; semiring_plus         := bop_plus
; semiring_times        := bop_times 
; semiring_plus_certs   := sg_C_certs_plus
; semiring_times_certs  := sg_certs_times   
; semiring_id_ann_certs := bop_plus_times_pid_is_tann_certs
; semiring_certs        := semiring_certs_plus_times
; semiring_ast          := Ast_plus_times 
|}.
  
End CAS.

Section MCAS.

Definition mcas_plus_times := BS_semiring plus_times. 

End MCAS.
  
Section Verify.

Theorem correct_plus_times : 
  plus_times = A2C_semiring nat A_plus_times. 
Proof. compute. reflexivity. Qed.


Theorem correct_mcas_plus_times : mcas_plus_times = A2C_mcas_bs nat A_mcas_plus_times.
Proof. compute. reflexivity. Qed. 


End Verify.   
