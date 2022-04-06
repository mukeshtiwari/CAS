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
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.cast_up.
Section Theory.

Open Scope nat.   

Lemma min_add : ∀ u s : nat, min (u + s) s = s. 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 


(* a + (b min c) = (a + b) min (a + c) *) 
Lemma bop_min_plus_left_distributive : 
        bop_left_distributive nat brel_eq_nat bop_min bop_plus. 
Proof. unfold bop_left_distributive, bop_plus, bop_min. 
       induction s. 
          intros t u. simpl. apply brel_eq_nat_reflexive.
          induction t. 
             simpl. rewrite plus_comm. simpl. intro u.  
             rewrite Min.min_comm. rewrite plus_comm. rewrite min_add. 
             apply brel_eq_nat_reflexive.
             induction u. 
                simpl. rewrite plus_comm. simpl. rewrite plus_comm. rewrite min_add. 
                apply brel_eq_nat_reflexive.
                rewrite plus_SS.  rewrite plus_SS. rewrite bop_min_S.  rewrite bop_min_S. 
                rewrite plus_SS.  apply injection_S_brel_eq_nat. apply IHs. 
Qed. 

Lemma bop_min_plus_right_distributive : 
        bop_right_distributive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bop_min_plus_left_distributive. 
Defined. 

Lemma plus_lemma_1 : ∀ (a b : nat), plus a b = b -> a = 0. 
Proof. induction a. 
          auto. 
          induction b; intro H. 
             rewrite plus_comm in H. simpl in H. assumption. 
             elim IHb; auto.              
             assert (F: S a + S b = S (S a + b)). 
                rewrite plus_comm at 1. 
                rewrite plus_Sn_m at 1. 
                rewrite plus_comm at 1. reflexivity. 
             rewrite F in H.  apply injective_S in H. assumption.              
Defined.

       
(* absorption *) 

Lemma bops_min_plus_left_left_absorptive : 
        bops_left_left_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. unfold bops_left_left_absorptive, bop_plus, bop_min, brel_eq_nat. 
       (* ugly --- cleanup ... *) 
       induction s. intro t. compute. reflexivity. 
       induction t. rewrite plus_comm. unfold plus. 
       assert (A := bop_min_idempotent). 
       unfold bop_idempotent in A. 
       assert (B := brel_eq_nat_symmetric). unfold brel_symmetric in B. 
       rewrite B. reflexivity. apply A. 
       rewrite plus_comm. rewrite min_comm. rewrite min_add. 
       apply brel_eq_nat_reflexive. 
Qed. 


Lemma bops_min_plus_left_right_absorptive  : 
       bops_left_right_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_left_absorptive_implies_left_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bops_min_plus_left_left_absorptive. 
Qed. 


Lemma bops_min_plus_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_min_commutative. 
       apply bop_plus_commutative. 
       apply bops_min_plus_left_right_absorptive. 
Qed. 



Lemma bops_min_plus_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bops_min_plus_right_left_absorptive. 
Qed.


Lemma bop_min_plus_exists_id_ann_equal : bops_exists_id_ann_equal nat brel_eq_nat bop_plus bop_min.
Proof. exists 0. split. apply bop_plus_zero_is_id. apply bop_min_zero_is_ann. Defined. 

End Theory.

Section ACAS.
Open Scope nat.

Definition bop_min_plus_pann_tid_proofs : pann_is_tid_proofs nat brel_eq_nat bop_min bop_plus := 
{|
  A_pann_is_tid_plus_times_d := Id_Ann_Proof_None _ _ _ _ (bop_min_not_exists_id, bop_plus_not_exists_ann)
; A_pann_is_tid_times_plus   := bop_min_plus_exists_id_ann_equal
|}. 
 
Definition dioid_proofs_min_plus : dioid_proofs nat brel_eq_nat bop_min bop_plus := 
  {| 
     A_dioid_left_distributive      := bop_min_plus_left_distributive
   ; A_dioid_right_distributive     := bop_min_plus_right_distributive
   ; A_dioid_left_left_absorptive   := bops_min_plus_left_left_absorptive
   ; A_dioid_left_right_absorptive  := bops_min_plus_left_right_absorptive
  |}.



Definition A_min_plus : A_selective_cancellative_pre_dioid_with_one nat := 
{|
   A_selective_cancellative_pre_dioid_with_one_eqv           := A_eqv_nat 
 ; A_selective_cancellative_pre_dioid_with_one_plus          := bop_min 
 ; A_selective_cancellative_pre_dioid_with_one_times         := bop_plus
 ; A_selective_cancellative_pre_dioid_with_one_plus_proofs   := sg_CS_proofs_min
 ; A_selective_cancellative_pre_dioid_with_one_times_proofs  := A_sg_CK_proofs_plus
 ; A_selective_cancellative_pre_dioid_with_one_id_ann_proofs := bop_min_plus_pann_tid_proofs
 ; A_selective_cancellative_pre_dioid_with_one_proofs        := dioid_proofs_min_plus
 ; A_selective_cancellative_pre_dioid_with_one_ast           := Ast_min_plus
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
