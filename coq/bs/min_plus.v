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


(* a + (b min c) = (a + c) min (b + c) *) 
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

  
Definition semiring_proofs_min_plus : semiring_proofs nat brel_eq_nat bop_min bop_plus := 
  {| 
     A_semiring_left_distributive      := bop_min_plus_left_distributive
   ; A_semiring_right_distributive     := bop_min_plus_right_distributive
   ; A_semiring_left_left_absorptive_d   := inl _ bops_min_plus_left_left_absorptive
   ; A_semiring_left_right_absorptive_d  := inl _ bops_min_plus_left_right_absorptive
  |}.


Definition A_selective_presemiring_min_plus : A_selective_presemiring nat := 
{|
  A_selective_presemiring_eqv          := A_eqv_nat 
; A_selective_presemiring_plus         := bop_min
; A_selective_presemiring_times        := bop_plus
; A_selective_presemiring_plus_proofs  := A_sg_CS_proofs _ A_sg_CS_min
; A_selective_presemiring_times_proofs := A_msg_proofs_plus
; A_selective_presemiring_id_ann_proofs := 
      id_ann_proofs_from_pann_is_tid_proofs _ _ _ _ bop_min_plus_pann_tid_proofs
; A_selective_presemiring_proofs       := semiring_proofs_min_plus 
; A_selective_presemiring_ast          := Ast_min_plus
|}.



Definition path_algebra_proofs_min_plus : path_algebra_proofs nat brel_eq_nat bop_min bop_plus := 
  {| 
     A_path_algebra_left_distributive      := bop_min_plus_left_distributive
   ; A_path_algebra_right_distributive     := bop_min_plus_right_distributive
   ; A_path_algebra_left_left_absorptive   := bops_min_plus_left_left_absorptive
   ; A_path_algebra_left_right_absorptive  := bops_min_plus_left_right_absorptive
  |}.

End ACAS.


Section CAS.

Open Scope nat.  

Definition semiring_certs_min_plus : @semiring_certificates nat := 
  {| 
     semiring_left_distributive      := Assert_Left_Distributive 
   ; semiring_right_distributive     := Assert_Right_Distributive 
   ; semiring_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
   ; semiring_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
  |}.

Definition path_algebra_certs_min_plus : @path_algebra_certificates nat := 
  {| 
     path_algebra_left_distributive      := Assert_Left_Distributive 
   ; path_algebra_right_distributive     := Assert_Right_Distributive 
   ; path_algebra_left_left_absorptive   := Assert_Left_Left_Absorptive 
   ; path_algebra_left_right_absorptive  := Assert_Left_Right_Absorptive 
  |}.

Definition bop_min_plus_pann_tid_certs : @pann_is_tid_certificates nat := 
{|
  pann_is_tid_plus_times_d := Id_Ann_Cert_None
; pann_is_tid_times_plus   := Assert_Exists_Id_Ann_Equal 0
|}. 


Definition selective_presemiring_min_plus : @selective_presemiring nat := 
{|
  selective_presemiring_eqv         := eqv_eq_nat 
; selective_presemiring_plus        := bop_min
; selective_presemiring_times       := bop_plus
; selective_presemiring_plus_certs  := sg_CS_certs sg_CS_min
; selective_presemiring_times_certs := msg_certs_plus
; selective_presemiring_id_ann_certs :=
      id_ann_certs_from_pann_is_tid_certs bop_min_plus_pann_tid_certs    
; selective_presemiring_certs       := semiring_certs_min_plus
; selective_presemiring_ast         := Ast_min_plus
|}.

End CAS.

Section Verify.

Theorem correct_selective_presemiring_min_plus : 
   selective_presemiring_min_plus = A2C_selective_presemiring nat (A_selective_presemiring_min_plus). 
Proof. compute. reflexivity. Qed. 

End Verify.   
