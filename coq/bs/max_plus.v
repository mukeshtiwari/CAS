Require Import Coq.Arith.Arith.     (* beq_nat *) 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.

Section Theory.

Open Scope nat.   

Lemma max_add_l : ∀ u s : nat, u + s = max (u + s) s. 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite <- IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 

Lemma max_add_r : ∀ u s : nat, u + s = max s (u + s). 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite <- IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 

Lemma max_0_l : ∀ s : nat, s = max s 0. 
Proof. induction s; simpl; reflexivity. Qed. 

Lemma max_0_r : ∀ s : nat, s = max 0 s. 
Proof. intro s; compute. reflexivity. Qed. 

Lemma plus_0 : ∀ s : nat, s = s + 0. 
Proof. induction s; simpl. reflexivity. rewrite <- IHs. reflexivity. Qed. 


Lemma S_cong : ∀ s t : nat, brel_eq_nat s t = true -> brel_eq_nat (S s) (S t) = true. 
Proof. induction s; induction t; simpl; auto. Qed. 

Lemma S_cong_neg : ∀ s t : nat, brel_eq_nat s t = false -> brel_eq_nat (S s) (S t) = false. 
Proof. induction s; induction t; simpl; auto. Qed. 

(* distributivity *) 

(* a + (b max c) = (a + c) max (b + c) *) 
Lemma bop_max_plus_left_distributive : 
        bop_left_distributive nat brel_eq_nat bop_max bop_plus. 
Proof. unfold bop_left_distributive, bop_plus, bop_max. 
       induction s. 
          intros t u. simpl. apply brel_eq_nat_reflexive.
          induction t. 
             simpl. rewrite plus_comm. simpl. intro u.  
             rewrite Max.max_comm. rewrite plus_comm. rewrite <- max_add_l. 
             apply brel_eq_nat_reflexive.
             induction u; simpl. 
                rewrite <- plus_0. rewrite plus_comm. rewrite <- max_add_l. 
                apply brel_eq_nat_reflexive.
                rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. 
                rewrite bop_max_S. 
                apply S_cong. unfold bop_max. 
                apply IHs. 
Qed. 

(* a max (b + c) <> (a max b) + (a max c) *) 
Lemma bop_plus_max_not_left_distributive : 
        bop_not_left_distributive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (1, (0, 0)). compute. reflexivity. Defined. 


Lemma bop_max_plus_right_distributive : 
        bop_right_distributive nat brel_eq_nat bop_max bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_max_congruence. 
       apply bop_plus_commutative. 
       apply bop_max_plus_left_distributive. 
Defined.

Lemma bop_plus_max_not_right_distributive : 
        bop_not_right_distributive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (1, (0, 0)). compute. reflexivity. Defined. 


(* absorption *) 

(* a <> max a (a + b) *) 
Lemma bops_max_plus_not_left_left_absorptive : 
        bops_not_left_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0,1); compute. reflexivity. Defined.

(* a <> a + (a max b) *) 
Lemma bops_plus_max_not_left_left_absorptive : 
        bops_not_left_left_absorptive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (0,1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_left_right_absorptive : 
        bops_not_left_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_plus_max_not_left_right_absorptive : 
        bops_not_left_right_absorptive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_right_left_absorptive : 
        bops_not_right_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined.

Lemma bops_plus_max_not_right_left_absorptive : 
        bops_not_right_left_absorptive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_right_right_absorptive : 
        bops_not_right_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined.

Lemma bops_plus_max_not_right_right_absorptive : 
        bops_not_right_right_absorptive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

(* strict absorption *)
Lemma bops_max_plus_not_left_strictly_absorptive : 
  bops_not_left_strictly_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute; right. reflexivity. Defined.

Lemma bops_max_plus_not_right_strictly_absorptive : 
  bops_not_right_strictly_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute; right. reflexivity. Defined.





End Theory.

Section ACAS.

Definition bops_max_plus_id_ann_proofs : id_ann_proofs nat brel_eq_nat bop_max bop_plus := 
{| 
  A_id_ann_plus_times_d := Id_Ann_Proof_Id_None _ _ _ _ (bop_max_exists_id, bop_plus_not_exists_ann) 
; A_id_ann_times_plus_d := Id_Ann_Proof_Id_None _ _ _ _ (bop_plus_exists_id, bop_max_not_exists_ann)
|}.


Definition semiring_proofs_max_plus : semiring_proofs nat brel_eq_nat bop_max bop_plus := 
  {| 
     A_semiring_left_distributive      := bop_max_plus_left_distributive
   ; A_semiring_right_distributive     := bop_max_plus_right_distributive
   ; A_semiring_left_left_absorptive_d   := inr _ bops_max_plus_not_left_left_absorptive
   ; A_semiring_left_right_absorptive_d  := inr _ bops_max_plus_not_left_right_absorptive
  |}.


Definition A_selective_presemiring_max_plus : A_selective_presemiring nat := 
{|
  A_selective_presemiring_eqv          := A_eqv_nat 
; A_selective_presemiring_plus         := bop_max
; A_selective_presemiring_times        := bop_plus
; A_selective_presemiring_plus_proofs  := A_sg_CS_wi_proofs _ A_sg_max
; A_selective_presemiring_times_proofs := A_sg_proofs_plus
; A_selective_presemiring_id_ann_proofs := bops_max_plus_id_ann_proofs
; A_selective_presemiring_proofs       := semiring_proofs_max_plus
; A_selective_presemiring_ast          := Ast_max_plus
|}.

End ACAS.

Section AMCAS.

Definition A_mcas_max_plus :=
    A_BS_selective_presemiring _ A_selective_presemiring_max_plus.

End AMCAS.


Section CAS.

  Open Scope nat.

Definition bops_max_plus_id_ann_certs : @id_ann_certificates nat :=
{| 
  id_ann_plus_times_d := Id_Ann_Cert_Id_None 0
; id_ann_times_plus_d := Id_Ann_Cert_Id_None 0 
|}.
  

Definition semiring_certs_max_plus : @semiring_certificates nat := 
  {| 
     semiring_left_distributive      := Assert_Left_Distributive 
   ; semiring_right_distributive     := Assert_Right_Distributive 
   ; semiring_left_left_absorptive_d   := Certify_Not_Left_Left_Absorptive (0, 1) 
   ; semiring_left_right_absorptive_d  := Certify_Not_Left_Right_Absorptive (0, 1) 
  |}. 


Definition selective_presemiring_max_plus : selective_presemiring (S := nat) := 
{|
  selective_presemiring_eqv         := eqv_eq_nat 
; selective_presemiring_plus        := bop_max
; selective_presemiring_times       := bop_plus
; selective_presemiring_plus_certs  := sg_CS_wi_certs sg_max
; selective_presemiring_times_certs := sg_certs_plus
; selective_presemiring_id_ann_certs := bops_max_plus_id_ann_certs
; selective_presemiring_certs       := semiring_certs_max_plus
; selective_presemiring_ast         := Ast_max_plus
|}.

End CAS.

Section MCAS.

Definition mcas_max_plus :=
    BS_selective_presemiring selective_presemiring_max_plus.

End MCAS.



Section Verify.

Theorem correct_semiring_max_plus : 
   selective_presemiring_max_plus = A2C_selective_presemiring nat (A_selective_presemiring_max_plus). 
Proof. compute. reflexivity. Qed.

Theorem correct_mcas_max_plus : mcas_max_plus = A2C_mcas_bs nat A_mcas_max_plus.
Proof. compute. reflexivity. Qed. 


End Verify.   
  
