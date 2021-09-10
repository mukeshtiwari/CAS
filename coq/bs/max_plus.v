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

Lemma bop_max_plus_right_distributive : 
        bop_right_distributive nat brel_eq_nat bop_max bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_max_congruence. 
       apply bop_plus_commutative. 
       apply bop_max_plus_left_distributive. 
Defined.


(*  Just for fun.  (+, max) is not distributive 
      a max (b + c) <> (a + b) max (a + c)
 2 =  0 max (1 + 1) <> (0 + 1) max (0 + 1) = 1
*) 
Lemma bop_plus_max_not_left_distributive : 
        bop_not_left_distributive nat brel_eq_nat bop_plus bop_max.
Proof. exists (2, (1, 1)); compute. reflexivity. Defined. 

Lemma bop_plus_max_not_right_distributive : 
        bop_not_right_distributive nat brel_eq_nat bop_plus bop_max.
Proof. exists (2, (1, 1)); compute. reflexivity. Defined. 



Lemma bop_max_plus_not_id_equals_ann : bops_not_id_equals_ann nat brel_eq_nat bop_max bop_plus. 
Proof. unfold bops_not_id_equals_ann. 
       unfold bop_not_is_id, bop_not_is_ann.
       unfold brel_eq_nat, bop_max, bop_plus.
       intro s. destruct s. right. exists (S 0). left. compute. reflexivity.
       left. exists 0. right. compute. reflexivity. 
Defined.

Lemma bop_plus_max_not_id_equals_ann : bops_not_id_equals_ann nat brel_eq_nat bop_plus bop_max. 
Proof. unfold bops_not_id_equals_ann. 
       unfold bop_is_id, bop_is_ann. 
       unfold bop_not_is_id, bop_not_is_ann.
       unfold brel_eq_nat, bop_max, bop_plus.
       intro s. destruct s. right. exists (S 0). left. compute. reflexivity.
       left. exists 0. left. simpl. reflexivity. 
Defined.


(* absorption *) 

Lemma bops_max_plus_not_left_left_absorptive : 
        bops_not_left_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_left_right_absorptive : 
        bops_not_left_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_right_left_absorptive : 
        bops_not_right_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma bops_max_plus_not_right_right_absorptive : 
        bops_not_right_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

End Theory.

Section ACAS.


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
; A_selective_presemiring_plus_proofs  := A_sg_CS_proofs _ A_sg_CS_max
; A_selective_presemiring_times_proofs := A_msg_proofs_plus
; A_selective_presemiring_id_ann_proofs :=
    {|
      A_id_ann_exists_plus_id_d       := inl bop_max_exists_id 
    ; A_id_ann_exists_plus_ann_d      := inr bop_max_not_exists_ann
    ; A_id_ann_exists_times_id_d      := inl bop_plus_exists_id
    ; A_id_ann_exists_times_ann_d     := inr bop_plus_not_exists_ann
    ; A_id_ann_plus_id_is_times_ann_d := inr bop_max_plus_not_id_equals_ann
    ; A_id_ann_times_id_is_plus_ann_d := inr bop_plus_max_not_id_equals_ann
    |}
; A_selective_presemiring_proofs       := semiring_proofs_max_plus
; A_selective_presemiring_ast          := Ast_max_plus
|}.

End ACAS.
Section CAS.

Open Scope nat.     

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
; selective_presemiring_plus_certs  := sg_CS_certs sg_CS_max
; selective_presemiring_times_certs := msg_certs_plus
; selective_presemiring_id_ann_certs :=
    {|
      id_ann_exists_plus_id_d       := Certify_Exists_Id 0 
    ; id_ann_exists_plus_ann_d      := Certify_Not_Exists_Ann 
    ; id_ann_exists_times_id_d      := Certify_Exists_Id 0 
    ; id_ann_exists_times_ann_d     := Certify_Not_Exists_Ann 
    ; id_ann_plus_id_is_times_ann_d := Certify_Not_Plus_Id_Equals_Times_Ann
    ; id_ann_times_id_is_plus_ann_d := Certify_Not_Times_Id_Equals_Plus_Ann
    |}
; selective_presemiring_certs       := semiring_certs_max_plus
; selective_presemiring_ast         := Ast_max_plus
|}.

End CAS.

Section Verify.

Theorem correct_semiring_max_plus : 
   selective_presemiring_max_plus = A2C_selective_presemiring nat (A_selective_presemiring_max_plus). 
Proof. compute. reflexivity. Qed. 
  
 
End Verify.   
  