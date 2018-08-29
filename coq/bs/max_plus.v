  Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.cast_up.

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

(*
      a max (b + c) <> (a + b) max (a + c)
 2 =  0 max (1 + 1) <> (0 + 1) max (0 + 1) = 1

Lemma bop_plus_max_not_left_distributive : 
        bop_not_left_distributive nat brel_eq_nat bop_plus bop_max.
Proof. exists (2, (1, 1)); compute. reflexivity. Defined. 

Lemma bop_plus_max_not_right_distributive : 
        bop_not_right_distributive nat brel_eq_nat bop_plus bop_max.
Proof. exists (2, (1, 1)); compute. reflexivity. Defined. 

*) 

(*
  s <> s + (s max t) 
  1 <> 1 + (1 max 1) = 2

Lemma bops_plus_max_not_left_absorption : 
        bops_not_left_absorption nat brel_eq_nat bop_plus bop_max. 
Proof. exists (1, 1); compute. reflexivity. Defined. 

Lemma bops_plus_max_not_right_absorption : 
        bops_not_right_absorption nat brel_eq_nat bop_plus bop_max. 
Proof. exists (1, 1); compute. reflexivity. Defined. 
*) 


(* special elements 

 id(plus) = 0 
ann(plus) = NONE 

 id(max) = 0 
ann(max) = NONE 

*) 

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


(*
Lemma plus_1 : ∀ s : nat, brel_eq_nat (bop_plus 1 s) s = false. 
Proof. induction s. compute. reflexivity. 
       unfold bop_plus.  rewrite <- plus_n_Sm. apply S_cong_neg. 
       assumption. 

Qed. 

Lemma max_S_false : ∀ s : nat, brel_eq_nat (bop_max (S s) s) s = false. 
Proof. induction s. compute. reflexivity. 
       unfold bop_max.  rewrite bop_max_S. apply S_cong_neg. 
       assumption. 
Qed. 

Lemma bop_max_plus_not_id_equals_ann : 
        bops_not_id_equals_ann nat brel_eq_nat bop_max bop_plus. 
Proof. unfold bops_not_id_equals_ann. 
       unfold bop_not_is_id, bop_not_is_ann. 
       intros i a H1 H2. 
       destruct (H2 1) as [L R]. 
       destruct a. 
          compute in L. discriminate.
          rewrite plus_1 in R. discriminate.
Qed. 

Lemma bop_plus_max_not_id_equals_ann : 
        bops_not_id_equals_ann nat brel_eq_nat bop_plus bop_max. 
Proof. unfold bops_not_id_equals_ann. 
       unfold bop_is_id, bop_is_ann. 
       intros i a H1 H2. 
       destruct (H2 (S a)) as [L R]. 
       destruct a. 
          compute in L. discriminate.
          rewrite max_S_false in R. discriminate.
Qed. 
 *)


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

   ; A_semiring_plus_id_is_times_ann_d   := inr _ bop_max_plus_not_id_equals_ann
   ; A_semiring_times_id_is_plus_ann_d   := inr _ bop_plus_max_not_id_equals_ann

   ; A_semiring_left_left_absorptive_d   := inr _ bops_max_plus_not_left_left_absorptive
   ; A_semiring_left_right_absorptive_d  := inr _ bops_max_plus_not_left_right_absorptive
  |}. 

Definition A_selective_dioid_max_plus : A_selective_dioid nat := 
{|
  A_selective_dioid_eqv          := A_eqv_nat 
; A_selective_dioid_plus         := bop_max
; A_selective_dioid_times        := bop_plus
; A_selective_dioid_plus_proofs  := A_sg_CS_proofs _ A_sg_CS_max
; A_selective_dioid_times_proofs := A_sg_proofs _ (A_sg_from_sg_CK _ A_sg_CK_plus)      (* cast up! *) 
; A_selective_dioid_proofs       := semiring_proofs_max_plus
; A_selective_dioid_plus_ast     := Ast_bop_max
; A_selective_dioid_times_ast    := Ast_bop_plus
; A_selective_dioid_ast          := Ast_selective_dioid_max_plus
|}.

End ACAS.

Section CAS.

Open Scope nat.     

Definition semiring_certs_max_plus : @semiring_certificates nat := 
  {| 
     semiring_left_distributive      := Assert_Left_Distributive 
   ; semiring_right_distributive     := Assert_Right_Distributive 
   ; semiring_plus_id_is_times_ann_d   := Certify_Not_Plus_Id_Equals_Times_Ann 
   ; semiring_times_id_is_plus_ann_d   := Certify_Not_Times_Id_Equals_Plus_Ann 
   ; semiring_left_left_absorptive_d   := Certify_Not_Left_Left_Absorptive (0, 1) 
   ; semiring_left_right_absorptive_d  := Certify_Not_Left_Right_Absorptive (0, 1) 
  |}. 


Definition selective_dioid_max_plus : selective_dioid (S := nat) := 
{|
  selective_dioid_eqv         := eqv_eq_nat 
; selective_dioid_plus        := bop_max
; selective_dioid_times       := bop_plus
; selective_dioid_plus_certs  := sg_CS_certs sg_CS_max
; selective_dioid_times_certs := sg_certs (sg_from_sg_CK sg_CK_plus)
; selective_dioid_certs       := semiring_certs_max_plus
; selective_dioid_plus_ast    := Ast_bop_max
; selective_dioid_times_ast   := Ast_bop_plus                                   
; selective_dioid_ast         := Ast_selective_dioid_max_plus
|}.

End CAS.

Section Verify.

Theorem correct_semiring_max_plus : 
   selective_dioid_max_plus = A2C_selective_dioid nat (A_selective_dioid_max_plus). 
Proof. compute. reflexivity. Qed. 
  
 
End Verify.   
  