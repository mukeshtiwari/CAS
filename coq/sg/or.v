
Require Import CAS.coq.common.base. 
Require Import Coq.Bool.Bool. 
Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.bool. 

Section Theory.

Lemma eqb_orb_congruence : 
   ∀ s1 s2 t1 t2 : bool,
   eqb s1 t1 = true → eqb s2 t2 = true → eqb (s1 || s2) (t1 || t2) = true. 
Proof.    
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := eqb_bool_to_prop s1 t1 H1). 
   assert (C2 := eqb_bool_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_bool_reflexive. 
Defined. 

Lemma bop_or_congruence : bop_congruence bool brel_eq_bool bop_or.
Proof. unfold bop_congruence. unfold brel_eq_bool, bop_or.
       exact eqb_orb_congruence. 
Defined. 

Lemma bop_or_idempotent : bop_idempotent bool brel_eq_bool bop_or.
Proof. unfold bop_idempotent. induction s; simpl; reflexivity. Defined. 

Lemma bop_or_commutative : bop_commutative bool brel_eq_bool bop_or.
Proof. unfold bop_commutative. induction s; induction t; simpl; reflexivity. Defined. 

Lemma bop_or_selective : bop_selective bool brel_eq_bool bop_or.
Proof. unfold bop_selective. induction s; induction t; simpl. 
      right. reflexivity. left. reflexivity. right. reflexivity. right. reflexivity. 
Defined. 

Lemma bop_or_associative : bop_associative bool brel_eq_bool bop_or.
Proof. unfold bop_associative. induction s; induction t; induction u; simpl; reflexivity. Defined. 

Lemma bop_or_not_is_left : bop_not_is_left bool brel_eq_bool bop_or.
Proof. unfold bop_not_is_left. exists (false, true); simpl. reflexivity. Defined. 

Lemma bop_or_not_is_right : bop_not_is_right bool brel_eq_bool bop_or.
Proof. unfold bop_not_is_right. exists (true, false); simpl. reflexivity. Defined. 

Lemma bop_or_false_is_id : bop_is_id bool brel_eq_bool bop_or false. 
Proof. unfold bop_is_id. induction s; auto. Qed.

Lemma bop_or_exists_id : bop_exists_id bool brel_eq_bool bop_or.
Proof. exists false. apply bop_or_false_is_id. Defined. 

Lemma bop_or_true_is_ann : bop_is_ann bool brel_eq_bool bop_or true. 
Proof. unfold bop_is_ann. induction s; auto. Qed.

Lemma bop_or_exists_ann : bop_exists_ann bool brel_eq_bool bop_or.
Proof. exists true. apply bop_or_true_is_ann. Defined. 


Lemma bop_or_not_left_cancellative : bop_not_left_cancellative bool brel_eq_bool bop_or.
Proof. exists (true, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_right_cancellative : bop_not_right_cancellative bool brel_eq_bool bop_or.
Proof. exists (true, (false, true)); simpl. auto. Defined. 
  
Lemma bop_or_not_left_constant : bop_not_left_constant bool brel_eq_bool bop_or.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_right_constant : bop_not_right_constant bool brel_eq_bool bop_or.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_anti_left : bop_not_anti_left bool brel_eq_bool bop_or.
Proof. exists (true, false); simpl. auto. Defined. 

Lemma bop_or_not_anti_right : bop_not_anti_right bool brel_eq_bool bop_or.
Proof. exists (true, false); simpl. auto. Defined. 

End Theory.

Section ACAS.

Definition sg_CS_proofs_or : sg_CS_proofs bool brel_eq_bool bop_or := 
{| 
  A_sg_CS_associative  := bop_or_associative
; A_sg_CS_congruence   := bop_or_congruence
; A_sg_CS_commutative  := bop_or_commutative
; A_sg_CS_selective    := bop_or_selective
; A_sg_CS_exists_id_d  := inl _ bop_or_exists_id 
; A_sg_CS_exists_ann_d := inl _ bop_or_exists_ann
|}. 


Definition A_sg_CS_or : A_sg_CS bool
:= {| 
     A_sg_CS_eqv         := A_eqv_bool
   ; A_sg_CS_bop         := bop_or
   ; A_sg_CS_proofs      := sg_CS_proofs_or
   ; A_sg_CS_ast         := Ast_sg_CS_or 
   |}. 



End ACAS.

Section CAS.



Definition sg_CS_certs_or : sg_CS_certificates (S := bool)
:= {| 
     sg_CS_associative        := Assert_Associative  
   ; sg_CS_congruence         := Assert_Bop_Congruence  
   ; sg_CS_commutative        := Assert_Commutative  
   ; sg_CS_selective          := Assert_Selective  
   ; sg_CS_exists_id_d        := Certify_Exists_Id  false 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann  true
   |}. 



Definition sg_CS_or : sg_CS (S := bool)
:= {| 
     sg_CS_eqv   := eqv_bool
   ; sg_CS_bop   := bop_or
   ; sg_CS_certs := sg_CS_certs_or
   ; sg_CS_ast   := Ast_sg_CS_or 
   |}. 
  

End CAS.

Section Verify.

Theorem correct_sg_CS_or : sg_CS_or = A2C_sg_CS bool (A_sg_CS_or). 
Proof. compute. reflexivity. Qed. 
 
End Verify.   
  