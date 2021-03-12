Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Max.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.nat. 

Section Theory.

  Open Scope nat.
  
Lemma beq_nat_max_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (max s1 s2) (max t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_max_congruence : bop_congruence nat brel_eq_nat bop_max.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_max.
       exact beq_nat_max_congruence. 
Defined. 

Lemma bop_max_associative : bop_associative nat brel_eq_nat bop_max.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_max. 
       rewrite (Max.max_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 

Lemma bop_max_idempotent : bop_idempotent nat brel_eq_nat bop_max.
Proof. unfold bop_idempotent, bop_max. induction s; simpl. 
       reflexivity. 
       assumption. 
Defined. 

Lemma bop_max_commutative : bop_commutative nat brel_eq_nat bop_max.
Proof. unfold bop_commutative, bop_max. intros s t. 
       rewrite Max.max_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_max_selective : bop_selective nat brel_eq_nat bop_max.
Proof. unfold bop_selective. induction s; induction t; simpl. 
      right. reflexivity. right. apply brel_eq_nat_reflexive. left. apply brel_eq_nat_reflexive.
      apply IHs. 
Defined. 


Lemma bop_max_not_is_left : bop_not_is_left nat brel_eq_nat bop_max.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 

Lemma bop_max_not_is_right : bop_not_is_right nat brel_eq_nat bop_max.
Proof. unfold bop_not_is_left. exists (1, 0); simpl. reflexivity. Defined. 



Lemma bop_max_zero_is_id : bop_is_id nat brel_eq_nat bop_max 0.  
intro s. unfold bop_max. split. 
       unfold max. apply brel_eq_nat_reflexive. 
       rewrite max_comm. unfold max. apply brel_eq_nat_reflexive. 
Qed. 
                                                                               
Lemma bop_max_exists_id : bop_exists_id nat brel_eq_nat bop_max.
Proof. exists 0. apply bop_max_zero_is_id. Defined. 

Lemma bop_max_S : ∀ s t : nat, bop_max (S s) (S t) = S (bop_max s t). 
Proof. unfold bop_max. induction s; induction t; compute; reflexivity. Defined. 

Lemma bop_max_not_exists_ann : bop_not_exists_ann nat brel_eq_nat bop_max.
Proof. unfold bop_not_exists_ann. induction a. 
       exists 1. left. compute. reflexivity. 
       destruct IHa as [s [H | H]]. 
          exists (S s). left.  rewrite bop_max_S. rewrite brel_nat_eq_S. assumption. 
          exists (S s). right.  rewrite bop_max_S. rewrite brel_nat_eq_S. assumption. 
Defined. 



Lemma  bop_max_not_left_cancellative : bop_not_left_cancellative nat brel_eq_nat bop_max.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_max_not_right_cancellative : bop_not_right_cancellative nat brel_eq_nat bop_max.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 
  
Lemma bop_max_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_max.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_max_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_max.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 


Lemma bop_max_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_max.
Proof. exists (1, 0); simpl. auto. Defined. 

Lemma bop_max_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_max.
Proof. exists (1, 0); simpl. auto. Defined. 

End Theory.

Section ACAS.


Definition sg_CS_proofs_max : sg_CS_proofs nat brel_eq_nat bop_max := 
{| 
  A_sg_CS_associative  := bop_max_associative
; A_sg_CS_congruence   := bop_max_congruence
; A_sg_CS_commutative  := bop_max_commutative
; A_sg_CS_selective    := bop_max_selective
|}. 


Definition A_sg_CS_max : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_nat 
   ; A_sg_CS_bop         := bop_max
   ; A_sg_CS_exists_id_d  := inl _ bop_max_exists_id
   ; A_sg_CS_exists_ann_d := inr _ bop_max_not_exists_ann
   ; A_sg_CS_proofs      := sg_CS_proofs_max
   ; A_sg_CS_bop_ast     := Ast_bop_max
   ; A_sg_CS_ast         := Ast_sg_CS_max
   |}. 

End ACAS.

Section CAS.
Open Scope nat.   

Definition sg_CS_certs_max : @sg_CS_certificates nat 
:= {| 
     sg_CS_associative        := Assert_Associative 
   ; sg_CS_congruence         := Assert_Bop_Congruence 
   ; sg_CS_commutative        := Assert_Commutative 
   ; sg_CS_selective          := Assert_Selective 
   |}. 


Definition sg_CS_max : @sg_CS nat 
:= {| 
     sg_CS_eqv     := eqv_eq_nat 
   ; sg_CS_bop     := bop_max
   ; sg_CS_exists_id_d        := Certify_Exists_Id 0
   ; sg_CS_exists_ann_d       := Certify_Not_Exists_Ann 
   ; sg_CS_certs   := sg_CS_certs_max
   ; sg_CS_bop_ast := Ast_bop_max                      
   ; sg_CS_ast     := Ast_sg_CS_max
   |}. 


End CAS.

Section Verify.

Theorem correct_sg_CS_max : sg_CS_max = A2C_sg_CS nat (A_sg_CS_max). 
Proof. compute. reflexivity. Qed. 
 
End Verify.   
  