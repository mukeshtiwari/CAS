Require Import CAS.coq.common.base. 

Section Theory.

  Variable S : Type.
  Variable r : brel S.
  Variable wS : S. 
  Variable f : S -> S.

  Variable Pf : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r. 

Lemma bop_right_associative : bop_associative S r (@bop_right S).
Proof. intros s t u. unfold bop_right. apply (refS u). Qed. 

Lemma bop_right_congruence : 
   ∀ (S : Type) (r : brel S), bop_congruence S r (@bop_right S).
Proof. intros s t u v H Q. compute. auto. Qed. 

Lemma bop_right_idempotent : bop_idempotent S r (@bop_right S).
Proof. intros s. unfold bop_right. apply (refS s). Qed. 

Lemma bop_right_not_commutative : bop_not_commutative S r (@bop_right S).
Proof. exists (f wS, wS). destruct (Pf wS) as [L R]. compute. exact L. Defined. 

Lemma bop_right_selective : bop_selective S r (@bop_right S).
Proof. intros s t. unfold bop_right. right. apply (refS t). Qed. 

Lemma bop_right_not_is_left : bop_not_is_left S r (@bop_right S).
Proof. exists (f wS, wS). compute. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_right_is_right : bop_is_right S r (@bop_right S).
Proof. intros s t. unfold bop_right. apply (refS t). Qed. 

Lemma bop_right_not_exists_id : bop_not_exists_id S r (@bop_right S).
Proof. intro i.  exists (f i). compute. destruct (Pf i) as [L _]. right. exact L. Defined. 

Lemma bop_right_not_exists_ann : bop_not_exists_ann S r (@bop_right S).
Proof. intros a.  exists (f a). compute. destruct (Pf a) as [_ R]. left. exact R. Defined. 

Lemma bop_right_left_cancellative : bop_left_cancellative S r (@bop_right S). 
Proof. intros s t u. compute. auto. Qed. 

Lemma bop_right_not_right_cancellative : bop_not_right_cancellative S r (@bop_right S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L _]. split. apply (refS wS). exact L. Defined. 

Lemma bop_right_not_left_constant : bop_not_left_constant S r (@bop_right S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_right_right_constant : bop_right_constant S r (@bop_right S). 
Proof. intros s t u. compute. auto. Qed. 
       
Lemma bop_right_not_anti_left : bop_not_anti_left S r (@bop_right S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined. 

Lemma bop_right_not_anti_right : bop_not_anti_right S r (@bop_right S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined. 

End Theory.

Section ACAS.

Definition sg_proofs_right : ∀ (S : Type) (rS : brel S) (s : S) (f : S -> S),
      brel_not_trivial S rS f → eqv_proofs S rS → sg_proofs S rS (@bop_right S)
:= λ S rS s f Pf eqvS, 
{| 
  A_sg_associative   := bop_right_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence    := bop_right_congruence S rS 
; A_sg_commutative_d := inr _ (bop_right_not_commutative S rS s f Pf) 
; A_sg_selective_d   := inl _ (bop_right_selective S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_left_d     := inr _ (bop_right_not_is_left S rS s f Pf) 
; A_sg_is_right_d    := inl _ (bop_right_is_right S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_idempotent_d  := inl _ (bop_right_idempotent S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_id_d   := inr _ (bop_right_not_exists_id S rS f Pf)
; A_sg_exists_ann_d  := inr _ (bop_right_not_exists_ann S rS f Pf) 
; A_sg_left_cancel_d    := inl _ (bop_right_left_cancellative S rS) 
; A_sg_right_cancel_d   := inr _ (bop_right_not_right_cancellative S rS s f Pf (A_eqv_reflexive _ _ eqvS))
; A_sg_left_constant_d  := inr _ (bop_right_not_left_constant S rS s f Pf)
; A_sg_right_constant_d := inl _ (bop_right_right_constant S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_left_d      := inr _ (bop_right_not_anti_left S rS s (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_right_d     := inr _ (bop_right_not_anti_right S rS s (A_eqv_reflexive _ _ eqvS))
|}. 



Definition A_sg_right : ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq         := eqvS
   ; A_sg_bop        := @bop_right S 
   ; A_sg_proofs     := sg_proofs_right S (A_eqv_eq S eqvS)
                                        (A_eqv_witness S eqvS)
                                        (A_eqv_new S eqvS)
                                        (A_eqv_not_trivial S eqvS)
                                        (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_right (A_eqv_ast _ eqvS)
   |}. 


End ACAS.

Section CAS.


Definition sg_certs_right : ∀ {S : Type},  S -> (S -> S) -> sg_certificates (S := S) 
:= λ {S} s f,  
{|
  sg_associative   := Assert_Associative 
; sg_congruence    := Assert_Bop_Congruence 
; sg_commutative_d := Certify_Not_Commutative (f s, s)
; sg_selective_d   := Certify_Selective 
; sg_is_left_d     := Certify_Not_Is_Left (f s, s)
; sg_is_right_d    := Certify_Is_Right 
; sg_idempotent_d  := Certify_Idempotent 
; sg_exists_id_d   := Certify_Not_Exists_Id  
; sg_exists_ann_d  := Certify_Not_Exists_Ann 
; sg_left_cancel_d    := Certify_Left_Cancellative
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (s, (s, f s))
; sg_left_constant_d  := Certify_Not_Left_Constant (s, (s, f s))
; sg_right_constant_d := Certify_Right_Constant
; sg_anti_left_d      := Certify_Not_Anti_Left (s, s) 
; sg_anti_right_d     := Certify_Not_Anti_Right (s, s) 
|}. 



Definition sg_right : ∀ {S : Type},  eqv (S := S) -> sg (S := S) 
:= λ {S} eqvS, 
   {| 
     sg_eq     := eqvS
   ; sg_bop    := bop_right 
   ; sg_certs  := sg_certs_right (eqv_witness eqvS) (eqv_new eqvS) 
   ; sg_ast    := Ast_sg_right (eqv_ast eqvS)
   |}. 

  

End CAS.

Section Verify.

Lemma correct_sg_certs_right : 
      ∀ (S : Type) (r : brel S) (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : eqv_proofs S r), 
       sg_certs_right s f 
       = 
       P2C_sg S r (@bop_right S) (sg_proofs_right S r s f Pf P). 
Proof. intros S r s f Pf P. compute. reflexivity. Defined. 


Theorem correct_sg_right :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_right (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_right S eS). 
Proof. intros S eS. unfold sg_right, A2C_sg; simpl. 
       rewrite <- correct_sg_certs_right. 
       reflexivity. 
Qed. 


  
 
End Verify.   
  