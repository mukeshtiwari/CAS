Require Import CAS.coq.common.base. 

Section Theory.

  Variable S : Type.
  Variable r : brel S.
  Variable wS : S. 
  Variable f : S -> S.

  Variable Pf : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r. 

Lemma bop_left_associative : bop_associative S r (@bop_left S).
Proof. intros s t u.  unfold bop_left.  apply (refS s). Qed. 

Lemma bop_left_congruence : bop_congruence S r (@bop_left S).
Proof. intros s t u v H Q. unfold bop_left. exact H. Qed. 

Lemma bop_left_not_commutative : bop_not_commutative S r (@bop_left S).
Proof. exists (wS, f wS). destruct (Pf wS) as [L _]. unfold bop_left. exact L. Defined. 

Lemma bop_left_idempotent : bop_idempotent S r (@bop_left S).
Proof. intro s. unfold bop_left. apply (refS s). Qed. 

Lemma bop_left_selective : bop_selective S r (@bop_left S).
Proof. intros s t. unfold bop_left. left. apply (refS s).  Qed. 

Lemma bop_left_is_left : bop_is_left S r (@bop_left S).
Proof. intros s t. unfold bop_left. apply (refS s). Qed. 

Lemma bop_left_not_is_right : bop_not_is_right S r (@bop_left S).
Proof. exists (wS, f wS). destruct (Pf wS) as [L _]. unfold bop_left. exact L. Defined. 

Lemma bop_left_not_exists_id : bop_not_exists_id S r (@bop_left S).
Proof. intro i. exists (f i). destruct (Pf i) as [L _]. left. unfold bop_left. exact L. Defined. 

Lemma bop_left_not_exists_ann : bop_not_exists_ann S r (@bop_left S).
Proof. intro a.  exists (f a). destruct (Pf a) as [_ R]. right. unfold bop_left. exact R. Defined. 

Lemma bop_left_not_left_cancellative : bop_not_left_cancellative S r (@bop_left S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L R]. split. apply (refS wS). exact L. Defined. 

Lemma bop_left_right_cancellative : bop_right_cancellative S r (@bop_left S). 
Proof. intros s t u. compute. auto. Qed. 

Lemma bop_left_left_constant : bop_left_constant S r (@bop_left S). 
Proof. intros s t u. compute. auto. Qed. 

Lemma bop_left_not_right_constant : bop_not_right_constant S r (@bop_left S). 
Proof. exists (wS, (wS, f wS)); compute. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_left_not_anti_left : bop_not_anti_left S r (@bop_left S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined.

Lemma bop_left_not_anti_right : bop_not_anti_right S r (@bop_left S). 
Proof. exists (wS, wS); compute. apply (refS wS). Defined.

End Theory.

Section ACAS.

Definition sg_proofs_left : ∀ (S : Type) (rS : brel S) (s : S) (f : S -> S),
      brel_not_trivial S rS f → eqv_proofs S rS → sg_proofs S rS (@bop_left S)
:= λ S rS s f Pf eqvS, 
{| 
  A_sg_associative      := bop_left_associative S rS (A_eqv_reflexive _ _ eqvS)
; A_sg_congruence       := bop_left_congruence S rS 
; A_sg_commutative_d    := inr _ (bop_left_not_commutative S rS s f Pf)
; A_sg_selective_d      := inl _ (bop_left_selective S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_left_d        := inl _ (bop_left_is_left S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_is_right_d       := inr _ (bop_left_not_is_right S rS s f Pf)
; A_sg_idempotent_d     := inl _ (bop_left_idempotent S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_exists_id_d      := inr _ (bop_left_not_exists_id S rS f Pf)
; A_sg_exists_ann_d     := inr _ (bop_left_not_exists_ann S rS f Pf)
; A_sg_left_cancel_d    := inr _ (bop_left_not_left_cancellative S rS s f Pf (A_eqv_reflexive _ _ eqvS))
; A_sg_right_cancel_d   := inl _ (bop_left_right_cancellative S rS) 
; A_sg_left_constant_d  := inl _ (bop_left_left_constant S rS (A_eqv_reflexive _ _ eqvS))
; A_sg_right_constant_d := inr _ (bop_left_not_right_constant S rS s f Pf)
; A_sg_anti_left_d      := inr _ (bop_left_not_anti_left S rS s (A_eqv_reflexive _ _ eqvS))
; A_sg_anti_right_d     := inr _ (bop_left_not_anti_right S rS s (A_eqv_reflexive _ _ eqvS))
|}. 


Definition A_sg_left: ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq        := eqvS
   ; A_sg_bop       := @bop_left S 
   ; A_sg_proofs    := sg_proofs_left S (A_eqv_eq S eqvS)
                                      (A_eqv_witness S eqvS)
                                      (A_eqv_new S eqvS)
                                      (A_eqv_not_trivial S eqvS)
                                      (A_eqv_proofs S eqvS)
   ; A_sg_bop_ast   := Ast_bop_left (A_eqv_ast _ eqvS)
   ; A_sg_ast       := Ast_sg_left (A_eqv_ast _ eqvS)
   |}. 


End ACAS.

Section CAS.

Definition sg_certs_left : ∀ {S : Type},  S -> (S -> S) -> @sg_certificates S 
:= λ {S} s f,  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Not_Commutative (s, f s)
; sg_selective_d      := Certify_Selective 
; sg_is_left_d        := Certify_Is_Left 
; sg_is_right_d       := Certify_Not_Is_Right (s, f s)
; sg_idempotent_d     := Certify_Idempotent 
; sg_exists_id_d      := Certify_Not_Exists_Id 
; sg_exists_ann_d     := Certify_Not_Exists_Ann 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative  (s, (s, f s)) 
; sg_right_cancel_d   := Certify_Right_Cancellative 
; sg_left_constant_d  := Certify_Left_Constant 
; sg_right_constant_d := Certify_Not_Right_Constant  (s, (s, f s)) 
; sg_anti_left_d      := Certify_Not_Anti_Left  (s, s) 
; sg_anti_right_d     := Certify_Not_Anti_Right  (s, s) 
|}. 



Definition sg_left: ∀ {S : Type},  @eqv S -> @sg S
:= λ {S} eqvS, 
   {| 
     sg_eq      := eqvS
   ; sg_bop     := bop_left 
   ; sg_certs   := sg_certs_left (eqv_witness eqvS) (eqv_new eqvS)
   ; sg_bop_ast := Ast_bop_left (eqv_ast eqvS)                                 
   ; sg_ast     := Ast_sg_left (eqv_ast eqvS)
   |}. 
  

End CAS.

Section Verify.


Lemma correct_sg_certs_left : 
      ∀ (S : Type) (r : brel S) (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : eqv_proofs S r), 
       sg_certs_left s f 
       = 
       P2C_sg S r (@bop_left S) (sg_proofs_left S r s f Pf P). 
Proof. intros S r s f Pf P. compute. reflexivity. Defined. 


Theorem correct_sg_left :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_left (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_left S eS). 
Proof. intros S eS. unfold sg_left, A2C_sg; simpl. 
       rewrite <- correct_sg_certs_left.  
       reflexivity. 
Qed. 
  
 
End Verify.   
  