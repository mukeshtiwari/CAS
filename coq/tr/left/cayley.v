
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.


Definition ltr_cayley {S : Type} (b : binary_op S) : left_transform S S := b.

Section Theory.

  Variable S : Type.
  Variable eqS : brel S.
  Variable bS : binary_op S.
  Variable bS_cong : bop_congruence S eqS bS.
  Variable refS : brel_reflexive S eqS. 

 Lemma ltr_cayley_congruence : ltr_congruence S S eqS eqS (ltr_cayley bS).
 Proof. unfold ltr_congruence. unfold ltr_cayley. intros. apply bS_cong; auto. Qed.

(* 
 Lemma ltr_cayley_partial_congruence : ltr_partial_congruence S S eqS (ltr_cayley bS). 
 Proof. unfold ltr_congruence. intros s s1 s2 H.
        unfold ltr_cayley. apply bS_cong; auto. 
 Qed.
 *)
 
 Lemma ltr_cayley_is_right : bop_is_right S eqS bS -> ltr_is_right S S eqS (ltr_cayley bS).
 Proof. auto. Qed. 
 
 Lemma ltr_cayley_not_is_right : bop_not_is_right S eqS bS -> ltr_not_is_right S S eqS (ltr_cayley bS).
 Proof. auto. Defined. 
 
 Lemma ltr_cayley_cancellative : bop_left_cancellative S eqS bS -> ltr_left_cancellative S S eqS (ltr_cayley bS).
 Proof. auto. Qed.

 Lemma ltr_cayley_not_cancellative : bop_not_left_cancellative S eqS bS -> ltr_not_left_cancellative S S eqS (ltr_cayley bS).
 Proof. auto. Defined. 
 
 Lemma ltr_cayley_exists_id : bop_exists_left_id S eqS bS -> ltr_exists_id S S eqS (ltr_cayley bS).
 Proof. auto. Qed. 

 Lemma ltr_cayley_not_exists_id : bop_not_exists_left_id S eqS bS -> ltr_not_exists_id S S eqS (ltr_cayley bS).
 Proof. auto. Defined. 
 
End Theory.

Section ACAS.



Definition ltr_cayley_proofs (S : Type) (eqS : brel S) (bS : binary_op S) (msgP : msg_proofs S eqS bS) : ltr_proofs S S eqS eqS (ltr_cayley bS) := 
{|
  A_ltr_congruence          := ltr_cayley_congruence S eqS bS (A_msg_congruence _ _ _ msgP)
; A_ltr_is_right_d          := match A_msg_is_right_d _ _ _ msgP with
                                   | inl IR => inl (ltr_cayley_is_right _ _ _ IR)
                                   | inr NIR => inr (ltr_cayley_not_is_right _ _ _ NIR)
                                   end 
; A_ltr_left_cancellative_d := match A_msg_left_cancel_d _ _ _ msgP with
                                   | inl LC => inl (ltr_cayley_cancellative _ _ _ LC)
                                   | inr NLC => inr (ltr_cayley_not_cancellative _ _ _ NLC)
                                   end 
|}.

(*
Definition A_ltr_cons (S : Type) (A_sg S) :=
{|
  A_ltr_carrier := 
; A_ltr_label   := 
; A_ltr_trans   := 
; A_ltr_proofs  := 
; A_ltr_ast     := 
|}.
*) 


End ACAS.

Section CAS.

Definition ltr_cayley_certs (S : Type) (msgP : @msg_certificates S) : @ltr_certificates S S := 
{|
  ltr_congruence_a          := @Assert_Ltr_Congruence S S 
; ltr_is_right_d          := match msg_is_right_d msgP with
                                   | Certify_Is_Right => Certify_Ltr_Is_Right
                                   | Certify_Not_Is_Right p => Certify_Ltr_Not_Is_Right p
                                   end 
; ltr_left_cancellative_d := match msg_left_cancel_d msgP with
                                   | Certify_Left_Cancellative => Certify_Ltr_Left_Cancellative
                                   | Certify_Not_Left_Cancellative t => Certify_Ltr_Not_Left_Cancellative t
                                   end 
|}.

  

End CAS.

Section Verify.
 
End Verify.   
  