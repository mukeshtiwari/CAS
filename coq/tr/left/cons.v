Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.list.

Require Import CAS.coq.sg.and. 

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.

Open Scope list.


Section Compute.

 Definition ltr_cons : ∀ {S : Type}, left_transform S (list S) := λ {S} x y,  (x :: y) .   

End Compute.   


Section Theory.

  Variable S : Type.
  Variable eq : brel S.
  Variable wS : S.
  Variable ref : brel_reflexive S eq. 


 Lemma ltr_cons_congruence : ltr_congruence S (list S) eq (brel_list eq) ltr_cons. 
 Proof. intros s1 s2 l1 l2 H1 H2.
        unfold ltr_cons. unfold brel_list. fold (@brel_list S). rewrite H1, H2. compute; auto.
 Qed.

 (*
 Lemma ltr_cons_partial_congruence : ltr_partial_congruence S (list S) (brel_list eq) ltr_cons. 
 Proof. intros s l1 l2 H.
        unfold ltr_cons. unfold brel_list. fold (@brel_list S). rewrite H. rewrite ref. compute; auto.
 Qed.
 *) 
 Lemma ltr_cons_not_is_right : ltr_not_is_right S (list S) (brel_list eq) ltr_cons. 
 Proof. unfold ltr_not_is_right. exists (wS, nil). compute; auto. Defined.
 
 Lemma ltr_cons_not_exists_id : ltr_not_exists_id S (list S) (brel_list eq) ltr_cons. 
 Proof. unfold ltr_not_exists_id. intro s. unfold ltr_not_is_id. exists nil. compute; auto. Defined.
 
 Lemma ltr_cons_cancellative : ltr_left_cancellative S (list S) (brel_list eq) ltr_cons. 
 Proof. unfold ltr_left_cancellative. intros s l1 l2 H. unfold ltr_cons in H. 
        unfold brel_list in H. fold (@brel_list S) in H. apply bop_and_elim  in H.
        destruct H as [_ H]. exact H.
Qed.        
 
End Theory.

Section ACAS.


Definition ltr_cons_proofs (S : Type) (eq : brel S) (s : S) : ltr_proofs S (list S) (brel_list eq) eq (@ltr_cons S) := 
{|
  A_ltr_congruence          := ltr_cons_congruence S eq
; A_ltr_is_right_d          := inr(ltr_cons_not_is_right S eq s)
(* ; A_ltr_exists_id_d         := inr(ltr_cons_not_exists_id S eq) *) 
; A_ltr_left_cancellative_d := inl(ltr_cons_cancellative S eq)
|}.

Definition A_ltr_cons (S : Type) (eqv : A_eqv S) :=
{|
  A_ltr_carrier := A_eqv_list S eqv 
; A_ltr_label   := eqv                                                     
; A_ltr_ltr   := @ltr_cons S 
; A_ltr_proofs  := ltr_cons_proofs S (A_eqv_eq S eqv) (A_eqv_witness S eqv)
; A_ltr_ast     := Ast_ltr_cons (A_eqv_ast S eqv) 
|}.

End ACAS.

Section CAS.

Definition ltr_cons_certs {S : Type} (wS : S) : @ltr_certificates S (list S) := 
{|
  ltr_congruence_a          := Assert_Ltr_Congruence 
; ltr_is_right_d          := Certify_Ltr_Not_Is_Right (wS, nil) 
(* ; ltr_exists_id_d         := Certify_Ltr_Not_Exists_Id  *) 
; ltr_left_cancellative_d := Certify_Ltr_Left_Cancellative 
|}.

Definition ltr_Cons {S : Type} (eqv : @eqv S) :=
{|
  ltr_carrier := eqv_list eqv 
; ltr_label   := eqv                                                     
; ltr_ltr   := @ltr_cons S 
; ltr_certs  := ltr_cons_certs (eqv_witness eqv) 
; ltr_ast     := Ast_ltr_cons (eqv_ast eqv) 
|}.
  

End CAS. 
Section Verify.


Lemma correct_ltr_certs_cons (S : Type) (eS : A_eqv S): 
    ltr_cons_certs (A_eqv_witness S eS)
    =                    
    P2C_ltr S (list S) (brel_list (A_eqv_eq S eS)) (A_eqv_eq S eS) ltr_cons (ltr_cons_proofs S (A_eqv_eq S eS) (A_eqv_witness S eS)). 
Proof. compute. reflexivity. Qed. 


Theorem correct_ltr_concat (S : Type) (eS : A_eqv S)  : 
         ltr_Cons (A2C_eqv S eS) 
         = 
         A2C_ltr S (list S) (A_ltr_cons S eS). 
Proof. unfold ltr_Cons, A2C_ltr, A_ltr_cons. simpl. 
       rewrite correct_eqv_list. 
       rewrite <- correct_ltr_certs_cons. 
       reflexivity. 
Qed. 
  
  
 
End Verify.   
  
