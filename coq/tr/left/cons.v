Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.list.

Require Import CAS.coq.sg.and. 

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Open Scope list.

Open Scope string_scope.
Import ListNotations.


Section Compute.

 Definition ltr_cons : ∀ {S : Type}, ltr_type S (list S) := λ {S} x y,  (x :: y) .   

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

 Lemma ltr_cons_not_is_right : ltr_not_is_right S (list S) (brel_list eq) ltr_cons. 
 Proof. unfold ltr_not_is_right. exists (wS, nil). compute; auto. Defined.
 
 Lemma ltr_cons_not_left_constant : ltr_not_left_constant S (list S) (brel_list eq) ltr_cons. 
 Proof. exists (wS, (nil, wS :: nil)). compute. rewrite (ref wS). reflexivity. Defined.
 


 Lemma ltr_cons_not_exists_id : ltr_not_exists_id S (list S) (brel_list eq) ltr_cons. 
 Proof. unfold ltr_not_exists_id. intro s. unfold ltr_not_is_id. exists nil. compute; auto. Defined.

(* this is rather convoluted! *) 
Lemma list_cons_not_ann (l : list S) : ∀ (s : S), brel_list eq (ltr_cons s l) l = false.
Proof. induction l.
        + intro s. compute. reflexivity. 
        + intro s. unfold ltr_cons.
          assert (A : brel_list eq (s :: a :: l) (a :: l)
                      =
                      bop_and (eq s a) (brel_list eq (ltr_cons a l) l)).
             unfold brel_list at 1. fold (brel_list eq l).
             destruct l. compute. reflexivity. 
             unfold brel_list at 2. fold (brel_list eq ((ltr_cons a (s0 :: l)))).
             unfold ltr_cons. unfold brel_list at 2. fold (brel_list eq l).
             unfold brel_list at 1. fold (brel_list eq l).
             reflexivity. 
          rewrite A. 
          case_eq (eq s a); intro B.
          ++ rewrite (IHl a). compute. reflexivity. 
          ++ simpl. reflexivity. 
Qed.

Lemma ltr_cons_not_exists_ann : ltr_not_exists_ann S (list S) (brel_list eq) ltr_cons. 
Proof. unfold ltr_not_exists_ann. intro s. unfold ltr_not_is_ann. exists wS.
        apply list_cons_not_ann. 
 Defined.

 
 Lemma ltr_cons_cancellative : ltr_left_cancellative S (list S) (brel_list eq) ltr_cons. 
 Proof. unfold ltr_left_cancellative. intros s l1 l2 H. unfold ltr_cons in H. 
        unfold brel_list in H. fold (@brel_list S) in H. apply bop_and_elim  in H.
        destruct H as [_ H]. exact H.
Qed.        
 
End Theory.

Section ACAS.


Definition ltr_cons_proofs (S : Type) (eq : brel S) (s : S) (eqvP : eqv_proofs S eq) :
    left_transform_proofs S (list S) (brel_list eq) eq (@ltr_cons S) := 
{|
  A_left_transform_congruence          := ltr_cons_congruence S eq
; A_left_transform_is_right_d          := inr(ltr_cons_not_is_right S eq s)
; A_left_transform_left_constant_d     := inr(ltr_cons_not_left_constant S eq s (A_eqv_reflexive _ _ eqvP))                                               
; A_left_transform_left_cancellative_d := inl(ltr_cons_cancellative S eq)
|}.

Definition A_left_transform_cons (S : Type) (eqv : A_eqv S) :=
{|
  A_left_transform_carrier      := A_eqv_list S eqv 
; A_left_transform_label        := eqv                                                     
; A_left_transform_ltr          := @ltr_cons S
; A_left_transform_exists_id_d  := inr(ltr_cons_not_exists_id S (A_eqv_eq S eqv)) 
; A_left_transform_exists_ann_d := inr(ltr_cons_not_exists_ann S (A_eqv_eq S eqv) (A_eqv_witness S eqv))
; A_left_transform_proofs       := ltr_cons_proofs S (A_eqv_eq S eqv) (A_eqv_witness S eqv) (A_eqv_proofs S eqv)
; A_left_transform_ast          := Cas_ast ("A_left_transform_cons", []) 
    (* I don't want to open pandora box so let's keept the second component empty of Ast
      Ast_ltr_cons (A_eqv_ast S eqv) *) 
|}.

End ACAS.

Section CAS.

Definition ltr_cons_certs {S : Type} (wS : S) : @left_transform_certificates S (list S) := 
{|
  left_transform_congruence          := Assert_Ltr_Congruence 
; left_transform_is_right_d          := Certify_Ltr_Not_Is_Right (wS, nil)
; left_transform_left_constant_d     := Certify_Ltr_Not_Left_Constant (wS, (nil, wS::nil))                                                        
; left_transform_left_cancellative_d := Certify_Ltr_Left_Cancellative 
|}.

Definition left_transform_cons {S : Type} (eqv : @eqv S) :=
{|
  left_transform_carrier      := eqv_list eqv 
; left_transform_label        := eqv                                                     
; left_transform_ltr          := @ltr_cons S
; left_transform_exists_id_d  := Certify_Ltr_Not_Exists_Id
; left_transform_exists_ann_d := Certify_Ltr_Not_Exists_Ann 
; left_transform_certs        := ltr_cons_certs (eqv_witness eqv) 
; left_transform_ast          := Cas_ast ("A_left_transform_cons", [])
|}.
  

End CAS. 
Section Verify.


Lemma correct_ltr_certs_cons (S : Type) (eS : A_eqv S): 
    ltr_cons_certs (A_eqv_witness S eS)
    =                    
    P2C_left_transform S
            (list S)
            (brel_list (A_eqv_eq S eS))
            (A_eqv_eq S eS)
            ltr_cons
            (ltr_cons_proofs S (A_eqv_eq S eS) (A_eqv_witness S eS) (A_eqv_proofs S eS)). 
Proof. compute. reflexivity. Qed. 


Theorem correct_left_transform_cons (S : Type) (eS : A_eqv S)  : 
         left_transform_cons (A2C_eqv S eS) 
         = 
         A2C_left_transform S (list S) (A_left_transform_cons S eS). 
Proof. unfold left_transform_cons, A2C_left_transform, A_left_transform_cons. simpl. 
       rewrite correct_eqv_list. 
       rewrite <- correct_ltr_certs_cons. 
       reflexivity. 
Qed. 
  
  
 
End Verify.   
  
