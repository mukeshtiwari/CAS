Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.theory.set. 
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.union. 
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.


Open Scope string_scope.
Import ListNotations.

Open Scope list.


Section Compute.

Definition ltr_insert {S : Type} (eq : brel S): ltr_type S (finite_set S) :=
    λ x y,  bop_union eq (x :: nil) y. 

End Compute.   


Section Theory.

  Variable S : Type.
  Variable eq : brel S.
  Variable wS : S.
  Variable f : S -> S.
  Variable nt : brel_not_trivial S eq f. 
  Variable ref : brel_reflexive S eq. 
  Variable sym : brel_symmetric S eq.
  Variable trn : brel_transitive S eq. 

 Lemma ltr_insert_congruence : ltr_congruence S (finite_set S) eq (brel_set eq) (ltr_insert eq). 
 Proof. intros s1 s2 l1 l2 H1 H2.
        unfold ltr_insert.
        assert (H3 : brel_set eq (s1 :: nil) (s2 :: nil) = true). compute. rewrite H1.
        apply sym in H1. rewrite H1. reflexivity. 
        exact (bop_union_congruence S eq ref sym trn _ _ _ _ H3 H2). 
 Qed.


 Lemma ltr_insert_not_left_cancellative : ltr_not_left_cancellative S (finite_set S) (brel_set eq) (ltr_insert eq). 
 Proof. unfold ltr_left_cancellative. exists (wS, (nil, wS::nil)). split.
        + assert (A : ltr_insert eq wS nil = wS :: nil). compute. reflexivity. 
          assert (B : ltr_insert eq wS (wS :: nil) = wS :: nil). compute. rewrite (ref wS). reflexivity. 
          rewrite A, B. apply brel_set_reflexive; auto. 
        + compute. reflexivity. 
 Defined.


 Lemma ltr_insert_not_left_constant : ltr_not_left_constant S (finite_set S) (brel_set eq) (ltr_insert eq). 
 Proof. exists (wS, (nil, (f wS) :: nil)).
        destruct (nt wS) as [F1 F2]. 
        case_eq(brel_set eq (ltr_insert eq wS nil) (ltr_insert eq wS (f wS :: nil))); intro A; auto. 
        apply brel_set_elim_prop in A; auto.
        destruct A as [A B].
        assert (C : in_set eq (ltr_insert eq wS (f wS :: nil)) (f wS) = true).
           unfold ltr_insert.
           apply in_set_bop_union_intro; auto.
           right. compute. rewrite ref. reflexivity. 
        assert (D := B _ C).
        unfold ltr_insert in D.
        apply in_set_bop_union_elim in D; auto.
        destruct D as [D | D]. 
        + compute in D. rewrite F2 in D. discriminate D. 
        + compute in D. discriminate D. 
 Defined.
 
 Lemma ltr_insert_not_is_right : ltr_not_is_right S (finite_set S) (brel_set eq) (ltr_insert eq). 
 Proof. unfold ltr_not_is_right. exists (wS, nil). compute; auto. Defined.
 
 Lemma ltr_insert_not_exists_id : ltr_not_exists_id S (finite_set S) (brel_set eq) (ltr_insert eq). 
 Proof. unfold ltr_not_exists_id. intro s. unfold ltr_not_is_id. exists nil. compute; auto. Defined.

Lemma ltr_insert_enum_is_ann (enum : carrier_is_finite S eq) : 
  ltr_is_ann S (finite_set S) (brel_set eq) (ltr_insert eq) ((projT1 enum) tt).
Proof. assert (A := bop_union_enum_is_ann S eq ref sym trn enum).
         intro s. unfold ltr_insert.
         destruct (A (s :: nil)) as [B C]. exact C. 
Qed. 

Lemma ltr_insert_exists_ann (enum : carrier_is_finite S eq) : ltr_exists_ann S (finite_set S) (brel_set eq) (ltr_insert eq).
Proof. exists (projT1 enum tt). apply ltr_insert_enum_is_ann. Defined.

Lemma ltr_insert_not_exists_ann (nfin : carrier_is_not_finite S eq) : ltr_not_exists_ann S (finite_set S) (brel_set eq) (ltr_insert eq). 
  intros s. unfold carrier_is_not_finite in nfin. 
  unfold ltr_not_is_ann. unfold ltr_insert.
  assert (A := nfin (fun tt => s)). simpl in A.
  destruct A as [t P].
  exists t. 
  case_eq(brel_set eq (bop_union eq (t :: nil) s) s); intro B; auto.
  apply brel_set_elim_prop in B; auto. destruct B as [B C].
  assert (D : set.in_set eq (bop_union eq (t :: nil) s) t = true).
  apply in_set_bop_union_intro; auto. left. compute. rewrite (ref t). reflexivity. 
  assert (E := B t D). 
  (* Fix this.  change def of carrier_is_not_finite so that f maps to sets*)
Admitted. 


 
 
End Theory.

Section ACAS.

Section Proofs.
Variable S : Type.
Variable eq : brel S.
Variable wS : S.
Variable f : S -> S.
Variable nt : brel_not_trivial S eq f.
Variable eqvP : eqv_proofs S eq. 

Definition ltr_insert_proofs : left_transform_proofs S (finite_set S) (brel_set eq) eq (ltr_insert eq) :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in     
{|
  A_left_transform_congruence          := ltr_insert_congruence S eq ref sym trn
; A_left_transform_is_right_d          := inr(ltr_insert_not_is_right S eq wS)
; A_left_transform_left_constant_d     := inr(ltr_insert_not_left_constant S eq wS f nt ref sym trn)                                               
; A_left_transform_left_cancellative_d := inr(ltr_insert_not_left_cancellative S eq wS ref sym)
|}.

End Proofs.

Definition A_left_transform_insert (S : Type) (eqv : A_eqv S) :=
let eq := A_eqv_eq _ eqv in
let wS := A_eqv_witness S eqv in
let f  := A_eqv_new S eqv in
let nt  := A_eqv_not_trivial S eqv in
let eqvP := A_eqv_proofs _ eqv in
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in 
{|
  A_left_transform_carrier      := A_eqv_set S eqv 
; A_left_transform_label        := eqv                                                     
; A_left_transform_ltr          := ltr_insert eq 
; A_left_transform_exists_id_d  := inr(ltr_insert_not_exists_id S eq) 
; A_left_transform_exists_ann_d :=
                        match A_eqv_finite_d _ eqv with
                        | inl fin => inl (ltr_insert_exists_ann S eq ref sym trn fin) 
                        | inr nfin => inr (ltr_insert_not_exists_ann S eq wS f nt ref sym trn nfin)
                        end 
; A_left_transform_proofs       := ltr_insert_proofs S eq wS f nt eqvP 
; A_left_transform_ast          := Cas_ast ("A_left_transform_insert", [])  (* Ast_ltr_insert (A_eqv_ast S eqv) *)
|}.

End ACAS.



Section CAS.

Definition ltr_insert_certs {S : Type} (wS : S) (f : S -> S) : @left_transform_certificates S (list S) := 
{|
  left_transform_congruence            := Assert_Ltr_Congruence 
; left_transform_is_right_d            := Certify_Ltr_Not_Is_Right (wS, nil)
; left_transform_left_constant_d       := Certify_Ltr_Not_Left_Constant (wS, (nil, (f wS) :: nil))                                                          
; left_transform_left_cancellative_d   := Certify_Ltr_Not_Left_Cancellative (wS, (nil, wS :: nil))
|}.


Definition left_transform_insert {S : Type} (eqv : @eqv S) :=
{|
  left_transform_carrier      := eqv_set eqv 
; left_transform_label        := eqv                                                     
; left_transform_ltr          := ltr_insert (eqv_eq eqv)
; left_transform_exists_id_d  := Certify_Ltr_Not_Exists_Id
; left_transform_exists_ann_d :=
                        match eqv_finite_d eqv with
                        | Certify_Is_Finite f => Certify_Ltr_Exists_Ann (f tt) 
                        | Certify_Is_Not_Finite => Certify_Ltr_Not_Exists_Ann 
                        end 
; left_transform_certs        := ltr_insert_certs (eqv_witness eqv) (eqv_new eqv) 
; left_transform_ast          := Cas_ast ("A_left_transform_insert", []) (*Ast_ltr_insert (eqv_ast eqv)*) 
|}.
  

End CAS. 
Section Verify.

Lemma correct_ltr_certs_insert (S : Type) (eS : A_eqv S): 
  P2C_left_transform
          S (finite_set S)
          (brel_set (A_eqv_eq S eS))
          (A_eqv_eq S eS)
          (ltr_insert (A_eqv_eq S eS))
          (ltr_insert_proofs S
                             (A_eqv_eq S eS)
                             (A_eqv_witness S eS)
                             (A_eqv_new S eS)
                             (A_eqv_not_trivial S eS)                                                          
                             (A_eqv_proofs S eS)
          ) 
    =                    
    ltr_insert_certs (A_eqv_witness S eS) (A_eqv_new S eS).
Proof. compute. reflexivity. Qed. 


Theorem correct_left_transform_insert (S : Type) (eS : A_eqv S)  : 
         left_transform_insert (A2C_eqv S eS) 
         = 
         A2C_left_transform S (finite_set S) (A_left_transform_insert S eS). 
Proof. unfold left_transform_insert, A_left_transform_insert, A2C_left_transform; simpl.
       rewrite correct_ltr_certs_insert.        
       rewrite correct_eqv_set.
       destruct (A_eqv_finite_d S eS) as [[f P] | nfin]; simpl; 
       try reflexivity. 
Qed. 
  
  
 
End Verify.   
