Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.theory.set. (* for uop_duplicate_elim *)
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.union. 
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Open Scope string_scope.
Import ListNotations.

Open Scope list.

Section Compute.


Fixpoint ltr_list_product_left {L S : Type} (ltr : ltr_type L S) (x : L) (Y : finite_set S) : finite_set S := 
  match Y with
  | nil => nil
  | a :: rest => (ltr x a) :: (ltr_list_product_left ltr x rest)
  end. 

Definition ltr_lift {L S : Type} (eq : brel S) (ltr : ltr_type L S): ltr_type L (finite_set S) :=
    λ x Y,  uop_duplicate_elim eq (ltr_list_product_left ltr x Y). 

End Compute.   

Section Theory.

Variables (L : Type)
          (S : Type)
          (eqL : brel L)
          (eqS : brel S)
          (wL : L)          
          (wS : S)
          (refL : brel_reflexive L eqL)          
          (ref : brel_reflexive S eqS)
          (sym : brel_symmetric S eqS)
          (trn : brel_transitive S eqS)
          (ltr : ltr_type L S)
          (ltr_cong: ltr_congruence L S eqL eqS ltr). 


Lemma in_set_ltr_list_product_left_elim (l : L) ( X : finite_set S) (s : S) 
  (A : in_set eqS (ltr_list_product_left ltr l X) s = true) : { x : S & (in_set eqS X x = true) * (eqS (ltr l x) s = true)}.
Proof. induction X.
       + compute in A. discriminate A. 
       + unfold ltr_list_product_left in A. fold (ltr_list_product_left ltr l) in A.
         apply in_set_cons_elim in A; auto.
         destruct A as [A | A].
         ++ exists a. split; auto.
            apply in_set_cons_intro; auto.             
         ++ destruct (IHX A) as [x [B C]].
            exists x; split; auto. 
            apply in_set_cons_intro; auto. 
Defined. 

Lemma in_set_ltr_list_product_left_intro (l : L) ( X : finite_set S) (s : S) 
  (A : { x : S & (in_set eqS X x = true) * (eqS (ltr l x) s = true)}) : in_set eqS (ltr_list_product_left ltr l X) s = true. 
Proof. induction X.
       + compute in A. destruct A as [_ [F _]]. discriminate F. 
       + unfold ltr_list_product_left. fold (ltr_list_product_left ltr l).
         apply in_set_cons_intro; auto.
         destruct A as [x [B C]].
         apply in_set_cons_elim in B; auto.             
         destruct B as [B | B].
         ++ left.
            assert (D := ltr_cong _ _ _ _ (refL l) B).
            exact (trn _ _ _ D C). 
         ++ right. apply IHX. 
            exists x; auto. 
Defined. 

Lemma in_set_ltr_lift_elim (l : L) ( X : finite_set S) (s : S)
  (A: in_set eqS (ltr_lift eqS ltr l X) s = true) : { x : S & (in_set eqS X x = true) * (eqS (ltr l x) s = true)}.
Proof. unfold ltr_lift in A.
       apply in_set_uop_duplicate_elim_elim in A.
       apply in_set_ltr_list_product_left_elim in A.
       exact A. 
Qed. 


Lemma in_set_ltr_lift_intro (l : L) ( X : finite_set S) (s : S) 
  (A : { x : S & (in_set eqS X x = true) * (eqS (ltr l x) s = true)}) : in_set eqS (ltr_lift eqS ltr l X) s = true. 
Proof. unfold ltr_lift.
       apply in_set_uop_duplicate_elim_intro; auto. 
       apply in_set_ltr_list_product_left_intro.
       exact A. 
Qed.

Lemma ltr_list_product_left_congruence
  (s1 s2 : L) 
  (l1 l2 : finite_set S) 
  (H1 : eqL s1 s2 = true)
  (H2 : brel_set eqS l1 l2 = true) : 
  brel_set eqS (ltr_list_product_left ltr s1 l1)
           (ltr_list_product_left ltr s2 l2) = true.
Proof. apply brel_set_elim_prop in H2; auto. destruct H2 as [H2 H3]. 
       apply brel_set_intro_prop; auto. split. 
       + intros s A.
         apply in_set_ltr_list_product_left_elim in A.
         apply in_set_ltr_list_product_left_intro.
         destruct A as [x [A B]].
         exists x. split.
         ++ apply H2; auto. 
         ++ assert (C := ltr_cong _ _ _ _ H1 (ref x)). apply sym in C.
            exact (trn _ _ _ C B). 
       + intros s A.
         apply in_set_ltr_list_product_left_elim in A.
         apply in_set_ltr_list_product_left_intro.
         destruct A as [x [A B]].
         exists x. split.
         ++ apply H3; auto. 
         ++ assert (C := ltr_cong _ _ _ _ H1 (ref x)). 
            exact (trn _ _ _ C B). 
Qed.


Lemma ltr_lift_congruence : ltr_congruence L (finite_set S) eqL (brel_set eqS) (ltr_lift eqS ltr). 
Proof. intros s1 s2 l1 l2 H1 H2. unfold ltr_lift.
       assert (A := ltr_list_product_left_congruence s1 s2 l1 l2 H1 H2).
       assert (B := uop_duplicate_elim_congruence_v2 _ _ sym trn _ _ A). 
       exact B. 
Qed. 

Lemma ltr_lift_not_exists_id (nid : ltr_not_exists_id L S eqS ltr) : ltr_not_exists_id L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr). 
Proof. unfold ltr_not_exists_id, ltr_not_is_id. intro l.
        destruct (nid l) as [s P]. 
        exists (s :: nil). compute. rewrite P.
        reflexivity. 
Defined.

Lemma ltr_lift_exists_id (id : ltr_exists_id L S eqS ltr) : ltr_exists_id L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr). 
Proof. unfold ltr_exists_id, ltr_is_id. destruct id as [l P].
        exists l. intro X. unfold ltr_is_id in P. 
        apply brel_set_intro_prop; auto. split.
        + intros s A.
          apply in_set_ltr_lift_elim in A; auto.
          destruct A as [x [A B]].
          assert (C := P x).
          apply sym in C.
          assert (D := trn _ _ _ C B). 
          exact (in_set_right_congruence S eqS sym trn _ _ _ D A). 
        + intros s A.
          apply in_set_ltr_lift_intro.
          assert (B := P s).
          exists s. split; auto. 
Defined. 
 
Lemma ltr_lift_is_ann : ltr_is_ann L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr) nil.
Proof. intro l. compute. reflexivity. Qed.

Lemma ltr_lift_exists_ann : ltr_exists_ann L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr). 
Proof. exists nil.  apply ltr_lift_is_ann. Defined.

(* note: with ltr's the (right) annihilator need not be unique! *) 
Lemma ltr_lift_exists_ann_version_2 (annP : ltr_exists_ann L S eqS ltr) : ltr_exists_ann L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr). 
  destruct annP as [ann P]. 
  exists (ann :: nil). intro l. unfold ltr_lift. compute. 
  assert (A := P l). rewrite A. rewrite (sym _ _ A). reflexivity. 
Defined.

Lemma ltr_lift_not_is_right (nr : ltr_not_is_right L S eqS ltr) : ltr_not_is_right L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr). 
Proof. destruct nr as [[l s] P]. 
       exists (l, s :: nil). compute.
       rewrite P. reflexivity. 
Defined.

Lemma ltr_lift_is_right (ir : ltr_is_right L S eqS ltr) : ltr_is_right L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr). 
Proof. intros l X.
       apply brel_set_intro_prop; auto. split. 
       + intros s A.
         apply in_set_ltr_lift_elim in A; auto.
         destruct A as [x [A B]].
         assert (C := ir l x).
         apply sym in C.
         assert (D := trn _ _ _ C B).
         exact (in_set_right_congruence S eqS sym trn _ _ _ D A).          
       + intros s A.
         apply in_set_ltr_lift_intro; auto.
         assert (B := ir l s).
         exists s. auto. 
Qed. 

Lemma ltr_lift_not_left_cancellative (nlc : ltr_not_left_cancellative L S eqS ltr) :
      ltr_not_left_cancellative L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr) .
Proof. destruct nlc as [[l [a b]] [P Q]].
       exists (l, (a :: nil, b ::nil)).
       compute. rewrite P, Q. apply sym in P. rewrite P. auto. 
Defined.
 
Lemma ltr_lift_left_cancellative (lc : ltr_left_cancellative L S eqS ltr) :
      ltr_left_cancellative L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr) .
Proof. unfold  ltr_left_cancellative. 
       intros l X Y A.
       apply brel_set_elim_prop in A; auto. destruct A as [A B]. 
       apply brel_set_intro_prop; auto. split. 
       + intros s C.
         assert (D : in_set eqS (ltr_lift eqS ltr l X) (ltr l s) = true).
            apply in_set_ltr_lift_intro; auto. exists s. auto. 
         assert (E := A _ D).
         apply in_set_ltr_lift_elim in E; auto. destruct E as [x [E F]].
         apply lc in F.
         exact (in_set_right_congruence S eqS sym trn _ _ _ F E). 
       + intros s C. 
         assert (D : in_set eqS (ltr_lift eqS ltr l Y) (ltr l s) = true).
            apply in_set_ltr_lift_intro; auto. exists s. auto. 
         assert (E := B _ D).
         apply in_set_ltr_lift_elim in E; auto. destruct E as [x [E F]].
         apply lc in F.
         exact (in_set_right_congruence S eqS sym trn _ _ _ F E). 
Qed. 

Lemma ltr_lift_not_left_constant :
      ltr_not_left_constant L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr) .
Proof. exists (wL, (nil, wS ::nil)). compute. reflexivity. Defined.

End Theory.

Section ACAS.

Section Proofs.

Variables (L : Type)
          (S : Type)
          (eqL : brel L)
          (eqS : brel S)
          (wL : L)          
          (wS : S)
          (ltr : ltr_type L S).

Definition ltr_lift_proofs
           (eqvL : eqv_proofs L eqL)           
           (eqvS : eqv_proofs S eqS)
           (ltrP : left_transform_proofs L S eqS eqL ltr) :
  left_transform_proofs L (finite_set S) (brel_set eqS) eqL (ltr_lift eqS ltr) :=
let refL := A_eqv_reflexive _ _ eqvL in
let ref  := A_eqv_reflexive _ _ eqvS in
let sym  := A_eqv_symmetric _ _ eqvS in
let trn  := A_eqv_transitive _ _ eqvS in
let ltr_cong := A_left_transform_congruence _ _ _ _ _ ltrP in
{|
  A_left_transform_congruence          := ltr_lift_congruence L S eqL eqS refL ref sym trn ltr ltr_cong 
; A_left_transform_is_right_d          :=
                               match A_left_transform_is_right_d _ _ _ _ _ ltrP with
                               | inl irP  => inl (ltr_lift_is_right L S eqL eqS refL ref sym trn ltr ltr_cong irP)
                               | inr nirP => inr (ltr_lift_not_is_right L S eqS ltr nirP)
                               end
; A_left_transform_left_constant_d     := inr (ltr_lift_not_left_constant L S eqS wL wS ltr) 
; A_left_transform_left_cancellative_d :=
                               match A_left_transform_left_cancellative_d _ _ _ _ _ ltrP with
                               | inl  lc => inl(ltr_lift_left_cancellative L S eqL eqS refL ref sym trn ltr ltr_cong lc)
                               | inr nlc => inr(ltr_lift_not_left_cancellative L S eqS sym ltr nlc)
                               end 
|}.

End Proofs.

Definition A_left_transform_lift (L S : Type) (A : A_left_transform L S) :=
let eqvS := A_left_transform_carrier _ _ A in
let eqvL := A_left_transform_label _ _ A in     
let eqS := A_eqv_eq _ eqvS in
let eqL := A_eqv_eq _ eqvL in
let wS := A_eqv_witness S eqvS in
let wL := A_eqv_witness L eqvL in
let eqvSP := A_eqv_proofs _ eqvS in
let eqvLP := A_eqv_proofs _ eqvL in
let refL := A_eqv_reflexive _ _ eqvLP in
let ref := A_eqv_reflexive _ _ eqvSP in
let sym := A_eqv_symmetric _ _ eqvSP in
let trn := A_eqv_transitive _ _ eqvSP in
let ltr := A_left_transform_ltr _ _ A in
let ltrP := A_left_transform_proofs _ _ A in 
let ltr_cong := A_left_transform_congruence _ _ _ _ _ ltrP in 
{|
  A_left_transform_carrier      := A_eqv_set S eqvS 
; A_left_transform_label        := eqvL 
; A_left_transform_ltr          := ltr_lift eqS ltr 
; A_left_transform_exists_id_d  := match A_left_transform_exists_id_d _ _ A with
                        | inl idP  => inl (ltr_lift_exists_id L S eqL eqS refL ref sym trn ltr ltr_cong idP) 
                        | inr nidP => inr (ltr_lift_not_exists_id L S eqS ltr nidP)
                        end
; A_left_transform_exists_ann_d := inl (ltr_lift_exists_ann L S eqS ltr)
; A_left_transform_proofs       := ltr_lift_proofs L S eqL eqS wL wS ltr eqvLP eqvSP ltrP 
; A_left_transform_ast          := Cas_ast ("A_left_transform_lift", [])  (*Ast_ltr_lift (A_left_transform_ast _ _ A)*) 
|}.

End ACAS.


Section CAS.

Definition ltr_lift_certs {L S : Type} (wL : L) (wS : S) (ltrP : @left_transform_certificates L S) :
       @left_transform_certificates L (finite_set S) := 
{|
  left_transform_congruence            := Assert_Ltr_Congruence 
; left_transform_is_right_d            :=
                               match left_transform_is_right_d ltrP with
                               | Certify_Ltr_Is_Right            => Certify_Ltr_Is_Right 
                               | Certify_Ltr_Not_Is_Right (s, t) => Certify_Ltr_Not_Is_Right (s, t :: nil)
                               end
; left_transform_left_constant_d       := Certify_Ltr_Not_Left_Constant (wL, (nil, wS :: nil))
; left_transform_left_cancellative_d   :=
                               match left_transform_left_cancellative_d ltrP with
                               | Certify_Ltr_Left_Cancellative => Certify_Ltr_Left_Cancellative
                               | Certify_Ltr_Not_Left_Cancellative (s, (t, u)) => Certify_Ltr_Not_Left_Cancellative (s, (t :: nil, u :: nil))
                               end 
|}.

Definition left_transform_lift {L S : Type} (A : @left_transform L S) :=
let eqvS := left_transform_carrier _ _ A in
let eqS  := eqv_eq eqvS in
let wS   := eqv_witness eqvS in
let wL   := eqv_witness (left_transform_label _ _ A) in 
{|
  left_transform_carrier      := eqv_set eqvS 
; left_transform_label        := left_transform_label _ _ A 
; left_transform_ltr          := ltr_lift eqS (left_transform_ltr _ _ A)
; left_transform_exists_id_d  :=
                        match left_transform_exists_id_d _ _ A with
                        | Certify_Ltr_Exists_Id id => Certify_Ltr_Exists_Id id
                        | Certify_Ltr_Not_Exists_Id => Certify_Ltr_Not_Exists_Id 
                      end 
; left_transform_exists_ann_d := Certify_Ltr_Exists_Ann nil 
; left_transform_certs        := ltr_lift_certs wL wS (left_transform_certs _ _ A) 
; left_transform_ast          := Cas_ast ("A_left_transform_lift", []) (*Ast_ltr_lift (left_transform_ast _ _ A)*) 
|}.
  

End CAS. 
Section Verify.

Lemma correct_ltr_certs_lift
      (L : Type)
      (S : Type)
      (wL : L)
      (wS : S)       
      (eqL : brel L)
      (eqS : brel S)
      (ltr : ltr_type L S)
      (eqvL : eqv_proofs L eqL)           
      (eqvS : eqv_proofs S eqS)
      (ltrP : left_transform_proofs L S eqS eqL ltr) :
      P2C_left_transform L (finite_set S)
              (brel_set eqS) eqL (ltr_lift eqS ltr) 
              (ltr_lift_proofs L S eqL eqS wL wS ltr eqvL eqvS ltrP)
      = 
      ltr_lift_certs wL wS (P2C_left_transform L S eqS eqL ltr ltrP). 
Proof. destruct ltrP. unfold ltr_lift_certs, ltr_lift_proofs, P2C_left_transform; simpl.
       destruct A_left_transform_left_cancellative_d as [ lc | [[s [t u]] [P Q]]];
       destruct A_left_transform_is_right_d as [ir | [[a b] nir]]; simpl;
       try reflexivity.     
Qed. 

Theorem correct_left_transform_insert (L S : Type) (A : A_left_transform L S)  : 
         left_transform_lift (A2C_left_transform L S A) 
         = 
         A2C_left_transform L (finite_set S) (A_left_transform_lift L S A). 
Proof. destruct A. unfold left_transform_lift, A_left_transform_lift, A2C_left_transform; simpl.
       rewrite correct_eqv_set.       
       rewrite correct_ltr_certs_lift.        
       destruct (A_left_transform_exists_id_d) as [[id P] | nid]; simpl; 
       try reflexivity. 
Qed. 

  
 
End Verify.   

