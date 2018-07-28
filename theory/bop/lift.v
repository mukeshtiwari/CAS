Require Import Coq.Bool.Bool.
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.
Require Import CAS.theory.bop.union. 

Section Lift. 

Variable S  : Type. 
Variable rS : brel S. 
Variable bS : binary_op S. 

Variable refS  : brel_reflexive S rS.    
Variable tranS : brel_transitive S rS. 
Variable symS  : brel_symmetric S rS. 

Variable bcong : bop_congruence S rS bS. 
Variable assS : bop_associative S rS bS. 

Definition bop_lift : binary_op(finite_set S) := 
    λ x y, uop_duplicate_elim rS (bop_list_product_left bS x y). 


(* MOVE *) 
Lemma brel_set_intro_false : ∀ (X Y : finite_set S), 
     {s : S & (in_set rS X s = true) * (in_set rS Y s = false)} → brel_set rS X Y = false. 
Proof. intros X Y [ s [T F]]. 
       case_eq(brel_set rS X Y); intro H. 
          apply brel_set_elim in H. destruct H as [L R]. 
          assert (K := brel_subset_elim S rS symS tranS X Y L s T). 
          rewrite K in F. discriminate. 
          reflexivity. 
Defined.

Lemma bop_list_product_nil_left : ∀ (X : finite_set S), bop_list_product_left bS nil X = nil.
Proof. intro X. compute; auto. Qed.

Lemma bop_list_product_nil_right : ∀ (X : finite_set S), bop_list_product_left bS X nil = nil.
Proof. induction X.
       compute; auto.
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       rewrite IHX.
       rewrite List.app_nil_r.
       compute; auto.
Qed.        

Lemma bop_lift_nil_left : ∀ (X : finite_set S), bop_lift nil X = nil.
Proof. intro X. compute; auto. Qed.

Lemma bop_lift_nil_right : ∀ (X : finite_set S), bop_lift X nil = nil.
Proof. intro X. unfold bop_lift. rewrite bop_list_product_nil_right. 
       compute; auto.
Qed.        


Lemma  in_set_ltran_list_product_elim :
  ∀ (a b : S) (Y : finite_set S),
    in_set rS (ltran_list_product bS a Y) b = true ->   
       {y : S & (in_set rS Y y = true) * (rS b (bS a y) = true)}.
Proof. intros a b. induction Y.
       compute. intro F. discriminate F.
       intro H. 
       unfold ltran_list_product in H. fold (@ltran_list_product S) in H.
       apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       exists a0. split; auto. 
       compute. rewrite (refS a0); auto. 

       destruct (IHY H) as [y [P1 P2]].
       exists y. split; auto.
       apply in_set_cons_intro; auto. 
Defined.


Lemma  in_set_ltran_list_product_intro :
   ∀ (x y : S) (Y : finite_set S),  
        in_set rS Y y = true -> 
           in_set rS (ltran_list_product bS x Y) (bS x y) = true. 
Proof. intros x y. induction Y.
       compute; auto. 
       intro H. apply in_set_cons_elim in H; auto. destruct H as [H | H].
       unfold ltran_list_product. fold (@ltran_list_product S).
       apply in_set_cons_intro; auto.
       assert (K := IHY H).
       unfold ltran_list_product. fold (@ltran_list_product S).       
       apply in_set_cons_intro; auto.
Qed. 

Lemma  in_set_list_product_elim :
 ∀ (a : S) (X Y : finite_set S),  in_set rS (bop_list_product_left bS X Y) a = true ->   
       {x : S & {y : S & (in_set rS X x = true) * (in_set rS Y y = true) * (rS a (bS x y) = true)}}.
Proof. intro a. induction X; induction Y. 
       compute. intro F. discriminate F.
       simpl. intro F. discriminate F.
       simpl. rewrite bop_list_product_nil_right. simpl. intro F. discriminate F.
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       intro H.
       apply in_set_concat_elim in H. destruct H as [H | H].
          destruct (in_set_ltran_list_product_elim a0 a _ H) as [y [Q1 Q2]].
          exists a0; exists y. split; auto. split; auto.
          apply in_set_cons_intro; auto.
          
          destruct (IHX _ H) as [x [y [[P1 P2] P3]]].
          exists x; exists y. split; auto. split; auto. 
          apply in_set_cons_intro; auto. 
Defined.        


Lemma  in_set_list_product_intro :
   ∀ (X Y : finite_set S),  ∀ (x y : S), 
        in_set rS X x = true -> 
        in_set rS Y y = true -> 
           in_set rS (bop_list_product_left bS X Y) (bS x y) = true. 
Proof. induction X. 
       intros Y x y H1 H2. compute in H1. discriminate.
       intros Y x y H1 H2.
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro.
       destruct (in_set_cons_elim _ _ symS _ _ _ H1) as [J | J].

       left. assert (N : rS (bS a y) (bS x y) = true). apply bcong. apply symS; auto. apply refS.
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (ltran_list_product bS a Y) N).
       apply M. 
       apply in_set_ltran_list_product_intro; auto. 

       right. apply IHX; auto.
Defined.        

          
Lemma  in_set_bop_lift_elim :
 ∀ (X Y : finite_set S),  ∀ (a : S), 
  in_set rS (bop_lift X Y) a = true -> 
   {x : S & {y : S & (in_set rS X x = true) * (in_set rS Y y = true) * (rS a (bS x y) = true)}}.
Proof. intros X Y a H. 
       unfold bop_lift in H.
       apply in_set_uop_duplicate_elim_elim in H.
       apply in_set_list_product_elim; auto. 
Defined. 

Lemma  in_set_bop_lift_intro :
   ∀ (X Y : finite_set S),  ∀ (x y : S), 
        in_set rS X x = true -> 
        in_set rS Y y = true -> 
           in_set rS (bop_lift X Y) (bS x y) = true. 
Proof. intros X Y x y H1 H2. 
       unfold bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_list_product_intro; auto.        
Qed. 

Lemma  lift_lemma_1 : 
   ∀ (a : S) (s t u : finite_set S) ,
   in_set rS (bop_lift (bop_lift s t) u) a = true
   → in_set rS (bop_lift s (bop_lift t u)) a = true.
Proof. intro a. induction s.
       intros t u H. compute in H. discriminate H. 
       induction t. 
       intros u H. rewrite bop_lift_nil_right in H. compute in H. discriminate H.  
       induction u.
       rewrite bop_lift_nil_right. simpl. intro F. discriminate F.
       intro H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       apply in_set_bop_lift_elim in P1.
       destruct  P1 as [z [w [[Q1 Q2] Q3]]].
       apply in_set_cons_elim in Q1; auto.
       apply in_set_cons_elim in Q2; auto.
       apply in_set_cons_elim in P2; auto.
       assert (K : rS (bS z (bS w y)) a = true).
          assert (J1 : rS (bS (bS z w) y) (bS z (bS w y))  = true). apply assS.
          assert (J2 : rS (bS x y) (bS (bS z w) y)  = true). apply (bcong _ _ _ _ Q3 (refS y)).
          assert (J3 := tranS _ _ _ J2 J1).
          assert (J4 := tranS _ _ _ P3 J3).
          apply symS. exact J4. 
       apply (in_set_right_congruence _ _ symS tranS _ _ (bop_lift (a0 :: s) (bop_lift (a1 :: t) (a2 :: u))) K).
       destruct Q1 as [Q1 | Q1]; destruct Q2 as [Q2 | Q2]; destruct P2 as [P2 | P2].
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.       
Qed.        


Lemma  lift_lemma_2 : 
   ∀ (a : S) (s t u : finite_set S) ,
   in_set  rS (bop_lift s (bop_lift t u)) a = true
    → in_set  rS (bop_lift (bop_lift s t) u) a = true. 
Proof. intro a. induction s.
       intros t u H. compute in H. discriminate H. 
       induction t. 
       intros u H. rewrite bop_lift_nil_left in H. rewrite bop_lift_nil_right in H. compute in H. discriminate H.  
       induction u.
       rewrite bop_lift_nil_right. rewrite bop_lift_nil_right. simpl. intro F. discriminate F.
       intro H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       apply in_set_bop_lift_elim in P2.
       destruct  P2 as [z [w [[Q1 Q2] Q3]]].
       apply in_set_cons_elim in Q1; auto.
       apply in_set_cons_elim in Q2; auto.
       apply in_set_cons_elim in P1; auto.
       assert (K : rS (bS (bS x z) w) a = true).
          assert (J1 : rS (bS (bS x z) w) (bS x (bS z w))  = true). apply assS.
          assert (J2 : rS (bS x y) (bS x (bS z w))  = true). apply (bcong _ _ _ _ (refS x) Q3).
          apply symS in J1. assert (J3 := tranS _ _ _ J2 J1).
          assert (J4 := tranS _ _ _ P3 J3).
          apply symS. exact J4. 
       apply (in_set_right_congruence _ _ symS tranS _ _ (bop_lift (bop_lift (a0 :: s) (a1 :: t)) (a2 :: u)) K).
       destruct Q1 as [Q1 | Q1]; destruct Q2 as [Q2 | Q2]; destruct P1 as [P1 | P1].
       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.       
Qed.        


Lemma bop_lift_associative : bop_associative (finite_set S) (brel_set rS) bop_lift. 
Proof. intros s t u. 
       apply brel_set_intro. 
       split; apply brel_subset_intro; auto.
       intro a. apply lift_lemma_1.
       intro a. apply lift_lemma_2.       
Qed. 

Lemma bop_lift_subset :   ∀ (X1 X2 Y1 Y2 : finite_set S),  
  brel_subset rS X1 Y1 = true -> 
  brel_subset rS X2 Y2 = true -> 
      brel_subset rS (bop_lift X1 X2) (bop_lift Y1 Y2) = true. 
Proof. intros X1 X2 Y1 Y2 H1 H2.
       apply brel_subset_intro; auto.
       assert (K1 := brel_subset_elim _ _ symS tranS _ _ H1); auto.
       assert (K2 := brel_subset_elim _ _ symS tranS _ _ H2); auto.       
       intros a J.
       apply in_set_bop_lift_elim in J; auto. destruct J as [x [y [[P1 P2] P3]]].
       apply symS in P3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift Y1 Y2) P3).
       apply M. 
       apply in_set_bop_lift_intro; auto.        
Qed. 

Lemma bop_lift_congruence : bop_congruence (finite_set S) (brel_set rS) bop_lift. 
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 H1 H2. 
       apply brel_set_elim in H1. apply brel_set_elim in H2. 
       destruct H1 as [L1 R1]. destruct H2 as [L2 R2]. 
       apply brel_set_intro. 
       split; apply bop_lift_subset; auto. 
Qed. 


Lemma bop_lift_subset_commutative : 
     bop_commutative S rS bS -> ∀ (X Y : finite_set S), brel_subset rS (bop_lift X Y) (bop_lift Y X) = true.
Proof. intros comm X Y. 
       apply brel_subset_intro; auto. 
       intros a H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (C := comm x y).
       assert (D := tranS _ _ _ P3 C).
       apply symS in D.       
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift Y X) D).
       apply M. 
       apply in_set_bop_lift_intro; auto.
Qed.        
  
Lemma bop_lift_commutative : 
     bop_commutative S rS bS -> bop_commutative (finite_set S) (brel_set rS) bop_lift. 
Proof. unfold bop_commutative. intros commS X Y. 
       apply brel_set_intro. 
       split; apply bop_lift_subset_commutative; auto. 
Qed. 

Lemma bop_lift_not_commutative : 
     bop_not_commutative S rS bS -> bop_not_commutative (finite_set S) (brel_set rS) bop_lift. 
Proof. intros [[x y] P]. 
       exists ((x :: nil), (y :: nil)).
       compute. rewrite P; auto. 
Qed. 


Lemma bop_lift_exists_ann : bop_exists_ann (finite_set S) (brel_set rS) bop_lift. 
Proof. exists nil. intro X. split. 
          rewrite bop_lift_nil_left; auto. 
          rewrite bop_lift_nil_right; auto.           
Defined. 

Lemma bop_lift_exists_id : bop_exists_id S rS bS  -> bop_exists_id (finite_set S) (brel_set rS) bop_lift. 
Proof. intros [i P]. exists (i :: nil). intro X.
       split. 

       apply brel_set_intro.
       split.

       apply brel_subset_intro; auto.
       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (T : rS y a = true). 
           compute in P1. case_eq(rS x i); intro J.
           destruct (P y) as [L R].
           assert (K1 := bcong _ _ _ _ J (refS y)).
           assert (K2 := tranS _ _ _ P3 K1).
           assert (K3 := tranS _ _ _ K2 L).
           apply symS in K3. exact K3.
           rewrite J in P1. discriminate P1. 
       assert (M := in_set_right_congruence _ _ symS tranS _ _ X T).
       apply M; auto. 

       apply brel_subset_intro; auto.
       intros a H.
       destruct (P a) as [L R].
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift (i :: nil) X) L).
       apply M.
       apply in_set_bop_lift_intro; auto.
       compute. rewrite refS; auto.

       apply brel_set_intro.
       split.
       
       apply brel_subset_intro; auto.
       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (T : rS x a = true). 
           compute in P2. case_eq(rS y i); intro J.
           destruct (P x) as [L R].
           assert (K1 := bcong _ _ _ _ (refS x) J).
           assert (K2 := tranS _ _ _ P3 K1).
           assert (K3 := tranS _ _ _ K2 R).
           apply symS in K3. exact K3.
           rewrite J in P2. discriminate P2. 
       assert (M := in_set_right_congruence _ _ symS tranS _ _ X T).
       apply M; auto.

       apply brel_subset_intro; auto.
       intros a H.
       destruct (P a) as [L R].
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift X (i :: nil)) R).
       apply M.
       apply in_set_bop_lift_intro; auto.
       compute. rewrite refS; auto.
Defined.

Lemma bop_list_product_left_contains_product : ∀ (a b : S) (X Y : finite_set S), in_set rS (bop_list_product_left bS (a :: X) (b :: Y)) (bS a b) = true.
Proof. intros a b X Y.
       unfold bop_list_product_left. fold (@bop_list_product_left (finite_set S)).
       unfold ltran_list_product. fold (@ltran_list_product S).
       apply in_set_concat_intro. left.
       apply in_set_cons_intro; auto. 
Qed.


Lemma bop_lift_contains_product : ∀ (a b : S) (X Y : finite_set S), in_set rS (bop_lift (a :: X) (b :: Y)) (bS a b) = true.
Proof. intros a b X Y.
       unfold  bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply bop_list_product_left_contains_product; auto. 
Qed. 


Lemma bop_lift_not_exists_id (s : S) : bop_not_exists_id S rS bS  -> bop_not_exists_id (finite_set S) (brel_set rS) bop_lift. 
Proof. unfold bop_not_exists_id. unfold bop_not_is_id. 
       intros H X.
       destruct X.
       exists (s :: nil). compute; auto.
       destruct (H s0) as [u [G | G]].
       exists (u :: nil). 
       left.  case_eq(brel_set rS (bop_lift (s0 :: X) (u :: nil)) (u :: nil) ); intro K; auto. 
       apply brel_set_elim in K. destruct K as [K1 K2].
       assert (J2 := brel_subset_elim _ _ symS tranS _ _ K1 (bS s0 u)).
       assert (K3 : in_set rS (u :: nil) (bS s0 u) = true). apply J2. 
       apply bop_lift_contains_product.
       apply in_set_cons_elim in K3; auto.
       destruct K3 as [K3 | K3]. apply symS in K3. rewrite K3 in G. discriminate G. 
       compute in K3.  discriminate K3.

       exists (u :: nil).
       right.
       case_eq(brel_set rS (bop_lift (u :: nil) (s0 :: X)) (u :: nil)); intro K; auto. 
       apply brel_set_elim in K. destruct K as [K1 K2].
       assert (J2 := brel_subset_elim _ _ symS tranS _ _ K1 (bS u s0)).
       assert (K3 : in_set rS (u :: nil) (bS u s0) = true). apply J2. 
       apply bop_lift_contains_product.
       apply in_set_cons_elim in K3; auto.
       destruct K3 as [K3 | K3]. apply symS in K3. rewrite K3 in G. discriminate G. 
       compute in K3.  discriminate K3.
Defined.        

Lemma bop_lift_not_idempotent : 
    bop_not_selective S rS bS -> 
    bop_not_idempotent (finite_set S) (brel_set rS) bop_lift. 
Proof. intros [[a b] [L R]]. exists (a :: b :: nil). 
       apply brel_set_intro_false. 
       exists (bS a b). split.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto. 
       apply in_set_cons_intro; auto. right. apply in_set_cons_intro; auto. 
       compute. rewrite L. rewrite R; auto. 
Qed. 

Lemma bop_lift_idempotent : 
    bop_selective S rS bS -> 
    bop_idempotent (finite_set S) (brel_set rS) bop_lift. 
Proof. intros selS X.
       apply brel_set_intro; auto. split; apply brel_subset_intro; auto. 

       intros a H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       destruct (selS x y) as [L | R].
       assert (K := tranS _ _ _ P3 L). 
       apply symS in K. assert (M := in_set_right_congruence _ _ symS tranS _ _ X K).
       apply M. exact P1. 
       assert (K := tranS _ _ _ P3 R). 
       apply symS in K. assert (M := in_set_right_congruence _ _ symS tranS _ _ X K).
       apply M. exact P2. 
      

       intros a H.
       assert (K : rS (bS a a) a = true). 
          destruct (selS a a) as [L | R]; auto. 
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift X X) K).
       apply M.  apply in_set_bop_lift_intro; auto. 
 Defined.


(* selectivity *)

Lemma bop_lift_selective_v1 : bop_is_left S rS bS -> bop_selective (finite_set S) (brel_set rS) bop_lift.
Admitted.
(*
Proof. unfold bop_is_left. unfold bop_selective.
       intros L X Y. left.
       apply brel_set_intro. split; apply brel_subset_intro; auto.

       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (K1 := L x y).
       assert (K2 := tranS _ _ _ P3 K1).
       apply symS in K2. assert (M := in_set_right_congruence _ _ symS tranS _ _ X K2).
       apply M; auto.


       intros a H.
       unfold bop_lift. 
       apply in_set_dup_elim_intro; auto. 
       induction X. 
       compute in H. discriminate H. 
       apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       unfold bop_list_product_left. fold (@bop_list_product_left S).        
       apply in_set_concat_intro.
       left. destruct Y. 
Defined. 
 *)

Definition exactly_two (S : Type) (r : brel S) (s t : S)  
  := (r s t = false) * (∀ (a : S), (r s a = true) + (r t a = true)).

Definition brel_exactly_two (S : Type) (r : brel S) 
  := { z : S * S & match z with (s, t) =>  exactly_two S r s t end}.

Definition brel_not_exactly_two (S : Type) (r : brel S) 
  := ∀ (s t : S), (r s t = true) + {a : S &  (r s a = false) * (r t a = false)}.

Lemma in_set_left_congruence : ∀ (a : S) (X Y : finite_set S),
    brel_set rS X Y = true -> in_set rS X a = true -> in_set rS Y a = true.
Admitted.

Lemma in_set_congruence : ∀ (a b : S) (X Y : finite_set S),
    brel_set rS X Y = true -> rS a b = true -> in_set rS X a = in_set rS Y b.
Admitted.

Lemma in_set_singleton_elim : ∀ (a b : S), in_set rS (a :: nil) b = true -> rS a b = true.
Admitted.  

Lemma in_set_singleton_intro : ∀ (a b : S), rS a b = true -> in_set rS (a :: nil) b = true. 
Admitted.  


Lemma brel_set_exactly_two_implies_four_subsets : ∀ (s t : S), exactly_two S rS s t -> ∀ (X : finite_set S),
      (brel_set rS X nil = true) +
      (brel_set rS X (s :: nil) = true) +
      (brel_set rS X (t :: nil) = true) +
      (brel_set rS X (s :: t :: nil) = true).
Proof. intros s t et X.
       destruct et as [L R]. 
       induction X.
       left. left. left. compute; auto. 
       destruct IHX as [[[H1 | H2] | H3] | H4]. 

       destruct (R a) as [J | J]. 
       left. left. right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       right. apply (in_set_left_congruence _ _ _ H1 H). 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. apply brel_set_symmetric in H1; auto. apply (in_set_left_congruence _ _ _ H1 H). 
       left. right. 
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       right. apply (in_set_left_congruence _ _ _ H1 H). 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. apply brel_set_symmetric in H1; auto. apply (in_set_left_congruence _ _ _ H1 H). 
           
       
       destruct (R a) as [J | J].
       left. left. right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       left. assert (K := in_set_left_congruence _ _ _ H2 H). compute in K. case_eq(rS x s); intro F.
       apply symS. exact F. rewrite F in K. discriminate K. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       compute in H. discriminate H. 
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       right. apply in_set_cons_intro; auto. left. apply (tranS _ _ _ J H).
       left. assert (K := in_set_left_congruence _ _ _ H2 H). compute in K. case_eq(rS x s); intro F.
       apply symS. exact F. rewrite F in K. discriminate K. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       right. apply symS in H. rewrite (in_set_congruence _ _ _ _ H2 H). compute. rewrite refS; auto. 
       left. compute in H. case_eq(rS x t); intro F. apply symS. apply (tranS _ _ _ F J).  rewrite F in H. discriminate H.

       destruct (R a) as [J | J].
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       right.  assert (K := in_set_left_congruence _ _ _ H3 H). exact K. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. apply brel_set_symmetric in H3; auto. apply (in_set_left_congruence _ _ _ H3 H). 
       left. right. 
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H). 
       left. assert (K := in_set_left_congruence _ _ _ H3 H). compute in K.  case_eq(rS x t); intro F; auto. 
       rewrite F in K. discriminate K.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left.  apply symS in J. apply (tranS _ _ _ J H). 
       compute in H. discriminate H. 

       destruct (R a) as [J | J].
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       compute. destruct (R x) as [F | F]; auto. apply symS in F. rewrite F. right; auto. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. rewrite (in_set_congruence _ _ _ _ H4 (refS x)). 
       apply in_set_cons_intro; auto.        
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       right. compute. assert (K := tranS _ _ _ J H). apply symS in K. rewrite K; auto. 
       compute. destruct (R x) as [F | F]; auto. apply symS in F. rewrite F. right; auto. 

       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       right. apply symS in J. apply symS in H. rewrite (in_set_congruence _ _ _ _ H4 H). 
       apply in_set_cons_intro; auto.
       right. apply in_set_singleton_elim in H. compute in H. 
       apply symS in H. rewrite (in_set_congruence _ _ _ _ H4 H). 
       apply in_set_cons_intro; auto.  right.  apply in_set_cons_intro; auto.  
Defined.         


End Lift. 