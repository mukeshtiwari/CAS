Require Import Coq.Bool.Bool.
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop.
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.facts.
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.

Require Import CAS.theory.bop.union. (* for in_set_uop_duplicate_elim_elim, etc.  move? *) 



Section Lift. 

Variable S  : Type. 
Variable rS : brel S. 
Variable bS : binary_op S. 

Variable refS  : brel_reflexive S rS.    
Variable tranS : brel_transitive S rS. 
Variable symS  : brel_symmetric S rS. 

Variable bcong : bop_congruence S rS bS. 
Variable assS : bop_associative S rS bS. 

(* MOVE *)

Lemma in_set_singleton_elim : ∀ (a b : S), in_set rS (a :: nil) b = true -> rS a b = true.
Proof. intros a b H.
       compute in H. case_eq(rS b a); intro F. apply symS. rewrite F in H; auto.
       rewrite F in H; discriminate H.
Qed.        

Lemma in_set_singleton_intro : ∀ (a b : S), rS a b = true -> in_set rS (a :: nil) b = true. 
Proof. intros a b H.
       compute. apply symS in H. rewrite H; auto. 
Qed.


Lemma in_set_two_set_elim : ∀ (a b c: S), in_set rS (a :: b :: nil) c = true -> (rS a c = true) + (rS b c = true).
Proof. intros a b c H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto. 
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       compute in H. discriminate H. 
 Qed.        

Lemma in_set_two_set_intro : ∀ (a b c: S), (rS a c = true) + (rS b c = true) -> in_set rS (a :: b :: nil) c = true.
Proof. intros a b c [H | H].
       apply in_set_cons_intro; auto. 
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.        
 Qed.        


Lemma in_set_three_set_elim : ∀ (a b c d : S), in_set rS (a :: b :: c :: nil) d = true -> (rS a d = true) + (rS b d = true) + (rS c d = true).
Proof. intros a b c d H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto. 
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       compute in H. discriminate H. 
Qed.        

Lemma in_set_three_set_intro : ∀ (a b c d : S), (rS a d = true) + (rS b d = true) + (rS c d = true) -> in_set rS (a :: b :: c :: nil) d = true.
Proof. intros a b c d [[H | H] | H]. 
       apply in_set_cons_intro; auto. 
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.       
 Qed.        


Lemma in_set_four_set_elim : ∀ (a b c d e : S), in_set rS (a :: b :: c :: d :: nil) e = true
                                                -> (rS a e = true) + (rS b e = true) + (rS c e = true) + (rS d e = true).
Proof. intros a b c d e H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto. 
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       compute in H. discriminate H. 
Qed.        

Lemma in_set_four_set_intro : ∀ (a b c d e : S), (rS a e = true) + (rS b e = true) + (rS c e = true) + (rS d e = true)
                                                 -> in_set rS (a :: b :: c :: d :: nil) e = true.
Proof. intros a b c d e [[[H | H] | H] | H].
       apply in_set_cons_intro; auto.  
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.       
 Qed.        



Lemma brel_set_intro_false : ∀ (X Y : finite_set S), 
     {s : S & (in_set rS X s = true) * (in_set rS Y s = false)} → brel_set rS X Y = false. 
Proof. intros X Y [ s [T F]]. 
       case_eq(brel_set rS X Y); intro H. 
          apply brel_set_elim in H. destruct H as [L R]. 
          assert (K := brel_subset_elim S rS symS tranS X Y L s T). 
          rewrite K in F. discriminate. 
          reflexivity. 
Defined.

Lemma in_set_left_congruence : ∀ (a : S) (X Y : finite_set S),
    brel_set rS X Y = true -> in_set rS X a = true -> in_set rS Y a = true.
Proof. intros a X Y H1 H2. 
       apply brel_set_elim in H1.
       destruct H1 as [H1 _]. 
       assert (K := brel_subset_elim _ _ symS tranS X Y H1). 
       apply K; auto. 
Qed.

Lemma in_set_left_congruence_v2 : ∀ (X Y : finite_set S),
    brel_set rS X Y = true -> ∀ (a : S), in_set rS X a = in_set rS Y a.
Proof. intros X Y H a. 
       apply brel_set_elim in H.
       destruct H as [H1 H2]. 
       assert (K1 := brel_subset_elim _ _ symS tranS X Y H1).
       assert (K2 := brel_subset_elim _ _ symS tranS Y X H2).        
       case_eq(in_set rS X a); intro J1; case_eq(in_set rS Y a); intro J2; auto.
       apply K1 in J1. rewrite J1 in J2. exact J2.
       apply K2 in J2. rewrite J1 in J2. exact J2.       
Qed.


Lemma in_set_congruence : ∀ (a b : S) (X Y : finite_set S),
    brel_set rS X Y = true -> rS a b = true -> in_set rS X a = in_set rS Y b.
Proof. intros a b X Y H1 H2.
       assert (J1 := in_set_right_congruence S rS symS tranS _ _ X H2).
       apply symS in H2. assert (J2 := in_set_right_congruence S rS symS tranS _ _ Y H2).        
       assert (Ma := in_set_left_congruence_v2 X Y H1 a).       
       assert (Mb := in_set_left_congruence_v2 X Y H1 b).
       case_eq(in_set rS X a); intro K1; case_eq(in_set rS Y b); intro K2; auto.
       rewrite (J1 K1) in Mb. rewrite <- Mb in K2. exact K2.
       rewrite (J2 K2) in Ma. rewrite K1 in Ma. exact Ma.
Qed. 

(* end MOVE *) 

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

Lemma bop_lift_nil_left : ∀ (X : finite_set S), bop_lift rS bS nil X = nil.
Proof. intro X. compute; auto. Qed.

Lemma bop_lift_nil_right : ∀ (X : finite_set S), bop_lift rS bS X nil = nil.
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
       apply in_set_concat_elim in H; auto. destruct H as [H | H].
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
  in_set rS (bop_lift rS bS X Y) a = true -> 
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
           in_set rS (bop_lift rS bS X Y) (bS x y) = true. 
Proof. intros X Y x y H1 H2. 
       unfold bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_list_product_intro; auto.        
Qed.

Lemma  in_set_bop_lift_intro_v2 :
   ∀ (X Y : finite_set S),  ∀ (a x y : S), 
        in_set rS X x = true -> 
        in_set rS Y y = true ->
        rS a (bS x y) = true -> 
           in_set rS (bop_lift rS bS X Y) a = true. 
Proof. intros X Y a x y H1 H2 H3. 
       unfold bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply symS in H3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_list_product_left bS X Y) H3).
       apply M. 
       apply in_set_list_product_intro; auto.        
Qed. 


Lemma  lift_lemma_1 : 
   ∀ (a : S) (s t u : finite_set S) ,
   in_set rS (bop_lift rS bS (bop_lift rS bS s t) u) a = true
   → in_set rS (bop_lift rS bS s (bop_lift rS bS t u)) a = true.
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
       apply (in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS (a0 :: s) (bop_lift rS bS (a1 :: t) (a2 :: u))) K).
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
   in_set  rS (bop_lift rS bS s (bop_lift rS bS t u)) a = true
    → in_set  rS (bop_lift rS bS (bop_lift rS bS s t) u) a = true. 
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
       apply (in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS (bop_lift rS bS (a0 :: s) (a1 :: t)) (a2 :: u)) K).
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


Lemma bop_lift_associative : bop_associative (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros s t u. 
       apply brel_set_intro. 
       split; apply brel_subset_intro; auto.
       intro a. apply lift_lemma_1.
       intro a. apply lift_lemma_2.       
Qed. 

Lemma bop_lift_subset :   ∀ (X1 X2 Y1 Y2 : finite_set S),  
  brel_subset rS X1 Y1 = true -> 
  brel_subset rS X2 Y2 = true -> 
      brel_subset rS (bop_lift rS bS X1 X2) (bop_lift rS bS Y1 Y2) = true. 
Proof. intros X1 X2 Y1 Y2 H1 H2.
       apply brel_subset_intro; auto.
       assert (K1 := brel_subset_elim _ _ symS tranS _ _ H1); auto.
       assert (K2 := brel_subset_elim _ _ symS tranS _ _ H2); auto.       
       intros a J.
       apply in_set_bop_lift_elim in J; auto. destruct J as [x [y [[P1 P2] P3]]].
       apply symS in P3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS Y1 Y2) P3).
       apply M. 
       apply in_set_bop_lift_intro; auto.        
Qed. 

Lemma bop_lift_congruence : bop_congruence (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 H1 H2. 
       apply brel_set_elim in H1. apply brel_set_elim in H2. 
       destruct H1 as [L1 R1]. destruct H2 as [L2 R2]. 
       apply brel_set_intro. 
       split; apply bop_lift_subset; auto. 
Qed. 


Lemma bop_lift_subset_commutative : 
     bop_commutative S rS bS -> ∀ (X Y : finite_set S), brel_subset rS (bop_lift rS bS X Y) (bop_lift rS bS Y X) = true.
Proof. intros comm X Y. 
       apply brel_subset_intro; auto. 
       intros a H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (C := comm x y).
       assert (D := tranS _ _ _ P3 C).
       apply symS in D.       
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS Y X) D).
       apply M. 
       apply in_set_bop_lift_intro; auto.
Qed.        
  
Lemma bop_lift_commutative : 
     bop_commutative S rS bS -> bop_commutative (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. unfold bop_commutative. intros commS X Y. 
       apply brel_set_intro. 
       split; apply bop_lift_subset_commutative; auto. 
Qed. 

Lemma bop_lift_not_commutative : 
     bop_not_commutative S rS bS -> bop_not_commutative (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros [[x y] P]. 
       exists ((x :: nil), (y :: nil)).
       compute. rewrite P; auto. 
Qed. 


Lemma bop_lift_exists_ann : bop_exists_ann (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. exists nil. intro X. split. 
          rewrite bop_lift_nil_left; auto. 
          rewrite bop_lift_nil_right; auto.           
Defined. 

Lemma bop_lift_exists_id : bop_exists_id S rS bS  -> bop_exists_id (finite_set S) (brel_set rS) (bop_lift rS bS). 
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
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS (i :: nil) X) L).
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
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS X (i :: nil)) R).
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


Lemma bop_lift_contains_product : ∀ (a b : S) (X Y : finite_set S), in_set rS (bop_lift rS bS (a :: X) (b :: Y)) (bS a b) = true.
Proof. intros a b X Y.
       unfold  bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply bop_list_product_left_contains_product; auto. 
Qed. 


Lemma bop_lift_not_exists_id (s : S) : bop_not_exists_id S rS bS  -> bop_not_exists_id (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. unfold bop_not_exists_id. unfold bop_not_is_id. 
       intros H X.
       destruct X.
       exists (s :: nil). compute; auto.
       destruct (H s0) as [u [G | G]].
       exists (u :: nil). 
       left.  case_eq(brel_set rS (bop_lift rS bS (s0 :: X) (u :: nil)) (u :: nil) ); intro K; auto. 
       apply brel_set_elim in K. destruct K as [K1 K2].
       assert (J2 := brel_subset_elim _ _ symS tranS _ _ K1 (bS s0 u)).
       assert (K3 : in_set rS (u :: nil) (bS s0 u) = true). apply J2. 
       apply bop_lift_contains_product.
       apply in_set_cons_elim in K3; auto.
       destruct K3 as [K3 | K3]. apply symS in K3. rewrite K3 in G. discriminate G. 
       compute in K3.  discriminate K3.

       exists (u :: nil).
       right.
       case_eq(brel_set rS (bop_lift rS bS (u :: nil) (s0 :: X)) (u :: nil)); intro K; auto. 
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
    bop_not_idempotent (finite_set S) (brel_set rS) (bop_lift rS bS). 
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
    bop_idempotent (finite_set S) (brel_set rS) (bop_lift rS bS). 
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
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS X X) K).
       apply M.  apply in_set_bop_lift_intro; auto. 
 Defined.

Lemma bop_lift_not_is_left (s : S) : bop_not_is_left (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (s :: nil, nil). compute; auto. Defined. 


Lemma bop_lift_not_is_right (s : S) : bop_not_is_right (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, s :: nil). compute; auto. Defined. 

Lemma bop_lift_not_anti_left : bop_not_anti_left (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, nil). compute; auto. Defined. 

Lemma bop_lift_not_anti_right : bop_not_anti_right (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, nil). compute; auto. Defined. 

Lemma bop_lift_not_left_constant (s : S) : bop_not_left_constant (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (s :: nil, (s :: nil, nil)). compute; auto. Defined. 

Lemma bop_lift_not_right_constant (s : S) : bop_not_right_constant (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (s :: nil, (s :: nil, nil)). compute; auto. Defined. 


Lemma bop_lift_not_left_cancellative (s : S) (f : S -> S) (ntS : brel_not_trivial S rS f) :
         bop_not_left_cancellative (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. destruct (ntS s) as [L R].
       exists (nil, (s :: nil, (f s) :: nil)).
       compute; auto.
       rewrite L; auto. 
Defined. 

Lemma bop_lift_not_right_cancellative (s : S) (f : S -> S) (ntS : brel_not_trivial S rS f) :
        bop_not_right_cancellative (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. destruct (ntS s) as [L R].
       exists (nil, (s :: nil, (f s) :: nil)).
       compute; auto.
       rewrite L; auto. 
Defined. 


(* selectivity *)

Lemma ltran_list_product_is_left_elim : bop_is_left S rS bS ->   ∀ (a b : S) (X : finite_set S),
  in_set rS (ltran_list_product bS a X) b = true -> rS a b = true. 
Proof. intros IL a b X H. induction X. compute in H. discriminate H. 
       unfold ltran_list_product in H. fold (@ltran_list_product S) in H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       assert (K := IL a a0). apply symS in K. apply (tranS _ _ _ K H). 
       apply IHX; auto.
Qed. 


Lemma bop_list_product_is_left_elim : bop_is_left S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS (bop_list_product_left bS X Y) a = true -> in_set rS X a = true. 
Proof. intros IL a X Y H. induction X. compute in H. discriminate H. 
       apply in_set_cons_intro; auto.   
       unfold bop_list_product_left in H. fold (@bop_list_product_left S) in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H].
       assert (K := ltran_list_product_is_left_elim IL a0 a Y H). 
       left; auto.
       right. apply IHX; auto.
Qed.



Lemma ltran_list_product_is_left_intro : bop_is_left S rS bS ->  ∀ (a b : S) (X : finite_set S),
      rS a b = true ->
      brel_set rS nil X = false -> in_set rS (ltran_list_product bS a X) b = true.
Proof. intros IL a b X E F.
       destruct X. 
       compute in F. discriminate F.
       unfold ltran_list_product. fold (@ltran_list_product S).       
       apply in_set_cons_intro; auto.
       left. assert (K := IL a s). apply (tranS _ _ _ K E). 
Qed.

Lemma ltran_list_product_is_right_intro : bop_is_right S rS bS ->  ∀ (a b c : S) (X : finite_set S),
      rS b c = true -> in_set rS (ltran_list_product bS a (b :: X)) c = true.
Proof. intros IR a b c X E.
       unfold ltran_list_product. fold (@ltran_list_product S).       
       apply in_set_cons_intro; auto.
       left. assert (K := IR a b). apply (tranS _ _ _ K E). 
Qed.

Lemma bop_list_product_is_left_intro : bop_is_left S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS X a = true -> (brel_set rS nil Y = false) -> (in_set rS (bop_list_product_left bS X Y) a = true). 
Proof. intros IL a X Y H1 H2. induction X. compute in H1. discriminate H1.
       apply in_set_cons_elim in H1; auto. 
       destruct H1 as [H1 | H1].
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro; auto.
       left. apply (ltran_list_product_is_left_intro IL a0 a Y H1 H2). 
       assert (K := IHX H1).
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro; auto.
Qed. 

Lemma bop_list_product_is_right_intro : bop_is_right S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS Y a = true -> (brel_set rS nil X = false) -> (in_set rS (bop_list_product_left bS X Y) a = true). 
Proof. intros IR a X Y H1 H2. induction Y. compute in H1. discriminate H1.
       apply in_set_cons_elim in H1; auto. 
       destruct H1 as [H1 | H1].
       destruct X.
       compute in H2. discriminate H2. 
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro; auto.
       left. apply (ltran_list_product_is_right_intro IR s a0 a Y H1). 
       assert (K := IHY H1).
       apply in_set_list_product_elim in K.
       destruct K as [x [y [[P1 P2] P3]]].
       apply symS in P3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_list_product_left bS X (a0 :: Y)) P3).
       apply M. 
       apply in_set_list_product_intro; auto. 
       apply in_set_cons_intro; auto.
Qed. 


Lemma ltran_list_product_is_right_elim : bop_is_right S rS bS ->   ∀ (a b : S) (X : finite_set S),
      in_set rS (ltran_list_product bS a X) b = true -> {c : S & (in_set rS X c = true) * (rS c b = true)}.
Proof. intros IR a b X. 
       induction X. intro H. 
       compute in H. discriminate H. 
       intro H. unfold ltran_list_product in H. fold (@ltran_list_product S) in H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       exists a0. split. 
       compute. rewrite refS; auto.
       assert (K := IR a a0). apply symS in K. apply (tranS _ _ _ K H). 
       destruct (IHX H) as [c [P Q]].
       exists c. split; auto.
       apply in_set_cons_intro; auto. 
Qed. 

Lemma bop_list_product_is_right_elim : bop_is_right S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS (bop_list_product_left bS X Y) a = true -> in_set rS Y a = true. 
Proof. intros IL a X Y H. induction X. 
       compute in H. discriminate H.
       unfold bop_list_product_left in H. fold (@bop_list_product_left S) in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H].
       apply ltran_list_product_is_right_elim in H; auto. destruct H as [c [P Q]].
       apply (in_set_right_congruence _ _ symS tranS _ _ _ Q P). 
       apply IHX; auto. 
Qed.        


Lemma bop_lift_selective_v1 : bop_is_left S rS bS -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. unfold bop_is_left. unfold bop_selective.
       intros L X Y.
       assert (refSet := brel_set_reflexive _ _ refS symS).
       assert (tranSet := brel_set_transitive _ _ refS symS tranS).
       assert (congSet := brel_set_congruence _ _ refS symS tranS).               

       case_eq(brel_set rS nil X); intro J1; case_eq(brel_set rS nil Y); intro J2.
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil nil)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil Y)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 (refSet Y)).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       right. assert (K1 : brel_set rS nil (bop_lift rS bS X nil)= true). rewrite bop_lift_nil_right.  compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ (refSet X) J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet Y)).
             rewrite <- K4. exact J2. 
       left.
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
       apply bop_list_product_is_left_intro; auto. 
Qed. 


Lemma bop_lift_selective_v2 : bop_is_right S rS bS -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. unfold bop_is_right. unfold bop_selective.
       intros R X Y.
       assert (refSet := brel_set_reflexive _ _ refS symS).
       assert (tranSet := brel_set_transitive _ _ refS symS tranS).
       assert (congSet := brel_set_congruence _ _ refS symS tranS).               
       
       case_eq(brel_set rS nil X); intro J1; case_eq(brel_set rS nil Y); intro J2.
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil nil)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil Y)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 (refSet Y)).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       right. assert (K1 : brel_set rS nil (bop_lift rS bS X nil)= true). rewrite bop_lift_nil_right.  compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ (refSet X) J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet Y)).
             rewrite <- K4. exact J2. 
       right. 
       apply brel_set_intro. split; apply brel_subset_intro; auto.

       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (K1 := R x y).
       assert (K2 := tranS _ _ _ P3 K1).
       apply symS in K2. assert (M := in_set_right_congruence _ _ symS tranS _ _ Y K2).
       apply M; auto.


       intros a H.
       unfold bop_lift. 
       apply in_set_dup_elim_intro; auto.
       apply bop_list_product_is_right_intro; auto. 
Qed. 


Definition exactly_two (S : Type) (r : brel S) (s t : S)  
  := (r s t = false) * (∀ (a : S), (r s a = true) + (r t a = true)).

Definition brel_exactly_two (S : Type) (r : brel S) 
  := { z : S * S & match z with (s, t) =>  exactly_two S r s t end}.

Definition brel_not_exactly_two (S : Type) (r : brel S) 
  := ∀ (s t : S), (r s t = true) + {a : S &  (r s a = false) * (r t a = false)}.

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

Lemma testX : ∀ (X Z Y W : finite_set S),
  brel_set rS X Z = true -> 
  brel_set rS Y W = true -> 
  brel_set rS (bop_lift rS bS X Y) X = brel_set rS (bop_lift rS bS Z W) Z.
Proof. intros X Z Y W H1 H2.
       assert (C := bop_lift_congruence _ _ _ _ H1 H2).
       assert (D := brel_set_congruence _ _ refS symS tranS).
       assert (E := D _ _ _ _ C H1). 
       exact E.
Qed.

Lemma testY : ∀ (X Z Y W : finite_set S),
  brel_set rS X Z = true -> 
  brel_set rS Y W = true -> 
     brel_set rS (bop_lift rS bS X Y) Y = brel_set rS (bop_lift rS bS Z W) W.
Proof. intros X Z Y W H1 H2.
       assert (C := bop_lift_congruence _ _ _ _ H1 H2).
       assert (D := brel_set_congruence _ _ refS symS tranS).
       assert (E := D _ _ _ _ C H2). 
       exact E.
Qed.


Lemma bop_lift_compute_1_by_2 : ∀ (a b c : S),  
    brel_set rS (bop_lift rS bS (a :: nil) (b :: c :: nil)) ((bS a b):: (bS a c) :: nil) = true.
Proof. intros a b c.
       apply brel_set_intro. split.
          apply brel_subset_intro; auto. intros e H. 
          apply in_set_bop_lift_elim in H; auto.
          destruct H as [x [y [[H1 H2] H3]]].
          apply in_set_two_set_intro.
          apply in_set_singleton_elim in H1.
          apply in_set_two_set_elim in H2.
          destruct H2 as [H2 | H2];
          assert (H4 := tranS _ _ _ H3 (symS _ _ (bcong _ _ _ _ H1 H2))); auto.
          apply brel_subset_intro; auto. intros e H.
          apply in_set_two_set_elim in H.
          destruct H as [H | H]. 
             apply (in_set_bop_lift_intro_v2 _ _ e a b); auto.
                apply in_set_singleton_intro. apply refS.
                apply in_set_two_set_intro. left. apply refS.
             apply (in_set_bop_lift_intro_v2 _ _ e a c); auto.
                apply in_set_singleton_intro. apply refS.
                apply in_set_two_set_intro. right. apply refS.
Qed. 


Lemma bop_lift_compute_2_by_1 : ∀ (a b c : S),  
    brel_set rS (bop_lift rS bS (a :: b :: nil) (c :: nil)) ((bS a c):: (bS b c) :: nil) = true.
Proof. intros a b c.
       apply brel_set_intro. split.
          apply brel_subset_intro; auto. intros e H. 
          apply in_set_bop_lift_elim in H; auto.
          destruct H as [x [y [[H1 H2] H3]]].
          apply in_set_two_set_intro.
          apply in_set_two_set_elim in H1.
          apply in_set_singleton_elim in H2.
          destruct H1 as [H1 | H1]; 
          assert (H4 := tranS _ _ _ H3 (symS _ _ (bcong _ _ _ _ H1 H2))); auto.
          apply brel_subset_intro; auto. intros e H.
          apply in_set_two_set_elim in H.
          destruct H as [H | H].
             apply (in_set_bop_lift_intro_v2 _ _ e a c); auto.
                apply in_set_two_set_intro. left. apply refS.
                apply in_set_singleton_intro. apply refS.
             apply (in_set_bop_lift_intro_v2 _ _ e b c); auto.
                apply in_set_two_set_intro. right. apply refS.
                apply in_set_singleton_intro. apply refS.
Qed. 


Lemma bop_lift_compute_2_by_2 : ∀ (a b c d : S),  
    brel_set rS (bop_lift rS bS (a :: b :: nil) (c :: d :: nil)) ((bS a c):: (bS a d) :: (bS b c) :: (bS b d) :: nil) = true.
Proof. intros a b c d.
       apply brel_set_intro. split.
          apply brel_subset_intro; auto. intros e H. 
          apply in_set_bop_lift_elim in H; auto.
          destruct H as [x [y [[H1 H2] H3]]].
          apply in_set_four_set_intro.
          apply in_set_two_set_elim in H1.
          apply in_set_two_set_elim in H2.
          destruct H1 as [H1 | H1];
          destruct H2 as [H2 | H2];
          assert (H4 := tranS _ _ _ H3 (symS _ _ (bcong _ _ _ _ H1 H2))); auto.
          apply brel_subset_intro; auto. intros e H.
          apply in_set_four_set_elim in H.
          destruct H as [[[H | H] | H] | H].
             apply (in_set_bop_lift_intro_v2 _ _ e a c); auto.
                apply in_set_two_set_intro. left. apply refS.
                apply in_set_two_set_intro. left. apply refS.
             apply (in_set_bop_lift_intro_v2 _ _ e a d); auto.
                apply in_set_two_set_intro. left. apply refS.
                apply in_set_two_set_intro. right. apply refS.
             apply (in_set_bop_lift_intro_v2 _ _ e b c); auto.
                apply in_set_two_set_intro. right. apply refS.
                apply in_set_two_set_intro. left. apply refS.
             apply (in_set_bop_lift_intro_v2 _ _ e b d); auto.
                apply in_set_two_set_intro. right. apply refS.
                apply in_set_two_set_intro. right. apply refS.                
Qed. 

Lemma bop_lift_selective_v3 :  bop_idempotent S rS bS -> brel_exactly_two S rS -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros idem [[s t] P] X Y.
       
       assert (Ls := idem s). assert (Rs := symS _ _ Ls). 
       assert (Lt := idem t). assert (Rt := symS _ _ Lt).        
       assert (KX := brel_set_exactly_two_implies_four_subsets s t P X).
       assert (KY := brel_set_exactly_two_implies_four_subsets s t P Y).

       unfold exactly_two in P. destruct P as [F Q]. 
       assert (Kst := Q (bS s t)).       
       assert (Kts := Q (bS t s)). 
       
       destruct KX as [[[KX | KX] | KX] | KX]; destruct KY as [[[KY | KY] | KY] | KY];
       rewrite (testX _ _ _ _ KX KY); rewrite (testY _ _ _ _ KX KY).
       
           
       compute; auto.
       compute; auto.
       compute; auto.        
       compute; auto.
       compute; auto.
       compute; auto.        
       rewrite Ls, Rs; auto. 
       compute; auto.
       destruct Kst as [Kst | Kst].
          rewrite Kst. rewrite (symS _ _ Kst). left; auto.
          rewrite Kst. rewrite (symS _ _ Kst). right; auto.
       destruct Kst as [Kst | Kst].
          left. apply brel_set_intro; split; apply brel_subset_intro; auto; intros a H.
          apply in_set_bop_lift_elim in H.
          destruct H as [x [y [[P1 P2] P3]]].
          compute. compute in P1. apply in_set_cons_elim in P2; auto.
          case_eq(rS x s); intro P4. destruct P2 as [P2 | P2].
          apply symS in P4. assert (P5 := bcong _ _ _ _ P4 P2). apply symS in P5. 
          assert (P6 := tranS _ _ _ P3 P5).
          assert (P7 := tranS _ _ _ P6 Ls). rewrite P7; auto.
          compute in P2. case_eq(rS y t); intro P5.
          assert (P6 := bcong _ _ _ _ P4 P5).
          assert (P7 := tranS _ _ _ P3 P6). apply symS in Kst. 
          assert (P8 := tranS _ _ _ P7 Kst). rewrite P8; auto.
          assert (P6 : rS y s = true). destruct (Q y) as [L | R]. 
          apply symS. exact L.  apply symS in R. rewrite R in P5. discriminate P5. 
          assert (P7 := bcong _ _ _ _ P4 P6).
          assert (P8 := tranS _ _ _ P3 P7).
          assert (P9 := tranS _ _ _ P8 Ls). rewrite P9; auto. 
          rewrite P4 in P1. discriminate P1.
          (**)
          apply in_set_singleton_elim in H.
          unfold bop_lift. apply in_set_uop_duplicate_elim_intro; auto. 
          unfold bop_list_product_left.
          apply in_set_concat_intro. left.
          unfold ltran_list_product.
          apply in_set_cons_intro; auto. left.
          apply (tranS _ _ _ Ls H). 
          (* * * *)
          right. apply brel_set_intro; split; apply brel_subset_intro; auto; intros a H.
          apply in_set_bop_lift_elim in H.
          destruct H as [x [y [[P1 P2] P3]]].
          compute. compute in P1. apply in_set_cons_elim in P2; auto.
          case_eq(rS x s); intro P4. destruct P2 as [P2 | P2].
          apply symS in P4. assert (P5 := bcong _ _ _ _ P4 P2). apply symS in P5. 
          assert (P6 := tranS _ _ _ P3 P5).
          assert (P7 := tranS _ _ _ P6 Ls). rewrite P7; auto.
          compute in P2. case_eq(rS y t); intro P5.
          assert (P6 := bcong _ _ _ _ P4 P5).
          assert (P7 := tranS _ _ _ P3 P6). apply symS in Kst. 
          assert (P8 := tranS _ _ _ P7 Kst). rewrite P8; auto. 
          (* same up to here *)
          case_eq(rS a s); intro P9; auto. 
          rewrite P5 in P2. discriminate P2.
          rewrite P4 in P1. discriminate P1.          
          (**)
          apply in_set_cons_elim in H; auto.
          destruct H as [H | H].
          apply (in_set_bop_lift_intro_v2 _ _ a s s ); auto.
          compute; rewrite refS; auto.
          compute. rewrite refS; auto. 
          apply symS in H. exact (tranS _ _ _ H Rs).
          apply in_set_singleton_elim in H; auto. 
          apply (in_set_bop_lift_intro_v2 _ _ a s t ); auto.
          compute; rewrite refS; auto.
          compute. rewrite refS. case_eq(rS t s); intro J1; auto. 
          apply symS in H. exact (tranS _ _ _ H Kst).
          
       admit. 

       compute. destruct Kts as [Kts | Kts].
          rewrite Kts. rewrite (symS _ _ Kts). right; auto.
          rewrite Kts. rewrite (symS _ _ Kts). left; auto.

       compute. rewrite Lt, Rt; auto. 

       admit. 

       compute; auto.  

       admit.

       admit.

       left. assert (J1 : brel_set rS (bop_lift rS bS (s :: t :: nil) (s :: t :: nil)) ((bS s s) :: (bS s t) :: (bS t s) :: (bS t t) :: nil) = true). admit.
              
Admitted.


Lemma bop_lift_selective :
  bop_is_left S rS bS +
  bop_is_right S rS bS +   
  (bop_idempotent S rS bS) * (brel_exactly_two S rS) -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros [[IL | IR] | [idim et]].
       apply bop_lift_selective_v1; auto.
       apply bop_lift_selective_v2; auto.
       apply bop_lift_selective_v3; auto.
Qed.        

Lemma bop_lift_not_selective_v1 (s : S) (f : S -> S):
  brel_not_trivial S rS f -> 
  bop_not_is_left S rS bS -> 
  bop_not_is_right S rS bS ->   
  bop_not_idempotent S rS bS -> bop_not_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros ntS [[x y] NL] [[u v] NR]  [a Nidem]. 
       exists (a :: nil, a :: nil).
       compute. rewrite Nidem; auto.
Qed.


Lemma in_set_cons_false_elim  : ∀ (a b : S) (X : finite_set S),
   in_set rS (a :: X) b = false -> ((rS a b = false) * (in_set rS X b = false)).   
Proof. intros a b X H.
       case_eq(rS a b); intro K1; case_eq(in_set rS X b); intro K2; auto.
       rewrite (in_set_cons_intro _ _ symS a b X (inl K1)) in H. discriminate H.
       rewrite (in_set_cons_intro _ _ symS a b X (inl K1)) in H. discriminate H.
       rewrite (in_set_cons_intro _ _ symS a b X (inr K2)) in H. discriminate H.       
Qed.        

Lemma in_set_cons_false_intro : ∀ (a b : S) (X : finite_set S),
    ((rS a b = false) * (in_set rS X b = false)) -> in_set rS (a :: X) b = false. 
Proof. intros a b X [L R].
       case_eq(in_set rS (a :: X) b); intro J; auto.
       destruct (in_set_cons_elim _ _ symS _ _ _ J) as [F | F].
       rewrite F in L. discriminate L.
       rewrite F in R. discriminate R.        
Qed.

Lemma brel_subset_false_elim : 
  ∀ (x w : finite_set S),
    brel_subset rS x w = false -> {a : S & (in_set rS x a = true) * (in_set rS w a = false)}. 
Proof. induction x; intros w H. 
       compute in H. discriminate H.
       unfold brel_subset in H. fold (@brel_subset S) in H. 
       apply andb_is_false_left in H.
       destruct H as [H | H].
       exists a. split. apply in_set_cons_intro; auto. exact H.
       destruct (IHx _ H) as [a0 [K1 K2]].
       exists a0. split. 
       apply in_set_cons_intro; auto.
       exact K2. 
Defined. 

Lemma brel_subset_false_intro : ∀ (x w : finite_set S), 
           {a : S & (in_set rS x a = true) * (in_set rS w a = false)} -> brel_subset rS x w = false. 
Proof. induction x.
       intros w [a [L R]].
       compute in L. discriminate L.
       intros w [b [L R]].  apply in_set_cons_elim in L; auto.
       unfold brel_subset. fold (@brel_subset S).
       destruct L as [L | L].
       apply andb_is_false_right. left.
       case_eq(in_set rS w a); intro J; auto.
       assert (K := in_set_right_congruence _ _ symS tranS _ _ _ L J).  rewrite K in R. discriminate R.
       apply andb_is_false_right. right.
       apply IHx.
       exists b. split; auto. 
Defined. 

Lemma brel_set_false_elim : ∀ (X Y : finite_set S), brel_set rS X Y = false -> (brel_subset rS X Y = false) + (brel_subset rS Y X = false).
Proof. intros X Y H.
       case_eq(brel_subset rS X Y); intro K1; case_eq(brel_subset rS Y X); intro K12; auto.
       rewrite (brel_set_intro  _ _ _ _ (K1, K12)) in H. discriminate H.        
Defined. 

Lemma brel_set_false_intro : ∀ (X Y : finite_set S), 
     (brel_subset rS X Y = false) + (brel_subset rS Y X = false) -> brel_set rS X Y = false.
Proof. intros X Y [H | H].
       case_eq(brel_set rS X Y); intro K; auto.
       apply brel_set_elim in K; auto. destruct K as [K1 K2]. rewrite K1 in H. discriminate H.
       case_eq(brel_set rS X Y); intro K; auto.
       apply brel_set_elim in K; auto. destruct K as [K1 K2]. rewrite K2 in H. discriminate H.
Defined. 


Lemma bop_lift_not_selective_initial_solution :
  bop_not_is_left S rS bS -> 
  bop_not_is_right S rS bS -> 
  (bop_idempotent S rS bS) -> 
  (brel_not_exactly_two S rS) -> bop_not_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros [[a b] NL] [[c d] NR] idem Net.

       assert (F1 : rS a b = false).
          case_eq(rS a b); intro F; auto.
          assert (K := idem a).
          assert (J := bcong _ _ _ _ (refS a) F).
          apply symS in K. assert (M := tranS _ _ _ K J).  apply symS in M. rewrite M in NL. discriminate NL. 

       assert (F2 : rS c d = false).
          case_eq(rS c d); intro F; auto.
          assert (K := idem d).
          assert (J := bcong _ _ _ _ F (refS d)).
          assert (M := tranS _ _ _ J K).  rewrite M in NR. discriminate NR.

       case_eq(rS (bS a b) b); intro J1.
          case_eq(rS (bS c d) c); intro J2. 
             destruct (Net a b) as [J3 | J3].
             rewrite J3 in F1. discriminate F1.
             destruct J3 as [e1 [J3 J4]].
             case_eq (rS e1 (bS e1 b)); intro J5; case_eq (rS b (bS e1 b)); intro J6.
                (* J5 : rS e1 (bS e1 b) = true,  J6 : rS b (bS e1 b) = true *) 
                apply symS in J5. rewrite (tranS _ _ _ J6 J5) in J4. discriminate J4.
                (* J5 : rS e1 (bS e1 b) = true,  J6 : rS b (bS e1 b) = false *) 
                (* {e1, a}.{b} = {e1b, ab} = {e1, b} *)
                exists (e1 :: a :: nil, b :: nil). split.
                   apply brel_set_false_intro; auto. 
                   right. apply brel_subset_false_intro; auto.
                   exists a. split.
                      compute. rewrite J3. rewrite refS. auto. 
                      case_eq(in_set rS (bop_lift rS bS (e1 :: a :: nil) (b :: nil)) a); intro K; auto.
                      apply in_set_bop_lift_elim in K; auto.
                      destruct K as [x [y [[K1 K2] K3]]].
                      apply in_set_cons_elim in K1; auto. apply in_set_cons_elim in K2; auto. 
                      destruct K1 as [K1 | K1]; destruct K2 as [K2 | K2].
                      assert (K4 := bcong _ _ _ _ K1 K2).
                      apply symS in K4. assert (K5 := tranS _ _ _ K3 K4).
                      apply symS in J5. assert (K6 := tranS _ _ _ K5 J5). rewrite K6 in J3. discriminate J3.
                      compute in K2. discriminate K2. 
                      apply in_set_cons_elim in K1; auto. destruct K1 as [K1 | K1].
                         assert (K4 := bcong _ _ _ _ K1 K2). 
                         apply symS in K4. assert (K5 := tranS _ _ _ K3 K4).
                         assert (K6 := tranS _ _ _ K5 J1). rewrite K6 in F1. discriminate F1.
                         compute in K1. discriminate K1.
                         compute in K2. discriminate K2.
                      case_eq(brel_set rS (bop_lift rS bS (e1 :: a :: nil) (b :: nil)) (b :: nil)); intro J7; auto. 
                         apply brel_set_elim in J7; auto. destruct J7 as [J7 J8].
                         assert (J9 := brel_subset_elim _ _ symS tranS _ _ J7 (bS e1 b)). 
                         assert (J10 : in_set rS (bop_lift rS bS (e1 :: a :: nil) (b :: nil)) (bS e1 b) = true).
                            apply in_set_bop_lift_intro; auto.
                                apply in_set_cons_intro; auto. apply in_set_cons_intro; auto. 
                         assert (J11 := J9 J10).
                         apply in_set_cons_elim in J11; auto. destruct J11 as [J11 | J11].
                            rewrite J11 in J6. discriminate J6. 
                            compute in J11. discriminate J11. 
                (* J5 : rS e1 (bS e1 b) = false,  J6 : rS b (bS e1 b) = true *) 
                destruct (Net c d) as [J7 | J7].
                rewrite J7 in F2. discriminate F2.
                destruct J7 as [e2 [J7 J8]].
                case_eq (rS e2 (bS c e2)); intro J9; case_eq (rS c (bS c e2)); intro J10.
                   (* J9 : rS e2 (bS c e2) = true   J10 : rS c (bS c e2) = true*) 
                   apply symS in J9. rewrite (tranS _ _ _ J10 J9) in J7. discriminate J7.
                   (* J9 : rS e2 (bS c e2) = true   J10 : rS c (bS c e2) = false *) 
                   (* {c}.{e2 d} = {ce2, cd} = {e2, c} *)
                   exists (c :: nil, e2 :: d :: nil). split.
                      (* brel_set rS (bop_lift rS bS (c :: nil) (e2 :: d :: nil)) (c :: nil) = false *)
                      apply brel_set_false_intro; auto.
                      left. apply brel_subset_false_intro; auto.
                      exists (bS c e2). split.
                         apply in_set_bop_lift_intro; auto.
                         compute. rewrite refS; auto.
                         apply in_set_cons_intro; auto. 
                         compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J10). auto. 
                      (* brel_set rS (bop_lift rS bS (c :: nil) (e2 :: d :: nil)) (e2 :: d :: nil) = false *)
                      apply brel_set_false_intro; auto.
                      left.
                      case_eq(brel_subset rS (bop_lift rS bS (c :: nil) (e2 :: d :: nil)) (e2 :: d :: nil) ); intro J11; auto.
                         assert (J12 := brel_subset_elim _ _ symS tranS _ _ J11 (bS c d)).
                         assert (J13 : in_set rS (bop_lift rS bS (c :: nil) (e2 :: d :: nil)) (bS c d) = true).
                             apply in_set_bop_lift_intro; auto. 
                             compute. rewrite refS; auto.
                             apply in_set_cons_intro; auto. right. compute. rewrite refS; auto.
                         assert (J14 := J12 J13).
                         apply in_set_cons_elim in J14; auto. destruct J14 as [J14 | J14 ].
                            assert (J15 := tranS _ _ _ J14 J2).
                            apply symS in J15. rewrite J15 in J7. discriminate J7.
                            apply in_set_cons_elim in J14; auto. destruct J14 as [J14 | J14].
                               assert (J15 := tranS _ _ _ J14 J2). apply symS in J15. rewrite J15 in F2. discriminate F2. 
                               compute in J14. discriminate J14. 
                   (* J9 : rS e2 (bS c e2) = false   J10 : rS d (bS c e2) = true *) 
                   case_eq (rS e1 (bS e1 e2)); intro J11; case_eq (rS e2 (bS e1 e2)); intro J12.
                      apply symS in J12. assert (J13 := tranS _ _ _ J11 J12).
                      (* DO THIS CASE EARLY ??? *) 
                      case_eq (rS e1 (bS e1 a)); intro J14; case_eq (rS a (bS e1 a)); intro J15.
                         apply symS in J14. rewrite (tranS _ _ _ J15 J14) in J3. discriminate J3.
                         (* {e}{a, b} = {ea, eb} = {e, b} *)
                         exists(e1 :: nil, a :: b :: nil). split.
                            apply brel_set_false_intro; auto.
                            left. apply brel_subset_false_intro; auto.
                            exists b. split. 
                               apply (in_set_bop_lift_intro_v2 _ _ b e1 b); auto.
                                  compute. rewrite refS; auto. 
                                  compute. rewrite refS. rewrite (brel_symmetric_implies_dual _ _ symS _ _ F1). auto. 
                               compute. rewrite J4; auto.                                 
                            apply brel_set_false_intro; auto. 
                            right. apply brel_subset_false_intro; auto.
                            exists a. split.
                               compute. rewrite refS; auto.                                 
                               case_eq(in_set rS (bop_lift rS bS (e1 :: nil) (a :: b :: nil)) a); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto.
                                  destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto. 
                                  destruct J16 as [J16 | J16]; destruct J17 as [J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17).  apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J15. discriminate J15.
                                     apply in_set_cons_elim in J17; auto. destruct J17 as [J17 | J17].
                                        assert (J19 := bcong _ _ _ _ J16 J17). 
                                        apply symS in J19. assert (J20 := tranS _ _ _ J18 J19). apply symS in J6.
                                        rewrite (tranS _ _ _ J20 J6) in F1. discriminate F1. 
                                        compute in J17. discriminate J17.
                                     compute in J16. discriminate J16.
                                     compute in J16. discriminate J16.
                         case_eq (rS e2 (bS d e2)); intro J16; case_eq (rS d (bS d e2)); intro J17.
                            apply symS in J16. rewrite (tranS _ _ _ J17 J16) in J8. discriminate J8.
                            (* {c,d}{e2} = {ce2, de2} = {c, e2} *)
                            exists (c :: d :: nil, e2 :: nil). split. 
                               apply brel_set_false_intro; auto.
                               right.  apply brel_subset_false_intro; auto.
                               exists d. split. 
                                  compute. rewrite refS. case_eq(rS d c); intro J18; auto.
                                  case_eq(in_set rS (bop_lift rS bS (c :: d :: nil) (e2 :: nil)) d); intro J18; auto.
                                  apply in_set_bop_lift_elim in J18. destruct J18 as [x [y [[J18 J19] J20]]].
                                  apply in_set_cons_elim in J18; auto. apply in_set_cons_elim in J19; auto.
                                  destruct J18 as [J18 | J18]; destruct J19 as [J19 | J19].
                                     assert (J21 := bcong _ _ _ _ J18 J19).
                                     apply symS in J21. assert (J22 := tranS _ _ _ J20 J21).
                                     apply symS in J22. rewrite (tranS _ _ _ J10 J22) in F2. discriminate F2.
                                     compute in J19. discriminate J19.                                      
                                     apply in_set_cons_elim in J18; auto. destruct J18 as [J18 | J18].
                                        assert (J21 := bcong _ _ _ _ J18 J19). apply symS in J21.
                                        assert (J22 := tranS _ _ _ J20 J21). rewrite J22 in J17. discriminate J17.
                                        compute in J18. discriminate J18. 
                                     compute in J19. discriminate J19.                                      
                               apply brel_set_false_intro; auto.
                               left. apply brel_subset_false_intro; auto.
                               exists (bS c e2). split.
                                  apply in_set_bop_lift_intro; auto.
                                     compute. rewrite refS; auto.
                                     compute. rewrite refS; auto.
                                  compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J9). auto.
                             case_eq(rS a c); intro J18.    
                               (*  {a}{b, e} = {ab, ae} = {b, a} *)
                               exists (a :: nil, e2 :: b :: nil). split.
                                  apply brel_set_false_intro; auto.
                                  left. apply brel_subset_false_intro; auto.
                                  exists b. split.
                                     apply (in_set_bop_lift_intro_v2 _ _ b a b); auto.
                                        compute; rewrite refS; auto.
                                        compute. rewrite refS. case_eq(rS b e2); intro J19; auto.
                                        compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ F1). auto. 
                                  apply brel_set_false_intro; auto.
                                  right. apply brel_subset_false_intro; auto.
                                  exists e2. split.
                                     compute. rewrite refS. auto. 
                                     case_eq(in_set rS (bop_lift rS bS (a :: nil) (e2 :: b :: nil)) e2); intro J19; auto.
                                        apply in_set_bop_lift_elim in J19; auto.
                                        destruct J19 as [x [y [[J19 J20] J21]]].
                                        apply in_set_singleton_elim in J19; auto. 
                                        apply in_set_cons_elim in J20; auto. 
                                        destruct J20 as [J20 | J20].
                                           assert (J22 := bcong _ _ _ _ J19 J20).
                                           apply symS in J22. assert (J23 := tranS _ _ _ J21 J22).
                                           assert (J24 := bcong _ _ _ _ J18 (refS e2)).
                                           rewrite (tranS _ _ _ J23 J24) in J9. discriminate J9.
                                        apply in_set_singleton_elim in J20; auto. 
                                        assert (J22 := bcong _ _ _ _ J19 J20).
                                        apply symS in J22. assert (J23 := tranS _ _ _ J21 J22).
                                        assert (J24 := tranS _ _ _ J23 J1).
                                        assert (J25 := tranS _ _ _ J13 J24).
                                        apply symS in J25. rewrite J25 in J4. discriminate J4. 
                               (* {e, c}{e, a} = {ee, ea, ce ca} = {e, a, c, ca} *)
                               exists (e1 :: c :: nil, e2 :: a :: nil). split.
                                  apply brel_set_false_intro; auto. 
                                  left. apply brel_subset_false_intro; auto.
                                  exists a. split.
                                     apply (in_set_bop_lift_intro_v2 _ _ a e1 a); auto.
                                        compute. rewrite refS; auto.
                                        compute. rewrite refS. case_eq(rS a e2); intro J19; auto.
                                        compute. rewrite J18. rewrite J3. auto. 
                                  apply brel_set_false_intro; auto.
                                  left. apply brel_subset_false_intro; auto.
                                  exists (bS c e2). split.
                                     apply in_set_bop_lift_intro; auto.
                                        compute. rewrite refS. case_eq(rS c e1); intro J19; auto. 
                                        compute. rewrite refS. auto. 
                                     compute. case_eq(rS (bS c e2) e2); intro J19; case_eq(rS (bS c e2) a); intro J20; auto.
                                        apply symS in J20. apply symS in J10. rewrite (tranS _ _ _ J20 J10) in J18. discriminate J18.  
                                        rewrite (tranS _ _ _ J10 J19) in J7. discriminate J7.
                                        apply symS in J20. apply symS in J10. rewrite (tranS _ _ _ J20 J10) in J18. discriminate J18. 
                          (* {d}{e2} = {de2}*)
                          exists (d:: nil, e2 :: nil). compute. rewrite J16, J17.
                               rewrite (brel_symmetric_implies_dual _ _ symS _ _ J16). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J17). auto. 
                         (* {e}{a} = {ea} *)                         
                         exists(e1 :: nil, a :: nil). split.
                            apply brel_set_false_intro; auto.
                            right. apply brel_subset_false_intro; auto.
                            exists e1. split. 
                               compute. rewrite refS; auto.
                               case_eq(in_set rS (bop_lift rS bS (e1 :: nil) (a :: nil)) e1); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto. destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto.
                                  destruct J16 as[J16 | J16]; destruct J17 as[J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17). apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J14. discriminate J14.
                                  compute in J17. discriminate J17.
                                  compute in J16. discriminate J16.
                                  compute in J17. discriminate J17.
                            apply brel_set_false_intro; auto.
                            right. apply brel_subset_false_intro; auto.
                            exists a. split. 
                               compute. rewrite refS; auto.
                               case_eq(in_set rS (bop_lift rS bS (e1 :: nil) (a :: nil)) a); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto. destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto.
                                  destruct J16 as[J16 | J16]; destruct J17 as[J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17). apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J15. discriminate J15.
                                  compute in J17. discriminate J17.
                                  compute in J16. discriminate J16.
                                  compute in J17. discriminate J17.
                      (* {e1}{e2, b} = {e1e2, e1b} = {e1, b} *)
                      exists (e1 :: nil, e2 :: b :: nil). split.
                         apply brel_set_false_intro; auto.
                         left. apply brel_subset_false_intro; auto.
                         exists (bS e1 b). split. 
                             apply in_set_bop_lift_intro; auto.                          
                                compute. rewrite refS; auto. 
                                compute. rewrite refS.
                                case_eq(rS b e2); intro J13; auto.
                                compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J5). auto. 
                         apply brel_set_false_intro; auto.
                         left. apply brel_subset_false_intro; auto.
                         exists e1. split.
                            apply (in_set_bop_lift_intro_v2 _ _ e1 e1 e2); auto. 
                               compute. rewrite refS; auto. 
                               compute. rewrite refS. auto.
                               compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J4).
                               assert (J13 : rS e1 e2 = false).
                                  case_eq(rS e1 e2); intro J13; auto. apply symS in J13. rewrite (tranS _ _ _ J13 J11) in J12. discriminate J12.                                            rewrite J13; auto.                    
                      (* {e1, c}{e2} = {e1e2, ce2} = {e2, c} *)
                      exists (e1 :: c :: nil, e2 :: nil). split.
                         apply brel_set_false_intro; auto.
                         right. apply brel_subset_false_intro; auto.
                         exists e1. split. 
                            compute. rewrite refS; auto. 
                            case_eq(in_set rS (bop_lift rS bS (e1 :: c :: nil) (e2 :: nil)) e1); intro J13; auto.
                               apply in_set_bop_lift_elim in J13; auto.
                               destruct J13 as [x [y [[J13 J14] J15]]].
                               apply in_set_cons_elim in J13; auto. apply in_set_cons_elim in J14; auto.
                               destruct J13 as [J13 | J13]; destruct J14 as [J14 | J14].
                                  assert (J16 := bcong _ _ _ _ J13 J14). apply symS in J16.
                                  rewrite (tranS _ _ _ J15 J16) in J11. discriminate J11. 
                                  compute in J14. discriminate J14. 
                                  apply in_set_singleton_elim in J13. (***********)
                                  assert (J16 := bcong _ _ _ _ J13 J14). apply symS in J16.
                                  assert (J17 := tranS _ _ _ J15 J16). apply symS in J17.
                                  case_eq(rS c e1); intro J18.
                                     assert (J19 := bcong _ _ _ _ J18 (refS e2)).
                                     assert (J20 := tranS _ _ _ J10 J19).
                                     apply symS in J12. rewrite (tranS _ _ _ J20 J12) in J7. discriminate J7.
                                     rewrite (tranS _ _ _ J10 J17) in J18. discriminate J18. 
                                  compute in J14. discriminate J14. 
                         apply brel_set_false_intro; auto. 
                         left. apply brel_subset_false_intro; auto.
                         exists c. split.
                            apply (in_set_bop_lift_intro_v2 _ _ c c e2); auto. 
                               compute. rewrite refS. case_eq(rS c e1); intro J13; auto.
                               compute. rewrite refS; auto.
                            compute. rewrite J7; auto. 
                      exists (e1 :: nil, e2 :: nil). compute. rewrite J11, J12.
                         rewrite (brel_symmetric_implies_dual _ _ symS _ _ J11). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J12). auto. 
                   (* J9 : rS e2 (bS c e2) = false   J10 : rS c (bS c e2) =  false*)
                   exists (c :: nil, e2 :: nil). compute. rewrite J9, J10.
                      rewrite (brel_symmetric_implies_dual _ _ symS _ _ J9). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J10). auto. 
                (* J5 : rS e1 (bS e1 b) = false,  J6 : rS b (bS e1 b) = false *)                 
                exists (e1 :: nil, b :: nil). compute. rewrite J5, J6.
                   rewrite (brel_symmetric_implies_dual _ _ symS _ _ J5). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J6). auto. 
          (* J2 : rS (bS c d) c = false *)           
          exists (c :: nil, d :: nil). compute.  rewrite NR. rewrite J2. auto.
       (* J1 : rS (bS a b) b = false *)           
       exists (a :: nil, b :: nil). compute.  rewrite NL. rewrite J1. auto. 
Defined. 

(* end selectivity *)

Definition brel_at_least_three (S : Type) (r : brel S) 
  := { z : S * (S * S) &
      match z with (s, (t, u)) =>
       (r s t = false) *
       (r s u = false) *
       (r t u = false) 
      end}.


Lemma brel_at_least_thee_implies_not_exactly_two :
  ∀ (T : Type) (eq : brel T),
    brel_symmetric T eq ->
    brel_transitive T eq ->     
    brel_at_least_three T eq -> brel_not_exactly_two T eq.
Proof. intros T eq sy tr [[s [t u] ] [[P1 P2] P3]] x y.
       case_eq(eq x y); intro J.
       left; auto. 
       right.
       case_eq(eq x s); intro K1; case_eq(eq x t); intro K2; case_eq(eq x u); intro K3.
       apply sy in K1. rewrite (tr _ _ _ K1 K2) in P1. discriminate P1. 
       apply sy in K1. rewrite (tr _ _ _ K1 K2) in P1. discriminate P1.        
       apply sy in K1. rewrite (tr _ _ _ K1 K3) in P2. discriminate P2. 
       case_eq(eq y s); intro J1; case_eq(eq y t); intro J2; case_eq(eq y u); intro J3.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J3) in P2. discriminate P2.
          exists t; split; auto. 
          apply sy in J2. rewrite (tr _ _ _ J2 J3) in P3. discriminate P3.
          exists u; split; auto.
          exists t; split; auto.
          exists t; split; auto.                     
       apply sy in K2. rewrite (tr _ _ _ K2 K3) in P3. discriminate P3.
       case_eq(eq y s); intro J1; case_eq(eq y t); intro J2; case_eq(eq y u); intro J3.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J3) in P2. discriminate P2.
          exists u; split; auto. 
          apply sy in J2. rewrite (tr _ _ _ J2 J3) in P3. discriminate P3.
          exists u; split; auto.
          exists s; split; auto.
          exists u; split; auto.                     
       case_eq(eq y s); intro J1; case_eq(eq y t); intro J2; case_eq(eq y u); intro J3.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J3) in P2. discriminate P2.
          exists t; split; auto. 
          apply sy in J2. rewrite (tr _ _ _ J2 J3) in P3. discriminate P3.
          exists s; split; auto.
          exists s; split; auto.
          exists s; split; auto.                     
       case_eq(eq y s); intro J1; case_eq(eq y t); intro J2; case_eq(eq y u); intro J3.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J2) in P1. discriminate P1.
          apply sy in J1. rewrite (tr _ _ _ J1 J3) in P2. discriminate P2.
          exists t; split; auto. 
          apply sy in J2. rewrite (tr _ _ _ J2 J3) in P3. discriminate P3.
          exists s; split; auto.
          exists s; split; auto.
          exists s; split; auto.                     
Defined. 

Lemma brel_set_at_least_three (s : S) (f : S -> S):
  brel_not_trivial S rS f -> 
  brel_at_least_three (finite_set S) (brel_set rS).
Proof. intro nt. destruct (nt s) as [L R].
       exists (nil, (s :: nil, (f s) :: nil)). 
       compute. rewrite L; auto. 
Defined. 


Lemma brel_set_not_exactly_two (s : S) (f : S -> S):
  brel_not_trivial S rS f -> 
  brel_not_exactly_two (finite_set S) (brel_set rS).
Proof. intro nt. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto.
       apply (brel_set_at_least_three s f); auto. 
Defined.

End Lift. 