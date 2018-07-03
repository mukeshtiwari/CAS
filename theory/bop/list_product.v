Require Import Coq.Bool.Bool.
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_list. 
(*
Require Import CAS.theory.brel2_in_list. 
*) 

(* 

What if we defined 

bop_list_product S bS A B = 
   flatten (map (\a -> a *> A) A) 


*) 



Definition ltran_congruence (U T : Type) (rU : brel U) (rT : brel T) (tr : left_transform U T) := 
   ∀ (s1 s2 : U) (t1 t2 : T), rU s1 s2 = true -> rT t1 t2 = true -> rT (tr s1 t1) (tr s2 t2) = true.

Definition rtran_congruence (U T : Type) (rU : brel U) (rT : brel T) (tr : right_transform U T) := 
   ∀ (s1 s2 : U) (t1 t2 : T), rU s1 s2 = true -> rT t1 t2 = true -> rT (tr t1 s1) (tr t2 s2) = true.





Lemma brel_list_cons_intro : ∀ (S : Type) (r : brel S), 
         ∀ (a b : S) (X  Y : list S), 
             r a b = true -> 
             brel_list r X Y = true -> 
             brel_list r (a :: X) (b :: Y) = true. 
Proof. intros T r  a b X Y H1 H2. 
       unfold brel_list. fold @brel_list. rewrite H1, H2. auto. 
Qed. 

Lemma brel_list_cons_elim : ∀ (S : Type) (r : brel S), 
         ∀ (a b : S) (X  Y : list S), 
             brel_list r (a :: X) (b :: Y) = true -> 
             ((r a b = true) *  (brel_list r X Y = true)). 

Proof. intros T r  a b X Y H. 
       unfold brel_list in H. fold @brel_list in H.
       apply andb_is_true_left in H. assumption. 
Qed. 

Lemma brel_list_nil_elim_left : ∀ (S : Type) (r : brel S), 
         ∀ (X : list S), brel_list r nil X = true -> X = nil. 
Proof. intros T r X H. induction X; auto. compute in H. discriminate. 
Qed. 

Lemma brel_list_nil_elim_right : ∀ (S : Type) (r : brel S), 
         ∀ (X : list S), brel_list r X nil = true -> X = nil. 
Proof. intros T r X H. induction X; auto. compute in H. discriminate. 
Qed. 


Lemma brel_list_app_elim_left : ∀ (S : Type) (r : brel S), 
         brel_reflexive S r -> 
         ∀ (X  Y Z : list S), brel_list r (Z  ++ X) (Z ++ Y) = brel_list r X Y. 
Proof. intros T r refT X Y Z. 
       induction Z; simpl. reflexivity. 
       rewrite refT, IHZ. auto. 
Qed. 

Lemma brel_list_cons_right_elim : ∀ (S : Type) (r : brel S), brel_symmetric S r -> 
        ∀ (Y X: list S)(a : S), 
        brel_list r Y (a :: X) = true ->  
        {b : S & { Z : list S & ( (r a b = true) * ( Y = (b :: Z)) * (brel_list r Z X = true))}}.  
Proof. intros S r symS Y. induction Y; simpl; auto. 
       intros. discriminate.         
       intro X. induction X; simpl; auto. 
       intros a0 H. apply andb_is_true_left in H.  destruct H as [L R]. 
       exists a. exists nil. split; auto. split. apply symS; auto. 
       apply brel_list_nil_elim_right in R. rewrite R. reflexivity. 
       intros a1 H. apply andb_is_true_left in H.  destruct H as [L R]. 
       exists a. exists Y. split; auto. 
Qed. 


Lemma brel_list_app_intro: ∀ (S : Type) (r : brel S) (X  Z Y W : list S), 
        (brel_list r X Z = true) ->  (brel_list r Y W = true) -> brel_list r (X  ++ Y) (Z ++ W) = true. 
Proof. intros S r X. induction X. 
         intro Z. induction Z; simpl; auto. 
         intros. discriminate. 
         intro Z. induction Z; simpl; auto.
         intros. discriminate. 
         intros Y W H1 H2.   
         apply andb_is_true_left in H1. destruct H1 as [L R].
         apply andb_is_true_right. split; auto. 
Qed. 

Lemma rev_nil : ∀ (U : Type), List.rev (@nil U) = @nil U. 
Proof. intro U. compute; auto. Qed. 

Lemma rev_append_not_nil : ∀ (U : Type) (X Y: list U) (a : U) , List.rev_append (a :: X) Y <> nil. 
Proof. intros U X. induction X. intros Y a. compute. intro. discriminate. 
      intros Y b. 
      assert (H : List.rev_append (b :: a :: X) Y = List.rev_append (a :: X) (b :: Y)).
        compute. auto. 
      rewrite H. 
      apply IHX. 
Qed. 

Lemma rev_not_nil : ∀ (U : Type) (X : list U) (a : U) , List.rev (a :: X) <> nil. 
Proof. intros U X a. rewrite List.rev_alt. apply rev_append_not_nil. Qed. 


Lemma rev_nil_elim : ∀ (U : Type) (X : list U), List.rev X = nil -> X = nil. 
Proof. intros U X. destruct X. compute. auto. 
       intro H. apply rev_not_nil in H. elim H. 
Qed. 

Lemma rev_cons : ∀ (U : Type) (X : list U) (a : U) , List.rev (a :: X) = (List.rev X) ++ (a :: nil). 
Proof. intros U X a. 
       assert (H : a :: X = (a :: nil) ++ X). compute. reflexivity. 
       rewrite H. 
       rewrite List.rev_app_distr. 
       assert (J : List.rev (a :: nil) = (a :: nil)). compute. reflexivity. 
       rewrite J. 
       reflexivity. 
Qed. 


Lemma brel_list_app_reverse_left : ∀ (T : Type) (r : brel T), 
   ∀ (X  Y : list T), brel_list r (List.rev X) Y = brel_list  r X (List.rev Y).
Proof. admit. 
Admitted. 

Lemma brel_list_app_reverse : ∀ (T : Type) (r : brel T), 
   ∀ (X  Y : list T), brel_list  r X Y = brel_list  r (List.rev X) (List.rev Y).
Proof. intros T r X Y. 
       assert (H := brel_list_app_reverse_left T r (List.rev X) Y). 
       rewrite List.rev_involutive in H. assumption. 
Qed.          

Lemma brel_list_app_elim_right : ∀ (T : Type) (r : brel T), 
         brel_reflexive T r -> 
         brel_symmetric T r -> 
         ∀ (X  Y Z : list T), 
            brel_list r (X ++ Z) (Y ++ Z) = brel_list r X Y. 
Proof. intros T r refT symT X Y Z. 
       rewrite brel_list_app_reverse. 
       (* rev distributes over ++ *) 
       rewrite List.rev_app_distr. rewrite List.rev_app_distr. 
       rewrite brel_list_app_elim_left; auto. 
       rewrite <- brel_list_app_reverse. reflexivity. 
Qed. 

Lemma brel_list_app_congruence_right : ∀ (S : Type) (r : brel S), 
         brel_reflexive S r -> 
          brel_symmetric S r -> 
         ∀ (X  Y Z : list S), 
             brel_list r X Y = true -> 
             brel_list r (X  ++ Z) (Y ++ Z) = true. 
Proof. intros T r refT symT X Y Z H. 
       induction Z; simpl. 
       rewrite List.app_nil_r. rewrite List.app_nil_r. 
       assumption. 
       rewrite brel_list_app_elim_right; auto. 
Qed. 



Section ListProduct. 

Open Scope list_scope. 

Variable S  : Type. 
Variable rS : brel S. 
Variable bS : binary_op S. 

Variable assocS  : bop_associative S rS bS. 
Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.  
Variable cong_rS : brel_congruence S rS rS. 
Variable cong_bS : bop_congruence S rS bS.

Notation "a [*] b"  := (bS a b) (at level 10).
Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).
Notation "A === B"  := (brel_list rS A B = true) (at level 15).
Notation "A ^* B" := (bop_list_product_left S bS A B) (at level 10, no associativity).
Notation "A *^ B" := (bop_list_product_right S bS A B) (at level 10, no associativity).
Notation "a *> B" := (ltran_list_product S bS a B) (at level 10, no associativity).
Notation "A <* b" := (rtran_list_product S bS A b) (at level 10, no associativity).




(*
Unset Printing Notations.
*) 


(* ltran *) 


Lemma ltran_list_product_nil : ∀ (a : S), a *> nil = nil.
Proof. intro a. compute. auto. Qed. 

Lemma rtran_list_product_nil : ∀ (a : S),  nil <* a = nil.
Proof. intro a. compute. auto. Qed. 


Lemma ltran_list_product_cons : ∀ (a b : S) (X : list S), a *> (b :: X) = (a [*] b) :: (a *> X). 
Proof. intros a b X. induction X. 
       rewrite ltran_list_product_nil. compute. reflexivity. 
       compute. fold ltran_list_product. reflexivity. 
Qed.    


Lemma rtran_list_product_cons : ∀ (a b : S) (X : list S), (b :: X) <* a = (b [*] a) :: (X <* a). 
Proof. intros a b X. induction X. 
       rewrite rtran_list_product_nil. compute. reflexivity. 
       compute. fold rtran_list_product. reflexivity. 
Qed.    


(* must set up order of quantifiers correctly to get the induction to work! *) 
Lemma ltran_list_product_congruence_aux : 
  ∀ (X Y : list S), X === Y → ∀ (s t : S), s == t → s *> X === t *> Y. 
Proof. intro X. induction X. 
       intros. apply brel_list_nil_elim_left in H. rewrite H. compute; auto. 
       intros. 
       apply (brel_list_symmetric _ _ symS) in H. 
       assert (H1 := brel_list_cons_right_elim S rS symS Y X a H).
       destruct H1 as [b [ Z [ [p1 p2] p3 ] ]]. 
       rewrite p2.
       rewrite ltran_list_product_cons.  rewrite ltran_list_product_cons.  
       apply brel_list_cons_intro. 
       apply cong_bS; auto. 
       apply IHX; auto. 
       apply (brel_list_symmetric _ _ symS). assumption. 
Qed. 


Lemma rtran_list_product_congruence_aux : 
  ∀ (X Y : list S), X === Y → ∀ (s t : S), s == t → X <* s === Y <* t. 
Proof. intro X. induction X. 
       intros. apply brel_list_nil_elim_left in H. rewrite H. compute; auto. 
       intros. 
       apply (brel_list_symmetric _ _ symS) in H. 
       assert (H1 := brel_list_cons_right_elim S rS symS Y X a H).
       destruct H1 as [b [ Z [ [p1 p2] p3 ] ]]. 
       rewrite p2.
       rewrite rtran_list_product_cons.  rewrite rtran_list_product_cons.  
       apply brel_list_cons_intro. 
       apply cong_bS; auto. 
       apply IHX; auto. 
       apply (brel_list_symmetric _ _ symS). assumption. 
Qed. 

(* 
   ∀ (s1 s2 : S) (t1 t2 : list S),
   s1 == s2 → t1 === t2 → s1 *> t1 === s2 *> t2
*) 
Lemma ltran_list_product_congruence : 
          ltran_congruence S (list S) rS (brel_list rS) (ltran_list_product S bS). 
Proof. intros s1 s2 X Y H1 H2. 
       assert (C := ltran_list_product_congruence_aux X Y H2 s1 s2 H1). 
       assumption. 
Qed. 

Lemma rtran_list_product_congruence : 
          rtran_congruence S (list S) rS (brel_list rS) (rtran_list_product S bS). 
Proof. intros s1 s2 X Y H1 H2. 
       assert (C := rtran_list_product_congruence_aux X Y H2 s1 s2 H1). 
       assumption. 
Qed. 


Lemma ltran_list_product_associative : ∀ (a b : S) (X : list S), a *> (b *> X) === (a [*] b) *> X. 
Proof. intros a b X. induction X. 
       compute. reflexivity.
       rewrite ltran_list_product_cons.  rewrite ltran_list_product_cons.  rewrite ltran_list_product_cons.  
       assert (C := brel_list_cons_intro S rS). 
       apply C. 
       apply symS. 
       apply assocS. 
       assumption. 
Qed.    


Lemma rtran_list_product_associative : ∀ (a b : S) (X : list S), (X <* b) <* a === X <* (b [*] a). 
Proof. intros a b X. induction X. 
       compute. reflexivity.
       rewrite rtran_list_product_cons.  
       rewrite rtran_list_product_cons.  
       rewrite rtran_list_product_cons.  
       assert (C := brel_list_cons_intro S rS). 
       apply C. 
       apply assocS. 
       assumption. 
Qed.    

Lemma ltran_list_product_left_left_distributive_over_app : ∀ (a : S) (X Y : list S), 
           a *> (X ++ Y) = (a *> X) ++(a *> Y). 
Proof. intros a X Y. induction X; induction Y; simpl. auto. 
       reflexivity. 
       rewrite List.app_nil_r. rewrite List.app_nil_r. reflexivity. 
       rewrite IHX. rewrite ltran_list_product_cons. reflexivity. 
Qed. 



Lemma rtran_list_product_rigth_right_distributive_over_app : ∀ (a : S) (X Y : list S), 
           (X ++ Y) <* a = (X <* a) ++(Y <* a). 
Proof. intros a X Y. induction X; induction Y; simpl. auto. 
       reflexivity. 
       rewrite List.app_nil_r. rewrite List.app_nil_r. reflexivity. 
       rewrite IHX. rewrite rtran_list_product_cons. reflexivity. 
Qed. 


Lemma  ltran_list_product_commutative_lemma1 : 
      bop_commutative S rS bS -> 
      ∀ (Y : list S) (a : S), (a *> Y) === Y ^* (a :: nil).
Proof. intros commS Y.        induction Y; simpl; auto. 
       intros. apply andb_is_true_right; split. apply commS. apply IHY. 
Qed. 

Lemma  ltran_list_product_commutative_lemma2 : 
      bop_commutative S rS bS -> 
      ∀ (Y : list S) (a : S), (a *> Y) === (Y <* a).
Proof. intros commS Y.        induction Y; simpl; auto. 
       intros. apply andb_is_true_right; split. apply commS. apply IHY. 
Qed. 

       

(*****************************************************************)

Lemma bop_list_product_left_left_nil : ∀ (X : list S), nil ^* X = nil. 
Proof. intro X. induction X; compute; auto. Qed. 

Lemma bop_list_product_right_left_nil : ∀ (X : list S), nil *^ X = nil. 
Proof. intro X. induction X; compute; auto. Qed. 

Lemma bop_list_product_left_right_nil : ∀ (X : list S), X ^* nil = nil. 
Proof. intro X. induction X; compute; auto. Qed.    

Lemma bop_list_product_right_right_nil : ∀ (X : list S), X *^ nil = nil. 
Proof. intro X. induction X. 
          compute; auto. 
          unfold bop_list_product_right. fold bop_list_product_right. 
          rewrite IHX. compute. reflexivity. 
Qed.    

       
Lemma bop_list_product_left_left_cons : ∀ (a : S) (X Y : list S), 
         (a :: X) ^* Y = (a *> Y) ++ (X ^* Y). 
Proof. intros. compute; auto. Qed.    


Lemma bop_list_product_right_right_cons : ∀ (a : S) (X Y : list S), 
        X *^ (a :: Y) = (X *^ Y) ++ (X <* a). 
Proof. admit. 
Admitted. 


(* 
Lemma  bop_list_product_left_right_pseudo_commutative : 
      bop_commutative S rS bS -> 
      ∀ (A  B: list S), A ^* B  === B *^ A. 
Proof. intros commS A. induction A. 
          intro B. simpl; auto. rewrite bop_list_product_right_right_nil.  reflexivity. 
          intro B. 
          rewrite bop_list_product_left_left_cons; rewrite bop_list_product_right_right_cons. 
          
Qed. 
*) 


Lemma ltrans_list_product_left_left_partial_distributivity : ∀ (a : S) (X Y : list S), 
           (a *> X) ^* Y === a *> (X ^* Y).
Proof. intros a X Y. induction X; simpl. auto. 
(*     show    ((a[*]a0) *> Y ++ (a *> X) ^* Y) === a *> (a0 *> Y ++ X ^* Y)   *) 
       assert (H1 : (a *> (a0 *> Y ++ X ^* Y)) === (a *> (a0 *> Y) ++ a *> (X ^* Y))). 
          rewrite ltran_list_product_left_left_distributive_over_app. 
       admit. admit. 

(* 
          apply brel_list_reflexive; auto. 
       assert (H2 : (a *> (a0 *> Y) ++ a *> (X ^* Y)) === (((a [*] a0) *> Y) ++ a *> (X ^* Y))). 
          apply brel_list_app_congruence_right; auto. 
          apply ltran_list_product_associative. 
       assert (H3 : (((a [*] a0) *> Y) ++ a *> (X ^* Y)) === (((a [*] a0) *> Y) ++ (a *> X) ^* Y)). 
          rewrite brel_list_app_elim_left; auto. 
          apply brel_list_symmetric; auto. 
       assert ( T := brel_list_transitive S rS transS). 
       unfold brel_transitive in T. 
       assert (T1 := T _ _ _ H1 H2). 
       assert (T2 := T _ _ _ T1 H3). 
       apply brel_list_symmetric; auto.  
*) 
Admitted. 


Lemma rtrans_list_product_right_right_partial_distributivity : ∀ (a : S) (X Y : list S), 
            Y *^ (X <* a)  === (Y *^ X) <* a.
Proof. intros a X Y. induction X; simpl. auto. 
       rewrite bop_list_product_right_right_nil. rewrite rtran_list_product_nil. auto. 
(*          show Y *^ (a0[*]a :: X <* a) === (Y *^ (a0 :: X)) <* a    *) 
            admit. 
(* 
       assert (H1 : (a *> (a0 *> Y ++ X ^* Y)) === (a *> (a0 *> Y) ++ a *> (X ^* Y))). 
          rewrite ltran_list_product_right_right_distributive_over_app. 
          apply brel_list_reflexive; auto. 
       assert (H2 : (a *> (a0 *> Y) ++ a *> (X ^* Y)) === (((a [*] a0) *> Y) ++ a *> (X ^* Y))). 
          apply brel_list_app_congruence_right; auto. 
          apply ltran_list_product_associative. 
       assert (H3 : (((a [*] a0) *> Y) ++ a *> (X ^* Y)) === (((a [*] a0) *> Y) ++ (a *> X) ^* Y)). 
          rewrite brel_list_app_elim_left; auto. 
          apply brel_list_symmetric; auto. 
       assert ( T := brel_list_transitive S rS transS). 
       unfold brel_transitive in T. 
       assert (T1 := T _ _ _ H1 H2). 
       assert (T2 := T _ _ _ T1 H3). 
       apply brel_list_symmetric; auto.  
*) 
Admitted. 


Lemma bop_list_product_left_right_distributive_over_app : ∀ (X Y Z: list S), 
          (X ++ Y) ^* Z = (X ^* Z) ++ (Y ^* Z). 
Proof. intros X Y Z. induction X.  
          simpl. reflexivity. 
(* 
          rewrite IHX. 
          rewrite List.app_assoc. reflexivity. 
*) 
admit. 
Admitted. 


Lemma bop_list_product_right_left_distributive_over_app : ∀ (X Y Z: list S), 
          Z *^ (X ++ Y) = (Z *^ X) ++ (Z *^ Y). 
Proof. intros X Y Z. induction X; simpl. 
(* 
          rewrite bop_list_product_right_right_nil. 
          rewrite bop_list_product_right_right_nil. 
          rewrite bop_list_product_right_right_nil. 

       reflexivity. 
       rewrite IHX. 
       rewrite List.app_assoc. reflexivity. 
*) 
admit. admit.  
Admitted. 

(* 
left distributivity  NO 
Lemma bop_list_product_left_left_distributive : ∀ (X Y Z: list S), Z ^* (X ++ Y)  = (Z ^* X) ++ (Z ^* Y). 
Proof. intros X. induction X; simpl. 
         intros Y Z. rewrite bop_list_product_left_right_nil. simpl. reflexivity. 
       intros. 
       rewrite IHX. 
       rewrite List.app_assoc. reflexivity. 

       [a1, .... ak] ^* (X ++ Y)
       ===         
       (a1 *> (X ++ Y)) ++ ... ++ (ak *> (X ++ Y))
       ===         
       (a1 *> X) ++ (a1 *> Y) ++ ... ++ (ak *> X) ++ (ak *> Y)

       =!= 

       (a1 *> X) ++ ... ++ (ak *> X) ++ (a1 *> Y) ++ ... ++ (ak *> Y)

*) 


(* Quantifier order! *) 
Lemma bop_list_product_left_congruence_aux : 
     ∀ (X Z : list S), X === Z → ∀ (Y W : list S), Y === W → X ^* Y === Z ^* W. 
Proof. intro X. induction X. 
       intros. apply brel_list_nil_elim_left in H. rewrite H. compute; auto. 
       intros.
       apply (brel_list_symmetric _ _ symS) in H. 
       assert (H1 := brel_list_cons_right_elim S rS symS Z X a H).
       destruct H1 as [b [ U [ [p1 p2] p3 ] ]]. 
       rewrite p2.
       rewrite bop_list_product_left_left_cons. rewrite bop_list_product_left_left_cons. 
       apply brel_list_app_intro. 
       apply ltran_list_product_congruence; auto. 
       apply IHX; auto. 
       apply (brel_list_symmetric _ _ symS). assumption. 
Qed. 

(* Quantifier order! 

   ∀ s1 s2 t1 t2 : list S, s1 === t1 → s2 === t2 → s1 ^* s2 === t1 ^* t2
*)  
Lemma bop_list_product_left_congruence : 
      bop_congruence (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. intros X Z Y W H1 H2. 
       assert (C := bop_list_product_left_congruence_aux X Y H1 Z W H2). 
       assumption. 
Qed. 

Lemma bop_list_product_left_associative : 
      ∀ (X Y Z : list S), X ^* (Y ^* Z) === (X ^* Y) ^* Z.      
Proof. 
    intros X Y Z. 
    induction X. 
     compute. reflexivity. 
     assert (H1 : ((a :: X) ^* (Y ^* Z)) === ((a *> (Y ^* Z)) ++ X ^* (Y ^* Z))). 
       rewrite bop_list_product_left_left_cons . apply brel_list_reflexive; auto. 
     assert (H2 : ((a *> (Y ^* Z)) ++ X ^* (Y ^* Z)) === ((a *> (Y ^* Z)) ++ ((X ^* Y) ^* Z))). 
          rewrite brel_list_app_elim_left; auto. 
     assert (H3 : ((a *> (Y ^* Z)) ++ ((X ^* Y) ^* Z)) ===  (((a *> Y) ^* Z) ++ ((X ^* Y) ^* Z))). 
          apply brel_list_app_congruence_right; auto. 
          apply brel_list_symmetric; auto. 
          apply ltrans_list_product_left_left_partial_distributivity. 
     assert (H4 : (((a *> Y) ^* Z) ++ ((X ^* Y) ^* Z))   ===  (((a *> Y) ++ (X ^* Y)) ^* Z) ). 
       rewrite bop_list_product_left_right_distributive_over_app. 
       apply brel_list_reflexive; auto. 
     assert (H5 : (((a *> Y) ++ (X ^* Y)) ^* Z) === (((a :: X) ^* Y) ^* Z)). 
       rewrite bop_list_product_left_left_cons. 
       apply brel_list_reflexive; auto. 
       assert ( T := brel_list_transitive S rS transS). 
       unfold brel_transitive in T. 
       assert (T1 := T _ _ _ H1 H2). 
       assert (T2 := T _ _ _ T1 H3). 
       assert (T3 := T _ _ _ T2 H4). 
       assert (T4 := T _ _ _ T3 H5).
       assumption.  
Qed.

(*  commutative 

[a b] * [c d] = [ac ad bc bd] 

[c d] * [a b] = [ca cb da db] 
              = [ac bc ad bd] 

exists a b c d, ad <> bc 
   -> exists c, exists a b, c <> ab 

forall a b c d, ad = bc 
   <-?-> exists c, forall a b, d = ab 



[a b] * [c d e] = [ac ad ae bc bd be] 

[c d e] * [a b] = [ca cb da db ea eb] 
                = [ac bc ad bd ae be] 
               <> [ac ad ae bc bd be] 


general arg about not_comm 

       [a1, .... ak] ^* B
       ===         
       (a1 *> B) ++ ... ++ (ak *> B)

       [b1, .... bn] ^* A
       ===         
       (b1 *> A) ++ ... ++ (bn *> A)

       (a1 *> B) ++ ... ++ (ak *> B)
       (b1 *> A) ++ ... ++ (bn *> A)


Really want 

       A ^* B  === B *^ A 

       where         

       B * [a1, .... ak]
       === 
       (B <* a1) ++ ... ++ (B <* ak)       

*) 


Definition bop_prop1 := {a : S & {b : S & {c : S & { d : S &  a [*] d != b [*] c}}}}. 
Definition bop_not_prop1 := ∀ (a b c d : S), a [*] d == b [*] c. 
Definition bop_prop2 := {c : S & ∀ (a b : S), a [*] b == c }. 

Lemma bop_prop2_implies_prop1 : bop_prop2 -> bop_not_prop1. 
Proof. intros [ e P ] a b c d. 
       assert (H1 := P a d). 
       assert (H2 := P b c). 
       apply symS in H2. 
       apply (transS _ _ _ H1 H2).
Defined. 

Lemma bop_not_prop1_implies_prop2 : brel_witness S rS -> bop_not_prop1 -> bop_prop2. 
Proof. intros [s Ps] P. 
       exists (s [*] s).
       intros a b. 
       assert (H := P a s s b).  assumption. 
Defined. 

Lemma ttest : bop_left_constant S rS bS -> bop_right_constant S rS bS -> bop_not_prop1. 
Proof. unfold bop_left_constant. unfold bop_right_constant. 
       intros L R a b c d. 
       assert (H1 := L a d c). 
       assert (H2 := R c a b). 
       apply (transS _ _ _ H1 H2).
Qed. 

Lemma ttest2 : bop_not_prop1 -> bop_left_constant S rS bS. 
Proof. unfold bop_left_constant. 
       intros P s t u. apply (P s s u t). 
Qed. 

Lemma ttest3 : bop_not_prop1 -> bop_right_constant S rS bS. 
Proof. unfold bop_right_constant. 
       intros P s t u. apply (P t u s s). 
Qed. 



Lemma bop_list_product_left_not_commutative_tmp1 : 
      bop_not_left_constant S rS bS -> 
      bop_not_commutative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_commutative, bop_not_left_constant. 
       intros [ [a [b c]] P].
       exists (a :: b :: nil, a :: c :: nil). compute. 
       rewrite refS. 
       case_eq(rS (a[*]c) (a[*]b)); intro H. 
         apply symS in H.  rewrite H in P.  discriminate. 
         reflexivity. 
Defined. 

Lemma bop_list_product_left_not_commutative_tmp2 : 
      bop_not_right_constant S rS bS -> 
      bop_not_commutative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_commutative, bop_not_left_constant. 
       intros [ [a [b c]] P].
       exists (a :: b :: nil, a :: c :: nil). compute. 
       rewrite refS. 
       case_eq(rS (b[*]a) (c[*]a)); intro H. 
         rewrite H in P.  discriminate. 
         case_eq(rS (a[*]c) (a[*]b)); auto. 
Defined. 

 
Lemma bop_list_product_left_commutative : 
      brel_witness S rS -> 
      bop_left_constant S rS bS -> bop_right_constant S rS bS -> 
      bop_commutative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. intros W LC RC X.  
       assert (H := bop_not_prop1_implies_prop2 W (ttest LC RC)). 
       destruct H as [c P]. 
       induction X. 
          intro Y. rewrite bop_list_product_left_left_nil. rewrite bop_list_product_left_right_nil. auto. 
          intro Y. induction Y. 
             rewrite bop_list_product_left_left_nil. rewrite bop_list_product_left_right_nil. auto. 
             rewrite bop_list_product_left_left_cons. 
             rewrite bop_list_product_left_left_cons. 
             rewrite bop_list_product_left_left_cons in IHY. 
             admit. 
Admitted. 


Lemma bop_list_product_left_not_commutative_v1 (s : S) : 
      bop_prop1 -> 
      bop_commutative S rS bS -> 
      bop_not_commutative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_commutative. 
       intros [ a [ b [ c [ d P1]]]] commS.       
       exists (a :: b :: nil, c::d::nil). compute. 
       case_eq(rS (a[*]c) (c[*]a)); intro H1; auto. 
       case_eq(rS (a[*]d) (c[*]b)); intro H2; auto. 
       case_eq(rS (b[*]c) (d[*]a)); intro H3; auto. 
       case_eq(rS (b[*]d) (d[*]b)); intro H4; auto. 
       assert (C := commS b c). 
       apply symS in C. 
       assert (T := transS _ _ _ H2 C).        
       rewrite T in P1. 
       discriminate. 
Defined. 

Lemma bop_list_product_left_not_commutative_v3 (s : S) : 
      bop_not_commutative S rS bS -> 
      bop_not_commutative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_commutative. 
       intros [ [a b] P].
       exists (a :: nil, b :: nil). compute. 
       rewrite P. reflexivity. 
Defined. 

(* ======================================================================== *) 
Lemma bop_list_product_left_not_idempotent (s : S) : 
      bop_not_idempotent (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_idempotent. 
       exists (s :: s :: nil). compute. 
       case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 


Lemma bop_list_product_right_not_idempotent (s : S) : 
      bop_not_idempotent (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_idempotent. 
       exists (s :: s :: nil). compute. 
       case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 

Lemma bop_list_product_left_not_is_left (s : S) : 
      bop_not_is_left (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_is_left. 
       exists (s :: s :: nil, s :: s :: nil). compute. 
       case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 


Lemma bop_list_product_right_not_is_left (s : S) : 
      bop_not_is_left (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_is_left. 
       exists (s :: s :: nil, s :: s :: nil). compute. 
       case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 

Lemma bop_list_product_left_not_is_right (s : S) : 
      bop_not_is_right (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_is_right. 
       exists (s :: s :: nil, s :: s :: nil). compute. 
       case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 


Lemma bop_list_product_right_not_is_right (s : S) : 
      bop_not_is_right (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_is_right. 
       exists (s :: s :: nil, s :: s :: nil). compute. 
       case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 

Lemma bop_list_product_left_not_left_cancellative (s t : S) : 
      rS s t = false -> 
      bop_not_left_cancellative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_left_cancellative. 
       intro H. 
       exists (nil, (s :: nil, t :: nil)).
       compute. rewrite H. auto. 
Defined. 

Lemma bop_list_product_right_not_left_cancellative (s t : S) : 
      rS s t = false -> 
      bop_not_left_cancellative (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_left_cancellative. 
       intro H. 
       exists (nil, (s :: nil, t :: nil)).
       compute. rewrite H. auto. 
Defined. 

Lemma bop_list_product_left_not_right_cancellative (s t : S) : 
      rS s t = false -> 
      bop_not_right_cancellative (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_right_cancellative. 
       intro H. 
       exists (nil, (s :: nil, t :: nil)).
       compute. rewrite H. auto. 
Defined. 

Lemma bop_list_product_right_not_right_cancellative (s t : S) : 
      rS s t = false -> 
      bop_not_right_cancellative (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_right_cancellative. 
       intro H. 
       exists (nil, (s :: nil, t :: nil)).
       compute. rewrite H. auto. 
Defined. 

Lemma bop_list_product_left_not_left_constant_v2 (s : S) : 
      bop_not_left_constant (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_left_constant. 
       exists (s :: nil, (nil, s :: nil)).
       compute. reflexivity. 
Defined. 


Lemma bop_list_product_right_not_left_constant_v2 (s : S) : 
      bop_not_left_constant (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_left_constant. 
       exists (s :: nil, (nil, s :: nil)).
       compute. reflexivity. 
Defined. 

Lemma bop_list_product_left_not_right_constant (s : S) : 
      bop_not_right_constant (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_right_constant. 
       exists (s :: nil, (nil, s :: nil)).
       compute. reflexivity. 
Defined. 

Lemma bop_list_product_right_not_right_constant (s : S) : 
      bop_not_right_constant (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_right_constant. 
       exists (s :: nil, (nil, s :: nil)).
       compute. reflexivity. 
Defined. 

Lemma bop_list_product_left_not_anti_left : 
      bop_not_anti_left (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_anti_left. 
       exists (nil, nil). compute. reflexivity. 
Defined. 

Lemma bop_list_product_right_not_anti_left : 
      bop_not_anti_left (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_anti_left. 
       exists (nil, nil). compute. reflexivity. 
Defined. 

Lemma bop_list_product_left_not_anti_right : 
      bop_not_anti_right (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_anti_right. 
       exists (nil, nil). compute. reflexivity. 
Defined. 

Lemma bop_list_product_right_not_anti_right : 
      bop_not_anti_right (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_anti_right. 
       exists (nil, nil). compute. reflexivity. 
Defined. 

Lemma bop_list_product_left_not_selective (s : S) : 
      bop_not_selective (list S) (brel_list rS) (bop_list_product_left S bS). 
Proof. unfold bop_not_selective. 
       exists (s :: s :: nil, s :: s :: nil). 
       compute.  case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 


Lemma bop_list_product_right_not_selective (s : S) : 
      bop_not_selective (list S) (brel_list rS) (bop_list_product_right S bS). 
Proof. unfold bop_not_selective. 
       exists (s :: s :: nil, s :: s :: nil). 
       compute.  case_eq (rS (s[*]s) s); intro H; auto. 
Defined. 


End ListProduct. 
