From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
  coq.common.compute
  coq.eqv.properties
  coq.eqv.list
  coq.eqv.nat
  coq.eqv.product   
  coq.sg.properties
  coq.tr.properties  
  coq.sg.and
  coq.algorithm.matrix_definition
  coq.algorithm.matrix_algorithms
  coq.algorithm.matrix_multiplication. 


Section Weighted_Paths.

  Local Open Scope nat_scope. 
  
Variables 
    (L R : Type)
    (zero one : R) (* 0 and 1 *)
    (plus : binary_op R)
    (ltr : ltr_type L R)    
    (eqL  : brel L)
    (eqR  : brel R)    
    (conR : brel_congruence R eqR eqR)            
    (refR :  brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (conL : brel_congruence L eqL eqL)            
    (refL :  brel_reflexive L eqL)
    (symL : brel_symmetric L eqL)
    (trnL : brel_transitive L eqL)
    (congrP : bop_congruence R eqR plus)
    .
      
  Definition is_eqR a b       := eqR a b = true.
  Definition is_eqL a b       := eqL a b = true.    
  Definition is_eq_nat a b    := brel_eq_nat a b = true.
  Definition not_eq_nat a b   := brel_eq_nat a b = false.      
  Local Notation "0" := zero.
  Local Notation "1" := one.
  Local Infix "+" := plus.
  Local Infix "|>" := ltr (at level 70).
  Local Infix "=l=" := is_eqL (at level 70).  
  Local Infix "=r=" := is_eqR (at level 70).
  Local Infix "=n=" := is_eq_nat (at level 70).
  Local Infix "<n>" := not_eq_nat (at level 70).    
  Local Infix "=r?=" := eqR (at level 70).
  Local Infix "=l?=" := eqL (at level 70).  
  Local Infix "=n?=" := brel_eq_nat (at level 70).

  Definition value_list : Type        := list R.

  Definition label_list : Type        := list L.  

  Definition weighted_arc : Type      := nat * nat * L. 

  Definition weighted_path : Type     := list weighted_arc.

  Definition weighted_path_set : Type := finite_set weighted_path.

  Local Definition CongR := functional_matrix_congruence R eqR.
  Local Definition CongL := functional_matrix_congruence L eqL.  

  Local Notation "a =M= b" := (eq_functional_matrix_prop R eqR a b) (at level 70).

  Local Infix "+M" := (matrix_add plus ) (at level 70).
  
  Local Notation "a *[ n ]>  b" := (left_matrix_mul zero plus ltr n a b) (at level 70).


  (********************** matrix_equality (move this?)  ***********************)

  Lemma matrix_equality_reflexive : 
    ∀X, X =M= X.
  Proof. intros X i j. apply refR. Qed. 

  Lemma matrix_equality_symmetric :
    ∀X Y, X =M= Y -> Y =M= X.
  Proof. intros X Y A i j. exact (symR _ _ (A i j)). Qed. 

  Lemma matrix_equality_transitive :
    ∀X Y Z, X =M= Y -> Y =M= Z -> X =M= Z.
  Proof. intros X Y Z A B i j. exact (trnR _ _ _ (A i j) (B i j)). Qed. 
  
  
  (********************** value_list equality ***********************)

  Definition eq_value_list : brel value_list := brel_list eqR. 

  Lemma eq_value_list_congurence : brel_congruence _ eq_value_list eq_value_list.
  Proof. apply brel_list_congruence; auto. Qed.

  Lemma eq_value_list_reflexive : brel_reflexive _ eq_value_list.
  Proof. apply brel_list_reflexive; auto. Qed.

  Lemma eq_value_list_symmetric : brel_symmetric _ eq_value_list.
  Proof. apply brel_list_symmetric; auto. Qed.
  
  Lemma eq_value_list_transitive : brel_transitive _ eq_value_list.
  Proof. apply brel_list_transitive; auto.  Qed.

  Definition eq_value_list_is_true l1 l2 := eq_value_list l1 l2 = true.  
  Local Infix "=vl=" :=  eq_value_list_is_true (at level 70).

  Definition eq_value_list_intro :
    ∀ (v v' : R) (l l' : value_list), v =r= v' -> l =vl= l' -> (v :: l) =vl= (v' :: l').
  Proof. intros v v' l l' A B. apply brel_list_cons_intro; auto. Qed. 
         
  
  Definition eq_value_list_elim :
    ∀ (v v' : R) (l l' : value_list), (v :: l) =vl= (v' :: l') -> (v =r= v') ∧ (l =vl= l').
  Proof. intros v v' l l' A. apply brel_list_cons_elim in A. destruct A as [A B]. auto. Qed. 
  
  (********************** label_list equality ***********************)

  Definition eq_label_list : brel label_list := brel_list eqL. 

  Lemma eq_label_list_congurence : brel_congruence _ eq_label_list eq_label_list.
  Proof. apply brel_list_congruence; auto. Qed.

  Lemma eq_label_list_reflexive : brel_reflexive _ eq_label_list.
  Proof. apply brel_list_reflexive; auto. Qed.

  Lemma eq_label_list_symmetric : brel_symmetric _ eq_label_list.
  Proof. apply brel_list_symmetric; auto. Qed.
  
  Lemma eq_label_list_transitive : brel_transitive _ eq_label_list.
  Proof. apply brel_list_transitive; auto.  Qed.

  Definition eq_label_list_is_true l1 l2 := eq_label_list l1 l2 = true.  
  Local Infix "=ll=" :=  eq_label_list_is_true (at level 70).

  Definition eq_label_list_intro :
    ∀ (l l' : L) (ls ls' : label_list), l =l= l' -> ls =ll= ls' -> (l :: ls) =ll= (l' :: ls').
  Proof. intros l l' ls ls' A B. apply brel_list_cons_intro; auto. Qed. 
         
  Definition eq_label_list_elim :
    ∀ (l l' : L) (ls ls' : label_list), (l :: ls) =ll= (l' :: ls') -> (l =l= l') ∧ (ls =ll= ls').
  Proof. intros l l' ls ls' A. apply brel_list_cons_elim in A. destruct A as [A B]. auto. Qed. 
  
  
  (********************** weighted arc equality ***********************)

  Definition eq_weighted_arc : brel weighted_arc :=
        brel_product (brel_product brel_eq_nat brel_eq_nat) eqL. 

  Lemma eq_weighted_arc_congruence : brel_congruence weighted_arc eq_weighted_arc eq_weighted_arc.
  Proof. apply brel_product_congruence; auto.
         apply brel_product_congruence; auto.
         apply brel_eq_nat_congruence.
         apply brel_eq_nat_congruence.          
  Qed.          
    
  Lemma eq_weighted_arc_reflexive : brel_reflexive weighted_arc eq_weighted_arc.
  Proof. apply brel_product_reflexive; auto. 
         apply brel_product_reflexive; auto.
         apply brel_eq_nat_reflexive.
         apply brel_eq_nat_reflexive.                  
  Qed.          

  Lemma eq_weighted_arc_symmetric : brel_symmetric weighted_arc eq_weighted_arc. 
  Proof. apply brel_product_symmetric; auto. 
         apply brel_product_symmetric; auto.
         apply brel_eq_nat_symmetric.
         apply brel_eq_nat_symmetric.                  
  Qed. 

  Lemma eq_weighted_arc_transitive : brel_transitive weighted_arc eq_weighted_arc.
  Proof. apply brel_product_transitive; auto.
         apply brel_product_transitive; auto.
         apply brel_eq_nat_transitive.
         apply brel_eq_nat_transitive.                  
  Qed. 

  Definition eq_weighted_arc_is_true a1 a2 := eq_weighted_arc a1 a2 = true.  
  Local Infix "=a=" :=  eq_weighted_arc_is_true (at level 70).

  Lemma eq_weighted_arc_intro :
    ∀ (a b c d : nat) (s t : L), a =n= b -> c=n=d -> s =l= t -> ((a, c), s) =a= ((b, d), t).
  Proof. intros a b c d s t A B C.
         apply brel_product_intro; auto. 
         apply brel_product_intro; auto. 
  Qed.
  
  Lemma eq_weighted_arc_elim :
    ∀ (a b c d : nat) (s t : L), ((a, c), s) =a= ((b, d), t) -> a =n= b ∧ c=n=d ∧ s =l= t.
  Proof. intros a b c d s t A.
         apply brel_product_elim in A. destruct A as [A B]. 
         apply brel_product_elim in A. destruct A as [A C].
         auto. 
  Qed.
  
(********************** weighted path equality ***********************)     
  
  Definition eq_weighted_path : brel weighted_path := brel_list eq_weighted_arc. 

   Lemma eq_weighted_path_congruence : brel_congruence _ eq_weighted_path eq_weighted_path.
   Proof. apply brel_list_congruence.
          exact eq_weighted_arc_symmetric.
          exact eq_weighted_arc_transitive.
          exact eq_weighted_arc_congruence.
   Qed.     

  Lemma eq_weighted_path_reflexive : brel_reflexive weighted_path eq_weighted_path. 
   Proof. apply brel_list_reflexive. exact eq_weighted_arc_reflexive. Qed.

  Lemma eq_weighted_path_symmetric : brel_symmetric weighted_path eq_weighted_path. 
   Proof. apply brel_list_symmetric. exact eq_weighted_arc_symmetric. Qed.
  
  Lemma eq_weighted_path_transitive : brel_transitive weighted_path eq_weighted_path. 
   Proof. apply brel_list_transitive. exact eq_weighted_arc_transitive. Qed.

  Definition eq_weighted_path_is_true p1 p2     := eq_weighted_path p1 p2 = true.  
  Local Infix "=p=" := eq_weighted_path_is_true (at level 70).

  Definition eq_weighted_path_intro :
    ∀ (a1 a2 : weighted_arc) (p q : weighted_path), a1 =a= a2 -> p =p= q -> (a1 :: p) =p= (a2 :: q).
  Proof. intros a1 a2 p q A B. apply brel_list_cons_intro. exact A. exact B. Qed. 

  Definition eq_weighted_path_elim :
    ∀ (a1 a2 : weighted_arc) (p q : weighted_path), (a1 :: p) =p= (a2 :: q) -> a1 =a= a2 ∧ p =p= q.
  Proof. intros a1 a2 p q A.
         apply brel_list_cons_elim in A.
         destruct A as [A B].
         split; auto. 
  Qed. 

(********************** weighted path set equality ***********************)     
  
  Definition eq_weighted_path_set : brel weighted_path_set := brel_list eq_weighted_path. 

   Lemma eq_weighted_path_set_congruence : brel_congruence _ eq_weighted_path_set eq_weighted_path_set.
   Proof. apply brel_list_congruence.
          exact eq_weighted_path_symmetric.
          exact eq_weighted_path_transitive.
          exact eq_weighted_path_congruence.
   Qed.     

  Lemma eq_weighted_path_set_reflexive : brel_reflexive weighted_path_set eq_weighted_path_set. 
   Proof. apply brel_list_reflexive. exact eq_weighted_path_reflexive. Qed.

  Lemma eq_weighted_path_set_symmetric : brel_symmetric weighted_path_set eq_weighted_path_set. 
   Proof. apply brel_list_symmetric. exact eq_weighted_path_symmetric. Qed.
  
  Lemma eq_weighted_path_set_transitive : brel_transitive weighted_path_set eq_weighted_path_set. 
   Proof. apply brel_list_transitive. exact eq_weighted_path_transitive. Qed.

  
  Definition in_path_set p X       := in_list eq_weighted_path X p = true.
  Definition test_in_path_set p X  := in_list eq_weighted_path X p.
  
  Local Infix "[in set]"   := in_path_set (at level 70).
  Local Infix "[?in set?]" := test_in_path_set (at level 70).    

         
  (****************** Source and target of a weighted path ********************)

  Definition arc_source (a : weighted_arc) : nat := 
    match a with 
    | (s, _, _) => s 
    end.

  Definition arc_target (a : weighted_arc) : nat := 
    match a with 
    | (_, t, _) => t
    end.

  Lemma arc_target_congruence : 
      ∀ a a', a =a= a' -> arc_target a =n= arc_target a'.
  Proof. intros [[b c] v] [[b' c'] v']  A. 
         apply eq_weighted_arc_elim in A.
         compute. destruct A as [_ [A _]]. exact A. 
  Qed. 
  
  Definition test_path_source (c : nat) (l : weighted_path) : bool :=
    match l with 
    | [] => false
    | a :: _ => c =n?= (arc_source a)
    end.

  
  Definition refN := brel_eq_nat_reflexive.  
  Definition symN := brel_eq_nat_symmetric.  
  Definition trnN := brel_eq_nat_transitive.

  Lemma test_path_source_congruence : 
    ∀ n n' p p', n =n= n' -> p =p= p' -> test_path_source n p = test_path_source n' p'.
  Proof. intros n n' p p' A B. 
         destruct p; destruct p'. 
         + compute. reflexivity. 
         + compute in B. congruence.
         + compute in B. congruence.
         + apply eq_weighted_path_elim in B. destruct B as [B C].
           destruct w as [[a b] v]; destruct w0 as [[a' b'] v']. simpl. 
           apply eq_weighted_arc_elim in B. destruct B as [B [D E]].
           case_eq(n =n?= a); intro F; case_eq(n' =n?= a'); intro G; auto.
           ++ rewrite (trnN _ _ _ (symN _ _ A) (trnN _ _ _ F B)) in G. congruence. 
           ++ rewrite (trnN _ _ _ (trnN _ _ _ A G) (symN _ _ B)) in F. congruence. 
  Qed.            

           
  Fixpoint test_path_target (d : nat) (l : weighted_path) : bool :=
    match l with
    | [] => false
    | [a] => d =n?= (arc_target a)
    | _ :: rest => test_path_target d rest 
    end.

  Definition is_path_source c p      := test_path_source c p = true.
  Definition is_path_target c p      := test_path_target c p = true.
  Local Infix "is_source_of" := is_path_source (at level 70).
  Local Infix "is_target_of" := is_path_target (at level 70).


  Lemma is_source_of_intro :
    ∀ a b c v p q, (p =p= (b, c, v) :: q) -> a =n= b -> a is_source_of p. 
  Proof. intros a b c v p q A B.
         compute. destruct p.
         + compute in A. congruence.
         + destruct w as [[d e] v'].
           apply eq_weighted_path_elim in A.
           destruct A as [A C].
           apply eq_weighted_arc_elim in A.
           destruct A as [A [D E]].
           exact (trnN _ _ _ B (symN _ _ A)). 
  Qed.

  Lemma is_source_of_elim : ∀ a p, a is_source_of p ->
      {' ((b,c,v),q) : weighted_arc * weighted_path |  (p =p= (b, c, v) :: q) ∧ a =n= b}. 
  Proof. intros a p G. destruct p.
         + compute in G. congruence. 
         + destruct w. destruct p0. 
           exists ((n, n0, l), p). split. 
           ++ apply eq_weighted_path_reflexive. 
           ++ compute in G. exact G. 
  Qed.


 Lemma source_same_path : (* prove this using a congruence on is_source_of  or test_path_source ? *) 
    ∀ p₁ p₂,  p₁ =p= p₂ -> 
        ∀ x y,  x is_source_of p₁ -> y is_source_of p₂ -> x =n= y.
  Proof. intros p₁ p₂ A x y B C.
         apply is_source_of_elim in B. destruct B as [[[[b c] v1] q1] [P1 Q1]]. 
         apply is_source_of_elim in C. destruct C as [[[[d e] v2] q2] [P2 Q2]].
         apply eq_weighted_path_symmetric in P1.         
         assert (D := eq_weighted_path_transitive _ _ _ P1 A).
         assert (E := eq_weighted_path_transitive _ _ _ D P2).
         apply eq_weighted_path_elim in E. destruct E as [E F]. 
         apply eq_weighted_arc_elim in E. destruct E as [E [I J]].
         exact (trnN _ _ _ Q1 (trnN _ _ _ E (symN _ _ Q2))). 
Qed. 


  (****************** congruence of map ********************)

  Lemma map_path_congruence
        (f : weighted_arc -> R)
        (conf : ∀ a a', a =a= a' -> (f a) =r= (f a')) : 
       ∀ (p q : weighted_path),  p =p= q -> map f p =vl= map f q. 
  Proof. induction p;  destruct q. 
         + intros A. compute. reflexivity. 
         + intros A. compute in A. congruence.
         + intros A. compute in A. congruence.            
         + intros A. simpl. 
           apply eq_weighted_path_elim in A. destruct A as [A B].
           apply eq_value_list_intro. 
           ++ exact (conf _ _ A). 
           ++ exact (IHp _ B). 
  Qed. 

    Lemma map_label_list_congruence
        (f : weighted_arc -> L)
        (conf : ∀ a a', a =a= a' -> (f a) =l= (f a')) : 
       ∀ (p q : weighted_path),  p =p= q -> map f p =ll= map f q. 
  Proof. induction p;  destruct q. 
         + intros A. compute. reflexivity. 
         + intros A. compute in A. congruence.
         + intros A. compute in A. congruence.            
         + intros A. simpl. 
           apply eq_weighted_path_elim in A. destruct A as [A B].
           apply eq_label_list_intro. 
           ++ exact (conf _ _ A). 
           ++ exact (IHp _ B). 
  Qed. 

 (****************** congruences of fold` ********************)

  (* generalize these proofs? *) 
  
  Lemma fold_right_path_congruence
        (f : weighted_arc -> R -> R)
        (conf : ∀ a a' v v', a =a= a' -> v=r=v' -> (f a v) =r= (f a' v')) :  (* make this a def *) 
    ∀ (p₁ p₂ : weighted_path) (v : R),
          p₁ =p= p₂ -> fold_right f v p₁ =r= fold_right f v p₂. 
  Proof. induction p₁;  destruct p₂. 
         + intros v A. compute. apply refR. 
         + intros v A. compute in A. congruence.
         + intros v A. compute in A. congruence.            
         + intros v A. simpl. 
           apply eq_weighted_path_elim in A. destruct A as [A B].
           assert (C := IHp₁ _ v B).
           exact (conf _ _ _ _ A C). 
  Qed. 

  Lemma fold_right_value_list_congruence
        (f : R -> R -> R)
        (conf : bop_congruence R eqR f) : 
      ∀ (l₁ l₂ : value_list) (v : R), (l₁ =vl= l₂) -> fold_right f v l₁ =r= fold_right f v l₂.
    Proof. induction l₁;  destruct l₂. 
         + intros v A. compute. apply refR. 
         + intros v A. compute in A. congruence.
         + intros v A. compute in A. congruence.            
         + intros v A. simpl. 
           apply eq_value_list_elim in A. destruct A as [A B].
           assert (C := IHl₁ _ v B).
           exact (conf _ _ _ _ A C). 
    Qed.


  Lemma fold_right_label_list_congruence
        (f : L -> R -> R)
        (conf : ltr_congruence L R eqL eqR f) : 
      ∀ (l₁ l₂ : label_list) (v : R), (l₁ =ll= l₂) -> fold_right f v l₁ =r= fold_right f v l₂.
    Proof. induction l₁;  destruct l₂. 
         + intros v A. compute. apply refR. 
         + intros v A. compute in A. congruence.
         + intros v A. compute in A. congruence.            
         + intros v A. simpl. 
           apply eq_label_list_elim in A. destruct A as [A B].
           assert (C := IHl₁ _ v B).
           exact (conf _ _ _ _ A C). 
    Qed.
    

 (****************** the weight of a weighted path ********************)

  
 Definition label_of_arc (a : weighted_arc) : L :=
    match a with 
    | (_, _, l) => l
    end.

 Lemma label_of_arc_congruence : ∀ a a', a =a= a' -> label_of_arc a =l= label_of_arc a'.
 Proof. intros a a' A. unfold label_of_arc.
        destruct a as [[a b] v]; destruct a' as [[a' b'] v'].
        apply eq_weighted_arc_elim in A. destruct A as [_ [_ A]]. 
        exact A. 
 Qed.         

 Definition ltr_of_list : label_list -> R := fold_right ltr 1. 

 Lemma ltr_of_list_congruence (ltr_cong : ltr_congruence L R eqL eqR ltr) : 
     ∀l1 l2 : label_list, l1 =ll= l2 -> ltr_of_list l1 =r= ltr_of_list l2.
 Proof. intros l1 l2 A.
        unfold ltr_of_list.
        apply fold_right_label_list_congruence; auto. 
 Qed. 
 
  Definition left_weight_of_path (p : weighted_path) : R := ltr_of_list (map label_of_arc p). 

  Definition lw := left_weight_of_path.
  
  Lemma map_label_of_arc_congruence : ∀ p q, p =p= q -> map label_of_arc p =ll= map label_of_arc q.
  Proof. intros p q A.
         apply map_label_list_congruence; auto.
         apply label_of_arc_congruence. 
  Qed. 
  
  Lemma left_weight_of_path_congruence (ltr_cong : ltr_congruence L R eqL eqR ltr) : 
        ∀ p q, p =p= q -> lw p =r= lw q. 
  Proof. intros p q E. unfold lw, left_weight_of_path.
         unfold ltr_of_list.
         assert (A := map_label_of_arc_congruence p q E). 
         apply fold_right_label_list_congruence; auto.
  Qed. 

  
(****************** Define when a path is well-formed wrt a matrix  ********************)

   Definition arc_has_matrix_label (m : functional_matrix L) (a : weighted_arc) : bool :=
     match a with
       ((b, c), v) =>  (m b c) =l?= v
     end.


   Lemma arc_has_matrix_label_congruence (m : functional_matrix L) (cong : CongL m) : 
     ∀ a a', a =a= a' -> arc_has_matrix_label m a = arc_has_matrix_label m a'.
   Proof. intros a a' A.
          destruct a as [[a b] v]; destruct a' as [[a' b'] v']. 
          apply eq_weighted_arc_elim in A. destruct A as [A [B C]]. 
          compute.
          assert (D := cong _ _ _ _ A B).
          case_eq(m a b =l?= v); intro E; case_eq(m a' b' =l?= v'); intro F; auto.
          ++ rewrite (trnL _ _ _ (trnL _ _ _ (symL _ _ D) E) C) in F. congruence. 
          ++ rewrite (trnL _ _ _ D (trnL _ _ _ F (symL _ _ C))) in E. congruence. 
   Qed.             
    
   
   Definition path_has_matrix_labels (m : functional_matrix L) (p : weighted_path) : bool :=
     forallb (arc_has_matrix_label m) p.

   Lemma path_has_matrix_labels_congruence (m : functional_matrix L) (cong : CongL m):
     ∀ p q,  p =p= q -> path_has_matrix_labels m p = path_has_matrix_labels m q. 
   Proof. unfold path_has_matrix_labels.
          induction p; destruct q.
          + compute; auto. 
          + intro A; compute in A; congruence. 
          + intro A; compute in A; congruence.
          + intro A. simpl.
            apply eq_weighted_path_elim in A; destruct A as [A B].
            rewrite (IHp _ B).
            rewrite (arc_has_matrix_label_congruence m cong _ _ A). 
            reflexivity. 
   Qed.           

   Definition arc_is_consistent_with_path  (a : weighted_arc) (p : weighted_path) : bool :=
     match p with
     | [] => true
     | _ => test_path_source (arc_target a) p
     end. 


   Lemma arc_is_consistent_with_path_congruence :
        ∀ a1 a2 p q, a1 =a= a2 -> p =p= q -> arc_is_consistent_with_path a1 p = arc_is_consistent_with_path a2 q. 
   Proof. intros a1 a2 p q A B.
          unfold arc_is_consistent_with_path.
          destruct p; destruct q; auto.
          + compute in B. congruence. 
          + compute in B. congruence. 
          + apply test_path_source_congruence. 
            ++ apply arc_target_congruence; auto. 
            ++ exact B. 
   Qed. 

   Fixpoint path_is_arc_consistent (p : weighted_path) :=
     match p with
     | [] => true
     | a :: q => bop_and (arc_is_consistent_with_path a q) (path_is_arc_consistent q)
     end.

   Lemma path_is_arc_consistent_congruence : ∀ p q, p =p= q -> path_is_arc_consistent p = path_is_arc_consistent q.
   Proof. induction p; destruct q; intro A; simpl. 
          + reflexivity. 
          + compute in A. congruence.
          + compute in A. congruence.
          + apply eq_weighted_path_elim in A. 
            destruct A as [A B].
            rewrite (IHp _ B).
            rewrite (arc_is_consistent_with_path_congruence _ _ _ _ A B). 
            reflexivity. 
   Qed.

(****************** Matrix of weighted paths of length k  *************************)

   Definition zeroP : weighted_path_set := [].
   Definition oneP : weighted_path_set := [[]].

   Definition plusP : binary_op weighted_path_set :=
     fun X => fun Y => X ++ Y.
   
   Definition ltr_extend_path : ltr_type weighted_arc weighted_path :=
    fun a => fun p =>  if test_path_source (arc_target a) p then a :: p else []. 

   Definition path_adjacency_arcs (m : functional_matrix L) : functional_matrix weighted_arc := 
    fun (i j : nat) =>  ((i, j), m i j). 
    
   Definition ltr_extend_paths : ltr_type weighted_arc weighted_path_set :=
     fun a (X : weighted_path_set) => List.map (ltr_extend_path a) X.

   Definition matrix_of_k_length_paths m n k :=
     left_matrix_exponentiation zeroP oneP plusP ltr_extend_paths n (path_adjacency_arcs m) k.
   

   (******* Local definitions ****************************************)
   
   Local Notation "Pk[ m , n ]^ k"  := (matrix_of_k_length_paths m n k) (at level 70).

   Local Notation "LW[ X ]" := (sum_fn zero plus lw X) (at level 70). 

   Local Notation "LWP[ X ]" := (fun i j => LW[ X i j]) (at level 100).

   Local Notation "[I]" := (matrix_mul_identity zero one) (at level 70).

   Local Notation "[IP]" := (matrix_mul_identity zeroP oneP) (at level 70).

   Local Notation "A[ m ]" := (path_adjacency_arcs m) (at level 70).

   Local Infix "*[| n |]>" := (left_matrix_mul zeroP plusP ltr_extend_paths n) (at level 70).
   
   Local Infix "+PM" := (matrix_add plusP ) (at level 70).
   
   Local Infix "+P" := (plusP) (at level 70).

   Local Notation "a =PM= b" := (eq_functional_matrix_prop weighted_path_set eq_weighted_path_set a b) (at level 70).   

   (*****************************************************************************)


   Lemma unfold_Pk (m : functional_matrix L) (n : nat) : 
     ∀ k, Pk[ m, n ]^(S k) =PM= (A[ m ] *[| n |]> (Pk[ m , n ]^k)). 
   Proof. intro k. unfold matrix_of_k_length_paths. 
          exact (unfold_left_matrix_exponentiation _ _
                    eq_weighted_path_set
                    plusP
                    zeroP
                    oneP
                    ltr_extend_paths
                    eq_weighted_path_set_reflexive
                    (A[ m ])
                    n
                    k).
   Qed.           

  Lemma identity_is_weight_of_matrix_of_paths_of_length_zero
        (plusID : bop_is_id R eqR plus 0)
        (m : functional_matrix L) (n : nat) : 
             [I] =M= LWP[ Pk[ m , n ]^0  ].
  Proof. intros i j.  unfold matrix_of_k_length_paths.
         simpl. unfold matrix_mul_identity.         
         case_eq(i =n?= j); intro A; compute. 
         + destruct (plusID 1) as [C D].
           apply symR in D. exact D. 
         + apply refR. 
  Qed.

  Lemma LWP_of_path_identity_is_identity (plusID : bop_is_id R eqR plus 0) :
         LWP[ [IP] ] =M= [I]. 
 Proof. intros i j. unfold matrix_mul_identity.
        unfold zeroP, oneP.
        case_eq(i =n?= j); intro A; compute. 
        + destruct (plusID 1) as [B C]. exact C. 
        + apply refR. 
 Qed.

 
 Lemma LWP_of_path_identity_is_weight_of_matrix_of_paths_of_length_zero
       (plusID : bop_is_id R eqR plus 0)
       (m : functional_matrix L) (n : nat) :        
         LWP[ [IP] ] =M= LWP[ Pk[ m , n ]^0  ].
 Proof. intros i j.
        assert (A := identity_is_weight_of_matrix_of_paths_of_length_zero plusID m n i j).
        assert (B := LWP_of_path_identity_is_identity plusID i j).
        simpl in A, B. 
        exact (trnR _ _ _ B A). 
 Qed.

 Lemma LW_distributes_over_path_plus
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus)
       (idP : bop_is_id R eqR plus 0) 
       (X Y : functional_matrix weighted_path_set): 
  ∀ i j, LW[ (X i j) +P (Y i j) ] =r= LW[ X i j ] + LW[ Y i j ]. 
 Proof. intros i j. apply sum_fn_distributes_over_concat; auto.  Qed. 

(*
  Lemma tst : 
  ∀m n i j,  1 < n -> (m *[ n ]> ([I])) i j = if i =n?= j then m i j |> 1 else zero. 
  Proof. intros m n i j C.
         unfold matrix_mul_identity.
         unfold left_matrix_mul.
         unfold sum_fn. unfold left_row_i_dot_col_j. 
         induction n.
         + admit. (* C : 1 < 0 *)
         + simpl.
           assert (D : 1 < n). admit. 
           rewrite (IHn D).
           case_eq(n =n?= j); intro A; case_eq(i =n?= j); intro B. 
           ++ admit. (* (m i n |> 1) + (m i j |> 1) = (m i j |> 1) *) 
           ++ admit. (* (n =n?= j) = true -> (m i n |> 1) + 0 = 0 *) 
           ++ admit. (* (m i n |> 0) + (m i j |> 1) = (m i j |> 1) *) 
           ++ admit. (* (m i n |> 0) + 0 = 0 *)
  Admitted.

  Lemma tst2 : 
  ∀m n i j,  1 < n -> ((A[ m]) *[| n |]> ([IP])) i j = if i =n?= j then [[((i, i), m i i)]]else zeroP. 
  Proof. intros m n i j C.
         unfold path_adjacency_arcs, matrix_mul_identity, zeroP.
         unfold left_matrix_mul, plusP, ltr_extend_paths, oneP. 
         unfold ltr_extend_path, sum_fn.
         unfold left_row_i_dot_col_j, arc_target.
  Admitted.          


 Lemma LWP_distributes_over_matrix_add_base_case_aux :  
   ∀m n, (LWP[ (A[ m]) *[| n |]> ([IP])])
          =M= 
          (m *[ n ]> [I]). 
 Proof. intros m n i j. simpl. 
        unfold left_matrix_mul at 2. 
 Admitted.
 
 Lemma LWP_distributes_over_matrix_add_base_case :  
   ∀m n, (LWP[ (A[ m]) *[| n |]> ([IP])])
          =M= 
          (m *[ n ]> (LWP[ Pk[ m, n ]^ 0])).
 Proof. intros m n i j.
        unfold left_matrix_mul at 2. 
        unfold left_row_i_dot_col_j.
        unfold sum_fn at 3.
        unfold matrix_of_k_length_paths.
        unfold left_matrix_exponentiation.
        unfold matrix_mul_identity at 2.
        unfold oneP, zeroP.
 Admitted.

 
 Lemma LWP_distributes_over_matrix_add
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus)
       (idP : bop_is_id R eqR plus 0) : 
            ∀ X Y, LWP[ X +PM Y ] =M= LWP[ X ] +M LWP[ Y ]. 
 Proof. intros X Y i j. unfold matrix_add.
        apply LW_distributes_over_path_plus; auto. 
 Qed. 
*)              

  Lemma LWP_distributes_over_left_exponentiation (m : functional_matrix L) (n : nat) : 
        ∀ k, LWP[ A[ m ] *[| n |]> (Pk[ m , n ]^k) ] =M= (m *[ n ]> LWP[ Pk[ m , n ]^k ]).
  Admitted. 

  Lemma  base_case_of_fundamental_theorem_on_paths_of_length_k
         (assoc : bop_associative R eqR plus)
         (comm : bop_commutative R eqR plus)
         (plusID : bop_is_id R eqR plus 0) :
        ∀ m n, LWP[ Pk[ m, n ]^1 ] =M= ((m *[ n ]> LWP[ Pk[ m, n ]^0 ])).
  Proof. intros m n. 
         unfold matrix_of_k_length_paths at 1. 
         unfold left_matrix_exponentiation.
         (* Show: 
          (LWP[ ((A[ m ]) *[| n |]> ([IP])) +PM ([IP])]) =M= ((m *[ n ]> (LWP[ Pk[ m, n ]^ 0])))
         Proof: 
          
          LWP[ ((A[ m ]) *[| n |]> ([IP])) +PM ([IP])]
          =M= {LWP_distributes_over_matrix_add}
          LWP[ ((A[ m ]) *[| n |]> ([IP])) ] +M LWP[ [IP] ]
          =M= {LWP_of_path_identity_is_identity} 
          LWP[ ((A[ m ]) *[| n |]> ([IP])) ] +M I ]
          =M= {} 
          ((m *[ n ]> (LWP[ Pk[ m, n ]^ 0])) +M ([I]))
          
         assert (B := LWP_distributes_over_matrix_add assoc comm plusID ((A[ m]) *[| n |]> ([IP])) ([IP])).
         assert (C : ((LWP[ (A[ m]) *[| n |]> ([IP])]) +M (LWP[ [IP]]))
                     =M=
                     ((LWP[ (A[ m]) *[| n |]> ([IP])]) +M [I])).
            apply matrix_add_congruence; auto.
            apply matrix_equality_reflexive. 
            apply LWP_of_path_identity_is_identity.
            apply plusID.
         assert (D : ((LWP[ (A[ m]) *[| n |]> ([IP])]) +M [I])
                     =M= 
                     ((m *[ n ]> (LWP[ Pk[ m, n ]^ 0])) +M ([I]))).
            apply matrix_add_congruence; auto. 
            apply LWP_distributes_over_matrix_add_base_case.
            apply matrix_equality_reflexive.             
         assert (CD := matrix_equality_transitive _ _ _ C D).
         assert (BCD := matrix_equality_transitive _ _ _ B CD).
         exact BCD. 
  Qed. 
          *)
         Admitted. 


  Lemma LWP_congruence (ltr_cong : ltr_congruence L R eqL eqR ltr) : 
    ∀ X Y, X =PM= Y -> LWP[ X ] =M= LWP[ Y ].
  Proof. intros X Y A i j.
         assert (B := A i j).
         assert (C := sum_fn_congruence_general R eqR plus zero refR congrP). 
         exact (C weighted_path lw lw eq_weighted_path (left_weight_of_path_congruence ltr_cong) _ _ B). 
  Qed. 

  Theorem fundamental_theorem_on_paths_of_length_k
         (assoc : bop_associative R eqR plus)
         (comm : bop_commutative R eqR plus)
         (plusID : bop_is_id R eqR plus 0)
         (ltr_cong : ltr_congruence L R eqL eqR ltr)
         (m : functional_matrix L) (n : nat) : 
    ∀ k, LWP[ Pk[ m , n ]^(k + 1) ]
          =M=
          (m *[ n ]> (LWP[ Pk[ m , n]^k ])). 
  Proof. induction k.
         + apply base_case_of_fundamental_theorem_on_paths_of_length_k; auto. 
         + (* Show: 
             IHk : (LWP[ Pk[ m, n ]^(k + 1)])  =M= (m *[ n ]> (LWP[ Pk[ m, n ]^ k]))
             ============================
             (LWP[ Pk[ m, n ]^((S k) + 1)])  =M= (m *[ n ]> (LWP[ Pk[ m, n ]^(S k)]))

             Proof: 
             LWP[ Pk[ m, n ]^((k + 1) + 1)]
             = {unfold_left_matrix_exponentiation} 
             LWP[ (A[ m ] *[| n |]> (Pk[ m , n ]^(k + 1)))]
             = {LWP_distributes_over_left_exponentiation, congruence}
             (m *[ n ]> (LWP[ Pk[ m, n ]^(k + 1)]))
            *)
           assert (B : LWP[ Pk[ m, n ]^((S k) + 1)]
                       =M=
                       LWP[ (A[ m ] *[| n |]> (Pk[ m , n ]^(S k))) ]).
               assert (C := unfold_Pk m n (S k)).             
               apply LWP_congruence; auto. 
               assert (D : S (S k) = ((S k) + 1)%nat). (* Ugh! *) 
                  assert (E := theory.plus_SS k 0).
                  rewrite <- plus_n_O in E.
                  rewrite E. reflexivity. 
               rewrite D in C. exact C. 
           assert (D : LWP[   (A[ m ] *[| n |]> (Pk[ m , n ]^(S k)))   ] 
                       =M=
                       (m *[ n ]> (LWP[ Pk[ m, n ]^(S k)]))).
              apply LWP_distributes_over_left_exponentiation. 
           exact (eq_functional_matrix_prop_transitive _ eqR trnR _ _ _ B D).
  Qed.

    
End Weighted_Paths. 
         
  
