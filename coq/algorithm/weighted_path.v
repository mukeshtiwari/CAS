From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
  coq.common.compute
  coq.eqv.properties
  coq.eqv.list
  coq.eqv.product   
  coq.sg.properties  
  coq.sg.and
  coq.algorithm.matrix_definition
  coq.algorithm.matrix_equality. 

Section Weighted_Paths. 
Variables 
    (Node : Type)
    (eqN  : brel Node)
    (* carrier set and the operators *)
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R)
    (conN : brel_congruence Node eqN eqN)        
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN)
    (conR : brel_congruence R eqR eqR)            
    (refR :  brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).
      
  Definition is_eqR a b          := eqR a b = true.
  Definition is_eqN a b          := eqN a b = true.
  Definition not_eqN a b          := eqN a b = false.      
  Local Notation "0" := zeroR.
  Local Notation "1" := oneR.
  Local Infix "+" := plusR.
  Local Infix "*" := mulR.
  Local Infix "=r=" := is_eqR (at level 70).
  Local Infix "=n=" := is_eqN (at level 70).
  Local Infix "<n>" := not_eqN (at level 70).    
  Local Infix "=r?=" := eqR (at level 70).
  Local Infix "=n?=" := eqN (at level 70).

  Definition weighted_arc : Type      := Node * Node * R. 

  Definition weighted_path : Type     := list weighted_arc.

  Definition value_list : Type        := list R.

  Local Definition Cong m              := mat_cong Node eqN R eqR m.

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
  
  
  (********************** weighted arc equality ***********************)

  Definition eq_weighted_arc : brel weighted_arc :=
        brel_product (brel_product eqN eqN) eqR. 

  Lemma eq_weighted_arc_congruence : brel_congruence weighted_arc eq_weighted_arc eq_weighted_arc.
  Proof. apply brel_product_congruence; auto. 
         apply brel_product_congruence; auto. 
  Qed.          
    
  Lemma eq_weighted_arc_reflexive : brel_reflexive weighted_arc eq_weighted_arc.
  Proof. apply brel_product_reflexive; auto. 
         apply brel_product_reflexive; auto. 
  Qed.          

  Lemma eq_weighted_arc_symmetric : brel_symmetric weighted_arc eq_weighted_arc. 
  Proof. apply brel_product_symmetric; auto. 
         apply brel_product_symmetric; auto.
  Qed. 

  Lemma eq_weighted_arc_transitive : brel_transitive weighted_arc eq_weighted_arc.
  Proof. apply brel_product_transitive; auto.
         apply brel_product_transitive; auto.
  Qed. 

  Definition eq_weighted_arc_is_true a1 a2 := eq_weighted_arc a1 a2 = true.  
  Local Infix "=a=" :=  eq_weighted_arc_is_true (at level 70).

  Lemma eq_weighted_arc_intro :
    ∀ (a b c d : Node) (s t : R), a =n= b -> c=n=d -> s =r= t -> ((a, c), s) =a= ((b, d), t).
  Proof. intros a b c d s t A B C.
         apply brel_product_intro; auto. 
         apply brel_product_intro; auto. 
  Qed.
  
  Lemma eq_weighted_arc_elim :
    ∀ (a b c d : Node) (s t : R), ((a, c), s) =a= ((b, d), t) -> a =n= b ∧ c=n=d ∧ s =r= t.
  Proof. intros a b c d s t A.
         apply brel_product_elim in A. destruct A as [A B]. 
         apply brel_product_elim in A. destruct A as [A C].
         auto. 
  Qed.
  
(********************** weighted path equality ***********************)     
  
  Definition eq_weighted_path : brel weighted_path := brel_list eq_weighted_arc. 

   Lemma eq_weighted_pathcongruence : brel_congruence _ eq_weighted_path eq_weighted_path.
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

         
  (****************** Source and target of a weighted path ********************)

  Definition arc_source (a : weighted_arc) : Node := 
    match a with 
    | (s, _, _) => s 
    end.

  Definition arc_target (a : weighted_arc) : Node := 
    match a with 
    | (_, t, _) => t
    end.

  Lemma arc_target_congruence : 
      ∀ a a', a =a= a' -> arc_target a =n= arc_target a'.
  Proof. intros [[b c] v] [[b' c'] v']  A. 
         apply eq_weighted_arc_elim in A.
         compute. destruct A as [_ [A _]]. exact A. 
  Qed. 
  
  Definition test_path_source (c : Node) (l : weighted_path) : bool :=
    match l with 
    | [] => false
    | a :: _ => c =n?= (arc_source a)
    end.

  Lemma test_path_source_congruence : 
    ∀ n n' p p', n =n= n' -> p =p= p' -> test_path_source n p = test_path_source n' p'.
  Proof. intros n n' p p' A B. 
         destruct p; destruct p'; compute. 
         + reflexivity. 
         + compute in B. congruence.
         + compute in B. congruence.
         + apply eq_weighted_path_elim in B. destruct B as [B C].
           destruct w as [[a b] v]; destruct w0 as [[a' b'] v'].
           apply eq_weighted_arc_elim in B. destruct B as [B [D E]]. 
           case_eq(n =n?= a); intro F; case_eq(n' =n?= a'); intro G; auto.
           ++ rewrite (trnN _ _ _ (symN _ _ A) (trnN _ _ _ F B)) in G. congruence. 
           ++ rewrite (trnN _ _ _ (trnN _ _ _ A G) (symN _ _ B)) in F. congruence. 
  Qed.            

           
  Fixpoint test_path_target (d : Node) (l : weighted_path) : bool :=
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
           exists ((n, n0, r), p). split. 
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


 (****************** the weight of a weighted path ********************)

  
 Definition weight_of_arc (a : weighted_arc) : R :=
    match a with 
    | (_, _, v) => v 
    end.

 Lemma weight_of_arc_congruence : ∀ a a', a =a= a' -> weight_of_arc a =r= weight_of_arc a'.
 Proof. intros a a' A. unfold weight_of_arc.
        destruct a as [[a b] v]; destruct a' as [[a' b'] v'].
        apply eq_weighted_arc_elim in A. destruct A as [_ [_ A]]. 
        exact A. 
 Qed.         

 Definition left_product_of_list : value_list -> R := fold_right mulR 1.

 Lemma left_product_of_list_congruence (congrM : bop_congruence R eqR mulR) : 
     ∀l1 l2 : value_list, l1 =vl= l2 -> left_product_of_list l1 =r= left_product_of_list l2.
 Proof. intros l1 l2 A.
        unfold left_product_of_list.
        apply fold_right_value_list_congruence; auto. 
 Qed. 
 
  (* call this left_weight_of_path? *) 
  Definition measure_of_path (p : weighted_path) : R := left_product_of_list (map weight_of_arc p). 

  Definition w := measure_of_path. 

  Lemma map_weight_of_arc_congruence : ∀ p q, p =p= q -> map weight_of_arc p =vl= map weight_of_arc q.
  Proof. intros p q A.
         apply map_path_congruence; auto.
         apply weight_of_arc_congruence. 
  Qed. 
  
  Lemma measure_of_path_congruence (congrM : bop_congruence R eqR mulR):
        ∀ p q, p =p= q -> w p =r= w q. 
  Proof. intros p q E. unfold w, measure_of_path.
         unfold left_product_of_list.
         assert (A := map_weight_of_arc_congruence p q E). 
         apply fold_right_value_list_congruence; auto.
  Qed. 


  Lemma w_distributes_over_concat 
        (mulID : bop_is_id R eqR mulR 1)    
        (congrM : bop_congruence R eqR mulR)
        (mul_associative : bop_associative R eqR mulR):
     ∀ q₁ q₂, w (q₁ ++ q₂) =r= (w q₁) * (w q₂).
  Proof. intros q₁ q₂.
         induction q₁.
         + simpl. apply symR. destruct (mulID (w q₂)) as [A _]. exact A. 
         + destruct a as ((a, b), v).          
           rewrite <- app_comm_cons.
           unfold w at 1 2. 
           unfold measure_of_path. simpl. 
           assert (A := congrM _ _ _ _ (refR v) IHq₁).
           assert (B := mul_associative v (w q₁) (w q₂)). apply symR in B. 
           exact (trnR _ _ _ A B). 
Qed. 

  (* change name to something reasonable? 
  *) 
  Lemma path_split_measure
        (mulID : bop_is_id R eqR mulR 1)    
        (congrM : bop_congruence R eqR mulR)
        (assocM : bop_associative R eqR mulR):
   ∀ p q₁ q₂, p =p= (q₁ ++ q₂) -> (w p) =r= (w q₁ * w q₂).
  Proof. intros p q₁ q₂ A.
         assert (B := measure_of_path_congruence congrM _ _ A).
         assert (C := w_distributes_over_concat mulID congrM assocM q₁ q₂). 
         exact (trnR _ _ _ B C).          
  Qed. 

  
(****************** Define when a path is well-formed wrt a matrix  ********************)

   Definition arc_has_matrix_weight (m : Matrix Node R) (a : weighted_arc) : bool :=
     match a with
       ((b, c), v) =>  (m b c) =r?= v
     end.

   Lemma arc_has_matrix_weight_congruence (m : Matrix Node R) (cong : Cong m) : 
     ∀ a a', a =a= a' -> arc_has_matrix_weight m a = arc_has_matrix_weight m a'.
   Proof. intros a a' A.
          destruct a as [[a b] v]; destruct a' as [[a' b'] v']. 
          apply eq_weighted_arc_elim in A. destruct A as [A [B C]]. 
          compute.
          assert (D := cong _ _ _ _ A B).
          case_eq(m a b =r?= v); intro E; case_eq(m a' b' =r?= v'); intro F; auto.
          ++ rewrite (trnR _ _ _ (trnR _ _ _ (symR _ _ D) E) C) in F. congruence. 
          ++ rewrite (trnR _ _ _ D (trnR _ _ _ F (symR _ _ C))) in E. congruence. 
   Qed.             
    
   
   Definition path_has_matrix_weights (m : Matrix Node R) (p : weighted_path) : bool :=
     forallb (arc_has_matrix_weight m) p.



   Lemma path_has_matrix_weights_congruence (m : Matrix Node R) (cong : Cong m):
     ∀ p q,  p =p= q -> path_has_matrix_weights m p = path_has_matrix_weights m q. 
   Proof. unfold path_has_matrix_weights.
          induction p; destruct q.
          + compute; auto. 
          + intro A; compute in A; congruence. 
          + intro A; compute in A; congruence.
          + intro A. simpl.
            apply eq_weighted_path_elim in A; destruct A as [A B].
            rewrite (IHp _ B).
            rewrite (arc_has_matrix_weight_congruence m cong _ _ A). 
            reflexivity. 
   Qed.           

   Lemma path_has_matrix_weights_distributes_over_concat (m : Matrix Node R) :
     ∀ p q, path_has_matrix_weights m (p ++ q) = true ->
            (path_has_matrix_weights m p = true) ∧ (path_has_matrix_weights m q = true). 
   Proof. unfold path_has_matrix_weights.
          intros p q A. 
          rewrite forallb_app in A. 
          apply bop_and_elim in A. destruct A as [A B].
          split; auto. 
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

   Lemma arc_is_consistent_with_path_concat_elim : 
   ∀ a p q, arc_is_consistent_with_path a (p ++ q) = true ->
            (p = [] /\ arc_is_consistent_with_path a q = true) \/ ( p <> [] /\ arc_is_consistent_with_path a p = true).
   Proof. intros a p q A.
          destruct p.
          + rewrite app_nil_l in A. 
            left. auto.
          + right. split.
            ++ congruence. 
            ++ destruct a as [[a b] v]; destruct w0 as [[a' b'] v'].
               unfold  arc_is_consistent_with_path in *.
               rewrite <- app_comm_cons in A. 
               simpl in *.
               exact A. 
   Qed.


   Lemma path_is_arc_consistent_distributes_over_concat : 
     ∀ p q, path_is_arc_consistent (p ++ q) = true ->
            (path_is_arc_consistent p = true) /\ (path_is_arc_consistent q = true). 
   Proof. induction p; destruct q; simpl; intro A.
          + compute. auto. 
          + rewrite A. auto. 
          + rewrite app_nil_r in A. rewrite A. split; congruence. 
          + apply bop_and_elim in A. destruct A as [A B].
            destruct (IHp _ B) as [C D].
            simpl in D. apply bop_and_elim in D. destruct D as [D E].             
            rewrite C, D, E. simpl. split; auto.
            apply bop_and_intro; auto.
            destruct (arc_is_consistent_with_path_concat_elim _ _ _ A) as [[F G] | [F G]].            
            ++ rewrite F. compute; auto. 
            ++ exact G. 
   Qed.               

   
   Definition weighted_path_is_well_formed m p := bop_and (path_is_arc_consistent p) (path_has_matrix_weights m p).

   Definition Wf m p := weighted_path_is_well_formed m p = true. 

   Lemma Wf_intro (m : Matrix Node R):   
        ∀ p, path_is_arc_consistent p = true -> path_has_matrix_weights m p =true -> Wf m p.
     Proof. intros p A B.
            unfold Wf, weighted_path_is_well_formed.
            rewrite A, B.
            compute; auto.
     Qed.             

     Lemma Wf_elim (m : Matrix Node R):   
        ∀ p, Wf m p -> (path_is_arc_consistent p = true) /\ (path_has_matrix_weights m p =true). 
     Proof.  unfold Wf, weighted_path_is_well_formed.
             intros p A. apply bop_and_elim in A. destruct A as [A B]. 
             split; auto.
     Qed.

     Lemma Wf_congruence (m : Matrix Node R) (cong : Cong m):
           ∀ p q,  p =p= q -> Wf m p -> Wf m q.
     Proof. intros p q A B.
            apply Wf_elim in B. destruct B as [B C]. 
            apply Wf_intro.
            + rewrite <- (path_is_arc_consistent_congruence _ _ A). exact B. 
            + rewrite <- (path_has_matrix_weights_congruence m cong  _ _ A). exact C. 
     Qed.               

     Lemma well_formed_path_rewrite (m : Matrix Node R) (cong : Cong m) :
         ∀ p q,  Wf m p -> p =p= q -> Wf m q.
     Proof. intros p q A B. exact (Wf_congruence m cong p q B A). Qed. 

     Lemma well_formed_path_snoc (m : Matrix Node R): 
       forall p q, Wf m (p ++ q) → Wf m p  ∧  Wf m q.
     Proof. intros p q A.
         apply Wf_elim in A. destruct A as [A B].
         apply path_has_matrix_weights_distributes_over_concat in B.
         destruct B as [B C].
         apply path_is_arc_consistent_distributes_over_concat in A.
         destruct A as [A D].
         split.
         + apply Wf_intro; auto. 
         + apply Wf_intro; auto.
     Qed.            

End Weighted_Paths. 
         
  
