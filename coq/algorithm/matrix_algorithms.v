From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.eqv.nat
     coq.eqv.list
     coq.sg.properties
     coq.tr.properties
     coq.algorithm.list_congruences     
     coq.algorithm.matrix_definition.


Section Computation. 

  (* pointwise addition to two matrices *)
    Definition matrix_add
               {R : Type}
               (plusR : binary_op R) 
               (m₁ m₂ : functional_matrix R) : functional_matrix R :=
    fun c d => plusR (m₁ c d) (m₂ c d).

    Definition sum_fn
               {V : Type}               
               {R : Type}
               (zeroR : R)               
               (plusR : binary_op R)                
               (f : V -> R)
               (row : list V) : R := fold_right plusR zeroR (map f row). 

  Definition left_row_i_dot_col_j 
             {L : Type}
             {R : Type}
             (ltr : ltr_type L R)
             (mt : functional_matrix L)
             (m : functional_matrix R)             
             (i j q : nat) : R := ltr (mt i q) (m q j).

  Definition right_row_i_dot_col_j 
             {L : Type}
             {R : Type}
             (rtr : rtr_type L R)
             (m : functional_matrix R)
             (mt : functional_matrix L)             
             (i j q : nat) : R := rtr (m i q) (mt q j).
  
  Definition left_matrix_mul
             {L : Type}
             {R : Type}
             (zeroR : R)                            
             (plusR : binary_op R)              
             (ltr : ltr_type L R)
             (dim : nat)             
             (mt : functional_matrix L)
             (m : functional_matrix R) : functional_matrix R :=            
    fun (i j : nat) => sum_fn zeroR plusR (@left_row_i_dot_col_j L R ltr mt m i j)  (list_enum dim). 

  Definition right_matrix_mul
             {L : Type}
             {R : Type}
             (zeroR : R)                            
             (plusR : binary_op R)              
             (rtr : rtr_type L R)
             (dim : nat)            
             (m : functional_matrix R)
             (mt : functional_matrix L) : functional_matrix R :=            
    fun (i j : nat) => sum_fn zeroR plusR (@right_row_i_dot_col_j L R rtr m mt i j)  (list_enum dim). 

  
  Definition matrix_mul
             {R : Type}
             (zeroR : R)                                         
             (plusR mulR : binary_op R) 
             (dim : nat)
             (m₁ m₂ : functional_matrix R) : functional_matrix R :=
    @left_matrix_mul R R zeroR plusR mulR dim m₁ m₂. 
   
  Definition matrix_mul_identity
             {R : Type}
             (zeroR oneR : R) : functional_matrix R := 
    fun (c d : nat) =>  if brel_eq_nat c d then oneR else zeroR.


  (* A |>k 
 
         A |>0 = I
     A |>(k+1) = A |> (A |> k) 
 
  *) 
  Fixpoint left_matrix_exponentiation
             {L : Type}           
             {R : Type}
             (zeroR oneR : R)                                         
             (plusR : binary_op R)
             (ltr : ltr_type L R)
             (dim : nat)
             (lm : functional_matrix L)             
             (k : nat) : functional_matrix R :=
    match k with 
    | 0%nat => matrix_mul_identity zeroR oneR  
    | S k'  => left_matrix_mul zeroR plusR ltr dim lm
                    (left_matrix_exponentiation zeroR oneR plusR ltr dim lm k')
    end.

  (* k <| A

        0 <|A = I
     (k+1)<|A = (k <| A) <| A 
 
  *) 
  Fixpoint right_matrix_exponentiation 
             {L : Type}           
             {R : Type}
             (zeroR oneR : R)                                         
             (plusR : binary_op R)
             (rtr : rtr_type L R)
             (dim : nat)
             (lm : functional_matrix L)                          
             (k : nat) : functional_matrix R :=
    match k with 
    | 0%nat => matrix_mul_identity zeroR oneR
    | S k'  => right_matrix_mul zeroR plusR rtr dim 
                    (right_matrix_exponentiation zeroR oneR plusR rtr dim lm k')
                    lm
    end.
  
    Definition matrix_exp
             {R : Type}
             (zeroR oneR : R)                                         
             (plusR mulR : binary_op R) 
             (dim : nat)
             (m : functional_matrix R)
             (k : nat) : functional_matrix R :=
      @left_matrix_exponentiation R R zeroR oneR plusR mulR dim m k.       

  (* A |>k 
 
     A |>0 = I
     A |>(k+1) = A |> (A |> k) + I 
 
  *) 
  Fixpoint left_matrix_iteration 
             {L : Type}           
             {R : Type}
             (zeroR oneR : R)                                         
             (plusR : binary_op R)
             (ltr : ltr_type L R)
             (dim : nat)
             (lm : functional_matrix L)             
             (k : nat) : functional_matrix R :=
    let id := matrix_mul_identity zeroR oneR in 
    match k with 
    | 0%nat => id 
    | S k'  => matrix_add plusR 
                  (left_matrix_mul zeroR plusR ltr dim lm
                         (left_matrix_iteration zeroR oneR plusR ltr dim lm k'))
                  id 
    end.

  (* k <| A
     0 <|A = I

     (k+1)<|A = (k <| A) <| A + I 
 
  *) 
  Fixpoint right_matrix_iteration 
             {L : Type}           
             {R : Type}
             (zeroR oneR : R)                                         
             (plusR : binary_op R)
             (rtr : rtr_type L R)
             (dim : nat)
             (lm : functional_matrix L)                          
             (k : nat) : functional_matrix R :=
    let id := matrix_mul_identity zeroR oneR in     
    match k with 
    | 0%nat => id 
    | S k'  => matrix_add plusR 
                 (right_matrix_mul zeroR plusR rtr dim 
                    (right_matrix_iteration zeroR oneR plusR rtr dim lm k')
                    lm)
                 id 
    end.


  
  
    
End Computation. 

Section Theory.

  Variables
    (L R : Type)
    (eqL  : brel L)
    (eqR  : brel R)
    (plus : binary_op R) 
    (zero one : R)
    (ltr : ltr_type L R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (refL : brel_reflexive L eqL)
    (symL : brel_symmetric L eqL)
    (trnL : brel_transitive L eqL)
    (congrP : bop_congruence R eqR plus)
    (congrLTR : ltr_congruence L R eqL eqR ltr)
    . 


  Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).    
  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Infix "+M" := (matrix_add plus) (at level 70).  
  Local Infix "=R=" := (eq_functional_matrix_prop R eqR) (at level 70).
  Local Infix "=L=" := (eq_functional_matrix_prop L eqL) (at level 70).  

  Local Definition domain dim := list_enum dim.
  Local Definition CongL := functional_matrix_congruence L eqL.
  Local Definition CongR := functional_matrix_congruence R eqR.  

  Lemma matrix_add_congruence :
      ∀ m₁ m₂ m₃ m₄, m₁ =R= m₃ -> m₂ =R= m₄ -> (m₁ +M m₂) =R= (m₃ +M m₄). 
  Proof. intros m₁ m₂ m₃ m₄ H₁ H₂. unfold matrix_add.
         intros a b. apply congrP. apply H₁. apply H₂. 
  Qed.

(*  Local Infix "*[ n ]" := (matrix_mul zero plus mul n) (at level 70). *) 

    
  Lemma sum_fn_cons : ∀ (f : nat -> R) a l, sum_fn zero plus f (a :: l) = plus (f a) (sum_fn zero plus f l).
  Proof. intros f a l. unfold sum_fn. simpl. reflexivity. Qed.

  Lemma sum_fn_congruence_general
        (V : Type)
        (f g : V -> R)
        (eqV : brel V)
        (cong : ∀ i j, eqV i j = true -> (f i) =r= (g j)):
    ∀ (l1 l2 : list V),  brel_list eqV l1 l2 = true -> 
          sum_fn zero plus f l1 =r= sum_fn zero plus g l2. 
  Proof. intros l1 l2 I.
         unfold sum_fn.
         apply (fold_right_congruence _ _ eqR eqR plus plus).
         intros b b' a a' J K. exact (congrP _ _ _ _ J K). 
         apply refR.
         apply (map_congruence V R eqV eqR f g cong); auto. 
  Qed.          
  Lemma sum_fn_congruence  (f g : nat -> R) (cong : ∀ i j, i =n= j -> (f i) =r= (g j)):
    ∀ l, sum_fn zero plus f l =r= sum_fn zero plus g l.
  Proof. intro l. apply (sum_fn_congruence_general nat f g brel_eq_nat cong). 
         apply brel_list_reflexive. apply brel_eq_nat_reflexive. 
  Qed.
  
  (* try to make this as general as possible *) 
  Lemma fold_right_lemma {A B : Type}
        (assoc : bop_associative R eqR plus)
        (comm : bop_commutative R eqR plus)                 
        (a : B) (b : R) (f : B → R)
        (l : list B) : 
    fold_right plus (plus (f a) b) (map f l) =r= plus (f a) (fold_right plus b (map f l)).
  Proof. induction l.
         + compute. apply refR. 
         + simpl.
           (* Show: 
             IHl :        fold_right plus (plus (f a) b) (map f l)  = plus (f a)              (fold_right plus b (map f l))
             ============================
             plus (f a0) (fold_right plus (plus (f a) b) (map f l)) = plus (f a) (plus (f a0) (fold_right plus b (map f l)))
            
             Proof: 
             plus (f a0) (fold_right plus (plus (f a) b) (map f l))
             = {IHl and congruence} 
             plus (f a0) (plus (f a) (fold_right plus b (map f l)))
             = {assoc} 
             plus(plus (f a0) (f a)) (fold_right plus b (map f l))
             = {comm and congruence} 
             plus(plus (f a) (f a0)) (fold_right plus b (map f l))
             = {assoc}            
             plus (f a) (plus (f a0) (fold_right plus b (map f l)))
        *) 
        assert (C : plus (f a0) (fold_right plus (plus (f a) b) (map f l))
                    =r=
                   plus (f a0) (plus (f a) (fold_right plus b (map f l)))). 
           apply congrP; auto. 
        assert (D : plus (f a0) (plus (f a) (fold_right plus b (map f l)))
                    =r=                    
                    plus(plus (f a0) (f a)) (fold_right plus b (map f l))).
           exact (symR _ _ (assoc (f a0) (f a) (fold_right plus b (map f l)))). 
        assert (E : plus(plus (f a0) (f a)) (fold_right plus b (map f l))
                    =r=
                    plus(plus (f a) (f a0)) (fold_right plus b (map f l))).
            assert (F := comm (f a) (f a0)).
            assert (G := assoc (f a0) (f a) (fold_right plus b (map f l))). 
            assert (I := congrP _ _ _ _ F (refR ((fold_right plus b (map f l))))).
            exact (symR _ _ I).             
        assert (F : plus(plus (f a) (f a0)) (fold_right plus b (map f l))
                    =r=
                    plus (f a) (plus (f a0) (fold_right plus b (map f l)))).                     
            apply assoc. 

        exact (trnR _ _ _ C (trnR _ _ _ D (trnR _ _ _ E F))).
  Qed.

  Lemma fold_right_extract_plus 
        (assoc : bop_associative R eqR plus)
        (comm : bop_commutative R eqR plus)
        (plusID : bop_is_id R eqR plus zero)        
        (v : R) 
        (l : list R) : 
    fold_right plus v l =r= plus (fold_right plus zero l) v.
  Proof. induction l; simpl.
         + destruct (plusID v) as [A B]. exact (symR _ _ A). 
         + assert (A := symR _ _ (assoc a ((fold_right plus zero l)) v)).
           assert (B := congrP _ _ _ _ (refR a) IHl). 
           exact (trnR _ _ _ B A). 
  Qed. 
           
   Lemma sum_fn_distributes_over_concat
        (assoc : bop_associative R eqR plus)
        (comm : bop_commutative R eqR plus)         
        (plusID : bop_is_id R eqR plus zero): 
      ∀ {V : Type} (l₁ l₂ : list V) (f : V -> R), 
      sum_fn zero plus f (l₁ ++ l₂) =r= plus (sum_fn zero plus f l₁) (sum_fn zero plus f l₂).
    Proof. intros V l₁ l₂ f. unfold sum_fn.
           rewrite map_app. 
           rewrite fold_right_app.
           (* Show 
             fold_right plus (fold_right plus zero (map f l₂)) (map f l₁) 
             =r=
             plus (fold_right plus zero (map f l₁)) (fold_right plus zero (map f l₂))

             Proof: 
             fold_right plus (fold_right plus zero (map f l₂)) (map f l₁) 
             =r= {fold_right_extract_plus} 
             plus (fold_right plus zero (map f l₂)) (fold_right plus zero (map f l₁)).
            *)
           apply fold_right_extract_plus; auto. 
    Qed. 

    Lemma left_row_i_dot_col_j_congruence' (m₁ : functional_matrix L) (m₂ : functional_matrix R) (c1 : CongL m₁) (c2 : CongR m₂):
    ∀ a b c d, a =n= c -> b =n= d -> 
                            ∀ i j, i =n= j → left_row_i_dot_col_j ltr m₁ m₂ a b i =r= left_row_i_dot_col_j ltr m₁ m₂ c d j. 
    Proof. intros a b c d A B i j C.
           unfold left_row_i_dot_col_j. 
           apply congrLTR.
           apply c1; auto.
           apply c2; auto. 
    Qed. 
           
    Lemma left_row_i_dot_col_j_congruence :
      ∀ m1 m2 m3 m4,  CongL m1 -> CongR m3 -> 
        m1 =L= m2 -> m3 =R= m4 -> 
           ∀ i j i' j',  i' =n= j' ->
                left_row_i_dot_col_j ltr m1 m3 i j i' =r= left_row_i_dot_col_j ltr m2 m4 i j j'.
    Proof. intros m1 m2 m3 m4 cong1 cong3 A B i j i' j' C. 
           unfold left_row_i_dot_col_j.
           apply congrLTR.
           + assert (D := cong1 _ _ _ _ (brel_eq_nat_reflexive i) C). 
             assert (E := A i j').
             exact (trnL _ _ _ D E).
           + assert (D := cong3 _ _ _ _ C (brel_eq_nat_reflexive j)). 
             assert (E := B j' j).
             exact (trnR _ _ _ D E).
    Qed.              

    Local Infix "*[ n ]>" := (left_matrix_mul zero plus ltr n) (at level 70).
    
    Lemma left_matrix_mul_congruence (n : nat) :
      ∀ m1 m2 m3 m4,
          CongL m1 -> CongR m3 -> 
            m1 =L= m2 -> m3 =R= m4 -> (m1 *[ n ]> m3) =R= (m2 *[ n ]> m4). 
    Proof. intros m1 m2 m3 m4 cong1 cong3 A B i j.
           unfold left_matrix_mul.
           apply sum_fn_congruence. 
           intros i' j' C.
           exact (left_row_i_dot_col_j_congruence m1 m2 m3 m4 cong1 cong3 A B i j i' j' C). 
    Qed.

    Lemma left_matrix_mul_preserves_congruence (n : nat) : ∀ m₁ m₂, CongL m₁ -> CongR m₂ -> CongR (m₁ *[n]> m₂). 
    Proof. intros m₁ m₂. unfold CongL, CongR.
           intros cong1 cong2 a b c d A B. 
           unfold left_matrix_mul.
           apply (sum_fn_congruence (left_row_i_dot_col_j ltr m₁ m₂ a b)
                                    (left_row_i_dot_col_j ltr m₁ m₂ c d)). 
           apply (left_row_i_dot_col_j_congruence' m₁ m₂ cong1 cong2 a b c d A B). 
    Qed. 


    Local Notation "[I]" := (matrix_mul_identity zero one) (at level 70). 

    Local Open Scope nat_scope.

    Local Notation "m ^( k , n )" := (left_matrix_exponentiation zero one plus ltr n m k) (at level 70).

    Lemma unfold_left_matrix_exponentiation :
      ∀ A n k, (A ^( S k , n))
                =R=
                (A *[ n ]> (A ^( k , n))). 
    Proof. intros A n k.
           unfold left_matrix_exponentiation at 1.
           fold (@left_matrix_exponentiation L R zero one plus ltr n A k). 
           intros i j.  apply refR.
    Qed.

    

End Theory.   
