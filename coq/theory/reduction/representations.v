Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.sg.properties.

(* First, the "classic" theory of reductions. 

   let (S, =, (x)) be a semigroup. 
   A function r : S -> S is a reduction for (x) if 
   (1) r(r(s)) = r(s)  
   (2) r(a (x) b) = r(r(a) (x) b) 
   (3) r(a (x) b) = r(a (x) r(b))  

   We can then define the reduced semigroup 

      (S_r, =, (x)_r) 

   where S_r = {a in S | r(a) = a}, and 
   equality on S_r is just 
   equality on S restricted to S_r, and 

      a (x)_r b = r(a (x) b). 

   The problem CAPP has with this classic picture is 
   that {a in S | r(a) = a} is not directly 
   representable as an OCaml datatype. 

   Our solution is the represent the reduced 
   semigroup as 

     (S, =_r, 

*) 

Section ReductionRepresentations.

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r : unary_op S.
  Variable eqS    : brel S.    

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable transS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.
  
  Variable b_cong : bop_congruence S eqS b. 
  Variable b_ass  : bop_associative S eqS b.

  (* make assumptions about r required to build the reduced semigroup *) 
  Variable r_cong  : uop_congruence S eqS r. 
  Variable r_idem  : uop_idempotent S eqS r.

  
  Definition is_a_fixed_point (x : S) := eqS (r x) x = true.  
  Definition reduced_type := { x : S & is_a_fixed_point x}.

  (* equality on reduced_type is just equality on S, but need to project out first components! *) 
  Definition reduced_equality : brel reduced_type := λ p1 p2, eqS ((projT1 p1)) ((projT1 p2)).

  Lemma reduced_equality_congruence : brel_congruence reduced_type reduced_equality reduced_equality. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4].   compute. apply eqS_cong. Qed. 

  Lemma reduced_equality_reflexive : brel_reflexive reduced_type reduced_equality. 
  Proof. intros [s p]. compute. apply refS. Qed.
       
  Lemma reduced_equality_symmetric : brel_symmetric reduced_type reduced_equality. 
  Proof. intros [s1 p1] [s2 p2].   compute. apply symS. Qed.

  Lemma reduced_equality_transitive : brel_transitive reduced_type reduced_equality. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute. apply transS. Qed.

  Lemma is_a_fixed_point_bop_reduce : ∀ (p1 p2 : reduced_type), is_a_fixed_point (bop_reduce r b (projT1 p1) (projT1 p2)).
  Proof. intros [s1 p1] [s2 p2]. compute. apply r_idem. Defined.

  Definition reduced_bop : binary_op reduced_type :=
    λ p1 p2,  existT is_a_fixed_point (bop_reduce r b (projT1 p1) (projT1 p2)) (is_a_fixed_point_bop_reduce p1 p2).

  Lemma reduced_bop_congruence : bop_congruence reduced_type reduced_equality reduced_bop.
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute.
         unfold is_a_fixed_point in *.  intros H1 H2.
         apply r_cong.
         apply b_cong; auto.
  Qed.

(* "classical" axioms of Semirings and path spaces by Ahnont Wongseelashote, 1979 *) 
Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r.  (* eqS (r (b (r s1) s2)) (r (b s1 s2))  = true. *) 
Variable r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r. (* eqS (r (b s1 (r s2))) (r (b s1 s2))  = true. *)
  

Lemma observation1 : (bop_left_uop_invariant S (brel_reduce eqS r) b r) <-> (bop_left_uop_invariant S eqS (bop_reduce r b) r).
Proof. compute. split; auto.   Qed. 

Lemma observation2 : (bop_right_uop_invariant S eqS (bop_reduce r b) r) <-> (bop_right_uop_invariant S (brel_reduce eqS r) b r).
Proof. split; auto.   Qed.

Lemma r_is_b_reduction : ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true. 
Proof. intros s1 s2. 
           assert (H1 := r_left s1 s2). compute in H1. 
           assert (H2 := r_right (r s1) s2). compute in H2.            
           assert (H3 := transS _ _ _ H2 H1). apply symS. 
           exact H3.            
    Qed. 

Lemma reduced_bop_ass : bop_associative reduced_type reduced_equality reduced_bop. 
Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := r_left (b s1 s2) s3).
         assert (H2 := r_right s1 (b s2 s3)).
         assert (H3 := r_cong _ _ (b_ass s1 s2 s3)).
         apply symS in H2. 
         assert (H4 := transS _ _ _ H3 H2).
         assert (H5 := transS _ _ _ H1 H4).
         exact H5. 
Qed.

Definition inj (s : S) : reduced_type := existT is_a_fixed_point (r s) (r_idem s).

Lemma reduced_bop_id :
  uop_preserves_id S eqS b r
  -> bop_exists_id S eqS b
  -> bop_exists_id reduced_type reduced_equality reduced_bop. 
  Proof. intros H [id p]. exists (inj id). unfold bop_is_id in p. unfold bop_is_id.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H id p).
          assert (H4 := r_left  id t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := transS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := transS _ _ _ H6 pt).
          exact H7.
          assert (H3 := H id p).
          assert (H4 := r_right  t id). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := transS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := transS _ _ _ H6 pt).
          exact H7.
Qed.

Lemma reduced_bop_ann :
  uop_preserves_ann S eqS b r
  -> bop_exists_ann S eqS b
  -> bop_exists_ann reduced_type reduced_equality reduced_bop. 
  Proof. intros H [ann p]. exists (inj ann). unfold bop_is_ann in p. unfold bop_is_ann.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H ann p).
          assert (H4 := r_left  ann t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := transS _ _ _ H4 H5).
          exact H6.
          assert (H3 := H ann p).
          assert (H4 := r_right  t ann). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := transS _ _ _ H4 H5).
          exact H6.
  Qed.


  (*
   f is a homomorphism for b and b' if 
    f(b(x, y)) = b'(f(x), f(y))

   The following show that 
    1) inj is a homomorphism for (bop_full_reduce r b) and reduced_bop. 
    2) projT1 is a homomorphism for reduced_bop and (bop_full_reduce r b). 
    3) (inj o projT1) is id on reduced_type
    4) (projT1 o inj) is id on r(S), the image of r 

    so we have an isomorphism between (S, (bop_full_reduce r b) and (reduced_type, bop_red) 

    HOWEVER, the isomorphism only works on the image of r, r(S). 

*)
  
  Lemma inj_homomorphism : ∀ (s1 s2 : S),  reduced_equality (inj (bop_full_reduce r b s1 s2)) (reduced_bop (inj s1) (inj s2)) = true. 
  Proof. intros s1 s2. compute. apply r_idem. Qed.
  
  Lemma proj1_homomorphism : ∀ (p1 p2 : reduced_type),  eqS (projT1 (reduced_bop p1 p2)) (bop_full_reduce r b (projT1 p1) (projT1 p2)) = true. 
  Proof. intros [s1 P1] [s2 P2]. compute. compute in P1. compute in P2.
         apply r_cong.
         assert (K := b_cong _ _ _ _ P1 P2).  apply symS.
         exact K. 
  Qed. 

  Lemma inj_proj1_is_id : ∀ p : reduced_type,  reduced_equality p (inj (projT1 p)) = true.
  Proof. intros [s P]. compute. compute in P. apply symS. exact P. Qed. 
  
  Lemma proj1_inj_is_id_on_image_of_r : ∀ s : S,  eqS (r s) (projT1 (inj (r s))) = true.
  Proof. intro s. compute. apply symS. apply r_idem. Qed.

  Lemma equality_lemma_1 : ∀ (p1 p2 : reduced_type),  eqS (projT1 p1) (projT1 p2) = reduced_equality p1 p2.
  Proof. intros [s1 P1] [s2 P2]. compute. reflexivity. Qed.

  Lemma equality_lemma_2 : ∀ (s1 s2 : S),  eqS (r s1) (r s2) = reduced_equality (inj s1) (inj s2).
  Proof. intros s1 s2. compute. reflexivity. Qed. 


  (*****************************************************************************************
      Now show that 
      (reduced_type, reduced_equality, reduced_bop) is "isomorphic" to 

      (S, brel_reduce r eqS, bop_full_reduce r b)
  *******************************************************************************************) 
  

(*
     Equality 
*)

Lemma reduced_equality_congruence_iff :
  brel_congruence reduced_type reduced_equality reduced_equality
  <->
  brel_congruence S (brel_reduce eqS r) (brel_reduce eqS r).
Proof. split. intros H x y m n. compute. intros H1 H2.
       assert (K := H (inj x) (inj y) (inj m) (inj n)). compute in K. 
       apply K; auto.
       intros H [s1 p1] [s2 p2] [s3 p3] [s4 p4].
       compute. apply eqS_cong.
Qed. 

Lemma reduced_equality_reflexive_iff :
  brel_reflexive reduced_type reduced_equality
  <->
  brel_reflexive S (brel_reduce eqS r).
  Proof. split. intros H s. compute.
         assert (K := H (inj s)).
         unfold reduced_equality in K. simpl in K.
         exact K. 
         intros H [s p]. unfold is_a_fixed_point in p.
         compute. apply refS. 
Qed.          

Lemma reduced_equality_symmetric_iff :
  brel_symmetric reduced_type reduced_equality
  <->
  brel_symmetric S (brel_reduce eqS r).
  Proof. split. intros H s1 s2. compute.
         assert (K := H (inj s1) (inj s2)).
         unfold reduced_equality in K. simpl in K.
         exact K. 
         intros H [s1 p1] [s2 p2]. unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2.
         compute. intro H2. 
         assert (K := symS _ _ H2).
         exact K.
Qed.          

Lemma reduced_equality_transitive_iff :
  brel_transitive reduced_type reduced_equality
  <->
  brel_transitive S (brel_reduce eqS r).
  Proof. split. intros H s1 s2 s3. compute. intros H1 H2. 
         assert (K := H (inj s1) (inj s2) (inj s3)). compute in K. 
         apply K; auto. 
         intros H [s1 p1] [s2 p2] [s3 p3]. 
         compute. apply transS. 
Qed.          

(*
     full reduction 
 *)

Lemma bop_reduce_is_bop_full_reduce 
    (r_is_b_reduction : ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true) :
    ∀ x y,
   brel_reduce eqS r (bop_reduce r b x y) (bop_full_reduce r b x y) = true.
Proof. intros x y. unfold bop_reduce, brel_reduce, bop_full_reduce.
       assert (A := r_idem (b x y)). 
       assert (B := r_idem (b (r x) (r y))).
       assert (C := transS _ _ _ A (r_is_b_reduction x y)). 
       apply symS in B. 
       exact (transS _ _ _ C B).
Qed.

Lemma reduced_bop_congruence_iff: 
  bop_congruence reduced_type reduced_equality reduced_bop
  <->
  bop_congruence S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. split.
       (* -> *) 
       intros H s1 s2 s3 s4. compute. intros H1 H2. 
       assert (K := H (inj s1) (inj s2) (inj s3) (inj s4)). compute in K.
       apply r_cong.        
       apply K; auto.
       (* <- *) 
       intros H [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute. intros H1 H2. 
       unfold is_a_fixed_point in p1, p2, p3, p4. 
       compute in H.
       assert (J1 := r_cong _ _ H1).
       assert (J2 := r_cong _ _ H2).
       assert (J3 := H _ _ _ _ J1 J2).
       assert (J4 := r_idem (b (r s1) (r s2))).
       assert (J5 := r_idem (b (r s3) (r s4))).
       assert (J6 := transS _ _ _ J3 J5).
       apply symS in J4.
       assert (J7 := transS _ _ _ J4 J6).
       assert (J8 := b_cong _ _ _ _ p1 p2). apply r_cong in J8.
       assert (J9 := b_cong _ _ _ _ p3 p4). apply r_cong in J9.
       assert (J10 := transS _ _ _ J7 J9).
       apply symS in J8.
       assert (J11 := transS _ _ _ J8 J10).
       exact J11.
Qed.


Lemma reduced_bop_associative_iff :
  bop_associative reduced_type reduced_equality reduced_bop
  <->
  bop_associative S (brel_reduce eqS r) (bop_full_reduce r b). 
Proof. split; intro H.
         intros s1 s2 s3. compute. 
         assert (H1 := H (inj s1) (inj s2) (inj s3)). compute in H1.
         apply r_cong.
         assert (H2 := r_idem (b (r s1) (r s2))).
         assert (H3 := r_idem (b (r s2) (r s3))).
         assert (H4 := b_cong _ _ _ _ H2 (refS (r s3))).
         assert (H5 := b_cong _ _ _ _ (refS (r s1)) H3).
         apply r_cong in H4. apply r_cong in H5.
         assert (H6 := transS _ _ _ H4 H1). apply symS in H5. 
         assert (H7 := transS _ _ _ H6 H5).          
         exact H7.
         intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := H s1 s2 s3). compute in H1. unfold is_a_fixed_point in p1, p2, p3.
         assert (H2 := b_cong _ _ _ _ p1 p2). apply r_cong in H2.
         assert (K2 := r_idem (b (r s1) (r s2))). 
         assert (K3 := transS _ _ _ K2 H2). 
         assert (H3 := b_cong _ _ _ _ K3 p3). apply r_cong in H3.
         assert (K4 := r_idem (b (r (r (b (r s1) (r s2)))) (r s3))). 
         assert (K5 := transS _ _ _ K4 H3).

         assert (H4 := b_cong _ _ _ _ p2 p3). apply r_cong in H4. 
         assert (K6 := r_idem (b (r s2) (r s3))). 
         assert (K7 := transS _ _ _ K6 H4).
         assert (H5 := b_cong _ _ _ _ p1 K7). apply r_cong in H5.
         assert (K8 := r_idem (b (r s1) (r (r (b (r s2) (r s3)))))). 
         assert (K9 := transS _ _ _ K8 H5).
         apply symS in K5.
         assert (H6 := transS _ _ _ K5 H1).
         assert (H7 := transS _ _ _ H6 K9).         
         exact H7.
Qed.


Lemma reduced_bop_commutative_iff :
  bop_commutative reduced_type reduced_equality reduced_bop
  <->
  bop_commutative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. split.
         intros H s1 s2. compute.
         assert (K := H (inj s1) (inj s2)). compute in K.
         apply r_cong.
         exact K. 
         intros H1 [s1 p1] [s2 p2]. compute.
         assert (K := H1 s1 s2). compute in K. 
         unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2.
         assert (J1 := r_idem (b (r s1) (r s2))).
         assert (J2 := r_idem (b (r s2) (r s1))).
         apply symS in J1.
         assert (J3 := transS _ _ _ J1 K).
         assert (J4 := transS _ _ _ J3 J2).
         assert (J5 := b_cong _ _ _ _ p1 p2). apply r_cong in J5. 
         assert (J6 := b_cong _ _ _ _ p2 p1). apply r_cong in J6. 
         assert (J7 := transS _ _ _ J4 J6).         
         apply symS in J5. 
         assert (J8 := transS _ _ _ J5 J7).
         exact J8.
Qed.

(* 
   Note : bop_commutative is a Prop while bop_not_commutative is a Type (fix this?) so 
   can't use <-> here, and need break up into -> and <- lemmas. 
*) 
Lemma reduced_bop_not_commutative_iff_left :
  bop_not_commutative reduced_type reduced_equality reduced_bop
  ->
  bop_not_commutative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof.   intros [[[s1 p1] [s2 p2]]  p3]. compute in p3.  unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2. 
         exists (s1, s2). compute.
         case_eq(eqS (r (r (b (r s1) (r s2)))) (r (r (b (r s2) (r s1))))); intro J1.
         assert (K : eqS (r (b s1 s2)) (r (b s2 s1)) = true).
            assert (J2 := b_cong _ _ _ _ p1 p2). apply r_cong in J2. apply symS in J2. 
            assert (J3 := r_idem (b (r s1) (r s2))).  apply symS in J3.
            assert (J4 := transS _ _ _ J2 J3).            
            assert (J5 := transS _ _ _ J4 J1).            
            assert (J6 := r_idem (b (r s2) (r s1))). 
            assert (J7 := transS _ _ _ J5 J6).            
            assert (J8 := b_cong _ _ _ _ p2 p1). apply r_cong in J8.
            assert (J9 := transS _ _ _ J7 J8).
            exact J9.
         rewrite K in p3.  discriminate p3. 
         reflexivity. 
Qed. 


Lemma reduced_bop_not_commutative_iff_right :
  bop_not_commutative S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_commutative reduced_type reduced_equality reduced_bop. 
Proof.  intros [[s1 s2]  p]. exists (inj s1, inj s2). compute.  
        compute in p. 
        case_eq(eqS (r (b (r s1) (r s2))) (r (b (r s2) (r s1)))); intro J1.
           apply r_cong in J1.
           rewrite J1 in p. discriminate p. 
        reflexivity. 
Qed. 

Lemma reduced_bop_selective_iff_left :
  bop_selective reduced_type reduced_equality reduced_bop
  ->
  bop_selective S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof. intros H s1 s2. compute.
  assert (K := H (inj s1) (inj s2)). compute in K.
  destruct K as [K | K]. left. 
  assert (A := r_idem (b (r s1) (r s2)) ).
  exact (transS _ _ _ A K).
  right. assert (A := r_idem (b (r s1) (r s2)) ).
  exact (transS _ _ _ A K).
 Qed.

 Lemma reduced_bop_selective_iff_right :
   bop_selective S (brel_reduce eqS r) (bop_full_reduce r b)
   ->
   bop_selective reduced_type reduced_equality reduced_bop.
 Proof. intros H1 [s1 p1] [s2 p2]. compute.
  assert (K := H1 s1 s2). compute in K. 
  unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2.
  destruct K as [K | K]. left. 
  assert (A := r_idem (b (r s1) (r s2)) ). apply symS in A.
  assert (B := transS _ _ _ A K).
  assert (C := b_cong (r s1) (r s2) s1 s2 p1 p2). apply r_cong in C. apply symS in C.
  assert (D := transS _ _ _ C B).
  exact (transS _ _ _ D p1).
  right.
  assert (A := r_idem (b (r s1) (r s2)) ). apply symS in A.
  assert (B := transS _ _ _ A K).
  assert (C := b_cong (r s1) (r s2) s1 s2 p1 p2). apply r_cong in C. apply symS in C.
  assert (D := transS _ _ _ C B).
  exact (transS _ _ _ D p2).
 Qed.


 (* not selective ... *)


 Lemma reduced_bop_idempotent_iff_left :
   bop_idempotent reduced_type reduced_equality reduced_bop
   ->
   bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof. intros H s . compute.
  assert (K := H (inj s)). compute in K.
  assert (A := r_idem (b (r s) (r s)) ).
  exact (transS _ _ _ A K).
 Qed.

 Lemma reduced_bop_idempotent_iff_right :
   bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r b)
   ->
   bop_idempotent reduced_type reduced_equality reduced_bop.
 Proof. intros H1 [s p]. compute.
  assert (K := H1 s). compute in K. 
  unfold is_a_fixed_point in p. 
  assert (A := r_idem (b (r s) (r s)) ). apply symS in A.
  assert (B := transS _ _ _ A K).
  assert (C := b_cong (r s) (r s) s s p p). apply r_cong in C. apply symS in C.
  assert (D := transS _ _ _ C B).
  exact (transS _ _ _ D p).
 Qed.

 (* not idempotent ... *) 

 Lemma red_exists_id_left :
   bop_exists_id reduced_type reduced_equality reduced_bop
   ->
   bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros [[id P] Q].
       exists id. intro s; compute. compute in Q.
       destruct (Q (inj s)) as [L R]. compute in L, R. unfold is_a_fixed_point in P.
       split.
       assert (J1 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J1.
       assert (J2 := transS _ _ _ J1 L). apply r_cong in J2.
       assert (J3 := r_idem s).
       assert (J4 := transS _ _ _ J2 J3).
       exact J4.
       assert (J1 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J1.
       assert (J2 := transS _ _ _ J1 R). apply r_cong in J2.
       assert (J3 := r_idem s).
       assert (J4 := transS _ _ _ J2 J3).
       exact J4. 
Qed. 

Lemma red_exists_id_right :
  bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_exists_id reduced_type reduced_equality reduced_bop.
Proof. intros [id Q].
       exists (inj id). intros [s P]; compute. compute in Q.
       destruct (Q s) as [L R].  unfold is_a_fixed_point in P.
       split.
       assert (J1 := b_cong _ _ _ _(refS (r id)) P). apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
       assert (J2 := transS _ _ _ J1 L). 
       assert (J3 := r_idem (b (r id) s)). apply symS in J3. 
       assert (J4 := transS _ _ _ J3 J2).
       assert (J5 := transS _ _ _ J4 P).       
       exact J5.
       assert (J1 := b_cong _ _ _ _ P (refS (r id))). apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
       assert (J2 := transS _ _ _ J1 R). 
       assert (J3 := r_idem (b s (r id))). apply symS in J3. 
       assert (J4 := transS _ _ _ J3 J2).
       assert (J5 := transS _ _ _ J4 P).       
       exact J5.
Qed. 


Lemma red_not_exists_id_left :
  bop_not_exists_id reduced_type reduced_equality reduced_bop
  ->
  bop_not_exists_id S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros H s. compute.
       destruct (H (inj s)) as [[s' P] Q]. compute in Q. unfold is_a_fixed_point in P.
       exists s'.
       destruct Q as [Q | Q].
       left.
       case_eq(eqS (r (r (b (r s) (r s')))) (r s')); intro J1.
       assert (K : eqS (r (b (r s) s')) s' = true).
          assert (J2 := transS _ _ _ J1 P).
          assert (J3 := r_idem (b (r s) (r s'))). apply symS in J3.
          assert (J4 := transS _ _ _ J3 J2).
          assert (J5 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J5. apply symS in J5.
          assert (J6 := transS _ _ _ J5 J4).
          exact J6. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
       right. 
       case_eq(eqS (r (r (b (r s') (r s)))) (r s')); intro J1.
       assert (K : eqS (r (b s' (r s))) s' = true).
          assert (J2 := transS _ _ _ J1 P).
          assert (J3 := r_idem (b (r s') (r s))). apply symS in J3.
          assert (J4 := transS _ _ _ J3 J2).
          assert (J5 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J5. apply symS in J5.
          assert (J6 := transS _ _ _ J5 J4).
          exact J6. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
Qed.

Lemma red_not_exists_id_right :
  bop_not_exists_id S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_exists_id reduced_type reduced_equality reduced_bop.
Proof. intros H [s P]. compute. unfold is_a_fixed_point in P. 
       destruct (H s) as [s' Q]. compute in Q.
       exists (inj s'). compute. 
       destruct Q as [Q | Q].
       left.
       case_eq(eqS (r (b s (r s'))) (r s')); intro J1.
       assert (K : eqS (r (r (b (r s) (r s')))) (r s') = true).
          assert (J2 := b_cong _ _ _ _ P (refS (r s'))). apply r_cong in J2. 
          assert (J3 := transS _ _ _ J2 J1). apply r_cong in J3. 
          assert (J4 := r_idem s'). 
          assert (J5 := transS _ _ _ J3 J4).
          exact J5. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
       right. 
       case_eq(eqS (r (b (r s') s)) (r s')); intro J1.
       assert (K : eqS (r (r (b (r s') (r s)))) (r s') = true).
          assert (J2 := b_cong _ _ _ _ (refS (r s')) P). apply r_cong in J2. 
          assert (J3 := transS _ _ _ J2 J1). apply r_cong in J3. 
          assert (J4 := r_idem s'). 
          assert (J5 := transS _ _ _ J3 J4).
          exact J5. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
Qed.

(* other properties on semigroups? ... 


*) 


  (* 
    Some sufficient conditions ...
  *) 
  
  (* 
    Commutativity 
   *)
  Lemma reduced_bop_comm : bop_commutative S eqS b -> bop_commutative reduced_type reduced_equality reduced_bop. 
  Proof. intros H1 [s1 p1] [s2 p2]. compute.
         unfold bop_commutative in H1. 
         apply r_cong. apply H1. 
  Qed.
  
  (* 
      idempotence 
  *)   
  Lemma reduced_bop_idem : bop_idempotent S eqS b -> bop_idempotent reduced_type reduced_equality reduced_bop. 
  Proof. intros idemS [s p]. compute.
         assert (H1 := idemS s).
         unfold is_a_fixed_point in p.
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p). 
         exact H3. 
  Qed.                                  
  (* 
      Selectivity 
  *)   
  Lemma reduced_bop_sel : bop_selective S eqS b -> bop_selective reduced_type reduced_equality reduced_bop. 
  Proof. intros selS [s1 p1] [s2 p2]. compute.
         destruct (selS s1 s2) as [H1 | H1].
         left. unfold is_a_fixed_point in p1. 
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p1). 
         exact H3.
         right. unfold is_a_fixed_point in p2. 
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p2). 
         exact H3. 
  Qed.                                  

End ReductionRepresentations.

