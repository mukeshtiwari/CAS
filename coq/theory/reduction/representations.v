
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

