Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction_representations. 

  (***************************************************************************************)
Section ReductionClassical. 

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

(* "classical" axioms of Semirings and path spaces by Ahnont Wongseelashote, 1979 *) 
Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r.  (* eqS (r (b (r s1) s2)) (r (b s1 s2))  = true. *) 
Variable r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r. (* eqS (r (b s1 (r s2))) (r (b s1 s2))  = true. *)
  

Lemma observation1 : (bop_left_uop_invariant S (brel_reduce eqS r) b r) <-> (bop_left_uop_invariant S eqS (bop_reduce r b) r).
Proof. compute. split; auto.   Qed. 

Lemma observation2 : (bop_right_uop_invariant S eqS (bop_reduce r b) r) <-> (bop_right_uop_invariant S (brel_reduce eqS r) b r).
Proof. split; auto.   Qed. 
  
Lemma r_left_and_right : ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true. 
Proof. intros s1 s2. 
           assert (H1 := r_left s1 s2). compute in H1. 
           assert (H2 := r_right (r s1) s2). compute in H2.            
           assert (H3 := transS _ _ _ H2 H1). apply symS. 
           exact H3.            
    Qed. 

Lemma reduced_bop_ass : bop_associative (reduced_type S r eqS) (reduced_equality S r eqS) (reduced_bop S b r eqS r_idem). 
Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := r_left (b s1 s2) s3).
         assert (H2 := r_right s1 (b s2 s3)).
         assert (H3 := r_cong _ _ (b_ass s1 s2 s3)).
         apply symS in H2. 
         assert (H4 := transS _ _ _ H3 H2).
         assert (H5 := transS _ _ _ H1 H4).
         exact H5. 
Qed.

Lemma bop_full_reduce_associative : bop_associative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. apply (reduced_bop_associative_iff S b r eqS refS symS transS b_cong r_cong r_idem).
       apply reduced_bop_ass.
Qed. 

Lemma reduced_bop_id : uop_preserves_id S eqS b r -> bop_exists_id S eqS b -> bop_exists_id (reduced_type S r eqS) (reduced_equality S r eqS) (reduced_bop S b r eqS r_idem). 
  Proof. intros H [id p]. exists (inj S r eqS r_idem id). unfold bop_is_id in p. unfold bop_is_id.
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
  (* 
      Ann 
  *)   
Lemma reduced_bop_ann : uop_preserves_ann S eqS b r -> bop_exists_ann S eqS b -> bop_exists_ann (reduced_type S r eqS) (reduced_equality S r eqS) (reduced_bop S b r eqS r_idem). 
  Proof. intros H [ann p]. exists (inj S r eqS r_idem ann). unfold bop_is_ann in p. unfold bop_is_ann.
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


End ReductionClassical. 
