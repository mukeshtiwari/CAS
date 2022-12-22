Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.reduce. 


Section Computation.

Definition uop_compose : ∀ {S : Type}, unary_op S → unary_op S → unary_op S 
  := λ {S} r2 r1 s, r2 (r1 s). 

End Computation.   
  

Section Theory. 

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r1 : unary_op S.
  Variable r2 : unary_op S.
  Variable eqS    : brel S.    

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable trnS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.

  Variable b_cong : bop_congruence S eqS b. 
  Variable b_ass  : bop_associative S eqS b.

  
  Variable r1_cong  : uop_congruence S eqS r1. 
  Variable r1_idem  : uop_idempotent S eqS r1.
  Variable r1_left  : bop_left_uop_invariant S eqS (bop_reduce r1 b) r1.  
  Variable r1_right : bop_right_uop_invariant S eqS (bop_reduce r1 b) r1.

  Variable r2_cong  : uop_congruence S eqS r2. 
  Variable r2_idem  : uop_idempotent S eqS r2.
  Variable r2_left  : bop_left_uop_invariant S eqS (bop_reduce r2 b) r2.  
  Variable r2_right : bop_right_uop_invariant S eqS (bop_reduce r2 b) r2.

  (* this seems to be required to get the composition to be a reduction *) 
  Variable r1_r2_commute : ∀ s, eqS (r2 (r1 s)) (r1 (r2 s)) = true. 

  Lemma composition_congruence : uop_congruence S eqS (uop_compose r2 r1).
  Proof. intros s t H. unfold uop_compose.
         apply r2_cong. apply r1_cong. exact H. 
  Qed.
  
  Lemma composition_idempotent : uop_idempotent S eqS (uop_compose r2 r1). 
  Proof. intro s. compute.
         assert (H1 := r1_r2_commute (r1 s)).
         assert (H2 := r1_idem s). apply r2_cong in H2.
         apply symS in H1.
         assert (H3 := trnS _ _ _ H1 H2).
         apply r2_cong in H3.
         assert (H4 := r2_idem (r1 s)).
         exact (trnS _ _ _ H3 H4). 
  Qed.
  
  Lemma composition_left_uop_invariant : bop_left_uop_invariant S eqS (bop_reduce (uop_compose r2 r1) b) (uop_compose r2 r1).
  Proof. intros s t. compute. 
         assert (H1 := r1_left s t). compute in H1. 
         assert (H2 := r2_left (r1 s) t). compute in H2.
         apply r1_cong in H2.
         assert (H4 := r1_r2_commute (b s t)). apply symS in H4. 
         assert (H5 := r1_r2_commute (b (r2 (r1 s)) t)).
         assert (H6 := trnS _ _ _ H5 H2). 
         assert (H7 := r1_r2_commute (b (r1 s) t)). apply symS in H7. 
         assert (H8 := trnS _ _ _ H6 H7). 
         apply r2_cong in H1.
         exact (trnS _ _ _ H8 H1). 
  Qed.


  Lemma composition_right_uop_invariant : bop_right_uop_invariant S eqS (bop_reduce (uop_compose r2 r1) b) (uop_compose r2 r1).
  Proof. intros s t. compute. 
         assert (H1 := r1_right s t). compute in H1. 
         assert (H2 := r2_right s (r1 t)). compute in H2.
         apply r1_cong in H2.
         assert (H4 := r1_r2_commute (b s t)). apply symS in H4. 
         assert (H5 := r1_r2_commute (b s (r2 (r1 t)))).
         assert (H6 := trnS _ _ _ H5 H2). 
         assert (H7 := r1_r2_commute (b s (r1 t))). apply symS in H7. 
         assert (H8 := trnS _ _ _ H6 H7). 
         apply r2_cong in H1.
         exact (trnS _ _ _ H8 H1). 
  Qed.

(* now we can build the classical reduced semigroup. Our "ground truth" *) 
  Lemma uop_compose_classical_bop_congruence :
     bop_congruence
       (reduced_type S eqS (uop_compose r2 r1))
       (reduced_equality S eqS (uop_compose r2 r1))
       (reduced_bop S b (uop_compose r2 r1) eqS composition_idempotent).
  Proof. apply reduced_bop_congruence; auto. 
         apply composition_congruence. 
  Qed. 

  Lemma uop_compose_classical_bop_associative :
     bop_associative
       (reduced_type S eqS (uop_compose r2 r1))
       (reduced_equality S eqS (uop_compose r2 r1))
       (reduced_bop S b (uop_compose r2 r1) eqS composition_idempotent).
  Proof. apply reduced_bop_ass; auto. 
         - apply composition_congruence.
         - apply composition_left_uop_invariant.
         - apply composition_right_uop_invariant. 
  Qed. 

  Lemma uop_compose_classical_bop_commutative (comm : bop_commutative S eqS b):
     bop_commutative
       (reduced_type S eqS (uop_compose r2 r1))
       (reduced_equality S eqS (uop_compose r2 r1))
       (reduced_bop S b (uop_compose r2 r1) eqS composition_idempotent).
  Proof. apply reduced_bop_commutative; auto. 
         - apply composition_congruence.
  Qed. 

  Lemma uop_compose_classical_bop_idempotent (idem : bop_idempotent S eqS b):
     bop_idempotent
       (reduced_type S eqS (uop_compose r2 r1))
       (reduced_equality S eqS (uop_compose r2 r1))
       (reduced_bop S b (uop_compose r2 r1) eqS composition_idempotent).
  Proof. apply reduced_bop_idempotent; auto. 
         - apply composition_congruence.
  Qed. 

  Lemma uop_compose_classical_bop_not_selective
    (nsel : bop_not_selective S eqS b)
    (Q1 : let (s, _) := projT1 nsel in eqS (uop_compose r2 r1 s) s = true)
    (Q2 : let (_, s) := projT1 nsel in eqS (uop_compose r2 r1 s) s = true)
    (P : let (s, t) := projT1 nsel in (eqS (uop_compose r2 r1 (b s t)) s = false) * (eqS (uop_compose r2 r1 (b s t)) t = false)) : 
     bop_not_selective
       (reduced_type S eqS (uop_compose r2 r1))
       (reduced_equality S eqS (uop_compose r2 r1))
       (reduced_bop S b (uop_compose r2 r1) eqS composition_idempotent).
  Proof. apply (reduced_bop_not_selective _ b (uop_compose r2 r1) eqS composition_idempotent nsel); auto.
  Qed. 
  
  (* now, show correctess of "OCaml" version by 
     tracing back to "ground truth". 
  *) 
  Lemma uop_compose_is_reduction : uop_is_bop_reduction eqS b (uop_compose r2 r1). 
  Proof. apply r_is_b_reduction; auto.
         + apply composition_left_uop_invariant.
         + apply composition_right_uop_invariant.
  Qed. 

  Lemma uop_compose_bop_congruence : 
    bop_congruence S (brel_reduce eqS (uop_compose r2 r1)) (bop_reduce (uop_compose r2 r1) b). 
  Proof. apply bop_full_reduce_congruence_iff_bop_reduce_congruence; auto.
         - apply composition_congruence.
         - apply uop_compose_is_reduction. 
         - apply (reduced_bop_congruence_iff S b (uop_compose r2 r1) 
                    eqS symS trnS b_cong  composition_congruence composition_idempotent).
           apply uop_compose_classical_bop_congruence.
  Qed. 

  Lemma uop_compose_bop_associative : 
    bop_associative S (brel_reduce eqS (uop_compose r2 r1)) (bop_reduce (uop_compose r2 r1) b). 
  Proof. apply bop_full_reduce_associative_iff_bop_reduce_associative; auto.
         - apply composition_congruence.
         - apply uop_compose_is_reduction. 
         - apply (reduced_bop_associative_iff S b (uop_compose r2 r1) 
                    eqS refS symS trnS b_cong  composition_congruence composition_idempotent).
           apply uop_compose_classical_bop_associative.
  Qed. 


  Lemma uop_compose_bop_commutative (comm : bop_commutative S eqS b) : 
    bop_commutative S (brel_reduce eqS (uop_compose r2 r1)) (bop_reduce (uop_compose r2 r1) b). 
  Proof. apply bop_full_reduce_commutative_iff_bop_reduce_commutative; auto.
         - apply composition_congruence.
         - apply uop_compose_is_reduction. 
         - apply (reduced_bop_commutative_iff S b (uop_compose r2 r1) 
                    eqS symS trnS b_cong  composition_congruence composition_idempotent).
           apply uop_compose_classical_bop_commutative; auto. 
  Qed. 

  Lemma uop_compose_bop_idempotent (idem : bop_idempotent S eqS b) : 
    bop_idempotent S (brel_reduce eqS (uop_compose r2 r1)) (bop_reduce (uop_compose r2 r1) b). 
  Proof. apply bop_full_reduce_idempotent_iff_bop_reduce_idempotent; auto.
         - apply composition_congruence.
         - apply uop_compose_is_reduction. 
         - apply (reduced_bop_idempotent_iff_left S b (uop_compose r2 r1) 
                    eqS trnS composition_idempotent).
           apply uop_compose_classical_bop_idempotent; auto.
  Qed. 

  Lemma uop_compose_bop_not_selective
    (nsel : bop_not_selective S eqS b)
    (Q1 : let (s, _) := projT1 nsel in eqS (uop_compose r2 r1 s) s = true)
    (Q2 : let (_, s) := projT1 nsel in eqS (uop_compose r2 r1 s) s = true)
    (P : let (s, t) := projT1 nsel in (eqS (uop_compose r2 r1 (b s t)) s = false) * (eqS (uop_compose r2 r1 (b s t)) t = false)) :           
    bop_not_selective S (brel_reduce eqS (uop_compose r2 r1)) (bop_reduce (uop_compose r2 r1) b). 
  Proof. apply bop_full_reduce_not_selective_implies_bop_reduce_not_selective; auto.
         - apply composition_idempotent.
         - apply (reduced_bop_not_selective_iff_left S b (uop_compose r2 r1) 
                    eqS symS trnS b_cong composition_congruence composition_idempotent).
           apply (uop_compose_classical_bop_not_selective nsel); auto.
  Qed. 

End Theory. 

