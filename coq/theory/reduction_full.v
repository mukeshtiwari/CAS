Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction_representations.
Require Import CAS.coq.theory.reduction_classical. 

  (***************************************************************************************)

Section FullReduce.

Variable S   : Type.
Variable eqS : brel S.
Variable r   : unary_op S.
Variable bS  : binary_op S. 

Variable r_cong : uop_congruence S eqS r.
Variable bS_cong : bop_congruence S eqS bS.

Variable refS : brel_reflexive S eqS. 
Variable symS : brel_symmetric S eqS.
Variable tranS : brel_transitive S eqS.

Variable r_idem : uop_idempotent S eqS r. 

Lemma bop_full_reduce_congruence : bop_congruence S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof.  intros a b c d. compute. intros E1 E2. apply r_cong. apply r_cong. apply bS_cong; auto. Qed.

Lemma bop_full_reduce_left_right_invariant_implies_associative : 
  bop_associative S eqS bS ->
  bop_left_uop_invariant S eqS (bop_reduce r bS) r ->
  bop_right_uop_invariant S eqS (bop_reduce r bS) r -> 
         bop_associative S (brel_reduce eqS r) (bop_full_reduce r bS). 
Admitted. 
(*
   Some sufficient conditions ... 
*)

(* 
    Commutativity 
*)
Lemma bop_full_reduce_commutative : 
      bop_commutative S eqS bS ->
           bop_commutative S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof.  intros C a b. compute. apply r_cong. apply r_cong. apply C. Qed. 
(* 
      idempotence 
*)   
Lemma bop_full_reduce_idempotent : 
  bop_idempotent S eqS bS -> bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros idemS s. compute.
       assert (H1 := idemS (r s)). apply r_cong in H1. 
       assert (H2 := r_idem s). 
       assert (H3 := tranS _ _ _ H1 H2).  apply r_cong in H3.
       assert (H4 := tranS _ _ _ H3 H2).       
       exact H4. 
Qed.

(* 
    Selectivity 
*)   
Lemma bop_full_reduce_selective : 
  bop_selective S eqS bS -> bop_selective S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros selS s1 s2. compute.
         destruct (selS (r s1) (r s2)) as [H1 | H1].
         left.
         apply r_cong in H1. 
         assert (H2 := r_idem s1).
         assert (H3 := tranS _ _ _ H1 H2). apply r_cong in H3.
         assert (H4 := tranS _ _ _ H3 H2). 
         exact H4.
         right.
         apply r_cong in H1. 
         assert (H2 := r_idem s2).
         assert (H3 := tranS _ _ _ H1 H2). apply r_cong in H3.
         assert (H4 := tranS _ _ _ H3 H2). 
         exact H4.         
Qed.                                  
(* 
      Id 
 *)

Lemma bop_full_reduce_is_id (id : S) :
  uop_preserves_id S eqS bS r -> bop_is_id S eqS bS id -> bop_is_id S (brel_reduce eqS r) (bop_full_reduce r bS) id. 
Proof. intros H p.
       assert (K := H id p).
       compute. 
       intros t. 
       destruct (p (r t)) as [H1  H2]. split. 
       assert (H3 := bS_cong _ _ _ _ K (refS (r t))).
       assert (H4 := tranS _ _ _ H3 H1). apply r_cong in H4. 
       assert (H5 := r_idem t). 
       assert (H6 := tranS _ _ _ H4 H5). apply r_cong in H6. 
       assert (H7 := tranS _ _ _ H6 H5).
       exact H7.
       assert (H3 := bS_cong _ _ _ _ (refS (r t)) K).
       assert (H4 := tranS _ _ _ H3 H2). apply r_cong in H4. 
       assert (H5 := r_idem t). 
       assert (H6 := tranS _ _ _ H4 H5). apply r_cong in H6. 
       assert (H7 := tranS _ _ _ H6 H5).
       exact H7.
Qed.


Lemma bop_full_reduce_exists_id : 
  uop_preserves_id S eqS bS r -> bop_exists_id S eqS bS -> bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros H [id p].
       exists id. 
       apply bop_full_reduce_is_id; auto. 
Qed.
(* 
      Ann 

*)

Lemma bop_full_reduce_is_ann (ann : S):
  uop_preserves_ann S eqS bS r -> bop_is_ann S eqS bS ann -> bop_is_ann S (brel_reduce eqS r) (bop_full_reduce r bS) ann. 
Proof. intros H p.
       assert (K := H ann p).
       compute. 
       intros t. 
       destruct (p (r t)) as [H1  H2]. split. 
       assert (H3 := bS_cong _ _ _ _ K (refS (r t))).
       assert (H4 := tranS _ _ _ H3 H1). apply r_cong in H4. 
       assert (H6 := tranS _ _ _ H4 K). apply r_cong in H6. 
       exact H6.
       assert (H3 := bS_cong _ _ _ _ (refS (r t)) K).
       assert (H4 := tranS _ _ _ H3 H2). apply r_cong in H4. 
       assert (H6 := tranS _ _ _ H4 K). apply r_cong in H6. 
       exact H6.
Qed.

Lemma bop_full_reduce_exists_ann : 
  uop_preserves_ann S eqS bS r -> bop_exists_ann S eqS bS -> bop_exists_ann S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros H [ann p].
       exists ann.
       apply bop_full_reduce_is_ann; auto. 
Qed.


End FullReduce.   
