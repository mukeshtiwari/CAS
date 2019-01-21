Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction.representations.
Require Import CAS.coq.theory.reduction.classical. 

(***************************************************************************************)

Section General.

Variable S   : Type.

Variable eqS   : brel S.
Variable refS  : brel_reflexive S eqS. 
Variable symS  : brel_symmetric S eqS.
Variable tranS : brel_transitive S eqS.

Variable r      : unary_op S.
Variable r_cong : uop_congruence S eqS r.
Variable r_idem : uop_idempotent S eqS r. 

Variable bS      : binary_op S. 
Variable bS_cong : bop_congruence S eqS bS.

Lemma bop_full_reduce_congruence : bop_congruence S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof.  intros a b c d. compute. intros E1 E2. apply r_cong. apply r_cong. apply bS_cong; auto. Qed.

(* 
    bop_commutative
 *)
Lemma bop_full_reduce_commutative : 
      bop_commutative S eqS bS -> bop_commutative S (brel_reduce eqS r) (bop_full_reduce r bS). 
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

Lemma bop_full_reduce_is_left : 
  bop_is_left S eqS bS  -> bop_is_left S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros H a b. compute. 
       assert (A := H (r a) (r b)). 
       apply r_cong in A. apply r_cong in A. 
       assert (B := r_idem a).
       assert (C := r_idem (r a)).
       assert (D := tranS _ _ _ C B).
       assert (E := tranS _ _ _ A D).
       exact E.
Qed.        

Lemma bop_full_reduce_is_right : 
  bop_is_right S eqS bS  -> bop_is_right S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros H a b. compute. 
       assert (A := H (r a) (r b)). 
       apply r_cong in A. apply r_cong in A. 
       assert (B := r_idem b).
       assert (C := r_idem (r b)).
       assert (D := tranS _ _ _ C B).
       assert (E := tranS _ _ _ A D).
       exact E.
Qed.

Lemma bop_full_reduce_left_constant : 
  bop_left_constant S eqS bS  -> bop_left_constant S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros H a b c. compute. 
       assert (A := H (r a) (r b) (r c)). 
       apply r_cong in A. apply r_cong in A.  exact A. 
Qed.        

Lemma bop_full_reduce_right_constant : 
  bop_right_constant S eqS bS  -> bop_right_constant S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros H a b c. compute. 
       assert (A := H (r a) (r b) (r c)). 
       apply r_cong in A. apply r_cong in A.  exact A. 
Qed.        

(* others? 
bop_left_cancellative
bop_right_cancellative
bop_anti_left
bop_anti_right
bop_associative 
*) 

End General. 


Section Classical.

Variable S   : Type.

Variable eqS   : brel S.
Variable refS  : brel_reflexive S eqS. 
Variable symS  : brel_symmetric S eqS.
Variable tranS : brel_transitive S eqS.

Variable r      : unary_op S.
Variable r_cong : uop_congruence S eqS r.
Variable r_idem : uop_idempotent S eqS r. 

Variable bS      : binary_op S. 
Variable bS_cong : bop_congruence S eqS bS.
Variable bS_ass  : bop_associative S eqS bS.

(* "classical" axioms of Semirings and path spaces by Ahnont Wongseelashote, 1979 *) 
Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r bS) r.  
Variable r_right : bop_right_uop_invariant S eqS (bop_reduce r bS) r. 

Lemma bop_full_reduce_associative_classical : bop_associative S (brel_reduce eqS r) (bop_full_reduce r bS).
Proof. apply (reduced_bop_associative_iff S bS r eqS refS symS tranS bS_cong r_cong r_idem); auto. 
       apply reduced_bop_ass; auto. 
Qed. 

Lemma bop_full_reduce_idempotent_classical : bop_idempotent S eqS bS -> bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r bS).
Proof. intro idem.
       apply (reduced_bop_idempotent_iff_left S bS r eqS tranS r_idem); auto. 
       apply reduced_bop_idem; auto. 
Qed. 

Lemma bop_full_reduce_selective_classical : bop_selective S eqS bS -> bop_selective S (brel_reduce eqS r) (bop_full_reduce r bS).
Proof. intro sel.
       apply (reduced_bop_selective_iff_left S bS r eqS tranS r_idem); auto. 
       apply reduced_bop_sel; auto. 
Qed. 

Lemma bop_full_reduce_commutative_classical : bop_commutative S eqS bS -> bop_commutative S (brel_reduce eqS r) (bop_full_reduce r bS).
Proof. intro com.
       apply (reduced_bop_commutative_iff S bS r eqS symS tranS bS_cong r_cong r_idem); auto. 
       apply reduced_bop_comm; auto. 
Qed. 

(*
Lemma bop_full_reduce_exists_id_classical : bop_exists_id S eqS bS -> bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r bS).
Proof. intro ID.
       apply (red_exists_id_left S bS r eqS refS tranS bS_cong r_cong r_idem); auto. 
       apply reduced_bop_exists_id; auto. 
Qed. 
bop_exists_id
bop_exists_ann
bop_is_left
bop_is_right
bop_left_cancellative
bop_right_cancellative
bop_left_constant
bop_right_constant
bop_anti_left
bop_anti_right
*) 



End Classical.
