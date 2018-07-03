Require Export Coq.Unicode.Utf8.
Require Import Coq.Bool.Bool.   
Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.theory.uop_properties.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.

Require Import CAS.theory.bop.reduction_theory.


Lemma bop_full_reduce_congruence (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  uop_congruence S eqS r ->
  bop_congruence S eqS bS -> bop_congruence S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof.  intros H C a b c d. compute.
        intros E1 E2. apply H. apply H. 
        apply C.
        exact E1.
        exact E2.
Qed.


Lemma bop_full_reduce_pseudo_associative_implies_associative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->
  brel_symmetric S eqS ->  
  brel_transitive S eqS ->   
  uop_idempotent S eqS r ->
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->
  bop_pseudo_associative S eqS r bS -> 
         bop_associative S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros refS symS tranS r_idem r_cong bS_cong p_assoc s1 s2 s3. compute.
       apply r_cong.
       assert (J1 := r_idem (bS (r s1) (r s2))).
       assert (J2 := bS_cong _ _ _ _ J1 (refS (r s3))). 
       assert (J3 := r_idem (bS (r s2) (r s3))).
       assert (J4 := bS_cong _ _ _ _ (refS (r s1)) J3). 
       apply r_cong in J2. apply r_cong in J4.
       assert (K : eqS (r (bS (r (bS (r s1) (r s2))) (r s3))) (r (bS (r s1) (r (bS (r s2) (r s3))))) = true). apply p_assoc. 
       assert (J5 := tranS _ _ _ J2 K).
       apply symS in J4.
       assert (J6 := tranS _ _ _ J5 J4).
       exact J6.
Qed.


Lemma bop_full_reduce_associative_implies_pseudo_associative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->
  brel_symmetric S eqS ->  
  brel_transitive S eqS ->   
  uop_idempotent S eqS r ->
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->
  bop_associative S (brel_reduce eqS r) (bop_full_reduce r bS) ->
      bop_pseudo_associative S eqS r bS. 
Proof. intros refS symS tranS r_idem r_cong bS_cong assoc s1 s2 s3. compute.
       assert (K := assoc s1 s2 s3). compute in K.
       assert (J1 := r_idem ((bS (r (r (bS (r s1) (r s2)))) (r s3)))). 
       assert (J2 := r_idem ((bS (r s1) (r (r (bS (r s2) (r s3))))))).
       assert (J3 := tranS _ _ _ K J2).
       apply symS in J1.
       assert (J4 := tranS _ _ _ J1 J3).       
       assert (J5 := r_idem (bS (r s1) (r s2))).
       assert (J6 := r_idem (bS (r s2) (r s3))).
       assert (J7 := bS_cong _ _ _ _ J5 (refS (r s3))). apply r_cong in J7.
       assert (J8 := bS_cong _ _ _ _ (refS (r s1)) J6). apply r_cong in J8.
       assert (J9 := tranS _ _ _ J4 J8).              
       apply symS in J7.
       assert (J10 := tranS _ _ _ J7 J9).               
       exact J10.
Qed.


Lemma bop_full_reduce_left_right_invariant_implies_associative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->
  brel_symmetric S eqS ->  
  brel_transitive S eqS ->
  uop_idempotent S eqS r ->  
  uop_congruence S eqS r ->
  bop_congruence S eqS bS -> 
  bop_associative S eqS bS ->
  bop_left_uop_invariant S eqS (bop_reduce r bS) r ->
  bop_right_uop_invariant S eqS (bop_reduce r bS) r -> 
         bop_associative S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros refS symS tranS r_idem r_cong b_cong assoc linv rinv.
       apply bop_full_reduce_pseudo_associative_implies_associative; auto.
       apply r_left_right_imply_pseudo_associative; auto. 
Qed.


(*
   Some sufficient conditions ... 
*)

(* 
    Commutativity 
*)
Lemma bop_full_reduce_commutative (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
      uop_congruence S eqS r -> 
      bop_commutative S eqS bS ->
           bop_commutative S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof.  intros H C a b. compute. apply H. apply H. apply C. Qed. 
(* 
      idempotence 
*)   
Lemma bop_full_reduce_idempotent (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->   
  bop_idempotent S eqS bS -> bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros transS r_cong r_idem idemS s. compute.
       assert (H1 := idemS (r s)). apply r_cong in H1. 
       assert (H2 := r_idem s). 
       assert (H3 := transS _ _ _ H1 H2).  apply r_cong in H3.
       assert (H4 := transS _ _ _ H3 H2).       
       exact H4. 
Qed.

(*
Definition bop_not_idempotent_witness (S : Type) (r : brel S) (b : binary_op S)  (s : S)  := r (b s s) s = false.

Lemma bop_full_reduce_not_idempotent (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) (w : S) :
   bop_not_idempotent_witness S eqS bS w -> 
   bop_not_idempotent_witness S (brel_reduce eqS r) (bop_full_reduce r bS) w. 
Proof. intro H. compute. compute in H.
(* Need: 
   (r w) <> r ((r w) + (r w))
*)        
Qed.                                  
*) 


(* 
    Selectivity 
*)   
Lemma bop_full_reduce_selective (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->   
  bop_selective S eqS bS -> bop_selective S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros transS r_cong r_idem selS s1 s2. compute.
         destruct (selS (r s1) (r s2)) as [H1 | H1].
         left.
         apply r_cong in H1. 
         assert (H2 := r_idem s1).
         assert (H3 := transS _ _ _ H1 H2). apply r_cong in H3.
         assert (H4 := transS _ _ _ H3 H2). 
         exact H4.
         right.
         apply r_cong in H1. 
         assert (H2 := r_idem s2).
         assert (H3 := transS _ _ _ H1 H2). apply r_cong in H3.
         assert (H4 := transS _ _ _ H3 H2). 
         exact H4.         
Qed.                                  
(* 
      Id 
 *)

Lemma bop_full_reduce_is_id (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) (id : S) :
  brel_reflexive S eqS ->  
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->
  bop_congruence S eqS bS ->  
  uop_preserves_id S eqS bS r -> bop_is_id S eqS bS id -> bop_is_id S (brel_reduce eqS r) (bop_full_reduce r bS) id. 
Proof. intros refS transS r_cong r_idem congS H p.
       assert (K := H id p).
       compute. 
       intros t. 
       destruct (p (r t)) as [H1  H2]. split. 
       assert (H3 := congS _ _ _ _ K (refS (r t))).
       assert (H4 := transS _ _ _ H3 H1). apply r_cong in H4. 
       assert (H5 := r_idem t). 
       assert (H6 := transS _ _ _ H4 H5). apply r_cong in H6. 
       assert (H7 := transS _ _ _ H6 H5).
       exact H7.
       assert (H3 := congS _ _ _ _ (refS (r t)) K).
       assert (H4 := transS _ _ _ H3 H2). apply r_cong in H4. 
       assert (H5 := r_idem t). 
       assert (H6 := transS _ _ _ H4 H5). apply r_cong in H6. 
       assert (H7 := transS _ _ _ H6 H5).
       exact H7.
Qed.


Lemma bop_full_reduce_exists_id (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->  
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  uop_idempotent S eqS r ->
  bop_congruence S eqS bS ->  
  uop_preserves_id S eqS bS r -> bop_exists_id S eqS bS -> bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros refS transS r_cong r_idem congS H [id p].
       exists id. 
       apply bop_full_reduce_is_id; auto. 
Qed.
(* 
      Ann 

*)

Lemma bop_full_reduce_is_ann (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) (ann : S):
  brel_reflexive S eqS ->  
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->  
  uop_preserves_ann S eqS bS r -> bop_is_ann S eqS bS ann -> bop_is_ann S (brel_reduce eqS r) (bop_full_reduce r bS) ann. 
Proof. intros refS transS r_cong congS H p.
       assert (K := H ann p).
       compute. 
       intros t. 
       destruct (p (r t)) as [H1  H2]. split. 
       assert (H3 := congS _ _ _ _ K (refS (r t))).
       assert (H4 := transS _ _ _ H3 H1). apply r_cong in H4. 
       assert (H6 := transS _ _ _ H4 K). apply r_cong in H6. 
       exact H6.
       assert (H3 := congS _ _ _ _ (refS (r t)) K).
       assert (H4 := transS _ _ _ H3 H2). apply r_cong in H4. 
       assert (H6 := transS _ _ _ H4 K). apply r_cong in H6. 
       exact H6.
Qed.

Lemma bop_full_reduce_exists_ann (S : Type) (eqS : brel S) (r : unary_op S) (bS : binary_op S) :
  brel_reflexive S eqS ->  
  brel_transitive S eqS -> 
  uop_congruence S eqS r ->
  bop_congruence S eqS bS ->  
  uop_preserves_ann S eqS bS r -> bop_exists_ann S eqS bS -> bop_exists_ann S (brel_reduce eqS r) (bop_full_reduce r bS). 
Proof. intros refS transS r_cong congS H [ann p].
       exists ann.
       apply bop_full_reduce_is_ann; auto. 
Qed.

(* 
Section Distributivity.
  Require Import CAS.theory.bs_properties.  

  Variable S : Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.  
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.   

  Variable r : unary_op S.
  Variable r_cong : uop_congruence S eq r.
  Variable r_idem : uop_idempotent S eq r.
  
  Variable b : binary_op S.
  Variable b_cong : bop_congruence S eq b.  

  Definition T : Type := red_Type S r eq.
  Definition eqT : brel T := red_eq S r eq.
  Definition bT : binary_op T := red_bop S b r eq r_idem.   

  Variable add mul : binary_op S.
  Variable add_cong : bop_congruence S eq add.
  Variable mul_cong : bop_congruence S eq mul.   
  Definition addT : binary_op T := red_bop S add r eq r_idem. 
  Definition mulT : binary_op T := red_bop S mul r eq r_idem.


  Lemma bop_reduce_pseudo_left_distributivity_iso :
                    bop_left_distributive S (brel_reduce r eq) (bop_reduce_args r add) (bop_reduce_args r mul)
                     <->
                     bop_pseudo_left_distributive S eq r add mul.
  Proof. split. intros H s1 s2 s3. 
         assert (K := H s1 s2 s3). compute in K. 
         exact K. 
         intros H s1 s2 s3. compute.
         assert (K := H s1 s2 s3). 
         exact K.
  Qed.

  Lemma bop_reduce_pseudo_right_distributivity_iso :
                    bop_right_distributive S (brel_reduce r eq) (bop_reduce_args r add) (bop_reduce_args r mul)
                     <->
                     bop_pseudo_right_distributive S eq r add mul.
Proof. split. intros H s1 s2 s3. 
  assert (K := H s1 s2 s3). compute in K. 
  exact K. 
  intros H s1 s2 s3. compute.
  assert (K := H s1 s2 s3). 
  exact K.
Qed.

  Lemma bop_reduce_left_distributivity_iso :
                     bop_left_distributive S (brel_reduce r eq) (bop_reduce_args r add) (bop_reduce_args r mul)
                     <->
                     bop_left_distributive S (brel_reduce r eq) (bop_full_reduce r add) (bop_full_reduce r mul).
  Proof. split. intros H s1 s2 s3. 
         assert (K := H s1 s2 s3). compute in K. compute. apply r_cong in K. 
         assert (L := r_idem (add (r s2) (r s3))).
         assert (J := mul_cong (r s1) (r (r (add (r s2) (r s3)))) (r s1) (r (add (r s2) (r s3))) (refS (r s1)) L).
         apply r_cong in J. apply r_cong in J.
         assert (M := tranS _ _ _ J K).
         assert (N := r_idem (mul (r s1) (r s2))).
         assert (O := r_idem (mul (r s1) (r s3))). apply symS in N. apply symS in O.
         assert (P := add_cong    (r (mul (r s1) (r s2))) 
                                  (r (mul (r s1) (r s3)))
                               (r (r (mul (r s1) (r s2)))) 
                               (r (r (mul (r s1) (r s3)))) N O).
         apply r_cong in P. apply r_cong in P. assert (Q := tranS _ _ _ M P).
         exact Q.
         intros H s1 s2 s3. compute.
         assert (K := H s1 s2 s3). compute in K. 
       assert (A := r_idem (mul (r s1) (r (r (add (r s2) (r s3)))))). apply symS in A.
       assert (B := r_idem (add (r (r (mul (r s1) (r s2)))) (r (r (mul (r s1) (r s3)))))).
       assert (C := tranS _ _ _ A K). assert (D := tranS _ _ _ C B).
       assert (L := r_idem (add (r s2) (r s3))). 
       assert (J := mul_cong (r s1) (r (r (add (r s2) (r s3)))) (r s1) (r (add (r s2) (r s3))) (refS (r s1)) L).
       apply r_cong in J. apply symS in J.
       assert (M := tranS _ _ _ J D).
       assert (N := r_idem (mul (r s1) (r s2))).
         assert (O := r_idem (mul (r s1) (r s3))). apply symS in N. apply symS in O.
         assert (P := add_cong    (r (mul (r s1) (r s2))) 
                                  (r (mul (r s1) (r s3)))
                               (r (r (mul (r s1) (r s2)))) 
                               (r (r (mul (r s1) (r s3)))) N O).
                               apply r_cong in P. apply symS in P. assert (Q := tranS _ _ _ M P).
    exact Q.
Qed.

  Lemma bop_reduce_right_distributivity_iso :
                     bop_right_distributive S (brel_reduce r eq) (bop_reduce_args r add) (bop_reduce_args r mul)
                     <->
                     bop_right_distributive S (brel_reduce r eq) (bop_full_reduce r add) (bop_full_reduce r mul).
Proof. split. intros H s1 s2 s3. 
         assert (K := H s1 s2 s3). compute in K. compute. apply r_cong in K. 
         assert (L := r_idem (add (r s2) (r s3))).
         assert (J := mul_cong (r (r (add (r s2) (r s3)))) (r s1) (r (add (r s2) (r s3))) (r s1)  L (refS (r s1))).
         apply r_cong in J. apply r_cong in J.
         assert (M := tranS _ _ _ J K).
         assert (N := r_idem (mul (r s2) (r s1))).
         assert (O := r_idem (mul (r s3) (r s1))). apply symS in N. apply symS in O.
         assert (P := add_cong    (r (mul (r s2) (r s1))) 
                                  (r (mul (r s3) (r s1)))
                               (r (r (mul (r s2) (r s1)))) 
                               (r (r (mul (r s3) (r s1)))) N O).
         apply r_cong in P. apply r_cong in P. assert (Q := tranS _ _ _ M P).
         exact Q.
         intros H s1 s2 s3. compute.
         assert (K := H s1 s2 s3). compute in K. 
       assert (A := r_idem (mul (r (r (add (r s2) (r s3))))(r s1) )). apply symS in A.
       assert (B := r_idem (add (r (r (mul (r s2) (r s1)))) (r (r (mul (r s3) (r s1)))))).
       assert (C := tranS _ _ _ A K). assert (D := tranS _ _ _ C B).
       assert (L := r_idem (add (r s2) (r s3))). 
       assert (J := mul_cong (r (r (add (r s2) (r s3)))) (r s1) (r (add (r s2) (r s3))) (r s1)  L (refS (r s1))).
       apply r_cong in J. apply symS in J.
       assert (M := tranS _ _ _ J D).
       assert (N := r_idem (mul (r s2) (r s1))).
         assert (O := r_idem (mul (r s3) (r s1))). apply symS in N. apply symS in O.
         assert (P := add_cong    (r (mul (r s2) (r s1))) 
                                  (r (mul (r s3) (r s1)))
                               (r (r (mul (r s2) (r s1)))) 
                               (r (r (mul (r s3) (r s1)))) N O).
                               apply r_cong in P. apply symS in P. assert (Q := tranS _ _ _ M P).
    exact Q.
Qed.

End Distributivity.
*) 