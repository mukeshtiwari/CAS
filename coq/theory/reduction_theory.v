Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction_representations. 

  (***************************************************************************************)


Section ClassicalReduction.

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


End ClassicalReduction. 


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






Definition uop_predicate_reduce : ∀ {S : Type}, S -> (S -> bool) -> unary_op S 
  := λ  {S} s1 P s2,  if P s2 then s1 else s2.

Definition bop_fpr {S : Type} (s : S ) (P : S -> bool) (bS : binary_op S) := 
  bop_full_reduce (uop_predicate_reduce s P) bS.


Section PredicateReduce.

(* non-commutativity *)

(* First, show that witnesses (w1, w2) must have P(w1) = P(w2) = false *) 

Definition bop_not_commutative_witness(S : Type) (r : brel S) (b : binary_op S) (z : S * S)
  := match z with (s, t) => r (b s t) (b t s) = false end.

Lemma bop_fpr_not_commutative_and_id_implies_witnesses_P_false {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_reflexive S eq ->
  brel_symmetric S eq ->
  brel_transitive S eq -> 
  pred_true S P s -> pred_congruence S eq P -> bop_is_id S eq bS s -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) -> 
  ((P w1 = false) * (P w2 = false)). 
Proof. intros refS symS tranS Ps Pc id W. compute in W. 
       case_eq(P w1); intro H1; case_eq(P w2); intro H2; rewrite H1, H2 in W.
       destruct (id s) as [L _]. apply Pc in L. rewrite Ps in L.  rewrite L in W. rewrite (refS s) in W. discriminate W.
       destruct (id w2) as [L R]. apply Pc in L. apply Pc in R. rewrite H2 in L, R.  rewrite L, R in W.
       destruct (id w2) as [L2 R2]. apply symS in R2.
       assert (H3 := tranS _ _ _ L2 R2). rewrite H3 in W. discriminate W.
       destruct (id w1) as [L R]. apply Pc in L. apply Pc in R. rewrite H1 in L, R.  rewrite L, R in W.
       destruct (id w1) as [L2 R2]. apply symS in L2.
       assert (H3 := tranS _ _ _ R2 L2). rewrite H3 in W. discriminate W.
       auto.
Qed.

Lemma bop_fpr_not_commutative_and_ann_implies_witnesses_P_false {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_reflexive S eq ->
  pred_true S P s -> pred_congruence S eq P -> bop_is_ann S eq bS s -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) -> 
  ((P w1 = false) * (P w2 = false)). 
Proof. intros refS Ps Pc ann W. compute in W. 
       case_eq(P w1); intro H1; case_eq(P w2); intro H2; rewrite H1, H2 in W.
       destruct (ann s) as [L _]. apply Pc in L. rewrite Ps in L.  rewrite L in W. rewrite (refS s) in W. discriminate W.
       destruct (ann w2) as [L R]. apply Pc in L. apply Pc in R. rewrite Ps in L, R.  rewrite L, R in W.
       rewrite (refS s) in W. discriminate W.
       destruct (ann w1) as [L R]. apply Pc in L. apply Pc in R. rewrite Ps in L, R.  rewrite L, R in W.
       rewrite (refS s) in W. discriminate W.
       auto. 
Qed.

Lemma bop_fpr_not_commutative_implies_witnesses_P_false {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_reflexive S eq ->
  brel_symmetric S eq ->
  brel_transitive S eq -> 
  pred_true S P s -> pred_congruence S eq P -> ((bop_is_id S eq bS s) + (bop_is_ann S eq bS s)) -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) -> 
  ((P w1 = false) * (P w2 = false)). 
Proof. intros refS symS tranS pS Pc [id | ann] W.
       apply (bop_fpr_not_commutative_and_id_implies_witnesses_P_false s w1 w2 P eq bS); auto.
       apply (bop_fpr_not_commutative_and_ann_implies_witnesses_P_false s w1 w2 P eq bS); auto.
Qed.        


(* Now, the othe direction ... *) 

Lemma bop_fpr_decompose_not_commutative {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  pred_true S P s -> pred_congruence S eq P ->
  pred_bop_decompose S P bS ->
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) ->   
  ((P w1 = false) * (P w2 = false)) ->
  bop_not_commutative S eq (bop_fpr s P bS). 
Proof. intros Ps Pc D W [H1 H2]; exists (w1, w2); compute.
       rewrite H1, H2. 
       case_eq(P (bS w1 w2)); intro H3; case_eq(P (bS w2 w1)); intro H4; auto.
          destruct (D _ _ H3) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2. 
          destruct (D _ _ H3) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2.
          destruct (D _ _ H4) as [F | F]. rewrite F in H2. discriminate H2. rewrite F in H1. discriminate H1.
          compute in W. rewrite H1, H2 in W. rewrite H3, H4 in W. exact W. 
Qed. 

(* a bit more general *)


Lemma bop_fpr_not_commutative {S : Type} (s w1 w2 : S ) (P : S -> bool) (eq: brel S) (bS : binary_op S) :
  brel_symmetric S eq -> 
  pred_true S P s -> pred_congruence S eq P ->
  pred_bop_weak_decompose S P bS ->
  bop_self_divisor S eq bS s -> 
  bop_not_commutative_witness S eq (bop_fpr s P bS) (w1, w2) ->   
  ((P w1 = false) * (P w2 = false)) ->
  bop_not_commutative S eq (bop_fpr s P bS). 
Proof. intros symS Ps Pc wD sd W [H1 H2]; exists (w1, w2); compute.
       rewrite H1, H2. compute in Ps. 
       case_eq(P (bS w1 w2)); intro H3; case_eq(P (bS w2 w1)); intro H4; auto.
          destruct (wD _ _ H3 H4) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2.
          case_eq(eq s (bS w2 w1)); intro J.
             apply symS in J.
             destruct (sd _ _ J) as [F | F].
             apply Pc in F. rewrite H2 in F. rewrite Ps in F. discriminate F.
             apply Pc in F. rewrite H1 in F. rewrite Ps in F. discriminate F.              
             reflexivity. 
          compute in W. rewrite H1, H2 in W. rewrite H3, H4 in W. exact W.
          compute in W. rewrite H1, H2 in W. rewrite H3, H4 in W. exact W.              
Qed. 

(* End non-commutative *) 

End PredicateReduce.







Section PredicateReduce2. 

Variable S : Type.
Variable P : S -> bool.

Variable eq : brel S. 
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.

Lemma uop_predicate_reduce_congruence (s : S) :
  pred_congruence S eq P -> uop_congruence S eq (uop_predicate_reduce s P). 
Proof. intros congP s1 s2; compute; intro H; compute; auto.
       case_eq(P s1); intro H1; case_eq(P s2); intro H2; auto.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.
       apply congP in H. rewrite H1 in H. rewrite H2 in H. discriminate H.        
Qed.

Lemma uop_predicate_reduce_idempotent : ∀ (s : S), uop_idempotent S eq (uop_predicate_reduce s P). 
Proof. intros s x; compute; auto.
       case_eq(P x); intro H; auto.
       case_eq(P s); intro H1; auto.
       rewrite H. apply refS. 
Qed.


Lemma bop_fpr_congruence (s : S) (bS : binary_op S) :
  pred_congruence S eq P ->
  bop_congruence S eq bS ->  
        bop_congruence S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P bS).       
Proof. intros congP congb.
       apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
Qed.


Lemma pred_bop_decompose_contrapositive (bS : binary_op S) : 
  pred_bop_decompose S P bS -> ∀ (a b : S), (P a = false) -> (P b = false) -> P (bS a b) = false.
Proof. intros D a b H1 H2.   
       case_eq(P (bS a b)); intro H3; auto. 
       destruct (D _ _ H3) as [H4 | H4].
       rewrite H4 in H1. discriminate.
       rewrite H4 in H2. discriminate.
Qed.

Lemma preduced_bop_compose_contrapositive (bS : binary_op S) : 
  pred_bop_compose S P bS -> ∀ (a b : S), P (bS a b) = false -> (P a = false) /\ (P b = false).
Proof. intros D a b H. split.
       case_eq(P a); intro K.
       assert (A : (P a = true) + (P b = true)).
       left. auto.
       assert (B := D a b A). rewrite H in B. discriminate.
       auto.
       case_eq(P b); 
       intro K. 
       assert (A : (P a = true) + (P b = true)).
       right. auto.
       assert (B := D a b A). rewrite H in B. discriminate.
       auto.
Qed.

Lemma preduced_bop_preserve_order_congrapositive (bS : binary_op S) : 
pred_preserve_order S P eq bS -> ∀ a b : S, eq (bS a b) a = true → P b = false → P a = false.
Proof. intros H a b M N.
    case_eq (P a); intro K.
    assert (A := H a b M K). rewrite N in A. discriminate. auto.
Qed.
       

Lemma preduced_bop_preserve_order_congrapositive_v2 (bS : binary_op S) : 
bop_selective S eq bS ->
bop_commutative S eq bS ->
pred_preserve_order S P eq bS -> ∀ a b : S, P b = true → P a = false -> eq (bS a b) a = true.
Proof. intros sel com H a b M N.
     assert (J:= sel a b). destruct J. auto.
     assert (cab := com a b). apply symS in cab.
     assert (cba := tranS _ _ _ cab e).
     assert (A := H _ _ cba M). rewrite A in N. discriminate. 
Qed.

(*

  Decompositional 

*) 

(* FIX 
Lemma bop_pseudo_associative_fpr_decompositional_id :
  ∀ (c : S) (bS : binary_op S),
    pred_true S P c ->
    preduced_equality_congruenceruence S eq P ->
    bop_congruence S eq bS ->     
    bop_associative S eq bS -> 
    preduced_bop_decompose S P bS ->
    bop_is_id S eq bS c -> 
       bop_pseudo_associative S eq (uop_predicate_reduce c P) bS. 
Proof. intros c bS Pc P_cong b_cong assoc H isId l1 l2 l3; compute; auto.
       destruct (isId c) as [Jc _].
       destruct (isId l1) as [L1 R1].
       destruct (isId l2) as [L2 R2].
       destruct (isId l3) as [L3 R3].
       assert (Pcc := P_cong _ _ Jc). rewrite Pc in Pcc.
       assert (PL1 := P_cong _ _ L1).
       assert (PR1 := P_cong _ _ R1).
       assert (PL2 := P_cong _ _ L2).
       assert (PR2 := P_cong _ _ R2).
       assert (PL3 := P_cong _ _ L3).
       assert (PR3 := P_cong _ _ R3).
       case_eq(P l1); intro H1; case_eq(P l2); intro H2; case_eq(P l3); intro H3;
         repeat (try rewrite Pcc;
                 try rewrite Pc;
                 try rewrite H1;
                 try rewrite H2;
                 try rewrite H3;                  
                 try auto). 
       rewrite H3 in PL3. rewrite PL3. 
       destruct (isId (bS c l3)) as [L4 R4].
       assert (PL4 := P_cong _ _ L4). rewrite PL3 in PL4. rewrite PL4. apply symS. exact L4.
       rewrite H2 in PL2. rewrite PL2. 
       destruct (isId (bS c l2)) as [L4 R4].       
       assert (PR4 := P_cong _ _ R4). rewrite PL2 in PR4. rewrite PR4. 
       rewrite H2 in PR2.  rewrite PR2. 
       destruct (isId (bS l2 c)) as [L5 R5].
       assert (PL5 := P_cong _ _ L5). rewrite PR2 in PL5. rewrite PL5. 
       apply assoc.
       rewrite H2 in PL2. rewrite PL2. 
       assert (H4 : P (bS l2 l3) = false). apply preduced_bop_decompose_contrapositive; auto. 
       rewrite H4.   
       assert (H5 : eq (bS (bS c l2) l3) (bS l2 l3) = true).
          destruct (isId l2) as [H6 _].
          assert (H7 := b_cong _ _ _ _ H6 (refS l3)).
          exact H7. 
       assert (H6 := P_cong _ _ H5).  rewrite H4 in H6. rewrite H6. 
       assert (H7 : eq (bS c (bS l2 l3)) (bS l2 l3) = true).
          destruct (isId (bS l2 l3)) as [H7 _].
          exact H7. 
       assert (H8 := P_cong _ _ H7).  rewrite H4 in H8. rewrite H8. 
       apply assoc.
       rewrite H1 in PR1. rewrite PR1. 
       assert (H5 : eq (bS (bS l1 c) c) l1 = true).
          destruct (isId l1) as [_ H4].
          destruct (isId (bS l1 c)) as [_ H5].
          assert (H6 := tranS _ _ _ H5 H4).
          exact H6.
       assert (H6 := P_cong _ _ H5). rewrite H1 in H6. rewrite H6. 
       apply isId.
       rewrite H1 in PR1. rewrite PR1. 
       rewrite H3 in PL3. rewrite PL3. 
       assert (H4 : P (bS l1 l3) = false). apply preduced_bop_decompose_contrapositive; auto. 
       assert (H5 : eq (bS (bS l1 c) l3) (bS l1 l3) = true).
          destruct (isId l1) as [_ H5].
          assert (H6 := b_cong _ _ _ _ H5 (refS l3)).
          exact H6. 
      assert (H6 : eq (bS l1 (bS c l3)) (bS l1 l3) = true).
          destruct (isId l3) as [H6 _].
          assert (H7 := b_cong _ _ _ _ (refS l1) H6).
          exact H7. 
       assert (H7 := P_cong _ _ H5). rewrite H4 in H7. 
       assert (H8 := P_cong _ _ H6). rewrite H4 in H8.
       rewrite H7, H8. 
       apply assoc.
       assert (H4 : P (bS l1 l2) = false). apply preduced_bop_decompose_contrapositive; auto. 
       rewrite H4. 
       assert (H5 : eq (bS (bS l1 l2) c) (bS l1 l2) = true).
          destruct (isId (bS l1 l2)) as [_ H5].
          exact H5. 
       assert (H6 := P_cong _ _ H5). rewrite H4 in H6.
       rewrite H6. 
       rewrite H2 in PR2. rewrite PR2. 
       assert (H7 : eq (bS l1 (bS l2 c)) (bS l1 l2) = true).
          destruct (isId l2) as [_ H7].
          assert (H8 := b_cong _ _ _ _ (refS l1) H7).
          exact H8. 
       assert (H8 := P_cong _ _ H7). rewrite H4 in H8.
       rewrite H8. 
       apply assoc.
       assert (H4 : P (bS l1 l2) = false). apply preduced_bop_decompose_contrapositive; auto. 
       assert (H5 : P (bS l2 l3) = false). apply preduced_bop_decompose_contrapositive; auto. 
       assert (H6 : P (bS (bS l1 l2) l3) = false). apply preduced_bop_decompose_contrapositive; auto. 
       assert (H7 : P (bS l1 (bS l2 l3)) = false). apply preduced_bop_decompose_contrapositive; auto. 
       repeat (
               try rewrite H4;
               try rewrite H5;
               try rewrite H6;
               try rewrite H7                             
             ). 
       apply assoc.        
Qed.
 

Lemma bop_pseudo_associative_fpr_decompositional_ann :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    preduced_equality_congruenceruence S eq P ->
    bop_associative S eq bS ->    
    preduced_bop_decompose S P bS ->
    bop_is_ann S eq bS s ->     
    bop_pseudo_associative S eq (uop_predicate_reduce s P) bS.
Proof. intros s bS P_true congP assoc D s_ann a b c.
       destruct (s_ann s) as [Lss Rss].
       destruct (s_ann a) as [Lsa Rsa].
       destruct (s_ann b) as [Lsb Rsb].
       destruct (s_ann c) as [Lsc Rsc].                     
       assert (Pss := congP _ _ Lss). rewrite P_true in Pss.
       assert (PLsa := congP _ _ Lsa). rewrite P_true in PLsa.
       assert (PLsb := congP _ _ Lsb). rewrite P_true in PLsb.
       assert (PLsc := congP _ _ Lsc). rewrite P_true in PLsc.
       assert (PRsa := congP _ _ Rsa). rewrite P_true in PRsa.
       assert (PRsb := congP _ _ Rsb). rewrite P_true in PRsb.
       assert (PRsc := congP _ _ Rsc). rewrite P_true in PRsc.       
       compute. 
       case_eq(P a); intro Pa; case_eq(P b); intro Pb; case_eq(P c); intro Pc;
         repeat (try rewrite Pss;
                 try rewrite PLsa;
                 try rewrite PLsb;
                 try rewrite PLsc;
                 try rewrite PRsa;
                 try rewrite PRsb;
                 try rewrite PRsc;                 
                 try rewrite P_true;
                 try rewrite Pa;
                 try rewrite Pb;
                 try rewrite Pc;                                                   
                 auto).
       assert (H1 : P (bS b c) = false). apply preduced_bop_decompose_contrapositive; auto.
       rewrite H1.
       destruct (s_ann (bS b c)) as [H2 H3].
       assert (H4 := congP _ _ H2). rewrite P_true in H4. rewrite H4. apply refS.

       assert (H1 : P (bS a b) = false). apply preduced_bop_decompose_contrapositive; auto.
       rewrite H1.
       destruct (s_ann (bS a b)) as [H2 H3].
       assert (H4 := congP _ _ H3). rewrite P_true in H4. rewrite H4. apply refS.

       assert (H1 : P (bS a b) = false). apply preduced_bop_decompose_contrapositive; auto.
       assert (H2 : P (bS b c) = false). apply preduced_bop_decompose_contrapositive; auto.
       rewrite H1. rewrite H2.
       assert (H3 : P (bS (bS a b) c) = false). apply preduced_bop_decompose_contrapositive; auto.
       assert (H4 : P (bS a (bS b c)) = false). apply preduced_bop_decompose_contrapositive; auto.              
       rewrite H3. rewrite H4.
       apply assoc. 
Qed. 

 *)

Lemma bop_associative_fpr_decompositional_id : 
  ∀ (c : S) (bS : binary_op S),
    pred_true S P c -> 
    pred_congruence S eq P -> 
    bop_congruence S eq bS ->     
    bop_associative S eq bS ->
    pred_bop_decompose S P bS ->
    bop_is_id S eq bS c -> 
        bop_associative S (brel_reduce eq (uop_predicate_reduce c P)) (bop_fpr c P bS). 
Admitted. 

Lemma bop_associative_fpr_decompositional_ann : 
  ∀ (c : S) (bS : binary_op S),
    pred_true S P c -> 
    pred_congruence S eq P -> 
    bop_congruence S eq bS ->     
    bop_associative S eq bS ->
    pred_bop_decompose S P bS ->
    bop_is_ann S eq bS c -> 
        bop_associative S (brel_reduce eq (uop_predicate_reduce c P)) (bop_fpr c P bS). 
Admitted. 

Lemma bop_left_uop_invariant_predicate_reduce_v2 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s ->
    pred_congruence S eq P -> 
    bop_selective S eq bS ->
    bop_is_id S eq bS s ->        
    pred_preserve_order S P eq bS ->
         bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS P_true P_cong selS is_id pres s1 s2; compute; auto.
       destruct (is_id s1) as [J1 J2].
       destruct (is_id s2) as [M1 K2].              
       case_eq(P s1); intro H1; auto. compute in pres.
       assert(K1 := P_cong _ _ M1). rewrite K1. 
       case_eq(P s2); intro H2; auto.
       destruct (selS s1 s2) as [H3 | H3]; apply P_cong in H3.
       rewrite H3. rewrite H1. apply refS. 
       rewrite H3. rewrite H2. apply refS.
       destruct (selS s1 s2) as [H3 | H3].
       assert (K := pres s1 s2 H3 H1). rewrite K in H2. discriminate H2.
       assert (K3 := P_cong _ _ H3). rewrite K3. rewrite H2.
       apply symS in H3.
       assert (K4 := tranS _ _ _ M1 H3). 
       exact K4. 
Qed. 

Lemma bop_right_uop_invariant_predicate_reduce_v2 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s ->
    pred_congruence S eq P -> 
    bop_selective S eq bS ->
    bop_commutative S eq bS ->
    bop_is_id S eq bS s ->        
    pred_preserve_order S P eq bS ->
    bop_right_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS P_true P_cong selS comS is_id pres s1 s2; compute; auto.
       destruct (is_id s1) as [J1 J2].
       destruct (is_id s2) as [M1 K2].              
       case_eq(P s2); intro H1; auto. compute in pres.
       assert(K1 := P_cong _ _ J2). rewrite K1. 
       case_eq(P s1); intro H2; auto.
       destruct (selS s1 s2) as [H3 | H3]; apply P_cong in H3.
       rewrite H3. rewrite H2. apply refS. 
       rewrite H3. rewrite H1. apply refS.
       destruct (selS s1 s2) as [H3 | H3].
       assert (K3 := P_cong _ _ H3). rewrite K3. rewrite H2.
       apply symS in H3.
       assert (K4 := tranS _ _ _ J2 H3). 
       exact K4. 
       assert (A := comS s2 s1).
       assert (B := tranS _ _ _  A H3).
       assert (C := pres s2 s1 B H1). rewrite C in H2. discriminate H2. 
Qed. 



Lemma conj1 :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_congruence S eq P ->
    bop_is_id S eq bS s -> 
  bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P)
  ->     pred_preserve_order S P eq bS.
Proof. intros s bS P_true P_cong is_id H s1 s2 H1 H2.
       assert (K := H s1 s2). compute in K. rewrite H2 in K.
       apply P_cong in H1. rewrite H1 in K. rewrite H2 in K.
       destruct (is_id s2) as [L R].
       assert (J := P_cong _ _ L). rewrite J in K. 
       case_eq(P s2); intro H3; auto.
       rewrite H3 in K.
       apply symS in K.
       assert (H4 := tranS _ _ _ K L).
       apply P_cong in H4.  rewrite P_true in H4.
       rewrite H3 in H4.
       discriminate H4.
Qed.        

(* *)

(*p

  Compositional 

*) 

Lemma bop_left_uop_invariant_predicate_reduce :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_bop_compose S P bS ->
         bop_left_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS B H s1 s2; compute; auto; case_eq(P s1); intro H1; auto. 
       assert (K := H s1 s2 (inl H1)). rewrite K; auto. 
       case_eq(P (bS s s2)); intro H2; auto.
       assert (J := H s s2 (inl B)). rewrite J in H2. discriminate H2. 
Qed. 

Lemma bop_right_uop_invariant_predicate_reduce :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s -> 
    pred_bop_compose S P bS ->    
       bop_right_uop_invariant S eq (bop_reduce (uop_predicate_reduce s P) bS) (uop_predicate_reduce s P).
Proof. intros s bS B H s1 s2; compute; auto; case_eq(P s2); intro H1; auto. 
       assert (K := H s1 s2 (inr H1)). rewrite K; auto. 
       case_eq(P (bS s1 s)); intro H2; auto.
       assert (J := H s1 s (inr B)). rewrite J in H2. discriminate H2.        
Qed.


Lemma bop_associative_fpr_compositional :
  ∀ (s : S) (bS : binary_op S),
    pred_true S P s    -> 
    pred_congruence S eq P ->     
    pred_bop_compose S P bS ->
    bop_congruence S eq bS ->         
    bop_associative S eq bS ->
    bop_associative S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P bS).      
Proof. intros s bS Ps P_cong H cong assoc.
       apply bop_full_reduce_left_right_invariant_implies_associative; auto.
       apply uop_predicate_reduce_congruence; auto.       
       apply uop_predicate_reduce_idempotent; auto.
       apply bop_left_uop_invariant_predicate_reduce; auto. 
       apply bop_right_uop_invariant_predicate_reduce; auto.
Qed.





(*  
    some sufficient conditions 
*) 


Lemma bop_fpr_selective (s : S) (bS : binary_op S) : 
(P s = true) ->
(∀ (a b : S), eq a b = true -> P a = P b) ->
(∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) -> 
bop_is_ann S eq bS s ->
bop_selective S eq bS ->  
bop_selective S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P bS).
Proof. intros X Y B is_ann H. compute. intros a b. compute in H.
      case_eq(P a); intro K;case_eq(P b); intro L;
      assert (M := is_ann s); destruct M as [M _].
      assert (Z := Y (bS s s) s M). rewrite X in Z. rewrite Z. rewrite X. auto.
      assert (Z := is_ann b); destruct Z as [Z _].
      assert (A := Y (bS s b) s Z). rewrite X in A. rewrite A. rewrite X. auto.
      assert (Z := is_ann a); destruct Z as [_ Z].
      assert (A := Y (bS a s) s Z). rewrite X in A. rewrite A. rewrite X. auto.
      assert (Z := B a b K L). rewrite Z. rewrite Z. auto.
Qed.

Lemma bop_fpr_selective_v2 (s : S) (bS : binary_op S) : 
(P s = true) ->
(∀ (a b : S), eq a b = true -> P a = P b) ->
(∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) -> 
bop_is_id S eq bS s ->
bop_selective S eq bS ->  
bop_selective S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P bS).
Proof. intros X Y B is_id H. compute. intros a b. compute in H.
      case_eq(P a); intro K;case_eq(P b); intro L;
      assert (M := is_id s); destruct M as [M _].
      assert (Z := Y (bS s s) s M). rewrite X in Z. rewrite Z. rewrite X. auto.
      assert (Z := is_id b); destruct Z as [Z _].
      assert (A := Y (bS s b) b Z). rewrite L in A. rewrite A,A. auto.
      assert (Z := is_id a); destruct Z as [_ Z].
      assert (A := Y (bS a s) a Z). rewrite K in A. rewrite A,A. auto.
      assert (Z := B a b K L). rewrite Z. rewrite Z. auto.
Qed.



 (* what about distributivity ? *) 

Lemma bop_fpr_id_true_true (s : S) (bS : binary_op S) :
  P(s) = true -> 
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_id S eq bS s ->       
  ∀ a b : S,  (P a = true) -> (P b = true) -> eq (bop_fpr s P bS a b) s = true.
Proof. intros P_true congP s_id a b Pa Pb. compute. rewrite Pa, Pb.
       destruct (s_id s) as [J _]. apply congP in J. rewrite P_true in J. rewrite J. 
       apply refS.
Qed.

Lemma bop_fpr_id_true_false (s : S) (bS : binary_op S) :
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_id S eq bS s ->       
  ∀ a b : S,  (P a = true) -> (P b = false) -> eq (bop_fpr s P bS a b) b = true.
Proof. intros congP s_id a b Pa Pb. compute. rewrite Pa, Pb.
       destruct (s_id b) as [J _]. apply congP in J. rewrite Pb in J. rewrite J. 
       apply s_id. 
Qed.

Lemma bop_fpr_id_false_true (s : S) (bS : binary_op S) :
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_id S eq bS s ->       
  ∀ a b : S,  (P a = false) -> (P b = true) -> eq (bop_fpr s P bS a b) a = true.
Proof. intros congP s_id a b Pa Pb. compute. rewrite Pa, Pb.
       destruct (s_id a) as [_ J]. apply congP in J. rewrite Pa in J. rewrite J. 
       apply s_id. 
Qed.

Lemma bop_fpr_false_false (s : S) (bS : binary_op S) :
  (∀ (a b : S), P a = false -> P b = false -> P (bS a b) = false) ->
       ∀ a b : S,  (P a = false) -> (P b = false) -> eq (bop_fpr s P bS a b) (bS a b) = true.
Proof. intros false_inv a b Pa Pb. compute. rewrite Pa, Pb.
       rewrite (false_inv a b Pa Pb). apply refS. 
Qed.

Lemma bop_fpr_ann_true (s : S) (bS : binary_op S) :
  P(s) = true -> 
  (∀ (a b : S), eq a b = true -> P a = P b) ->
  bop_is_ann S eq bS s ->       
  ∀ a b : S,  ((P a = true) + (P b = true)) -> eq (bop_fpr s P bS a b) s = true.
Proof. intros P_true congP s_ann a b [Pa | Pb]; compute.
       rewrite Pa.
       case_eq(P b); intro Pb. 
       destruct (s_ann s) as [J _]. apply congP in J. rewrite P_true in J. rewrite J. 
       apply refS.
       destruct (s_ann b) as [J _]. apply congP in J. rewrite P_true in J. rewrite J.
       apply refS.       
       rewrite Pb.
       case_eq(P a); intro Pa. 
       destruct (s_ann s) as [J _]. apply congP in J. rewrite P_true in J. rewrite J. 
       apply refS.
       destruct (s_ann a) as [_ J]. apply congP in J. rewrite P_true in J. rewrite J.
       apply refS.       
Qed.


Lemma bop_fpr_left_distributive :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul ->          
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_left_distributive S eq add mul ->
    bop_left_distributive S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd dmul cong_add cong_mul s_id s_ann ldist a b c.
       assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
          apply pred_bop_decompose_contrapositive; auto. 
       assert (mul_false : ∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false).
          apply pred_bop_decompose_contrapositive; auto.           
       compute.
       case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
       assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
       assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC.
       assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
       assert (PmulSASC := congP (mul s (add s c)) s mulSASCL). rewrite P_true in PmulSASC. rewrite PmulSASC.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB.
       assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
       assert (PmulSABS := congP (mul s (add b s)) s mulSABSL). rewrite P_true in PmulSABS. rewrite PmulSABS.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
       assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
       assert (PmulSABC := congP (mul s (add b c)) s mulSABCL). rewrite P_true in PmulSABC. rewrite PmulSABC.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       rewrite PaddSS. rewrite P_true.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
       assert (addSAC := s_id (mul a c)). destruct addSAC as [addSACL addSACR].
       assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite mulAC in PaddSAC. rewrite PaddSAC. (* rewrite PaddSAC *) 
       assert (PmulASC := mul_false a (add s c) L PaddSC). rewrite PmulASC. rewrite PmulASC.
       assert (mulASC := cong_mul a (add s c) a c (refS a) addSCL). rewrite P_true. rewrite PaddSAC. rewrite P_true. rewrite PaddSAC. rewrite P_true. 
       assert (K := tranS _ _ _ mulASC (symS _ _ addSACL)). exact K. 
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (PmulAB := mul_false a b L M). rewrite PmulAB. rewrite PmulAB.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (addSAB := s_id (mul a b)). destruct addSAB as [addSABL addSABR].
       assert (PaddSAB := congP (add (mul a b) s) (mul a b) addSABR). rewrite PmulAB in PaddSAB. rewrite PaddSAB. 
       assert (PmulSABC := mul_false a (add b s) L PaddBS). rewrite PmulSABC. rewrite PmulSABC.
       assert (mulASB := cong_mul a (add b s) a b (refS a) addBSR). rewrite P_true. rewrite PaddSAB. rewrite P_true. rewrite PaddSAB. rewrite P_true. 
       assert (K := tranS _ _ _ mulASB (symS _ _ addSABR)). exact K.
       assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
       assert (mulAB := mul_false a b L M). rewrite mulAB. rewrite mulAB.
       assert (mulAC := mul_false a c L N). rewrite mulAC. rewrite mulAC.
       assert (mulAABC := mul_false a (add b c) L addBC). rewrite mulAABC. rewrite mulAABC.
       assert (addMABMAC := add_false (mul a b) (mul a c) mulAB mulAC). rewrite addMABMAC. rewrite addMABMAC.
       assert (K := ldist a b c). exact K.
Qed.

Lemma selective_implies_preserve_pred (bS : binary_op S) : 
bop_selective S eq bS ->
pred_congruence S eq P ->
bop_preserve_pred S P bS.
Proof. intros sel congP a b.
     assert(A := sel a b). destruct A; intros Pa Pb.
     assert(B := congP _ _ e). rewrite Pa in B. auto.
     assert(B := congP _ _ e). rewrite Pb in B. auto.
Qed.


(*
  delete decompose of mul
  add preserve_order properties of add
  add selectivity of add
  add commutativity of add
*)
Lemma bop_fpr_left_distributive_v2 :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_preserve_order S P eq add ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_selective S eq add ->
     bop_commutative S eq add ->
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_left_distributive S eq add mul ->
       bop_left_distributive S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd padd cong_add cong_mul sel_add com_add s_id s_ann ldist a b c.
  assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
     apply pred_bop_decompose_contrapositive; auto.
     assert (app : bop_preserve_pred S P add).
     apply selective_implies_preserve_pred; auto. 
     assert (add_SelP : ∀ a b : S, P b = true → P a = false -> eq (add a b) a = true).
     apply preduced_bop_preserve_order_congrapositive_v2;auto.
     compute.
     case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
     assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
     assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
     assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
     assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
     rewrite PaddSS. rewrite P_true. auto.
     assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
     assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
     assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
     assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
     assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
     assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC.
     assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
     assert (PmulSASC := congP (mul s (add s c)) s mulSASCL). rewrite P_true in PmulSASC. rewrite PmulSASC.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
     assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
     assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
     assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB.
     assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
     assert (PmulSABS := congP (mul s (add b s)) s mulSABSL). rewrite P_true in PmulSABS. rewrite PmulSABS.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
     assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
     assert (PmulSABC := congP (mul s (add b c)) s mulSABCL). rewrite P_true in PmulSABC. rewrite PmulSABC.
     assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
     assert (PmulSB := congP (mul s b) s mulSBL). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
     assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
     assert (PmulSC := congP (mul s c) s mulSCL). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
     rewrite PaddSS. rewrite P_true. auto.
     rewrite PaddSS. rewrite P_true.
     assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
     assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
     rewrite PaddSS. rewrite P_true. auto.
     assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
     assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
     assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
     assert (PmulAS := congP (mul a s) s mulASR). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
     case_eq (P (mul a c)); intros K;
     rewrite P_true;
     apply symS in addSCL;
     assert (mulASC := cong_mul a c a (add s c) (refS a) addSCL);
     assert (PASC := congP (mul a c) (mul a (add s c)) mulASC); rewrite K in PASC; rewrite <- PASC.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PASC. rewrite K.
     assert (addSAC := s_id (mul a c)). destruct addSAC as [addSACL addSACR].
     assert (PaddSAC := congP (add s (mul a c)) (mul a c) addSACL). rewrite K in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
     assert (J := tranS _ _ _ addSACL mulASC). apply symS in J. rewrite P_true. rewrite P_true. rewrite PaddSAC. exact J.
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     case_eq (P (mul a b)); intros K;
     apply symS in addBSR;
     assert (mulABS := cong_mul a b a (add b s) (refS a) addBSR);
     assert (PABS := congP (mul a b) (mul a (add b s)) mulABS); rewrite K in PABS; rewrite <- PABS;
     assert (mulAS := s_ann a); destruct mulAS as [mulASL mulASR];
     assert (PAS := congP (mul a s) s mulASR); rewrite P_true in PAS; rewrite PAS. 
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PABS. rewrite K. rewrite P_true.
     assert (addABS := s_id (mul a b)). destruct addABS as [addABSL addABSR].
     assert (PaddABS := congP (add (mul a b) s) (mul a b) addABSR). rewrite K in PaddABS. rewrite PaddABS. rewrite P_true. rewrite P_true. rewrite PaddABS.
     rewrite P_true.
     assert (J := tranS _ _ _ addABSR mulABS). apply symS in J. exact J.
     assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
     assert (addABAC := ldist a b c).
     case_eq (P (mul a b)); intro J; case_eq (P (mul a c)); intro K.
     assert (PABAC := app _ _ J K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC.
     rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite P_true. rewrite P_true. rewrite K. rewrite P_true. rewrite P_true.
     assert (addACS := s_id (mul a c)). destruct addACS as [addACSL addACSR].
     assert (PSAC := congP _ _ addACSL). rewrite K in PSAC. rewrite PSAC. rewrite PSAC.
     assert (addACAB := add_SelP _ _ J K).
     assert (addPABAC := com_add (mul a b) (mul a c)).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (mulPABC := tranS _ _ _ mulABC addACAB).
     assert (PABC := congP _ _ mulPABC). rewrite K in PABC.
     rewrite PABC. rewrite PABC. apply symS in addACSL.
     exact (tranS _ _ _ mulPABC addACSL).
     rewrite J. rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true.
     assert (addABS := s_id (mul a b)). destruct addABS as [addABSL addABSR].
     assert (PSAB := congP _ _ addABSR). rewrite J in PSAB. rewrite PSAB. rewrite PSAB.
     assert (addPABAC := add_SelP _ _ K J).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (PABC := congP _ _ mulABC). rewrite J in PABC. rewrite PABC. rewrite PABC.
     apply symS in addABSR. exact (tranS _ _ _ mulABC addABSR).
     assert (PABAC := add_false _ _ J K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC. rewrite PABC.
     rewrite J. rewrite K. rewrite PABAC. rewrite PABAC. exact addABAC.
Qed.

Lemma bop_fpr_right_distributive_v2 :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_preserve_order S P eq add ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_selective S eq add ->
     bop_commutative S eq add ->
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
    bop_right_distributive S eq add mul ->
         bop_right_distributive S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd padd cong_add cong_mul sel_add com_add s_id s_ann rdist a b c.
  assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
     apply pred_bop_decompose_contrapositive; auto.
     assert (app : bop_preserve_pred S P add).
     apply selective_implies_preserve_pred; auto. 
     assert (add_SelP : ∀ a b : S, P b = true → P a = false -> eq (add a b) a = true).
     apply preduced_bop_preserve_order_congrapositive_v2;auto.
       compute;case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
       assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
       assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul c s) s mulSCR). rewrite P_true in PmulSC. rewrite PmulSC.
       assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
       assert (PmulSASC := congP (mul (add s c) s) s mulSASCR). rewrite P_true in PmulSASC. rewrite PmulSASC.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul b s) s mulSBR). rewrite P_true in PmulSB. rewrite PmulSB.
       assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
       assert (PmulSABS := congP (mul (add b s) s) s mulSABSR). rewrite P_true in PmulSABS. rewrite PmulSABS.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
       assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
       assert (PmulSABC := congP (mul (add b c) s) s mulSABCR). rewrite P_true in PmulSABC. rewrite PmulSABC.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul b s) s mulSBR). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul c s) s mulSCR). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       rewrite PaddSS. rewrite P_true.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
     case_eq (P (mul c a)); intros K;
     rewrite P_true;
     apply symS in addSCL;
     assert (mulASC := cong_mul c a (add s c) a  addSCL (refS a));
     assert (PASC := congP (mul c a) (mul (add s c) a) mulASC); rewrite K in PASC; rewrite <- PASC.
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PASC. rewrite K.
     assert (addSAC := s_id (mul c a)). destruct addSAC as [addSACL addSACR].
     assert (PaddSAC := congP (add s (mul c a)) (mul c a) addSACL). rewrite K in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
     assert (J := tranS _ _ _ addSACL mulASC). apply symS in J. rewrite P_true. rewrite P_true. rewrite PaddSAC. exact J.
     assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
     assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
     case_eq (P (mul b a)); intros K;
     apply symS in addBSR;
     assert (mulABS := cong_mul b a (add b s) a addBSR (refS a));
     assert (PABS := congP (mul b a) (mul (add b s) a) mulABS); rewrite K in PABS; rewrite <- PABS;
     assert (mulAS := s_ann a); destruct mulAS as [mulASL mulASR];
     assert (PAS := congP (mul s a) s mulASL); rewrite P_true in PAS; rewrite PAS. 
     rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite <- PABS. rewrite K. rewrite P_true.
     assert (addABS := s_id (mul b a)). destruct addABS as [addABSL addABSR].
     assert (PaddABS := congP (add (mul b a) s) (mul b a) addABSR). rewrite K in PaddABS. rewrite PaddABS. rewrite P_true. rewrite P_true. rewrite PaddABS.
     rewrite P_true.
     assert (J := tranS _ _ _ addABSR mulABS). apply symS in J. exact J.
     assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
     assert (addABAC := rdist a b c).
     case_eq (P (mul b a)); intro J; case_eq (P (mul c a)); intro K.
     assert (PABAC := app _ _ J  K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC.
     rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
     rewrite P_true. rewrite P_true. rewrite K. rewrite P_true. rewrite P_true.
     assert (addACS := s_id (mul c a)). destruct addACS as [addACSL addACSR].
     assert (PSAC := congP _ _ addACSL). rewrite K in PSAC. rewrite PSAC. rewrite PSAC.
     assert (addACAB := add_SelP _ _ J K).
     assert (addPABAC := com_add (mul b a) (mul c a)).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (mulPABC := tranS _ _ _ mulABC addACAB).
     assert (PABC := congP _ _ mulPABC). rewrite K in PABC.
     rewrite PABC. rewrite PABC. apply symS in addACSL.
     exact (tranS _ _ _ mulPABC addACSL).
     rewrite J. rewrite P_true. rewrite P_true. rewrite P_true. rewrite P_true.
     assert (addABS := s_id (mul b a)). destruct addABS as [addABSL addABSR].
     assert (PSAB := congP _ _ addABSR). rewrite J in PSAB. rewrite PSAB. rewrite PSAB.
     assert (addPABAC := add_SelP _ _ K J).
     assert (mulABC := tranS _ _ _ addABAC addPABAC).
     assert (PABC := congP _ _ mulABC). rewrite J in PABC. rewrite PABC. rewrite PABC.
     apply symS in addABSR. exact (tranS _ _ _ mulABC addABSR).
     assert (PABAC := add_false _ _ J K).
     assert (PABC := congP _ _ addABAC). rewrite PABAC in PABC. rewrite PABC. rewrite PABC.
     rewrite J. rewrite K. rewrite PABAC. rewrite PABAC. exact addABAC.
Qed.

Lemma bop_fpr_right_distributive :
  ∀ (s : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul ->          
    bop_congruence S eq add ->     
    bop_congruence S eq mul -> 
    bop_is_id S eq add s ->     
    bop_is_ann S eq mul s ->
    bop_right_distributive S eq add mul ->
         bop_right_distributive S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P add) (bop_fpr s P mul).
Proof. intros s add mul P_true congP dadd dmul cong_add cong_mul s_id s_ann rdist a b c.
       assert (add_false : ∀ (a b : S), P a = false -> P b = false -> P (add a b) = false).
          apply pred_bop_decompose_contrapositive; auto. 
       assert (mul_false : ∀ (a b : S), P a = false -> P b = false -> P (mul a b) = false).
       apply pred_bop_decompose_contrapositive; auto.
       compute in P_true.
       compute;case_eq (P a); intro L; case_eq (P b); intro M; case_eq (P c); intro N;
       assert (addSS := s_id s); destruct addSS as [addSSL addSSR];
       assert (PaddSS := congP (add s s) s addSSL);rewrite P_true in PaddSS. rewrite PaddSS. rewrite P_true.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul c s) s mulSCR). rewrite P_true in PmulSC. rewrite PmulSC.
       assert (mulSASC := s_ann (add s c)). destruct mulSASC as [mulSASCL mulSASCR].
       assert (PmulSASC := congP (mul (add s c) s) s mulSASCR). rewrite P_true in PmulSASC. rewrite PmulSASC.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (mulSS := s_ann s). destruct mulSS as [mulSSL mulSSR].
       assert (PmulSS := congP (mul s s) s mulSSL). rewrite P_true in PmulSS. rewrite PmulSS. rewrite P_true.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul b s) s mulSBR). rewrite P_true in PmulSB. rewrite PmulSB.
       assert (mulSABS := s_ann (add b s)). destruct mulSABS as [mulSABSL mulSABSR].
       assert (PmulSABS := congP (mul (add b s) s) s mulSABSR). rewrite P_true in PmulSABS. rewrite PmulSABS.
       rewrite P_true. rewrite PaddSS. rewrite P_true. auto.
       assert (PaddBC := add_false b c M N). rewrite PaddBC. rewrite PaddBC.
       assert (mulSABC := s_ann (add b c)). destruct mulSABC as [mulSABCL mulSABCR].
       assert (PmulSABC := congP (mul (add b c) s) s mulSABCR). rewrite P_true in PmulSABC. rewrite PmulSABC.
       assert (mulSB := s_ann b). destruct mulSB as [mulSBL mulSBR].
       assert (PmulSB := congP (mul b s) s mulSBR). rewrite P_true in PmulSB. rewrite PmulSB. rewrite P_true.
       assert (mulSC := s_ann c). destruct mulSC as [mulSCL mulSCR].
       assert (PmulSC := congP (mul c s) s mulSCR). rewrite P_true in PmulSC. rewrite PmulSC. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       rewrite PaddSS. rewrite P_true.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       rewrite PaddSS. rewrite P_true. auto.
       assert (addSC := s_id c). destruct addSC as [addSCL addSCR].
       assert (PaddSC := congP (add s c) c addSCL). rewrite N in PaddSC. rewrite PaddSC. rewrite PaddSC.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (mulAC := mul_false c a N L). rewrite mulAC. rewrite mulAC.
       assert (addSAC := s_id (mul c a)). destruct addSAC as [addSACL addSACR].
       assert (PaddSAC := congP (add s (mul c a)) (mul c a) addSACL). rewrite mulAC in PaddSAC. rewrite PaddSAC. rewrite PaddSAC.
       assert (PmulASC := mul_false (add s c) a PaddSC L ). rewrite PmulASC. rewrite PmulASC.
       assert (mulASC := cong_mul (add s c) a c a addSCL  (refS a)).
       assert (K := tranS _ _ _ mulASC (symS _ _ addSACL)). exact K.
       assert (addBS := s_id b). destruct addBS as [addBSL addBSR].
       assert (PaddBS := congP (add b s) b addBSR). rewrite M in PaddBS. rewrite PaddBS. rewrite PaddBS.
       assert (PmulAB := mul_false b a M L). rewrite PmulAB. rewrite PmulAB.
       assert (mulAS := s_ann a). destruct mulAS as [mulASL mulASR].
       assert (PmulAS := congP (mul s a) s mulASL). rewrite P_true in PmulAS. rewrite PmulAS. rewrite P_true.
       assert (addSAB := s_id (mul b a)). destruct addSAB as [addSABL addSABR].
       assert (PaddSAB := congP (add (mul b a) s) (mul b a) addSABR). rewrite PmulAB in PaddSAB. rewrite PaddSAB. rewrite PaddSAB.
       assert (PmulSABC := mul_false (add b s) a PaddBS L). rewrite PmulSABC. rewrite PmulSABC.
       assert (mulASB := cong_mul  (add b s) a b a addBSR  (refS a)).
       assert (K := tranS _ _ _ mulASB (symS _ _ addSABR)). exact K.
       assert (addBC := add_false b c M N). rewrite addBC. rewrite addBC.
       assert (mulAB := mul_false b a M L). rewrite mulAB. rewrite mulAB.
       assert (mulAC := mul_false c a N L). rewrite mulAC. rewrite mulAC.
       assert (mulAABC := mul_false (add b c) a addBC L). rewrite mulAABC. rewrite mulAABC.
       assert (addMABMAC := add_false (mul b a) (mul c a) mulAB mulAC). rewrite addMABMAC. rewrite addMABMAC.
       assert (K := rdist a b c). exact K.
Qed.



(* look at not left distributivity *)

Definition bop_not_left_distributive_witness (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) (a : S * S * S)
  := match a with (s,t,u) => r (mul s (add t u)) (add (mul s t) (mul s u)) = false end.


Lemma bop_fpr_not_left_distributive_implies_witnesses_P_false :
  ∀ (s w1 w2 w3 : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     bop_not_left_distributive_witness S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P add) (bop_fpr s P mul) ((w1, w2), w3) ->
     (P w1 = false) * (P w2 = false) * (P w3 = false). 
Proof. intros s w1 w2 w3 add mul P_true congP cong_add cong_mul s_id s_ann nLD.
       compute in nLD. compute in P_true.
       assert (PLmul : ∀ (x : S),  P(mul s x) = true). intro x. destruct (s_ann x) as [L _]. apply congP in L. rewrite P_true in L. exact L.
       assert (PRmul : ∀ (x : S),  P(mul x s) = true). intro x. destruct (s_ann x) as [_ R]. apply congP in R. rewrite P_true in R. exact R.        
       assert (PLadd : ∀ (x : S),  P(add s x) = P x). intro x. destruct (s_id x) as [L _]. apply congP in L. exact L.
       assert (PRadd : ∀ (x : S),  P(add x s) = P x). intro x. destruct (s_id x) as [_ R]. apply congP in R. exact R.        
       case_eq(P w1); intro H1; case_eq(P w2); intro H2; case_eq(P w3); intro H3;
         repeat (
             try rewrite H1 in nLD;
             try rewrite H2 in nLD;
             try rewrite H3 in nLD;
             try rewrite P_true in nLD;
             try rewrite PLmul in nLD;
             try rewrite PRmul in nLD;             
             try rewrite PLadd in nLD;
             try rewrite PRadd in nLD; auto                                                  
           ).
       rewrite (refS s) in nLD.  discriminate nLD. 
       rewrite (refS s) in nLD.  discriminate nLD. 
       rewrite (refS s) in nLD.  discriminate nLD. 
       rewrite (refS s) in nLD.  discriminate nLD.
       rewrite (refS s) in nLD.  discriminate nLD.

       assert (K : P (mul w1 (add s w3)) = P (mul w1 w3)).
         destruct (s_id w3) as [L _]. assert (J := cong_mul _ _ _ _ (refS w1) L). apply congP in J. exact J. 
       case_eq(P (mul w1 w3)); intro H4;
         repeat (
             try rewrite H1 in nLD;
             try rewrite H2 in nLD;
             try rewrite H3 in nLD;
             try rewrite H4 in nLD;
             try rewrite K in nLD;                          
             try rewrite P_true in nLD;
             try rewrite PLmul in nLD;
             try rewrite PRmul in nLD;             
             try rewrite PLadd in nLD;
             try rewrite PRadd in nLD; auto                                                  
           ).
       rewrite (refS s) in nLD.  discriminate nLD.       
       destruct (s_id (mul w1 w3)) as [L1 _].
       destruct (s_id w3) as [L2 _].
       assert (J := cong_mul _ _ _ _ (refS w1) L2).
       apply symS in L1.
       assert (T := tranS _ _ _ J L1).
       rewrite T in nLD. discriminate nLD.

       assert (K : P (mul w1 (add w2 s)) = P (mul w1 w2)).
         destruct (s_id w2) as [_ R]. assert (J := cong_mul _ _ _ _ (refS w1) R). apply congP in J. exact J.        
       case_eq(P (mul w1 w2)); intro H4;
         repeat (
             try rewrite H1 in nLD;
             try rewrite H2 in nLD;
             try rewrite H3 in nLD;
             try rewrite H4 in nLD;
             try rewrite K in nLD;                          
             try rewrite P_true in nLD;
             try rewrite PLmul in nLD;
             try rewrite PRmul in nLD;             
             try rewrite PLadd in nLD;
             try rewrite PRadd in nLD; auto                                                  
           ).
       rewrite (refS s) in nLD.  discriminate nLD.
       destruct (s_id (mul w1 w2)) as [_ R1].
       destruct (s_id w2) as [_ R2].
       assert (J := cong_mul _ _ _ _ (refS w1) R2).
       apply symS in R1.
       assert (T := tranS _ _ _ J R1).
       rewrite T in nLD. discriminate nLD.
Qed.


Lemma bop_fpr_not_left_distributive :
  ∀ (s w1 w2 w3 : S) (add mul : binary_op S),
     pred_true S P s -> 
     pred_congruence S eq P ->
     bop_congruence S eq add ->     
     bop_congruence S eq mul -> 
     bop_is_id S eq add s ->     
     bop_is_ann S eq mul s ->
     pred_bop_decompose S P add ->
     pred_bop_decompose S P mul -> 
     (P w1 = false) * (P w2 = false) * (P w3 = false) ->      
     bop_not_left_distributive_witness S eq add mul ((w1, w2), w3) ->
       bop_not_left_distributive_witness S (brel_reduce eq (uop_predicate_reduce s P)) (bop_fpr s P add) (bop_fpr s P mul) ((w1, w2), w3).
Proof. intros s w1 w2 w3 add mul P_true congP cong_add cong_mul s_id s_ann addD mulD [[H1 H2] H3] nLD. 
       assert (PLmul : ∀ (x : S),  P(mul s x) = true). intro x. destruct (s_ann x) as [L _]. apply congP in L. rewrite P_true in L. exact L.
       assert (PRmul : ∀ (x : S),  P(mul x s) = true). intro x. destruct (s_ann x) as [_ R]. apply congP in R. rewrite P_true in R. exact R.        
       assert (PLadd : ∀ (x : S),  P(add s x) = P x). intro x. destruct (s_id x) as [L _]. apply congP in L. exact L.
       assert (PRadd : ∀ (x : S),  P(add x s) = P x). intro x. destruct (s_id x) as [_ R]. apply congP in R. exact R.        
       compute.       
       case_eq(P (add w2 w3)); intro H4; case_eq(P (mul w1 w2)); intro H5; case_eq(P (mul w1 w3)); intro H6;
         repeat
           ( try rewrite P_true; 
             try rewrite H1;
             try rewrite H2;
             try rewrite H3;
             try rewrite H4;
             try rewrite H5;
             try rewrite H6;             
             try rewrite PLmul;
             try rewrite PRmul;
             try rewrite PLadd;
             try rewrite PRadd;                           
             auto
           ).  
       destruct (addD _ _ H4) as [F | F]. rewrite F in H2. discriminate H2. rewrite F in H3. discriminate H3. 
       (* 2 *)
       case_eq(eq s (add s (mul w1 w3))); intro H7.
          apply congP in H7. rewrite P_true in H7.
          assert (H8 := PLadd (mul w1 w3)). rewrite H6 in H8. rewrite H8 in H7. discriminate H7. 
          reflexivity.
       (* 3 *)          
       case_eq(eq s (add (mul w1 w2) s)); intro H7.
          apply congP in H7. rewrite P_true in H7.
          assert (H8 := PRadd (mul w1 w2)). rewrite H5 in H8. rewrite H8 in H7. discriminate H7. 
          reflexivity.
       case_eq(P (add (mul w1 w2) (mul w1 w3))); intro H7.
          rewrite P_true.
          destruct (addD _ _ H4) as [F | F]. rewrite F in H2. discriminate H2. rewrite F in H3. discriminate H3.       
          rewrite H7.
          case_eq(eq s (add (mul w1 w2) (mul w1 w3))); intro H8.
             apply congP in H8. rewrite P_true in H8. rewrite H7 in H8. discriminate H8.
             reflexivity.
       (* 5 *)              
       case_eq(P (mul w1 (add w2 w3))); intro H7.
          rewrite P_true.
          destruct (mulD _ _ H5) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2. 
          rewrite H7.
           case_eq(eq (mul w1 (add w2 w3)) s); intro H8. 
              apply congP in H8. rewrite P_true in H8. rewrite H7 in H8. discriminate H8.
              reflexivity.               
       (* 6 *)
       case_eq(P (mul w1 (add w2 w3))); intro H7.
           rewrite P_true.  
           assert (K : P(add s (mul w1 w3)) = P(mul w1 w3)). destruct (s_id (mul w1 w3)) as [L _]. apply congP in L. exact L. 
           rewrite H6 in K.
           case_eq(eq s (add s (mul w1 w3))); intro H8.
              apply congP in H8. rewrite P_true in H8. rewrite K in H8. discriminate H8.
              reflexivity.
          rewrite H7.
          destruct (mulD _ _ H5) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H2. discriminate H2.               
      (* 7 *)
      case_eq(P (mul w1 (add w2 w3))); intro H7.
         rewrite P_true.
         case_eq (eq s (add (mul w1 w2) s) ); intro H8.
            apply congP in H8. rewrite P_true in H8.
            destruct (s_id (mul w1 w2)) as [_ R].
            apply congP in R. rewrite H5 in R. rewrite R in H8. discriminate H8.
            reflexivity. 
         rewrite H7. 
         destruct (mulD _ _ H6) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H3. discriminate H3.               
       (* 8 *)
       case_eq(P (add w2 w3)); intro H7; case_eq(P (add (mul w1 w2) (mul w1 w3))); intro H8; case_eq(P (mul w1 (add w2 w3))); intro H9; 
         repeat
           ( try rewrite P_true; 
             try rewrite H1;
             try rewrite H2;
             try rewrite H3;
             try rewrite H4;
             try rewrite H5;
             try rewrite H6;
             try rewrite H7;
             try rewrite H8;
             try rewrite H9;                                       
             try rewrite PLmul;
             try rewrite PRmul;
             try rewrite PLadd;
             try rewrite PRadd; auto
           ).
       rewrite H7 in H4.  discriminate H4. 
       case_eq(eq (mul w1 (add w2 w3)) s); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H9 in H10. discriminate H10. 
          reflexivity. 
       case_eq(eq s (add (mul w1 w2) (mul w1 w3))); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H8 in H10. discriminate H10. 
          reflexivity. 
       destruct (mulD _ _ H9) as [F | F]. rewrite F in H1. discriminate H1. rewrite F in H4. discriminate H4.                      
       case_eq(eq (mul w1 (add w2 w3)) s); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H9 in H10. discriminate H10. 
          reflexivity.        
       case_eq(eq s (add (mul w1 w2) (mul w1 w3))); intro H10.
          apply congP in H10. rewrite P_true in H10. rewrite H8 in H10. discriminate H10. 
          reflexivity. 
Qed. 


End PredicateReduce2.

Section EqvReduction.

Lemma brel_reduce_uop_congruence : ∀ (S : Type) (eq : brel S)  (u : unary_op S) (f : unary_op S), 
      uop_uop_congruence S eq u f  → 
          uop_congruence S (brel_reduce eq u) f. 
Proof. intros S eq u f cong. 
       unfold uop_congruence.  
       unfold brel_reduce. 
       apply cong. 
Defined. 


Lemma brel_reduce_bop_congruence : ∀ (S : Type) (eq : brel S)  (u : unary_op S) (b : binary_op S), 
       bop_uop_congruence S eq u b  → 
          bop_congruence S (brel_reduce eq u) b. 
Proof. intros S eq u b cong. 
       unfold bop_congruence.  
       unfold brel_reduce. 
       apply cong. 
Defined. 

Lemma brel_reduce_bop_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b :binary_op S), 
   brel_reflexive S r    → 
   uop_congruence S r u  → 
   bop_idempotent S r b  → 
       bop_idempotent S (brel_reduce r u) b. 
Proof. intros S r u b refS cong_u idem_b. unfold brel_reduce, bop_idempotent. intro s. 
       assert (A := idem_b s). 
       assert (B := cong_u _ _ A). assumption. 
Defined. 


Lemma brel_reduce_bop_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b :binary_op S), 
   brel_reflexive S r    → 
   uop_congruence S r u  → 
   bop_commutative S r b  → 
       bop_commutative S (brel_reduce r u) b. 
Proof. intros S r u b refS cong_u comm_b. unfold brel_reduce, bop_commutative. intros s t. 
       assert (A := comm_b s t). 
       assert (B := cong_u _ _ A). assumption. 
Defined. 


Lemma brel_reduce_preserves_left_positive : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (u : unary_op S), 
   brel_transitive S eq →
   uop_congruence S eq u →
   uop_idempotent S eq u →
   uop_preserves_left_positive S (brel_reduce eq u) u. 
Proof. intros S eq lt u transS cong idem. unfold uop_preserves_left_positive. unfold brel_reduce. 
       unfold uop_congruence in cong. intros s t H. 
       assert (A := idem s). 
       assert (B := transS _ _ _ A H). assumption. 
Defined. 


Lemma brel_reduce_preserves_left_negative : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (u : unary_op S), 
   brel_symmetric S eq →
   brel_transitive S eq →
   uop_congruence S eq u →
   uop_idempotent S eq u →
   uop_preserves_left_negative S (brel_reduce eq u) u. 
Proof. intros S eq lt u symS transS cong idem. 
       unfold uop_preserves_left_negative. unfold brel_reduce. 
       unfold uop_congruence in cong. intros s t H. 
       assert (A := idem s). apply symS in A. 
       assert (B := brel_transititivity_implies_dual _ _ transS _ _ _ A H). assumption. 
Defined. 


(*
    u (u (s + t) + v) = u (s + u (t + v))

    u (u (s + t) + v) = u ((s + t) + v)      () 
                      = u (s + (t + v))      () 
                      = u (s + u(t + v))     () 
*) 
Lemma brel_reduce_uop_bop_associative : 
  ∀ (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S),
    brel_symmetric S eq →
    brel_transitive S eq →
    bop_associative S eq b →
    uop_congruence S eq u →
    uop_bop_left_invariant S eq u b →
    uop_bop_right_invariant S eq u b →
      uop_bop_associative S (brel_reduce eq u) u b. 
Proof. intros S eq u b symS transS assS cong_u Li Ri. 
       unfold brel_reduce, uop_bop_associative. intros s t v. 
       assert (A := assS s t v). 
       assert (B := Li (b s t) v). apply symS in B. 
       assert (C := Ri s (b t v)). 
       assert (D := cong_u _ _ A). 
       assert (T := transS _ _ _ B D). 
       assert (QED := transS _ _ _ T C). assumption. 
Defined. 

  
End EqvReduction. 



Section ReduceAnnihilators.

  Require Import CAS.coq.eqv.reduce.
  Require Import CAS.coq.eqv.product.
  Require Import CAS.coq.sg.product.
  Require Import CAS.coq.bs.product_product. 

  

  Variable S : Type.
  Variable T : Type.     
  Variable eqS : brel S.
  Variable eqT : brel T.
  Variable refS : brel_reflexive S eqS.
  Variable symS : brel_symmetric S eqS.
  Variable tranS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.      
  Variable refT : brel_reflexive T eqT.
  Variable symT : brel_symmetric T eqT.
  Variable tranT : brel_transitive T eqT.
  Variable eqT_cong : brel_congruence T eqT eqT.        
  Variable zeroS oneS: S.
  Variable zeroT oneT : T.

  Variable addS : binary_op S.
  Variable addT : binary_op T.
  Variable cong_addS : bop_congruence S eqS addS.
  Variable cong_addT : bop_congruence T eqT addT.
  Variable ass_addS : bop_associative S eqS addS.
  Variable ass_addT : bop_associative T eqT addT.
  

  Variable mulS : binary_op S.
  Variable mulT : binary_op T.
  Variable cong_mulS : bop_congruence S eqS mulS.
  Variable cong_mulT : bop_congruence T eqT mulT.
  Variable ass_mulS : bop_associative S eqS mulS.
  Variable ass_mulT : bop_associative T eqT mulT.

  Variable zeroS_is_add_id  : bop_is_id S eqS addS zeroS.
  Variable oneS_is_mul_id   : bop_is_id S eqS mulS oneS.
  Variable zeroS_is_mul_ann : bop_is_ann S eqS mulS zeroS.
  Variable oneS_is_add_ann  : bop_is_ann S eqS addS oneS.

  Variable zeroT_is_add_id  : bop_is_id T eqT addT zeroT.
  Variable oneT_is_mul_id   : bop_is_id T eqT mulT oneT.
  Variable zeroT_is_mul_ann : bop_is_ann T eqT mulT zeroT.
  Variable oneT_is_add_ann  : bop_is_ann T eqT addT oneT.

  Variable oneS_not_zeroS : eqS oneS zeroS = false.
  Variable oneT_not_zeroT : eqT oneT zeroT = false.   

  Variable zeroS_squ : bop_self_square S eqS addS zeroS. (* ∀ a b : S,  eqS (addS a b) zeroS = true -> (eqS a zeroS = true) * (eqS b zeroS = true).  *) 
  Variable zeroT_squ : bop_self_square T eqT addT zeroT. (* ∀ a b : T,  eqT (addT a b) zeroT = true -> (eqT a zeroT = true) * (eqT b zeroT = true).  *) 
  
  Variable zeroS_div : bop_self_divisor S eqS mulS zeroS. (* ∀ a b : S,  eqS (mulS a b) zeroS = true -> (eqS a zeroS = true) + (eqS b zeroS = true).  *) 
  Variable zeroT_div : bop_self_divisor T eqT mulT zeroT. (* ∀ a b : T,  eqT (mulT a b) zeroT = true -> (eqT a zeroT = true) + (eqT b zeroT = true).  *) 




  Definition P : (S *T) -> bool := λ p, match p with (s, t) => orb (eqS s zeroS) (eqT t zeroT) end.

  Definition uop_rap : unary_op (S * T) := uop_predicate_reduce (zeroS, zeroT) P.

  Lemma brel_reduce_rap_reflexive : brel_reflexive (S * T) (brel_reduce (brel_product eqS eqT) uop_rap ).
  Proof. apply brel_reduce_reflexive.
         apply brel_product_reflexive; auto.
  Qed.

  Lemma brel_reduce_rap_symmetric : brel_symmetric (S * T) (brel_reduce  (brel_product eqS eqT) uop_rap ).
  Proof. apply brel_reduce_symmetric.
         apply brel_product_symmetric; auto.
  Qed.

  Lemma brel_reduce_rap_transitive : brel_transitive (S * T) (brel_reduce (brel_product eqS eqT) uop_rap ).
  Proof. apply brel_reduce_transitive.
         apply brel_product_transitive; auto.
  Qed.

  Lemma brel_reduce_rap_congruence : brel_congruence (S * T) (brel_reduce (brel_product eqS eqT) uop_rap) (brel_reduce  (brel_product eqS eqT) uop_rap). 
  Proof. apply brel_reduce_congruence; auto. 
         apply brel_product_congruence; auto. 
  Qed. 


              
Lemma P_congruence : pred_congruence (S * T) (brel_product eqS eqT) P. 
Proof. intros [s1 t1] [s2 t2]; compute; intro H.
         case_eq(eqS s1 zeroS); intro J1; case_eq(eqS s2 zeroS); intro J2; auto.
         assert (J3 := brel_transitive_dual_v2 S eqS symS tranS s2 zeroS s1 J2 (symS _ _ J1)).
         case_eq(eqS s1 s2); intro J4. apply symS in J4. rewrite J4 in J3. discriminate J3. 
         rewrite J4 in H. discriminate H. 
         assert (J3 := brel_transitive_dual_v2 S eqS symS tranS _ _ _ J1 (symS _ _ J2)). 
         rewrite J3 in H. discriminate H. 
         case_eq(eqT t1 zeroT); intro J3; case_eq(eqT t2 zeroT); intro J4; auto. 
         assert (J5 := brel_transitive_dual_v2 T eqT symT tranT _ _ _ J4 (symT _ _ J3)).                 
         case_eq(eqS s1 s2); intro J6. rewrite J6 in H.  apply symT in H. rewrite J5 in H. discriminate H.
         rewrite J6 in H. discriminate H.
         case_eq(eqS s1 s2); intro J5. rewrite J5 in H.
         assert (K := tranT _ _ _ H J4). rewrite K in J3. discriminate J3. 
         rewrite J5 in H. discriminate H.                  
Qed.
  

Lemma uop_rap_congruence : 
  uop_congruence (S * T) (brel_product eqS eqT) (uop_predicate_reduce (zeroS, zeroT) P).
Proof. apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
Qed.
  
Lemma P_true : pred_true (S * T) P (zeroS, zeroT).
Proof. compute; auto. rewrite refS; auto. Qed.


Lemma P_add_decompose : pred_bop_decompose (S * T) P (bop_product addS addT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 zeroS); intro H1; case_eq(eqS s2 zeroS); intro H2; auto.  
       case_eq(eqS (addS s1 s2) zeroS); intro K1.
       destruct (zeroS_squ s1 s2 K1) as [L R]. 
       rewrite L in H1. discriminate H1.
       rewrite K1 in H. 
       case_eq(eqT t1 zeroT); intro H3; case_eq(eqT t2 zeroT); intro H4; auto.  
       destruct (zeroT_squ t1 t2 H) as [L  R]. 
       rewrite L in H3. discriminate H3. 
Qed.

Lemma P_mul_decompose : pred_bop_decompose (S * T) P (bop_product mulS mulT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 zeroS); intro H1; case_eq(eqS s2 zeroS); intro H2; auto.  
       case_eq(eqS (mulS s1 s2) zeroS); intro K1.
       destruct (zeroS_div s1 s2 K1) as [L | R]. 
         rewrite L in H1. discriminate H1.
         rewrite R in H2. discriminate H2.       
       rewrite K1 in H. 
       case_eq(eqT t1 zeroT); intro H3; case_eq(eqT t2 zeroT); intro H4; auto.  
       destruct (zeroT_div t1 t2 H) as [L | R]. 
          rewrite L in H3. discriminate H3.
          rewrite R in H4. discriminate H4.        
Qed.

(* important!! mul is always not decompose but compose!! *)
Lemma P_mul_compose : pred_bop_compose (S * T) P (bop_product mulS mulT).
Proof. intros [s1 t1] [s2 t2]; compute.
       intro H.
       case_eq(eqS s1 zeroS); intro H1; case_eq(eqS s2 zeroS); intro H2; auto.
       assert (A := cong_mulS s1 s2 zeroS zeroS H1 H2).
       assert (B := zeroS_is_mul_ann zeroS). destruct B as [B _].
       assert (C := tranS _ _ _ A B). rewrite C. auto.
       assert (A := cong_mulS s1 s2 zeroS s2 H1 (refS s2)).
       assert (B := zeroS_is_mul_ann s2). destruct B as [B _].
       assert (C := tranS _ _ _ A B). rewrite C. auto.
       assert (A := cong_mulS s1 s2 s1 zeroS (refS s1) H2).
       assert (B := zeroS_is_mul_ann s1). destruct B as [_ B].
       assert (C := tranS _ _ _ A B). rewrite C. auto.
       rewrite H2 in H. rewrite H1 in H.   
       case_eq(eqS (mulS s1 s2) zeroS); intro K. auto.
       destruct H as [H | H].
       assert (A := cong_mulT t1 t2 zeroT t2 H (refT t2)).
       assert (B := zeroT_is_mul_ann t2). destruct B as [B _].
       assert (C := tranT _ _ _ A B). rewrite C. auto.
       assert (A := cong_mulT t1 t2 t1 zeroT (refT t1) H).
       assert (B := zeroT_is_mul_ann t1). destruct B as [_ B].
       assert (C := tranT _ _ _ A B). rewrite C. auto.
Qed.

Definition bop_rap_add : binary_op (S * T) := bop_fpr (zeroS, zeroT) P (bop_product addS addT).
Definition bop_rap_lexicographic_add : brel S -> binary_op (S * T) := λ eqS, bop_fpr (zeroS, zeroT) P (bop_llex eqS addS addT).
Definition bop_rap_mul : binary_op (S * T) := bop_fpr (zeroS, zeroT) P (bop_product mulS mulT).

Lemma bop_rap_add_congruence : bop_congruence (S * T) (brel_reduce (brel_product eqS eqT) uop_rap) bop_rap_add.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence. 
       apply bop_product_congruence; auto. 
Qed.

Lemma bop_rap_mul_congruence : bop_congruence (S * T) (brel_reduce (brel_product eqS eqT) uop_rap) bop_rap_mul.
Proof. apply bop_full_reduce_congruence; auto.
       apply uop_predicate_reduce_congruence; auto.
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence. 
       apply bop_product_congruence; auto. 
Qed.

Lemma bop_rap_add_associative :  bop_associative (S * T) (brel_reduce  (brel_product eqS eqT) uop_rap) bop_rap_add.
Proof. apply bop_associative_fpr_decompositional_id; auto. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true. 
       unfold pred_congruence. apply P_congruence.
       apply bop_product_congruence; auto.
       apply bop_product_associative; auto.
       apply P_add_decompose.
       apply bop_product_is_id; auto. 
Qed.


Lemma bop_rap_mul_associative :  bop_associative (S * T) (brel_reduce  (brel_product eqS eqT) uop_rap) bop_rap_mul.
Proof. apply bop_associative_fpr_decompositional_ann; auto. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true. 
       unfold pred_congruence. apply P_congruence.
       apply bop_product_congruence; auto.
       apply bop_product_associative; auto.
       apply P_mul_decompose.
       apply bop_product_is_ann; auto. 
Qed.

Lemma bop_rap_mul_associative_compositional :  bop_associative (S * T) (brel_reduce  (brel_product eqS eqT) uop_rap) bop_rap_mul.
Proof. apply bop_associative_fpr_compositional; auto. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true. 
       unfold pred_congruence. apply P_congruence.
       apply P_mul_compose.
       apply bop_product_congruence; auto.
       apply bop_product_associative; auto.
Qed.



Lemma bop_rap_add_commutative :
  bop_commutative S eqS addS ->
  bop_commutative T eqT addT ->
     bop_commutative (S * T) (brel_reduce  (brel_product eqS eqT) uop_rap) bop_rap_add.
Proof. intros C1 C2. 
       apply bop_full_reduce_commutative; auto.
       apply uop_predicate_reduce_congruence; auto.       
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
       apply bop_product_commutative; auto.
Qed.


Lemma bop_rap_mul_commutative :
  bop_commutative S eqS mulS ->
  bop_commutative T eqT mulT ->
     bop_commutative (S * T) (brel_reduce  (brel_product eqS eqT) uop_rap) bop_rap_mul.
Proof. intros C1 C2. 
       apply bop_full_reduce_commutative; auto.
       apply uop_predicate_reduce_congruence; auto.       
       apply brel_product_reflexive; auto.
       unfold pred_congruence. apply P_congruence.
       apply bop_product_commutative; auto.
Qed.


Lemma uop_rap_add_preserves_id :
 uop_preserves_id (S * T) (brel_product eqS eqT) (bop_product addS addT) uop_rap. 
Proof. unfold uop_preserves_id.
       intros [idS idT]. intro H.
       assert (J1 : bop_is_id S eqS addS idS). apply (bop_product_is_id_left S T eqS eqT addS addT idS idT H); auto. 
       assert (J2 : bop_is_id T eqT addT idT). apply (bop_product_is_id_right S T eqS eqT addS addT idS idT H); auto.
       assert (J3 : eqS zeroS idS  = true). apply (bop_is_id_equal _ _ symS tranS addS zeroS idS zeroS_is_add_id J1). 
       assert (J4 : eqT zeroT idT = true).  apply (bop_is_id_equal  _ _ symT tranT addT zeroT idT zeroT_is_add_id J2). 
       assert (J5 : P (idS, idT) = true).
          compute. apply symS in J3. rewrite J3; auto.  
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce. 
       rewrite J5. rewrite J3. rewrite J4. compute; auto. 
Qed.

Lemma uop_rap_add_preserves_ann :
 uop_preserves_ann (S * T) (brel_product eqS eqT) (bop_product addS addT) uop_rap. 
Proof. unfold uop_preserves_ann.
       intros [annS annT]. intro H.
       assert (J1 : bop_is_ann S eqS addS annS). apply (bop_product_is_ann_left S T eqS eqT addS addT annS annT H); auto. 
       assert (J2 : bop_is_ann T eqT addT annT). apply (bop_product_is_ann_right S T eqS eqT addS addT annS annT H); auto. 
       assert (J3 : eqS oneS annS  = true).  apply (bop_is_ann_equal _ _ symS tranS addS oneS annS oneS_is_add_ann J1). 
       assert (J4 : eqT oneT annT = true). apply (bop_is_ann_equal _ _ symT tranT addT oneT annT oneT_is_add_ann J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (annS, annT) = false). 
          compute. apply symS in J3. 
          assert(J5 : eqS annS zeroS = false).
          exact (brel_transitive_dual_v3 _ eqS symS tranS _ _ _ J3 oneS_not_zeroS).
          rewrite J5. apply symT in J4.
          assert(J6 : eqT annT zeroT = false).
          exact (brel_transitive_dual_v3 _ eqT symT tranT _ _ _ J4 oneT_not_zeroT).
          rewrite J6. reflexivity. 
       rewrite J5. rewrite refS. rewrite refT. compute; auto. 
Qed. 

Lemma uop_rap_mul_preserves_ann :
 uop_preserves_ann (S * T) (brel_product eqS eqT) (bop_product mulS mulT) uop_rap. 
Proof. unfold uop_preserves_ann.
       intros [annS annT]. intro H.
       assert (J1 : bop_is_ann S eqS mulS annS). apply (bop_product_is_ann_left S T eqS eqT mulS mulT annS annT H); auto. 
       assert (J2 : bop_is_ann T eqT mulT annT). apply (bop_product_is_ann_right S T eqS eqT mulS mulT annS annT H); auto. 
       assert (J3 : eqS zeroS annS  = true).  apply (bop_is_ann_equal _ _ symS tranS mulS zeroS annS zeroS_is_mul_ann J1). 
       assert (J4 : eqT zeroT annT = true). apply (bop_is_ann_equal _ _ symT tranT mulT zeroT annT zeroT_is_mul_ann J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (annS, annT) = true).
          compute. apply symS in J3. rewrite J3; auto.  
       rewrite J5. rewrite J3. rewrite J4. compute; auto. 
Qed. 

Lemma uop_rap_mul_preserves_id :
 uop_preserves_id (S * T) (brel_product eqS eqT) (bop_product mulS mulT) uop_rap. 
Proof. unfold uop_preserves_id.
       intros [idS idT]. intro H.
       assert (J1 : bop_is_id S eqS mulS idS). apply (bop_product_is_id_left S T eqS eqT mulS mulT idS idT H); auto. 
       assert (J2 : bop_is_id T eqT mulT idT). apply (bop_product_is_id_right S T eqS eqT mulS mulT idS idT H); auto. 
       assert (J3 : eqS oneS idS  = true).  apply (bop_is_id_equal _ _ symS tranS mulS oneS idS oneS_is_mul_id J1). 
       assert (J4 : eqT oneT idT = true). apply (bop_is_id_equal _ _ symT tranT mulT oneT idT oneT_is_mul_id J2). 
       unfold brel_product. unfold uop_rap. unfold uop_predicate_reduce.        
       assert (J5 : P (idS, idT) = false). 
          compute. apply symS in J3. 
          assert(J5 : eqS idS zeroS = false). exact (brel_transitive_dual_v3 _ eqS symS tranS _ _ _ J3 oneS_not_zeroS).
          rewrite J5. apply symT in J4.
          assert(J6 : eqT idT zeroT = false).  exact (brel_transitive_dual_v3 _ eqT symT tranT _ _ _ J4 oneT_not_zeroT).
          rewrite J6. reflexivity. 
       rewrite J5. rewrite refS. rewrite refT. compute; auto. 
Qed. 

Lemma  bop_rap_add_is_id : bop_is_id (S * T)
                                     (brel_reduce (brel_product eqS eqT) uop_rap)
                                     bop_rap_add
                                     (zeroS, zeroT).
Proof.  apply bop_full_reduce_is_id; auto.
        apply uop_predicate_reduce_congruence; auto.        
        apply brel_product_reflexive; auto.
        apply P_congruence.        
        apply bop_product_congruence; auto.
        apply brel_product_reflexive; auto.        
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_idempotent; auto.
        apply brel_product_reflexive; auto.
        apply uop_rap_add_preserves_id; auto. 
        apply bop_product_is_id; auto. 
Qed.  

Lemma  bop_rap_add_is_ann : bop_is_ann (S * T)
                                     (brel_reduce  (brel_product eqS eqT) uop_rap)
                                     bop_rap_add
                                     (oneS, oneT).
Proof.  apply bop_full_reduce_is_ann; auto.
        apply uop_predicate_reduce_congruence; auto.        
        apply brel_product_reflexive; auto.
        apply P_congruence.
        apply bop_product_congruence; auto.
        apply brel_product_reflexive; auto.        
        apply brel_product_transitive; auto.
        apply uop_rap_add_preserves_ann; auto. 
        apply bop_product_is_ann; auto. 
Qed.  

Lemma  bop_rap_mul_is_ann : bop_is_ann (S * T)
                                     (brel_reduce  (brel_product eqS eqT) uop_rap)
                                     bop_rap_mul
                                     (zeroS, zeroT).
Proof.  apply bop_full_reduce_is_ann; auto.
        apply uop_predicate_reduce_congruence; auto.        
        apply brel_product_reflexive; auto.
        apply P_congruence.
        apply bop_product_congruence; auto.
        apply brel_product_reflexive; auto.        
        apply brel_product_transitive; auto.
        apply uop_rap_mul_preserves_ann; auto.
        apply bop_product_is_ann; auto. 
Qed.

Lemma  bop_rap_mul_is_id : bop_is_id (S * T)
                                     (brel_reduce  (brel_product eqS eqT) uop_rap)
                                     bop_rap_mul
                                     (oneS, oneT).
Proof.  apply bop_full_reduce_is_id; auto.
        apply uop_predicate_reduce_congruence; auto.        
        apply brel_product_reflexive; auto.
        apply P_congruence.
        apply bop_product_congruence; auto.
        apply brel_product_reflexive; auto.        
        apply brel_product_transitive; auto.
        apply uop_predicate_reduce_idempotent; auto.        
        apply brel_product_reflexive; auto.
        apply uop_rap_mul_preserves_id; auto.
        apply bop_product_is_id; auto. 
Qed.


Lemma bop_rap_add_mul_left_distributive :
  bop_left_distributive S eqS addS mulS ->
  bop_left_distributive T eqT addT mulT ->   
      bop_left_distributive (S * T) (brel_reduce (brel_product eqS eqT) uop_rap) bop_rap_add bop_rap_mul. 
Proof. intros ldistS ldistT.
       apply bop_fpr_left_distributive. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true.
       apply P_congruence.
       apply P_add_decompose.
       apply P_mul_decompose.        
       apply bop_product_congruence; auto.
       apply bop_product_congruence; auto.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto.        
       apply bop_product_left_distributive; auto.  
Qed.


Lemma bop_rap_add_mul_right_distributive :
  bop_right_distributive S eqS addS mulS ->
  bop_right_distributive T eqT addT mulT ->   
     bop_right_distributive (S * T) (brel_reduce (brel_product eqS eqT) uop_rap ) bop_rap_add bop_rap_mul.
Proof. intros rdistS rdistT.
       apply bop_fpr_right_distributive. 
       apply brel_product_reflexive; auto.
       apply brel_product_symmetric; auto.       
       apply brel_product_transitive; auto.
       apply P_true.
       apply P_congruence.
       apply P_add_decompose.
       apply P_mul_decompose.        
       apply bop_product_congruence; auto.
       apply bop_product_congruence; auto.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto.        
       apply bop_product_right_distributive; auto.  
Qed.


End ReduceAnnihilators.

(*
Check bop_rap_add_mul_right_distributive.

bop_rap_add_mul_right_distributive
     : ∀ (S T : Type) (eqS : brel S) (eqT : brel T),
       brel_reflexive S eqS
       → brel_symmetric S eqS
         → brel_transitive S eqS
           → brel_reflexive T eqT
             → brel_symmetric T eqT
               → brel_transitive T eqT
                 → ∀ (zeroS : S) (zeroT : T) (addS : binary_op S) (addT : binary_op T),
                   bop_congruence S eqS addS
                   → bop_congruence T eqT addT
                     → ∀ (mulS : binary_op S) (mulT : binary_op T),
                       bop_congruence S eqS mulS
                       → bop_congruence T eqT mulT
                         → bop_is_id S eqS addS zeroS
                           → bop_is_ann S eqS mulS zeroS
                             → bop_is_id T eqT addT zeroT
                               → bop_is_ann T eqT mulT zeroT
                                 → bop_self_square S eqS addS zeroS
                                   → bop_self_square T eqT addT zeroT
                                     → bop_self_divisor S eqS mulS zeroS
                                       → bop_self_divisor T eqT mulT zeroT
                                         → bop_right_distributive S eqS addS mulS
                                           → bop_right_distributive T eqT addT mulT
                                             → bop_right_distributive (S * T) (brel_reduce (brel_product eqS eqT) (uop_rap S T eqS eqT zeroS zeroT))
                                                 (bop_rap_add S T eqS eqT zeroS zeroT addS addT) (bop_rap_mul S T eqS eqT zeroS zeroT mulS mulT)
*)
  