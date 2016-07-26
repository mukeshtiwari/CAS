Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel.and_sym. 
Require Import CAS.theory.brel.reduce. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.
Require Import CAS.theory.uop.duplicate_elim. 
Require Import CAS.theory.bop.union. 

Require Import CAS.theory.uop.filter. 
Require Import CAS.theory.bprop.forall. 
Require Import CAS.theory.brel.is_minimal_in. 
Require Import CAS.theory.uop.minset. 
Require Import CAS.theory.brel.minset. 
Require Import CAS.theory.bop.reduction. 



(*

Definition bop_then_unary : ∀ (S : Type) (u : unary_op S) (b : binary_op S), binary_op S 
:= λ S u b x y,  u (b x y). 

Definition bop_minset_union : ∀ S : Type, brel S → brel S → binary_op (finite_set S) 
:= λ S eq lt,  bop_then_unary (finite_set S) (uop_minset S eq lt) (bop_union S eq).

Definition brel_reduce : ∀ S : Type, brel S → unary_op S → brel S
:= λ S r u x y,  r (u x) (u y). 

Definition brel_minset : ∀ S : Type, brel S → brel S → brel (finite_set S) 
:= λ S eq lt,  brel_reduce (finite_set S) (brel_set S eq) (uop_minset S eq lt). 

is_minimal_in S r lt s X 

in_set S r X s 

Definition uop_minset : ∀ S : Type, brel S → brel S → unary_op (finite_set S) 
:= λ S eq lt, uop_filter_from_brel2 S (is_minimal_in S eq lt).


*) 


Hypothesis tmp5 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : finite_set S),
   brel_subset S eq (uop_minset S eq lt (bop_union S eq (uop_minset S eq lt s) t))
                     (uop_minset S eq lt (bop_union S eq s t)) = true. 

Hypothesis tmp4 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S)  (s t : finite_set S),
   brel_reflexive S eq →
   brel_symmetric S eq →
   brel_transitive S eq →
   brel_congruence S eq lt →
    brel_subset S eq (uop_minset S eq lt (bop_union S eq s t))
                     (uop_minset S eq lt (bop_union S eq (uop_minset S eq lt s) t)) = true. 
(* 


Hypothesis zzzz :    

∀ (S : Type) (eq : brel S) (lt : brel S)  (a : S) (s t : finite_set S),
     is_minimal_in S eq lt a (bop_union S eq s t) = true  →
     in_set S eq s a = true  →
         in_set S eq (uop_minset S eq lt s) a = true. 


Proof. intros S eq lt s t refS symS transS cong. 
       apply brel_subset_intro; auto. 
       intros a J.  
       apply in_set_uop_minset_intro; auto.
       apply in_set_uop_minset_elim in J; auto.
       apply in_set_bop_union_intro; auto. destruct J as [JL JR].
       apply in_set_bop_union_elim in JR; auto.
       destruct JR as [JR | JR].
          left. apply (zzzz _ _ _ _ _ _ JL); auto. 
          right. assumption. 
       apply in_set_uop_minset_elim in J; auto. destruct J as [JL JR].
              
Defined. 
*) 


(*
    minset(A U B) = minset((minset A) U B)
*) 

(* DELETE *) 
Lemma bop_union_uop_minset_left_invariant : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt  →
      uop_bop_left_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. unfold uop_bop_left_invariant. 
       intros s t. apply brel_set_intro. split. 
          apply tmp4; auto. 
          apply tmp5. 
Defined. 

Lemma minset_union_uop_bop_left_reduction : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt  →
      uop_bop_left_reduction (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. unfold uop_bop_left_reduction. 
       intros s t. apply brel_set_intro. split. 
          apply tmp4; auto. 
          apply tmp5. 
Defined. 


(*
    minset(A U B) = minset(A U (minset B))
*) 
Lemma bop_union_uop_minset_right_invariant : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt →
       uop_bop_right_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. 
       apply bop_commutative_left_implies_right_invariant.
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_commutative; auto.
       apply uop_minset_brel_set_congruence; auto. 
       apply bop_union_uop_minset_left_invariant; auto.  
Defined. 


(* 
     ∀ s1 s2, min (s1 U s2) =set= min ((min s1) U (min s2)) 
*) 
Lemma uop_minset_bop_union_uop_bop_invariant : 
       ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt →
           uop_bop_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. 
       apply uop_bop_invariant_left_intro. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_commutative; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply bop_union_uop_minset_left_invariant; auto. 
Defined. 



(* 
   min s1 = min t1 -> min s2 = min t2 -> min (s1 U s2) = min (t1 U t2) 
*) 
Lemma bop_union_uop_minset_congruence : ∀ (S : Type) (eq : brel S) (lt : brel S), 
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt →
       bop_uop_congruence (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. 
       unfold bop_uop_congruence. intros s1 s2 t1 t2 H1 H2. 
       (* 
         A : min (s1 U s2) = min (min(s1) U min(s2))    
         B : min (t1 U t2) = min (min(t1) U min(t2)) 
         C : min(s1) U min(s2) = min(t1) U min(t2)               (U congruence) 
         D : min(min(s1) U min(s2)) = min(min(t1) U min(t2))     (minset congruence) 

             result then follows by transitivity. 

         T   : min (s1 U s2) = min(min(t1) U min(t2))            (from A, D)
         QED : min (s1 U s2) = min (t1 U t2)                     (from T, B)
       *) 
       assert (A := uop_minset_bop_union_uop_bop_invariant _ _ lt refS symS transS cong s1 s2). 
       assert (B := uop_minset_bop_union_uop_bop_invariant _ _ lt refS symS transS cong t1 t2). 
       assert (C := bop_union_congruence S eq refS symS transS _ _ _ _ H1 H2). 
       assert (D := uop_minset_brel_set_congruence S eq lt refS symS transS cong _ _ C). 
       assert (T := brel_set_transitive S eq refS symS transS _ _ _ A D). 
       apply (brel_set_symmetric S eq symS) in B. 
       assert (QED := brel_set_transitive S eq refS symS transS _ _ _ T B). assumption. 
Defined. 






Lemma bop_minset_union_congruence : ∀ (S : Type) (eq : brel S) (lt : brel S), 
   (brel_reflexive _ eq) → 
   (brel_symmetric _ eq) → 
   (brel_transitive _ eq) → 
   brel_congruence S eq lt → 
       bop_congruence (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. 
    intros S eq lt refS symS transS cong. unfold brel_minset. unfold bop_minset_union. 
    apply bop_reduction_congruence. 
    apply brel_set_transitive; auto. 
    apply brel_set_symmetric; auto. 
    apply uop_minset_brel_set_congruence; auto. 
    apply bop_union_congruence; auto. 
    apply uop_minset_idempotent;  auto. 
(*
   uop_bop_reduction (finite_set S) (brel_set S eq) 
     (uop_minset S eq lt) (bop_union S eq)

*) 
    apply uop_minset_bop_union_uop_bop_invariant; auto.    (* NB !!! *) 
Qed. 

(* a different proof *) 
Lemma bop_minset_union_congruence_v2 : ∀ (S : Type) (eq : brel S) (lt : brel S), 
   (brel_reflexive _ eq) → 
   (brel_symmetric _ eq) → 
   (brel_transitive _ eq) → 
   brel_congruence S eq lt → 
       bop_congruence (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. 
    intros S eq lt refS symS transS cong. unfold bop_congruence.  intros s1 s2 t1 t2 H1 H2. 
    unfold bop_minset_union. 
    apply bop_then_unary_congruence; auto. 
       apply uop_minset_congruence; auto. 
       unfold brel_minset. 
       apply brel_reduce_bop_congruence. 
       apply bop_union_uop_minset_congruence; auto. 
Defined. 



Lemma uop_minset_bop_union_uop_associative : 
  ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_reflexive S eq →
    brel_symmetric S eq →
    brel_transitive S eq →
    brel_congruence S eq lt →
      uop_bop_associative (finite_set S) (brel_minset S eq lt) 
        (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. unfold brel_minset. 
       apply brel_reduce_uop_bop_associative. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_associative; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply bop_union_uop_minset_left_invariant; auto. 
       apply bop_union_uop_minset_right_invariant; auto. 
Defined. 

Lemma bop_minset_union_idempotent : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
   (brel_reflexive _ eq) → 
   (brel_symmetric _ eq) → 
   (brel_transitive _ eq) → 
   brel_congruence S eq lt → 
      bop_idempotent (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong. 
       unfold brel_minset, bop_minset_union. 
       apply bop_reduction_idempotent. 
       apply brel_set_transitive; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply uop_minset_idempotent; auto. 
       apply bop_union_idempotent; auto. 
Defined. 

Lemma bop_minset_union_associative : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
   (brel_reflexive S eq) → 
   (brel_symmetric S eq) → 
   (brel_transitive S eq) → 
   brel_congruence S eq lt → 
      bop_associative (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong.
       unfold brel_minset, bop_minset_union. 
       apply bop_reduction_associative. 
       apply brel_set_transitive; auto. 
       apply brel_set_symmetric; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply bop_union_associative; auto. 
       apply uop_minset_idempotent; auto. 
       apply minset_union_uop_bop_left_reduction; auto. 
       apply bop_union_uop_minset_right_invariant; auto. (* CHANGE NAME *) 
Defined. 



Lemma bop_minset_union_commutative : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
   (brel_reflexive S eq) → 
   (brel_symmetric S eq) → 
   (brel_transitive S eq) → 
   brel_congruence S eq lt → 
      bop_commutative (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong. 
       unfold brel_minset, bop_minset_union. 
       apply bop_reduction_commutative. 
       apply brel_set_transitive; auto. 
       apply brel_set_symmetric; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply uop_minset_idempotent; auto. 
       apply bop_union_commutative; auto. 
Defined. 


Lemma brel_subset_false_intro : ∀ (S : Type) (r : brel S), 
     brel_reflexive S r ->
     brel_symmetric S r -> 
     brel_transitive S r -> 
        ∀ (x w : finite_set S), 
          { a:S & (in_set S r x a = true)  * (in_set S r w a = false)} -> 
               brel_subset S r x w = false. 
Proof. intros S r refS symS transS. induction x; intros w [s [P1 P2]]. 
       compute in P1. discriminate. 
       unfold brel_subset. fold brel_subset. 
       unfold in_set in P1. fold in_set in P1. 
       apply orb_is_true_left in P1. destruct P1 as [P1 | P1].
       assert (fact1 := in_set_bProp_congruence S r symS transS w _ _ P1). 
       rewrite P2 in fact1. 
       rewrite <- fact1. simpl. reflexivity. 
       assert (fact1 : brel_subset S r x w = false). 
          apply IHx. exists s; auto. 
       rewrite fact1. apply andb_comm. 
Defined. 

Lemma brel_set_false_intro : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     ((brel_subset S eq X Y = false) + (brel_subset S eq Y X = false))  → brel_set S eq X Y = false. 
Proof. unfold brel_set. unfold brel_and_sym. intros S eq X Y [H | H]. 
       rewrite H. simpl. reflexivity. 
       rewrite H. apply andb_comm. 
Defined. 


Hypothesis in_set_minset_intro : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
   is_minimal_in S eq lt a X = true -> in_set S eq (uop_minset S eq lt X) a = true. 

Hypothesis in_set_minset_false_intro : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
   is_minimal_in S eq lt a X = false -> in_set S eq (uop_minset S eq lt X) a = false. 

Hypothesis in_set_minset_false_intro_v2 : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
   in_set S eq X a = false -> in_set S eq (uop_minset S eq lt X) a = false. 

Hypothesis is_minimal_in_implies_in_set : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
  is_minimal_in S eq lt a X = true -> in_set S eq X a = true. 


Lemma brel_minset_false_intro : ∀ (S : Type) (eq lt : brel S) (X Y : finite_set S), 
      brel_reflexive S eq -> 
      brel_symmetric S eq -> 
      brel_transitive S eq -> 
      brel_congruence S eq lt -> 
      ({a : S & (in_set S eq X a = true) * (is_minimal_in S eq lt a X = true) * 
           ((is_minimal_in S eq lt a Y = false) + (in_set S eq Y a = false))} 
       + 
       {a : S & (in_set S eq Y a = true) * (is_minimal_in S eq lt a Y = true) * 
           ((is_minimal_in S eq lt a X = false) + (in_set S eq X a = false))}) -> 
            brel_minset S eq lt X Y = false. 
Proof. intros S eq lt X Y refS symS transS lt_cong D. 
       unfold brel_minset, brel_reduce. 
       apply brel_set_false_intro. 
       destruct D as [ [a [[P1 P2] [P3 | P4] ]] | [a [[P1 P2] [P3 | P4]]] ]. 
          left. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro; auto. 

          left. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro_v2; auto. 
 
          right. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro; auto. 


          right. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro_v2; auto. 
Qed. 




Lemma support_lemma_1 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
    brel_symmetric S eq     → 
    brel_asymmetric S lt    → 
    brel_irreflexive S lt   → 
    brel_strict S eq lt     → 
    lt s t = true           →  (* NB !!! *) 
        is_minimal_in S eq lt s (bop_minset_union S eq lt (t :: nil) (s :: nil)) = true. 
Proof. intros S eq lt s t symS asym irr str P. 
       unfold bop_minset_union, bop_then_unary, bop_union, bop_concat. 
       unfold bop_then_unary, app, uop_duplicate_elim, in_set.  
       rewrite (brel_symmetric_implies_dual _ _ symS _ _ (str s t P)). simpl. 
       unfold uop_minset, uop_filter_from_brel2, uop_filter, filter. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl. 
       rewrite (irr t), P. simpl. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl.   
       rewrite (irr s), (asym _ _ P). compute. 
       rewrite (irr s). reflexivity. 
Defined. 



Lemma support_lemma_2 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
    brel_symmetric S eq     → 
    brel_asymmetric S lt    → 
    brel_irreflexive S lt   → 
    brel_strict S eq lt     → 
    lt s t = true           →  (* NB !!! *) 
        is_minimal_in S eq lt s (bop_minset_union S eq lt (s :: nil) (t :: nil)) = true. 
Proof. intros S eq lt s t symS asym irr str P. 
       unfold bop_minset_union, bop_then_unary, bop_union, bop_concat. 
       unfold bop_then_unary, app, uop_duplicate_elim, in_set.  
       rewrite (str s t P). simpl. 
       unfold uop_minset, uop_filter_from_brel2, uop_filter, filter. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl. 
       rewrite irr, (asym _ _ P).  simpl. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl.   
       rewrite (irr t), P. compute. 
       rewrite (irr s). reflexivity. 
Defined. 


Lemma bop_minset_union_not_is_left : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_reflexive S eq → 
    brel_symmetric S eq  → 
    brel_transitive S eq → 
    brel_congruence S eq lt → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
    ({ s1 : S & { s2 : S & lt s1 s2 = true}}) →  (* NB !!! *) 
      bop_not_is_left (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong_lt asym irr str [s [t P]]. 
       exists (t :: nil, s :: nil). 
       apply brel_minset_false_intro; auto. left. exists s. 
       assert (fact1 : is_minimal_in S eq lt s (bop_minset_union S eq lt (t :: nil) (s :: nil)) 
                       = true). 
          apply support_lemma_1; auto. 
       split. split.
          apply (is_minimal_in_implies_in_set S eq lt); auto. 
          assumption. 
          right. compute. rewrite (str s t P). reflexivity. 
Defined. 


Lemma bop_minset_union_not_is_right : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_reflexive S eq → 
    brel_symmetric S eq  → 
    brel_transitive S eq → 
    brel_congruence S eq lt → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
    ({ s1 : S & { s2 : S & lt s1 s2 = true}}) →  (* NB !!! *) 
      bop_not_is_right (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong_lt asym irr str [s [t P]]. 
       exists (s :: nil, t :: nil). 
       apply brel_minset_false_intro; auto. left. exists s. 
       assert (fact1 : is_minimal_in S eq lt s (bop_minset_union S eq lt (s :: nil) (t :: nil)) 
                       = true). 
          apply support_lemma_2; auto. 
       split. split.
          apply (is_minimal_in_implies_in_set S eq lt); auto. 
          assumption. 
          right. compute. rewrite (str s t P). reflexivity. 
Defined. 



Definition brel_strict_total (S : Type) (eq r : brel S) := 
    ∀ s t : S, eq s t = false -> (r s t = true) + (r t s = true). 

Definition brel_not_strict_total (S : Type) (eq r : brel S) := 
    {s : S & { t : S & (eq s t = false) * (r s t = false) * (r t s = false)}}. 


Hypothesis bop_minset_total  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt   → 
    brel_strict_total S eq lt → 
     ∀ (X : finite_set S), 
       (brel_minset S eq lt nil X = true) + 
       { s : S & brel_minset S eq lt (s::nil) X = true}. 
(* 
Proof. intros S eq lt symS asym irr str tot X Y. 
       unfold bop_selective. intros s t. 
Defined. 
*) 

Hypothesis bop_minset_union_nil_left : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S), 
   brel_minset S eq lt nil X = true -> 
     brel_minset S eq lt (bop_minset_union S eq lt X Y) Y = true. 

(*
assert (minset_ref   := brel_minset_reflexive S eq lt refS symS transS). 
assert (minset_sym   := brel_minset_symmetric S eq lt symS). 
assert (minset_trans := brel_minset_transitive S eq lt refS symS transS). 
assert (minset_union_cong := bop_minset_union_congruence S eq lt refS symS transS cong_lt). 

   assert (fact1 := minset_union_cong _ _ _ _ nilX nilY). 
   assert (fact2 : brel_minset S eq lt nil (bop_minset_union S eq lt nil nil) = true). 
      compute. reflexivity. 
   assert (fact3 := minset_trans _ _ _ fact2 fact1).  
   apply minset_sym in fact3. 
   assert (fact4 := minset_trans _ _ _ fact3 nilX).  
   assumption. 
*) 

Hypothesis bop_minset_union_nil_right : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S), 
   brel_minset S eq lt nil X = true -> 
     brel_minset S eq lt (bop_minset_union S eq lt Y X) Y = true. 


Lemma bop_minset_union_selective  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
brel_reflexive S eq
          → brel_symmetric S eq
            → brel_transitive S eq
              → brel_congruence S eq lt → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
    brel_strict_total S eq lt → 
      bop_selective (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. 
intros S eq lt refS symS transS cong_lt asym irr str tot X Y. unfold bop_selective. 
assert (factX := bop_minset_total S eq lt asym irr str tot X). 
assert (factY := bop_minset_total S eq lt asym irr str tot Y). 
destruct factX as [nilX | [x pX]]; destruct factY as [nilY | [y pY]]. 
left. apply bop_minset_union_nil_right; auto. 
right. apply bop_minset_union_nil_left; auto. 
left. apply bop_minset_union_nil_right; auto. 
case_eq(eq x y); intro E. 
   admit. 
   destruct (tot _ _ E) as [H | H]. 
      left. admit. 
      right. admit. 
Defined. 


(* want A, B such that 

min(min A U min B) <> min A
min(min A U min B) <> min B

s < t < v 

A = {s, v} 

min {s} = {s} 
min {t} = {t} 

*) 
Hypothesis aux_lemma1  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
      lt s t = false -> lt t s = false -> 
         bop_minset_union S eq lt (s :: nil) (t :: nil) = s :: t :: nil. 
(* n
Proof. intros S eq lt s t L R. 
       unfold bop_minset_union. 
       unfold bop_then_unary. 
       unfold bop_union, bop_concat. unfold bop_then_unary. 
Defined.
*) 

Hypothesis aux_lemma2  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
      lt s t = false -> lt t s = false -> 
         brel_minset S eq lt (s :: t :: nil) (s :: nil) = false. 

Hypothesis aux_lemma3  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
      lt s t = false -> lt t s = false -> 
         brel_minset S eq lt (s :: t :: nil) (t :: nil) = false. 


Lemma bop_minset_union_not_selective  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_symmetric S eq  → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
   (brel_not_total S lt) → 
      bop_not_selective (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt symS asym irr str [ [s t] [L R]]. 
       unfold bop_not_selective. 
       exists (s :: nil, t :: nil).
       rewrite aux_lemma1; auto. 
       rewrite aux_lemma2; auto. 
       rewrite aux_lemma3; auto. 
Defined. 

(* 

id ann

*) 


(* 

Definition ltr_set_scalar_product : ∀ S : Type, binary_op S → left_transform S (finite_set S) 
:= λ S b x Y, List.map (λ y, b x y) Y. 

Definition ltr_set_map : ∀ S : Type, binary_op S → left_transform (finite_set S) (finite_set (finite_set S))
:= λ S b x Y, List.map (λ y, b x y) Y. 

Definition bop_set_product : ∀ S T : Type, binary_op S → binary_op (finite_set S) 
:= λ S b X Y, 
   List.map (λ x, List.map (λ y, b x y) Y) X. 

*) 

























