Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.code.bprop. 
Require Import CAS.code.combined. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.reduce.
Require Import CAS.theory.brel.set.



(* 
*) 

Lemma brel_minset_reflexive : ∀ (S : Type) (r : brel S) (lt : brel S), 
       brel_reflexive S r  →  
       brel_symmetric S r → 
       brel_transitive S r → 
         brel_reflexive (finite_set S) (brel_minset S r lt). 
Proof. intros S r lt refS symS transS s. unfold brel_minset. 
       apply brel_reduce_reflexive. 
       apply brel_set_reflexive; auto. 
Defined. 

Lemma brel_minset_symmetric : ∀ (S : Type) (r : brel S)  (lt : brel S), 
              (brel_symmetric S r) → brel_symmetric (finite_set S) (brel_minset S r lt). 
Proof. intros S r u symS. 
       unfold brel_minset. 
       apply brel_reduce_symmetric. 
       apply brel_set_symmetric.  assumption. 
Defined. 

Lemma brel_minset_transitive : ∀ (S : Type) (r : brel S)  (lt : brel S), 
        (brel_reflexive _ r) → (brel_symmetric _ r) → (brel_transitive _ r) → 
           brel_transitive (finite_set S) (brel_minset S r lt). 
Proof. intros S r lt refS symS transS. 
       unfold brel_minset. 
       apply brel_reduce_transitive. 
       apply brel_set_transitive; auto. 
Defined.          


Lemma brel_minset_congruence : 
  ∀ (S : Type) (r lt : brel S), 
      brel_congruence S r r -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_congruence (finite_set S) (brel_minset S r lt) (brel_minset S r lt). 
Proof. intros S r lt congS  refS symS transS. unfold brel_minset. 
       apply brel_reduce_congruence. 
       apply brel_set_congruence; auto. 
Qed. 


Lemma brel_minset_witness : ∀ (S : Type) (r lt : brel S), 
              brel_reflexive S r -> 
              brel_symmetric S r -> 
              brel_transitive S r -> 
              brel_witness S r -> 
              brel_witness (finite_set S) (brel_minset S r lt). 
Proof. intros S r lt refS symS transS wtS. unfold brel_minset. 
       apply brel_reduce_witness. 
       apply brel_set_reflexive; auto. 
       apply brel_set_witness. 
Defined. 


Definition minset_negate (S : Type) (s : S) (f : S -> S) ( x : finite_set S) :=
   match x with 
   | nil => s :: nil 
   | t :: _ => (f t) :: nil 
  end. 

(* FIX THESE 

Lemma brel_minset_intro : ∀ (S : Type) (eq lt : brel S) (X Y : finite_set S), 
      brel_reflexive S eq -> 
      brel_symmetric S eq -> 
      brel_transitive S eq -> 
      brel_congruence S eq lt -> 
      (∀ a : S, in_set S eq X a = true -> is_minimal_in S eq lt a X = true -> 
           (is_minimal_in S eq lt a Y = true) * (in_set S eq Y a = true)) * 
      (∀ a : S, in_set S eq Y a = true -> is_minimal_in S eq lt a Y = true -> 
           (is_minimal_in S eq lt a X = true) * (in_set S eq X a = true)) -> 
            brel_minset S eq lt X Y = true. 
Proof. intros S eq lt X Y refS symS transS lt_cong [L R]. 
       unfold brel_minset, brel_reduce. 
       apply brel_set_intro. split. 
       
       apply brel_subset_intro; auto. 
       unfold uop_minset, uop_filter_from_brel2. intros a H. 
       apply in_set_uop_filter_intro. 
         unfold bProp_congruence. intros s t J. 
         apply is_minimal_in_left_congruence; auto. 
       apply in_set_uop_filter_elim in H. 
       destruct H as [HL HR]. 
       apply L; auto.
         unfold bProp_congruence. intros s t J. 
         apply is_minimal_in_left_congruence; auto. 

       apply brel_subset_intro; auto. 
       unfold uop_minset,  uop_filter_from_brel2. intros a H. 
       apply in_set_uop_filter_intro. 
         unfold bProp_congruence. intros s t J. 
         apply is_minimal_in_left_congruence; auto. 
       apply in_set_uop_filter_elim in H. 
       destruct H as [HL HR]. 
       apply R; auto. 
         unfold bProp_congruence. intros s t J. 
         apply is_minimal_in_left_congruence; auto. 
Qed. 


Lemma brel_minset_elim : ∀ (S : Type) (eq lt : brel S) (X Y : finite_set S), 
      brel_reflexive S eq -> 
      brel_symmetric S eq -> 
      brel_transitive S eq -> 
      brel_congruence S eq lt -> 
      brel_minset S eq lt X Y = true -> 
      (∀ a : S, in_set S eq X a = true -> is_minimal_in S eq lt a X = true -> 
           (is_minimal_in S eq lt a Y = true) * (in_set S eq Y a = true)) * 
      (∀ a : S, in_set S eq Y a = true -> is_minimal_in S eq lt a Y = true -> 
           (is_minimal_in S eq lt a X = true) * (in_set S eq X a = true)). 
Proof. intros S eq lt X Y refS symS transS lt_cong H. 
       unfold brel_minset, brel_reduce in H. 
       apply brel_set_elim in H. destruct H as [ L R ]. 
       assert (fact_L := brel_subset_elim S eq symS transS _ _ L); auto. 
       assert (fact_R := brel_subset_elim S eq symS transS _ _ R); auto. 
       split. 
       intros a H J. 
       assert (fact1 : in_set S eq (uop_minset S eq lt X) a = true). 
          apply in_set_uop_minset_intro; auto. 
       assert (fact2 := fact_L a fact1).        
       apply in_set_uop_minset_elim in fact2; auto. 
       intros a H J. 
       assert (fact1 : in_set S eq (uop_minset S eq lt Y) a = true). 
          apply in_set_uop_minset_intro; auto. 
       assert (fact2 := fact_R a fact1).        
       apply in_set_uop_minset_elim in fact2; auto. 
Qed. 

*) 
