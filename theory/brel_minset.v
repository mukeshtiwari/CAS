Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_reduce.
Require Import CAS.theory.brel_set.
Require Import CAS.theory.brel_subset.
Require Import CAS.theory.brel2_in_set. 
Require Import CAS.theory.brel2_is_minimal_in. 


(* 
Definition brel_and_sym : ∀ (S : Type), brel S -> brel S 
:= λ S r x y,  (r x y) && (r y x). 

Definition in_set : ∀ S : Type,  ∀ r : brel S, brel2 (finite_set S) S
:= fix f S r l s := 
   match l with 
   | nil => false 
   | a :: rest => r s a || f S r rest s
   end. 

Definition brel_subset : ∀ S : Type,  ∀ r : brel S, brel (finite_set S)
:= fix f S r set1 set2 := 
   match set1 with 
   | nil => true 
   | a :: rest => (in_set S r set2 a) && (f S r rest set2)
   end. 

Definition brel_set : ∀ S : Type, brel S → brel(finite_set S) 
:= λ S r,  brel_and_sym (list S) (brel_subset S r). 


Definition bProp_forall: ∀ S : Type, bProp S → bProp(finite_set S) := List.forallb. 

Definition brel2_from_brel : ∀ S : Type, (brel S) → brel2 S (finite_set S)
:= λ S r x, (bProp_forall S (r x)).


Definition is_minimal_in : ∀ S : Type, brel S → brel S → brel2 S (finite_set S)
:= λ S eq lt a X, if brel_set S eq nil X
                  then false 
                  else brel2_from_brel S (λ x, λ y, negb (lt y x)) a X. 

lt SEEMS WRONG !!! 


Fixpoint filter {A : Type} (f : A -> bool) (l:list A) : list A :=
      match l with
	| nil => nil
	| x :: l => if f x then x::(filter f l) else filter f l
      end.

Definition uop_filter : ∀ S : Type, (bProp S) → unary_op (finite_set S) := λ S, @filter S. 

Definition uop_filter_from_brel2 : ∀ S : Type, (brel2 S (finite_set S)) → unary_op (finite_set S)
:= λ S r X, uop_filter S (λ a, r a X) X.

Definition uop_minset : ∀ S : Type, brel S → brel S → unary_op (finite_set S) 
:= λ S eq lt, uop_filter_from_brel2 S (is_minimal_in S eq lt).

Definition brel_reduce : ∀ S : Type, brel S → unary_op S → brel S
:= λ S r u x y,  r (u x) (u y). 

Definition brel_minset : ∀ S : Type, brel S → brel S → brel (finite_set S) 
:= λ S eq lt,  brel_reduce (finite_set S) (brel_set S eq) (uop_minset S eq lt). 

   
   X = Y === brel_set (uop_minset S eq lt X) (uop_minset S eq lt Y)
         === brel_set (uop_filter_from_brel2 S (is_minimal_in S eq lt) X) 
                      (uop_filter_from_brel2 S (is_minimal_in S eq lt) Y)
         === brel_set (filter (λ a, is_minimal_in S eq lt a X) X) 
                      (filter (λ a, is_minimal_in S eq lt a Y) Y) 
         === brel_set (filter (λ a, if brel_set S eq nil X then false else brel2_from_brel S (λ x, λ y, negb (lt y x)) a X) X) 
                      (filter (λ a, if brel_set S eq nil Y then false else brel2_from_brel S (λ x, λ y, negb (lt y x)) a Y) Y) 
         === brel_set (filter (λ a, if brel_set S eq nil X then false else  bProp_forall S (λ y, negb (lt y a)) X) X) 
                      (filter (λ a, if brel_set S eq nil Y then false else  bProp_forall S (λ y, negb (lt y a)) Y) Y) 
         === brel_set (filter (λ a, if brel_set S eq nil X then false else  forallb S (λ y, negb (lt y a)) X) X) 
                      (filter (λ a, if brel_set S eq nil Y then false else  forallb S (λ y, negb (lt y a)) Y) Y) 
                  

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


(*
*) 


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




(* 
brel_negate = 
λ (S : Type) (r : brel S),

    {f : S → S & ∀ s : S, (r s (f s) = false) * (r (f s) s = false)}
     
: ∀ S : Type, brel S → Type




Lemma brel_minset_negate : ∀ (S : Type) (r lt : brel S), 
   brel_nontrivial S r -> 
   brel_irreflexive S lt -> 
     brel_negate (finite_set S) (brel_minset S r lt). 
Proof. intros S r lt [ [s Ps] [f Pf] ] irr. 
       exists (minset_negate S s f). 


intro x. 
split. 
unfold brel_minset. 
unfold brel_reduce. 

   brel_set S r 
     (uop_minset S r lt x)
     (uop_minset S r lt (minset_negate S s f x)) = false

       intro x. case x. 
       unfold minset_negate. 
       split. 
          unfold brel_minset. 
          unfold brel_reduce. 
          unfold uop_minset at 1.       
          unfold uop_filter_from_brel2. 
          unfold uop_filter. 
          unfold filter. 

          unfold uop_minset. 
          unfold uop_filter_from_brel2. 
          unfold uop_filter. 
          unfold filter. 
          assert (fact1 : is_minimal_in S r lt s (s :: nil) = true). admit. 
          rewrite fact1. compute. 
          reflexivity. 
          admit. 
      intros w l. 
      unfold minset_negate. 
      split. 
          unfold brel_minset. 
          unfold brel_reduce. 
          unfold uop_minset.       
          unfold uop_filter_from_brel2. 
          unfold uop_filter. 
          unfold filter. 
          assert (fact1 : is_minimal_in S r lt w (w :: nil) = true). admit.                
          rewrite fact1. 
        
Defined. 

Lemma uop_minset_nontrivial : ∀ (S : Type) (eq : brel S)  (lt : brel S), 
   brel_nontrivial S eq -> 
   brel_irreflexive S lt -> 
   uop_nontrivial (finite_set S) (brel_set S eq) (uop_minset S eq lt). 
Proof. 

*) 


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
