Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 

Open Scope list_scope. 

Definition uop_duplicate_elim : ∀ S : Type, brel S -> unary_op (finite_set S) 
:= λ S r,  fix f x := 
      match x with
         | nil => nil
         | a :: y => 
            if in_set S r y a 
              then f y
              else a :: (f y)
      end.

(* copied here from Coq.Lists.List.v    
   so that extraction does not construct a 
   List module (which conflicts with Ocaml's 
*) 
Fixpoint filter {A : Type} (f : A -> bool) (l:list A) : list A :=
      match l with
	| nil => nil
	| x :: l => if f x then x::(filter f l) else filter f l
      end.

Definition uop_filter : ∀ S : Type, (bProp S) → unary_op (finite_set S) := λ S, @filter S. 

Definition uop_filter_from_brel2 : ∀ S : Type, (brel2 S (finite_set S)) → unary_op (finite_set S)
:= λ S r X, uop_filter S (λ a, r a X) X.


Definition uop_minset :  ∀ S : Type, brel S -> brel S -> unary_op (finite_set S) 
:= λ S rS lte, uop_filter_from_brel2 S (λ a X, dominates_set S rS lte X a).

