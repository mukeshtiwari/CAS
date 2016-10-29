Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 

Open Scope list_scope. 

Definition uop_not : unary_op bool := λ b, if b then false else true.  

Definition uop_id : ∀ (S : Type), (unary_op S) := λ S s, s.  


Definition uop_with_constant : ∀ S : Type, unary_op S → unary_op (with_constant S)
:= λ S g x ,  
      match x with
         | (inl _) => x 
         | (inr s) => inr _ (g s) 
      end.

Definition uop_list_map : ∀ S : Type, unary_op S → unary_op (list S) 
:= λ S f,  
  fix map (l : list S) : list S :=
  match l with
  | nil => nil
  | a :: t => f a :: map t
  end. 

Definition uop_product : ∀ S T : Type, unary_op S → unary_op T → unary_op (S * T) 
:= λ S T f g p,  
   match p with
    | (s, t) => (f s, g t) 
   end.

Definition uop_sum : ∀ S T : Type, unary_op S → unary_op T → unary_op (S + T)
:= λ S T f g x ,  
      match x with
         | (inl s) => inl _ (f s)
         | (inr t) => inr _ (g t) 
      end.

Definition uop_duplicate_elim : ∀ S : Type, brel S -> unary_op (finite_set S) 
:= λ S r,  fix f x := 
      match x with
         | nil => nil
         | a :: y => 
            if in_set S r y a 
              then f y
              else a :: (f y)
      end.

(* yes, cheating for now ... *) 
Definition uop_set_map : ∀ S : Type, unary_op S → unary_op (finite_set S) 
:= λ S f X,  uop_list_map S f X. 

Definition uop_set_rep : ∀ S : Type, brel S -> unary_op S → unary_op (finite_set S) 
:= λ S eq f X,  uop_duplicate_elim S eq (uop_set_map S f X). 

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

(*
Definition uop_minset :  ∀ S : Type, brel S -> brel S -> unary_op (finite_set S) 
:= λ S rS lte, uop_filter_from_brel2 S (λ a X, dominates_set S rS lte X a).
*) 
