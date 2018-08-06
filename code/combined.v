Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.code.bprop. 


(*

(a, b) llex (c, d) = (a + c, test(=, a,  c, b + d, test(<, a, c, b, d)))

*) 
Definition bop_llex : ∀ {S T : Type}, brel S → binary_op S → binary_op T → binary_op (S * T) 
:= λ {S T} eq b1 b2 x y,  
   match x, y with
    | (a, b), (c, d) => 
        (b1 a c, 
         if eq a c 
         then (b2 b d)
         else if brel_llt eq b1 a c 
              then b 
              else d)
   end.


(* Sets 

Currently implemented as lists

*) 

Definition is_empty : ∀ {S : Type}, bProp (finite_set S) 
:= λ {S} X,  match X with nil => true | _ => false end. 

Definition singleton : ∀ {S : Type}, S → finite_set S 
:= λ {S} s, s :: nil. 

Definition ltr_insert : ∀ {S : Type}, brel S → left_transform S (finite_set S) 
:= λ {S} r s X,  if in_set r X s then X else (s :: X). 

Definition ltr_delete : ∀ {S : Type}, brel S → left_transform S (finite_set S) 
:= λ {S} r s X,  if in_set r X s then (uop_filter (λ x, negb (r x s)) X) else X. 

(* 
Definition bop_union : ∀ {S : Type}, brel S → binary_op (finite_set S) 
:= λ {S} r,  bop_then_unary (uop_duplicate_elim r) (bop_concat (@S)).

Definition bop_intersect : ∀ {S : Type}, brel S → binary_op (finite_set S) 
:= λ {S} r X,  uop_filter (in_set r X). 
*)  


Definition is_minimal_in : ∀ {S : Type}, brel S → brel S → brel2 S (finite_set S)
:= λ {S} eq lte a X, 
      if brel_set eq nil X
      then false 
      else (bProp_forall S (λ y, bop_or (uop_not (lte y a)) (eq y a))) X. 

Definition uop_minset : ∀ {S : Type}, brel S → brel S → unary_op (finite_set S) 
:= λ {S} eq lte X, uop_filter (λ a, is_minimal_in eq lte a X) X. 

Definition brel_minset : ∀ {S : Type}, brel S → brel S → brel (finite_set S) 
:= λ {S} eq lt,  brel_reduce (brel_set eq) (uop_minset eq lt). 


Definition bop_lift : ∀ {S : Type}, brel S → binary_op S → binary_op(finite_set S) := 
    λ {S} eq bS X Y, uop_duplicate_elim eq (bop_list_product_left bS X Y). 

Definition bop_union : ∀ {S : Type}, brel S → binary_op (finite_set S) 
:= λ {S} r,  bop_then_unary (uop_duplicate_elim r) (@bop_concat S).

Definition bop_intersect : ∀ {S : Type}, brel S → binary_op (finite_set S) 
:= λ {S} eq X,  uop_filter (in_set eq X). 
