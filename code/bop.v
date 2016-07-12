Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 

Open Scope list_scope.


(* BASE *) 

Definition bop_and    : binary_op bool := andb. 
Definition bop_or     : binary_op bool := orb. 
Definition bop_plus   : binary_op nat := plus.
Definition bop_times  : binary_op nat := mult.
Definition bop_min    : binary_op nat := min.
Definition bop_max    : binary_op nat := max.
Definition bop_left   : ∀ S : Type, binary_op S := λ S l r,  l.
Definition bop_right  : ∀ S : Type, binary_op S := λ S l r,  r. 
Definition bop_concat : ∀ S : Type, binary_op (list S) := λ S x y,  x ++ y. 


(* Combinators *) 

Definition bop_then_unary : ∀ (S : Type) (u : unary_op S) (b : binary_op S), binary_op S 
:= λ S u b x y,  u (b x y). 

(*
Definition bop_reduce : ∀ (S : Type) (u : unary_op S) (b : binary_op S), binary_op S 
:= λ S u b x y,  u (b (u x) (u y)). 
*) 

Definition bop_product : ∀ S T : Type, binary_op S → binary_op T → binary_op (S * T) 
:= λ S T U V x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (U x1 y1, V x2 y2) 
   end.

Definition bop_left_sum : ∀ S T : Type, binary_op S → binary_op T → binary_op (S + T)
:= λ S T opS opT x y,  
      match x, y with
         | (inl a), (inl b) => inl _ (opS a b)
         | (inl _), (inr _) => x
         | (inr _), (inl _) => y
         | (inr a), (inr b) => inr _ (opT a b)
      end.

Definition bop_right_sum : ∀ S T : Type, binary_op S → binary_op T → binary_op (S + T)
:= λ S T opS opT x y,  
      match x, y with
         | (inl a), (inl b) => inl _ (opS a b)
         | (inl _), (inr _) => y
         | (inr _), (inl _) => x
         | (inr a), (inr b) => inr _ (opT a b)
      end.


Definition bop_add_id : ∀ S : Type, binary_op S → cas_constant → binary_op (cas_constant + S)
:= λ  S bS c x y, 
   match x, y with
   | (inl _), (inl _) => y 
   | (inl _), (inr _) => y
   | (inr _), (inl _) => x
   | (inr a), (inr b) => inr _ (bS a b)
   end.

Definition bop_add_ann : ∀ S : Type, binary_op S → cas_constant → binary_op (cas_constant + S)
:= λ  S bS c x y, 
   match x, y with
   | (inl _), (inl _) => x
   | (inl _), (inr _) => x
   | (inr _), (inl _) => y
   | (inr a), (inr b) => inr _ (bS a b)
   end.

(* define lex products with this? *) 
Definition bop_test : ∀ S : Type, brel S → S → S → binary_op S  
:= λ S r x y z w ,  if (r x y) then z else w. 

(*

(a, b) llex (c, d) = (a + c, test(=, a,  c, b + d, test(<, a, c, b, d)))

*) 
Definition bop_llex : ∀ S T : Type, brel S → binary_op S → binary_op T → binary_op (S * T) 
:= λ S T eq b1 b2 x y,  
   match x, y with
    | (a, b), (c, d) => 
        (b1 a c, 
         if eq a c 
         then (b2 b d)
         else if brel_llt _ eq b1 a c 
              then b 
              else d)
   end.


(* Sets 

Currently implemented as lists

*) 

Definition is_empty : ∀ S : Type, bProp (finite_set S) 
:= λ S X,  match X with nil => true | _ => false end. 

Definition singleton : ∀ S : Type, S → finite_set S 
:= λ S s, s :: nil. 

Definition ltr_insert : ∀ S : Type, brel S → left_transform S (finite_set S) 
:= λ S r s X,  if in_set S r X s then X else (s :: X). 

Definition ltr_delete : ∀ S : Type, brel S → left_transform S (finite_set S) 
:= λ S r s X,  if in_set S r X s then (uop_filter S (λ x, negb (r x s)) X) else X. 

Definition bop_union : ∀ S : Type, brel S → binary_op (finite_set S) 
:= λ S r,  bop_then_unary (finite_set S) (uop_duplicate_elim S r) (bop_concat S).

Definition bop_intersect : ∀ S : Type, brel S → binary_op (finite_set S) 
:= λ S r X,  uop_filter  S (in_set S r X). 



Definition ltran_list_product : ∀ (s : Type) (bs : binary_op s), left_transform s (list s) 
:= fix f s bs a y := 
      match y with
         | nil => nil 
         | b :: rest => (bs a b ) :: (f s bs a rest)
      end.

Definition rtran_list_product : ∀ (S : Type) (bS : binary_op S), right_transform S (list S) 
:= fix f S bS Y a := 
      match Y with
         | nil => nil 
         | b :: rest => (bS b a) :: (f S bS rest a)
      end.

Definition bop_list_product_left : ∀ (s : Type) (bs : binary_op s), binary_op(list s) 
:= fix f s bs x y := 
      match x with
         | nil => nil 
         | a :: rest => (ltran_list_product s bs a y) ++ (f s bs rest y) 
      end.

Definition bop_list_product_right : ∀ (s : Type) (bs : binary_op s), binary_op(list s) 
:= fix f s bs x y := 
      match x with
         | nil => nil 
         | a :: rest =>  (rtran_list_product s bs y a) ++ (f s bs rest y)
      end.



