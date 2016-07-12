Require Import CAS.code.basic_types. 


Definition left_trop_from_bop : ∀ S : Type, binary_op S → left_transform S S 
:= λ S bop,  bop.

Definition right_trop_from_bop : ∀ S : Type, binary_op S → right_transform S S 
:= λ S bop,  bop.

Definition left_trop_from_right_trop : ∀ S T: Type, right_transform S T → left_transform S T
:= λ S T rt s t,  rt t s. 

Definition right_trop_from_left_trop : ∀ S T: Type, left_transform S T → right_transform S T
:= λ S T rt t s,  rt s t. 

Definition left_trop_product : ∀ S T U V: Type, left_transform S T → left_transform U V → left_transform (S * U) (T * V)
:= λ S T U V top1 top2 x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (top1 x1 y1, top2 x2 y2) 
   end.

(* identical code! *) 
Definition right_trop_product : ∀ S T U V: Type, right_transform S T → right_transform U V → right_transform (S * U) (T * V)
:= λ S T U V top1 top2 x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (top1 x1 y1, top2 x2 y2) 
   end.

Definition left_trop_left_sum : ∀ S T U: Type, left_transform S T → left_transform U T → left_transform (S + U) T 
:= λ S T U top1 top2 d t,  
   match d with
    | (inl s) => top1 s t
    | (inr u) => top2 u t
   end.

Definition left_trop_right_sum : ∀ S T U: Type, left_transform S T → left_transform S U → left_transform S (T + U)
:= λ S T U top1 top2 s d,  
   match d with
    | (inl t) => inl _ (top1 s t)
    | (inr u) => inr _ (top2 s u)
   end.

Definition right_trop_left_sum : ∀ S T U: Type, right_transform S T → right_transform S U → right_transform S (T + U) 
:= λ S T U top1 top2 d t,  
   match d with
    | (inl s) => inl _ (top1 s t)
    | (inr u) => inr _ (top2 u t)
   end.

Definition right_trop_right_sum : ∀ S T U: Type, right_transform S T → right_transform U T → right_transform (S + U) T
:= λ S T U top1 top2 s d,  
   match d with
    | (inl t) => (top1 s t)
    | (inr u) => (top2 s u)
   end.
