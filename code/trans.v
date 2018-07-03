Require Import CAS.code.basic_types. 

Open Scope list_scope.

Definition lt_from_bop : ∀ {S : Type}, binary_op S → left_transform S S 
:= λ {S} bop,  bop.

Definition rt_from_bop : ∀ {S : Type}, binary_op S → right_transform S S 
:= λ {S} bop,  bop.

Definition lt_from_rt : ∀ {S T: Type}, right_transform S T → left_transform S T
:= λ {S T} rt s t,  rt t s. 

Definition rt_from_lt : ∀ {S T: Type}, left_transform S T → right_transform S T
  := λ {S T} rt t s,  rt s t.

Definition lt_cons : ∀ {S : Type},  left_transform S (list S) := λ {S} x l,  x :: l. 

Definition lt_product : ∀ {S T U V: Type}, left_transform S T → left_transform U V → left_transform (S * U) (T * V)
:= λ {S T U V} top1 top2 x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (top1 x1 y1, top2 x2 y2) 
   end.

(* identical code! *) 
Definition rt_product : ∀ {S T U V: Type}, right_transform S T → right_transform U V → right_transform (S * U) (T * V)
:= λ {S T U V} top1 top2 x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (top1 x1 y1, top2 x2 y2) 
   end.

(*
      +++++++++++++++ Sums ++++++++++++++++++++
*) 

Definition lt_left_sum : ∀ {S T U: Type}, left_transform S T → left_transform U T → left_transform (S + U) T 
:= λ {S T U} top1 top2 d t,  
   match d with
    | (inl s) => top1 s t
    | (inr u) => top2 u t
   end.

Definition lt_right_sum : ∀ {S T U: Type}, left_transform S T → left_transform S U → left_transform S (T + U)
:= λ {S T U} top1 top2 s d,  
   match d with
    | (inl t) => inl _ (top1 s t)
    | (inr u) => inr _ (top2 s u)
   end.

Definition lt_product_sum : ∀ {S T U V: Type}, left_transform S T → left_transform U V → left_transform (S * U)  (T + V)
:= λ {S T U V} top1 top2 p a,  
   match p, a with
    | (s, u), (inl t) => inl _ (top1 s t)
    | (s, u), (inr v) => inr _ (top2 u v)
   end.

Definition lt_sum_product : ∀ {S T U V: Type}, left_transform S T → left_transform U V → left_transform (S + U)  (T * V)
:= λ {S T U V} top1 top2 d p,  
   match d, p with
    | (inl s), (t, v) => (top1 s t, v)
    | (inr u), (t, v) => (t, top2 u v)
   end.


(* right *) 


Definition rt_left_sum : ∀ {S T U: Type}, right_transform S T → right_transform S U → right_transform S (T + U) 
:= λ S T U top1 top2 d t,  
   match d with
    | (inl s) => inl _ (top1 s t)
    | (inr u) => inr _ (top2 u t)
   end.

Definition rt_right_sum : ∀ {S T U: Type}, right_transform S T → right_transform U T → right_transform (S + U) T
:= λ {S T U} top1 top2 s d,  
   match d with
    | (inl t) => (top1 s t)
    | (inr u) => (top2 s u)
   end.
