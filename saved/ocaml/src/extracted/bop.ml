open Datatypes
open Peano
open Basic_types
open Brel
open Uop

(** val bop_and : bool binary_op **)

let bop_and b1 b2 =
  if b1 then b2 else false

(** val bop_or : bool binary_op **)

let bop_or b1 b2 =
  if b1 then true else b2

(** val bop_plus : int binary_op **)

let bop_plus =
  plus

(** val bop_times : int binary_op **)

let bop_times =
  mult

(** val bop_min : int binary_op **)

let bop_min =
  min

(** val bop_max : int binary_op **)

let bop_max =
  max

(** val bop_left : 'a1 binary_op **)

let bop_left l r =
  l

(** val bop_right : 'a1 binary_op **)

let bop_right l r =
  r

(** val bop_concat : 'a1 list binary_op **)

let bop_concat x y =
  app x y

(** val bop_then_unary : 'a1 unary_op -> 'a1 binary_op -> 'a1 binary_op **)

let bop_then_unary u b x y =
  u (b x y)

(** val bop_product :
    'a1 binary_op -> 'a2 binary_op -> ('a1*'a2) binary_op **)

let bop_product u v x y =
  let x1,x2 = x in let y1,y2 = y in (u x1 y1),(v x2 y2)

(** val bop_left_sum :
    'a1 binary_op -> 'a2 binary_op -> ('a1, 'a2) sum binary_op **)

let bop_left_sum opS opT x y =
  match x with
  | Coq_inl a ->
    (match y with
     | Coq_inl b -> Coq_inl (opS a b)
     | Coq_inr t -> x)
  | Coq_inr a ->
    (match y with
     | Coq_inl s -> y
     | Coq_inr b -> Coq_inr (opT a b))

(** val bop_right_sum :
    'a1 binary_op -> 'a2 binary_op -> ('a1, 'a2) sum binary_op **)

let bop_right_sum opS opT x y =
  match x with
  | Coq_inl a ->
    (match y with
     | Coq_inl b -> Coq_inl (opS a b)
     | Coq_inr t -> y)
  | Coq_inr a ->
    (match y with
     | Coq_inl s -> x
     | Coq_inr b -> Coq_inr (opT a b))

(** val bop_add_id :
    'a1 binary_op -> cas_constant -> (cas_constant, 'a1) sum binary_op **)

let bop_add_id bS c x y =
  match x with
  | Coq_inl c0 ->
    (match y with
     | Coq_inl c1 -> y
     | Coq_inr s -> y)
  | Coq_inr a ->
    (match y with
     | Coq_inl c0 -> x
     | Coq_inr b -> Coq_inr (bS a b))

(** val bop_add_ann :
    'a1 binary_op -> cas_constant -> (cas_constant, 'a1) sum binary_op **)

let bop_add_ann bS c x y =
  match x with
  | Coq_inl c0 ->
    (match y with
     | Coq_inl c1 -> x
     | Coq_inr s -> x)
  | Coq_inr a ->
    (match y with
     | Coq_inl c0 -> y
     | Coq_inr b -> Coq_inr (bS a b))

(** val bop_llex :
    'a1 brel -> 'a1 binary_op -> 'a2 binary_op -> ('a1*'a2) binary_op **)

let bop_llex eq b1 b2 x y =
  let a,b = x in
  let c,d = y in
  (b1 a c),(if eq a c then b2 b d else if brel_llt eq b1 a c then b else d)

(** val bop_union : 'a1 brel -> 'a1 finite_set binary_op **)

let bop_union r =
  bop_then_unary (uop_duplicate_elim r) bop_concat

(** val bop_intersect : 'a1 brel -> 'a1 finite_set binary_op **)

let bop_intersect r x =
  uop_filter (in_set r x)

