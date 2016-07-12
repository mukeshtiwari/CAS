open Bool
open Datatypes
open EqNat
open Basic_types

(** val cas_infinity : cas_constant **)

let cas_infinity =
  'I'::('N'::('F'::('I'::('N'::('I'::('T'::('Y'::[])))))))

(** val brel_eq_bool : bool brel **)

let brel_eq_bool =
  eqb

(** val brel_eq_nat : int brel **)

let brel_eq_nat =
  beq_nat

(** val brel_dual : 'a1 brel -> 'a1 brel **)

let brel_dual r x y =
  if r x y then false else true

(** val brel_list : 'a1 brel -> 'a1 list brel **)

let rec brel_list u x y =
  match x with
  | [] ->
    (match y with
     | [] -> true
     | y0::l -> false)
  | a::tla ->
    (match y with
     | [] -> false
     | b::tlb -> if u a b then brel_list u tla tlb else false)

(** val brel_product : 'a1 brel -> 'a2 brel -> ('a1*'a2) brel **)

let brel_product u v x y =
  let x1,x2 = x in let y1,y2 = y in if u x1 y1 then v x2 y2 else false

(** val brel_sum : 'a1 brel -> 'a2 brel -> ('a1, 'a2) sum brel **)

let brel_sum u v x y =
  match x with
  | Coq_inl a ->
    (match y with
     | Coq_inl b -> u a b
     | Coq_inr t -> false)
  | Coq_inr a ->
    (match y with
     | Coq_inl s -> false
     | Coq_inr b -> v a b)

(** val brel_add_constant :
    'a1 brel -> cas_constant -> (cas_constant, 'a1) sum brel **)

let brel_add_constant rS c x y =
  match x with
  | Coq_inl a ->
    (match y with
     | Coq_inl b -> true
     | Coq_inr s -> false)
  | Coq_inr a ->
    (match y with
     | Coq_inl c0 -> false
     | Coq_inr b -> rS a b)

(** val brel_conjunction : 'a1 brel -> 'a1 brel -> 'a1 brel **)

let brel_conjunction r1 r2 x y =
  if r1 x y then r2 x y else false

(** val brel_llte : 'a1 brel -> 'a1 binary_op -> 'a1 brel **)

let brel_llte eq b x y =
  eq x (b x y)

(** val brel_llt : 'a1 brel -> 'a1 binary_op -> 'a1 brel **)

let brel_llt eq b =
  brel_conjunction (brel_llte eq b) (brel_dual eq)

(** val brel_and_sym : 'a1 brel -> 'a1 brel **)

let brel_and_sym r x y =
  if r x y then r y x else false

(** val in_set : 'a1 brel -> ('a1 finite_set, 'a1) brel2 **)

let rec in_set r l s =
  match l with
  | [] -> false
  | a::rest -> if r s a then true else in_set r rest s

(** val brel_subset : 'a1 brel -> 'a1 finite_set brel **)

let rec brel_subset r set1 set2 =
  match set1 with
  | [] -> true
  | a::rest -> if in_set r set2 a then brel_subset r rest set2 else false

(** val brel_set : 'a1 brel -> 'a1 finite_set brel **)

let brel_set r =
  brel_and_sym (brel_subset r)

