(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let app x =
  let rec app0 l m =
    match l with
    | [] -> m
    | a::l1 -> a::(app0 l1 m)
  in app0 x

