(** val plus : int -> int -> int **)

let rec plus n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    m)
    (fun p -> succ
    (plus p m))
    n

(** val mult : int -> int -> int **)

let rec mult n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    0)
    (fun p ->
    plus m (mult p m))
    n

(** val max : int -> int -> int **)

let rec max n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    m)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      n)
      (fun m' -> succ
      (max n' m'))
      m)
    n

(** val min : int -> int -> int **)

let rec min n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    0)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      0)
      (fun m' -> succ
      (min n' m'))
      m)
    n

