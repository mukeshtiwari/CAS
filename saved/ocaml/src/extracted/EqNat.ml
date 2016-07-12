(** val beq_nat : int -> int -> bool **)

let rec beq_nat n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      true)
      (fun n0 ->
      false)
      m)
    (fun n1 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      false)
      (fun m1 ->
      beq_nat n1 m1)
      m)
    n

