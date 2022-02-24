
(* define type matrix 
   define = for matricies 
*)

Record square_matrix {S: Type} := 
{
  sm_size   : nat 
; sm_matrix : nat -> nat -> S
}.
