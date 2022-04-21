
Definition Matrix (Node R : Type) := Node -> Node -> R.


Record square_matrix {S: Type} := 
{
  sm_size   : nat 
; sm_matrix : nat -> nat -> S
}.

