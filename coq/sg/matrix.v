Require Import CAS.coq.common.matrix_def.
Require Import CAS.coq.eqv.string 
  CAS.coq.eqv.ascii
  CAS.coq.eqv.list.
Require Import Coq.Strings.Ascii
  List.
Import ListNotations.
Local Open Scope char_scope.





Section Computation.

(* define + and * for matricies *)
  Context {S : Type}
    (plus : S -> S -> S)
    (mul : S -> S -> S).


  Definition matrix_addiiton (m₁ m₂ : (@square_matrix S) + list ascii) 
    : (@square_matrix S) + list ascii :=
    match m₁, m₂ with
    | inl {| sm_size := n₁; sm_matrix := f₁ |},
      inl {| sm_size := n₂; sm_matrix := f₂ |} => 
        if Nat.eqb n₁ n₂ 
        then inl {| sm_size := n₁; sm_matrix := fun c d => plus (f₁ c d) (f₂ c d) |}
        else inr ["e"; "r"; "r"; "o"; "r"]
    | _, _ => inr ["e"; "r"; "r"; "o"; "r"]
    end.

  Definition get_row_of_matrix (f : nat -> nat -> S) (r : nat) 
    : nat -> S := f r.

  Definition get_cold_of_matrx (f : nat -> nat -> S) (c : nat)
    : nat -> S := fun d => f d c.

  (* generic function to add two rows, cols, or 
     a row and a column *)
  Definition add_two_vectors (f g : nat -> S) := 
    fun c => plus (f c) (g c).

  (* generic function to multiply two rows, cols, or
     a row and a column *)
  Definition mul_two_vectors (f g : nat -> S) :=
    fun c => mul (f c) (g c).
  
  (* *)

  
    
  
End Computation. 

Section Theory.

  Section Addition.

  End Addition.

  Section Multiplication.
    
  End Multiplication.         


End Theory.   

