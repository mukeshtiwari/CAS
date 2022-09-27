Require Import List ListSet.
Import ListNotations.

(* Find a library with proofs *)
Section Priority_Queue.


  Context 
    {A : Type}
    {Hdec : forall (x y : A), {x = y} + {x <> y}}.

  Context 
    {U : Type} (* Type *)
    {C : U -> U -> bool}. (* Comparison operator *)


  (* This function returns the minimum node *)
  Fixpoint find_min_node
    (nund : U * A)
    (ls : list (U * A)) : A :=
  match ls with 
  | [] => snd nund
  | (nuh, ndh) :: t => 
    match C (fst nund) nuh with 
    (* nu is so far minimal element *)
    | true =>  find_min_node nund t 
    (* nuh is minimal element *)
    | false => find_min_node (nuh, ndh) t 
    end
  end.


  Definition remove_min
    (vs : list A) (* list of nodes *)
    (f : A -> U) :  (* one row *)
    option (A * list A) :=
  match vs with 
  | [] => None
  | h :: t => 
    let qk := 
      find_min_node (f h, h) 
        (List.map (fun x => (f x, x)) t) 
    in Some (qk, List.remove Hdec qk vs)
  end.
  

End Priority_Queue.
