(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)

Require Import List ListSet.
From CAS Require Import 
  coq.algorithms.matrix_definition.

Import ListNotations.



Section Priority.

  Context 
    {U : Type} (* Type *)
    (u : U) (* bottom most element *)
    {C : U -> U -> bool}. (* Comparison operator *)


  (* I turn each row into a list (U * nat )*)
  Fixpoint get_list_of_nodes  
    (n : nat) (f : nat -> U) : list (U * nat) :=
  match n with 
  | 0 => [(f 0, 0)]
  | S n' => (f n, n) :: get_list_of_nodes n' f
  end.

  
  Fixpoint find_min_pair
    (nund : U * nat)
    (ls : list (U * nat)) : U * nat :=
  match ls with 
  | [] => nund
  | (nuh, ndh) :: t => 
    match C (fst nund) nuh with 
    (* nu is so far minimal element *)
    | true =>  find_min_pair nund t 
    (* nuh is minimal element *)
    | false => find_min_pair (nuh, ndh) t 
    end
  end.

  Definition find_min 
    (n : nat) (f : nat -> U) : U * nat :=
    find_min_pair (f 0, 0) (get_list_of_nodes n f).
  
End Priority.



Section Computation.

  Context 
    {U : Type} 
    {zero one : U}
    {plus mul : U -> U -> U}.
  

  (* 
    
    V is the set of nodes 
    A is the graphs |V| -> |V| -> R
    n is number of nodes
    S is the initial set
  *)

  (* Notes: 
    V - S_{k-1} can be represented in 
    one set, so I don't need to carry
    these two. 
    Idea : we have a priority queue vs
    and we pick a minimum element according 
    to (<+ ). 
    nd := pick_minimum R(i, q) (<+)


    Some wrinkels: How to force it 
    to finite type
  
  *)

  (* I need a function that 
    walk through one row R(i, _) 
    and return the column number 
    which has minimum value 
    according to <+ 
    Line 4 
  *)


  Context 
    {n : nat} (* total number of nodes*)
    (A : functional_matrix U)
    (i : nat). (* node i *)


  Definition find_min (i : nat) 
    (R : nat -> nat -> U) := 
  List.map 

  Definition generic_dijkstra : forall
    (V : set nat) (A : functional_matrix U) 
    (n : nat)
    (S : set nat), functional_matrix U ->
    functional_matrix U.
  Proof.
    intros V A.
    refine (fix Fn n {struct n} := 
    match n with 
    | 0 => fun S R => R 
    | S n' => fun S R => _
      (* find qk \in V - S *)
    end).
    (* Challenge will be termination. 
    Should I write my own custom inducition 
    
    *)
  




  




