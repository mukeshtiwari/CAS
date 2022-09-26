(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat
  Vector Fin.
Import ListNotations.

(* Find a library with proofs *)
Section Priority_Queue.

  Context 
    {U : Type} (* Type *)
    {C : U -> U -> bool}. (* Comparison operator *)



  (* This function returns the minimum node *)
  Fixpoint find_min_node
    {n : nat}
    (nund : U * Fin.t n)
    (ls : list (U * Fin.t n)) : Fin.t n :=
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
    {n : nat} 
    (vs : list (Fin.t n)) (* list of nodes *)
    (f : Fin.t n -> U) :  (* one row *)
    option (Fin.t n * list (Fin.t n)) :=
  match vs with 
  | [] => None
  | h :: t => 
    let qk := 
      find_min_node (f h, h) 
        (List.map (fun x => (f x, x)) t) 
    in Some (qk, List.remove Fin.eq_dec qk vs)
  end.
  
End Priority_Queue.

Section Computation.

  (*Most of the code is taken/inspired from Tim's 
    ssreflect formalisation *)
  Context
    {T : Type}
    {zero one : T}
    {add mul : T -> T -> T}
    {C : T -> T -> bool} (* comparision  *)
    {n : nat}. (* num of nodes and it is represented by Fin.t *)

   Context 
    (A : Fin.t n -> Fin.t n -> T)
    (i : nat). (* node i *)


  Declare Scope Dij_scope.
  Delimit Scope Dij_scope with T.
  Bind Scope Dij_scope with T.
  Local Open Scope Dij_scope.

  Local Infix "+" := add : Dij_scope.
  Local Infix "*" := mul : Dij_scope.

  (* state captures all the information.  *)   
  Record state :=
    mk_state 
    {
      vis : list (Fin.t n); (* visited so far *)
      pq : list (Fin.t n); (* priority_queue, we are going to pop one from the top *)
      Ri : Fin.t n -> T (* the ith row under consideration *)
    }.

  (* 
      Look for minimum element in Ri
      Some (qk, pq') := find_min pq Ri
      new priority queue is pq'
      for every j in pq', relax the edges
      fun j : Fin.t n => (Ri j) + ((Ri qk) * (A qk j)) 
    *)
    
  Definition relax 
    (qk : Fin.t n) 
    (pq : list (Fin.t n))
    (Ri : Fin.t n -> T) : Fin.t n -> T :=
    fun (j : Fin.t n) =>
      match List.in_dec Fin.eq_dec j pq with 
      | left _ => (Ri j) + ((Ri qk) * (A qk j)) (* update if j is in vs' *)
      | right _ => Ri j 
      end.

  Definition dijkstra_one_step (s : state) : state :=
    match s with 
    |  mk_state vis pq Ri => 
      match @remove_min _ C n pq Ri with 
      | None => s 
      | Some (qk, pq') => 
          mk_state 
            (qk :: vis) (* add qk to visited set *)
            pq' (* new priority queue *)
            (relax qk pq' Ri) (* relax the row *)
      end 
    end.

  
  (* it computes f^n (init_state) *)
  Definition dijkstra (m : nat) (s : state) : state :=
    Nat.iter m dijkstra_one_step s.
    
End Computation.

  




