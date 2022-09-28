(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat
  Vector Fin Utf8.

From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory 
  coq.dijkstra_algorithm.priority_queue
  coq.dijkstra_algorithm.Finite.


Import ListNotations.

Section Computation.

  (*Most of the code is taken/inspired from Tim's 
    ssreflect formalisation 
    https://www.cl.cam.ac.uk/~tgg22/metarouting/rie-1.0.v
  *)
  Context
    {T : Type}
    {zero one : T}
    {add mul : T -> T -> T}
    {eqT : brel T}
    {refT : brel_reflexive T eqT}
    {symT : brel_symmetric T eqT}
    {trnT : brel_transitive T eqT}.
    


   Context 
    {Node : Type}
    {Hdec : ∀ (x y : Node), {x = y} + {x <> y}}
    (A : Node -> Node -> T). (* Adjacency Matrix *)



  Declare Scope Dij_scope.
  Delimit Scope Dij_scope with T.
  Bind Scope Dij_scope with T.
  Local Open Scope Dij_scope.

  Local Infix "+" := add : Dij_scope.
  Local Infix "*" := mul : Dij_scope.
  Local Notation "0" := zero : Dij_scope.
  Local Notation "1" := one : Dij_scope.
  Local Infix "==" := eqT (at level 70) : Dij_scope.

  (* <=+ order *)
  Definition C (a b : T) := (a + b == a).


  (* state captures all the information.  *)   
  Record state :=
    mk_state 
    {
      vis : list Node; (* visited so far *)
      pq  : list Node; (* priority_queue *)
      Ri  : Node -> T  (* the ith row under consideration *)
    }.

  (* 
      Look for minimum element in Ri
      Some (qk, pq') := remove_min pq Ri
      new priority queue is pq'
      for every j in pq', relax the edges
      fun j : A => (Ri j) + ((Ri qk) * (A qk j)) 
  *)

  
  (* we relax all the edges in pq from qk,
    i.e., every node in pq has a new (shortest) 
    path from qk *)
  Definition relax_edges 
    (qk : Node) 
    (pq : list Node)
    (Ri : Node -> T) : Node -> T :=
    fun (j : Node) =>
      match List.in_dec Hdec j pq with 
      | left _ => (Ri j) + ((Ri qk) * (A qk j)) (* update if j is in pq *)
      | right _ => Ri j (* do nothing, if j in not in pq *)
      end.


  (* one iteration of Dijkstra. *)
  Definition dijkstra_one_step (s : state) : state :=
    match s with 
    |  mk_state vis pq Ri => 
      match @remove_min _ Hdec T C pq Ri with 
      | None => s 
      | Some (qk, pq') => 
          mk_state 
            (qk :: vis) (* add qk to visited set *)
            pq' (* new priority queue *)
            (relax_edges qk pq' Ri) (* relax the row *)
      end 
    end.


  (* 
    construct a state.
    i is the starting node
    l is the list of nodes except i 
    Ri is the ith row 
  *)
  Definition construct_a_state 
    (i : Node) (l : list Node) 
    (Ri : Node -> T) : state :=
    (mk_state [i] (List.remove Hdec i l) Ri).


  Definition I := λ (i j : Node),
    if Hdec i j then 1 else 0.


  Definition initial_state (i : Node) (l : list Node) :=
    construct_a_state i l 
    (fun j : Node => I i j + A i j).


  (* it computes f^n (init_state) *)
  Definition dijkstra (m : nat) (s : state) : state :=
    Nat.iter m dijkstra_one_step s.



(* 
  This section contains proofs about 
  Dijkstra algorithm. 
  
  Notes from Tim's slides:
  if we drop distributivity, then 
  Dijkstra algorithm computes for a given 
  source vertex i:
  ∀ j : V, R i j := I i j + (forall q : V, R i q * A q j)

  R := R * A + I 
  *)
  

  (* Finite Node *)
  Context 
    {l : list Node}
    {Hfin : ∀ x : Node, List.In x l}.
  
  Let nl := List.length l.


  (* Lemmas needed for proof *)
  Context
    {associative : forall (a b c : T), (a + b + c == a + (b + c)) = true}
    {commutative : forall (a b : T), (a + b == b + a) = true}
    {zero_add_id : forall (a : T), (0 + a == a) = true}
    {one_mul_id : forall (a : T), (1 * a == a) = true}
    {add_sel : forall (a b : T), ((a + b == a) = true) + ((a + b == b) = true)}
    {one_add_ann : forall (a : T), (1 + a == 1) = true}
    {add_mul_right_absorption : forall (a b : T), (a + (a * b) == a) = true}.

  
  (* Everything good upto this point *)

  
  
  
  
    




End Computation.


  




