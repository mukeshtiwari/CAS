(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat
  Utf8.

From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory 
  coq.dijkstra_algorithm.priority_queue
  coq.po.from_sg
  coq.algorithms.list_congruences
  coq.algorithms.matrix_addition
  coq.algorithms.matrix_algorithms
  coq.algorithms.matrix_definition
  coq.algorithms.weighted_path
  coq.algorithms.matrix_multiplication.

Import ListNotations.

(* 
Most of the code is taken/inspired from Tim's 
ssreflect formalisation 
https://www.cl.cam.ac.uk/~tgg22/metarouting/rie-1.0.v
*)
Section Computation.

  
  Context
    {T : Type}
    {zero one : T}
    {add mul : T -> T -> T}
    {eqT : brel T}
    {refT : brel_reflexive T eqT}
    {symT : brel_symmetric T eqT}
    {trnT : brel_transitive T eqT}.
    

  (* Nodes are natural numbers *)
  Definition Node := nat.

   Context 
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


  (* state captures all the information.  *)   
  Record state :=
    mk_state 
    {
      vis : list Node; (* visited so far *)
      pq  : list Node; (* priority_queue *)
      ri  : Node -> T  (* the ith row under consideration *)
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
    (ri : Node -> T) : Node -> T :=
    fun (j : Node) =>
      match List.in_dec Nat.eq_dec j pq with 
      | left _ => (ri j) + ((ri qk) * (A qk j)) (* update if j is in pq *)
      | right _ => ri j (* do nothing, if j in not in pq *)
      end.


  (* one iteration of Dijkstra. *)
  Definition dijkstra_one_step (s : state) : state :=
    match s with 
    |  mk_state vis pq ri => 
      match @remove_min _ (brel_lte_left eqT add) pq ri with 
      | None => s 
      | Some (qk, pq') => 
          mk_state 
            (qk :: vis) (* add qk to visited set *)
            pq' (* new priority queue *)
            (relax_edges qk pq' ri) (* relax the row *)
      end 
    end.



  (* Short hand of identity *)
  Definition I := I T 0 1.

  Definition initial_state (i : Node) (l : list Node) :=
    (mk_state [i] (List.remove Nat.eq_dec i l) 
    (fun j : Node => I i j + A i j)).


  (* it computes f^n (init_state) *)
  Definition dijkstra_gen (m : nat) (s : state) : state :=
    Nat.iter m dijkstra_one_step s.

  
  Definition dijkstra (m : nat) (i : Node) (l : list Node):= 
    dijkstra_gen m (initial_state i l).


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
    {n : nat} (* number of nodes*)
    {l : list Node} (* list of nodes 0, 1, 2, .... n-1 *)
    {Hndup: NoDup l} (* There are no duplicates *)
    {Hnfin: forall x : Node, In x l -> x < n}.

  (* Lemmas needed for proof *)
  Context
    {associative : forall (a b c : T), (a + b + c == a + (b + c)) = true}
    {commutative : forall (a b : T), (a + b == b + a) = true}
    {zero_add_id : forall (a : T), (0 + a == a) = true}
    {one_mul_id : forall (a : T), (1 * a == a) = true}
    {add_sel : forall (a b : T), ((a + b == a) = true) + ((a + b == b) = true)}
    {one_add_ann : forall (a : T), (1 + a == 1) = true}
    {add_mul_right_absorption : forall (a b : T), (a + (a * b) == a) = true}.


  
  
  (* Proof idea:
    After n iterations, all the nodes 
    have been in visited state and there 
    is no more change.
  *)

  
  Lemma dijkstra_fixpoint (i : Node) :
    ∀ k : nat, 
    dijkstra n i l = 
    dijkstra (k + n) i l.
  Proof.
  Admitted.
  
  Lemma dijkstra_main_proof (i : Node) : 
    ∀ (k : nat) (j : Node), k < n -> 
    List.In j (vis (dijkstra k i l)) -> 
    ri (dijkstra k i l) j = I i j + 
      (List.fold_right (fun x y => x + y)
        0 
        (List.map (fun q => ri (dijkstra k i l) q * A q j) 
          (vis (dijkstra k i l)))). 
  Proof.
  Admitted.
  
  
    




End Computation.


  




