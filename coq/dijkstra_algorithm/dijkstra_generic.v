(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat
  Utf8
  Coq.Sorting.Permutation
  Psatz.

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
      vis : list (T * Node); (* visited so far *)
      pq  : list (T * Node); (* priority_queue *)
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
    (qk : T * Node) 
    (pq : list (T * Node))
    (ri : Node -> Node -> T) : list (T * Node).
  Admitted.

  (* one iteration of Dijkstra. *)
  Definition dijkstra_one_step (m : Node -> Node -> T) 
    (s : state) : state.
  refine
    match s with 
    |  mk_state vis pq => 
      match remove_min pq with 
      | None => s 
      | Some ((w, qk), pq') => 
          mk_state 
            ((w, qk) :: vis) (* add qk to visited set *)
            (relax_edges (w, qk) pq' m) (* new priority queue *)
      end 
    end.



  (* Short hand of identity *)
  Definition I := I T 0 1.

  Definition initial_state (i : Node) (l : list Node) 
    (m : Node -> Node -> T) :=
    (mk_state [] (List.map (λ j, (m i j, j)) l)) 
    

  (* it computes f^n (init_state) 
  Definition dijkstra (m : Node -> Node -> T) 
    (s : state) : state :=
    Nat.iter () dijkstra_one_step s.
  *)
  
  Definition dijkstra (i : Node) (l : list Node) 
      (m : Node -> Node -> T) := 
    Nat.iter (List.length l) 
    dijkstra_one_step (initial_state i l m).


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


  
  (* 
    In every step, 
    either we take an element from the priority queue
    and move it to the visited node or it's 
    empty.   
    
  *)

  Lemma dijkstra_permutation :
    forall k lgen i,
    Permutation 
    (vis (dijkstra k i lgen) ++ 
    pq (dijkstra k i lgen)) lgen.
  Proof.
    induction k.
    + simpl;
      intros ? ?.
      admit.
    + simpl.
      unfold dijkstra_one_step;
      cbn.
  Admitted. 

  
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
    unfold dijkstra,
    dijkstra_gen.
  Admitted.
  
  Lemma dijkstra_main_proof (i : Node) : 
    ∀ (k : nat) (j : Node), 
    k <= n -> 
    List.In j (vis (dijkstra k i l)) -> 
    (ri (dijkstra k i l) j == I i j + 
      sum_fn 0 add 
        (fun q => ri (dijkstra k i l) q * A q j)
        (vis (dijkstra k i l))) = true.
  Proof.
    induction k.
    + unfold sum_fn; 
      simpl;
      intros ? Hn [H | H].
      - subst.
        unfold I, 
        matrix_multiplication.I,
        matrix_mul_identity,
        brel_eq_nat.
        rewrite Nat.eqb_refl.
        (* + is congruence *)
        (* 
          A j j = ((1 + A j j) * A j j + 0))
          We have (1 + A j j) =  1 by one_add_ann
          A j j = (1 * A j j + 0) 
          We 1 * A j j = A j j by one_mul_id 
          A j j = A j j + 0 
          and we have A j j + 0 = A j j
          A j j = A j j and we are home
        *)
        admit.
      - tauto.
    + (* inductive case *)
      simpl; 
      intros ? Ha Hb.
      (* From Hb : In j (vis (dijkstra_one_step (dijkstra k i l)))
         I know what j = qk or inductive case.
      *)
      unfold dijkstra_one_step in Hb.
      destruct (dijkstra k i l) eqn:Hd.
      destruct (remove_min pq0 ri0) eqn:He.
      destruct p.
      simpl in He, Hb.
      simpl in IHk.
      simpl.
      rewrite He.
      simpl.
      unfold sum_fn.
      simpl.

      assert (k <= n). nia. (* this condition is spurious *)
      simpl.
      unfold dijkstra_one_step, 
      dijkstra,
      dijkstra_gen,
      initial_state,
      dijkstra_one_step.

    
        

  Admitted.
  
  
    




End Computation.


  




