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

  
  (* we relax all the edges in pq from qk,
    i.e., every node in pq has a new (shortest) 
    path from qk 
  *)
  
  Definition relax_edges 
    (qk : T * Node) 
    (pq : list (T * Node))
    (ri : Node -> Node -> T) : list (T * Node) :=
    match qk with 
    | (w, qk') =>  
      List.map 
        (λ '(tdist, tnode), 
          if brel_lte_left eqT add (w + (ri qk' tnode)) tdist 
          then (w + (ri qk' tnode), tnode) (* relax *)
          else (tdist, tnode)) pq  (* don't change *)
    end.
    (* Note: make lambda a separate function *)


  (* one iteration of Dijkstra. *)
  Definition dijkstra_one_step (m : Node -> Node -> T) 
    (s : state) : state :=
    match s with 
    |  mk_state vis pq => 
      match @remove_min_pq T eqT add pq with 
      | None => s 
      | Some ((w, qk), pq') => 
          mk_state 
            ((w, qk) :: vis) (* add qk to visited set *)
            (relax_edges (w, qk) pq' m)  (* new priority queue *)
      end 
    end.


  (* Short hand of identity *)
  Definition I := I T 0 1.

  Definition initial_state (i : Node) (l : list Node) 
    (m : Node -> Node -> T) : state :=
    let pq := (List.map (λ j, (m i j, j)) 
      (List.remove Nat.eq_dec i l)) in 
    (mk_state [(1, i)] pq).
    

  (* it computes f^n (init_state)  
  Definition dijkstra_aux (m : Node -> Node -> T) 
    (n : nat)
    (s : state) : state :=
    Nat.iter n (dijkstra_one_step m) s.
  *)
  
  
  Definition dijkstra_aux (i : Node) (k : nat) (l : list Node) 
    (m : Node -> Node -> T) : state := 
    Nat.iter k 
    (dijkstra_one_step m) (initial_state i l m).


  Definition visited_to_map (s : state) : Node -> T := 
    List.fold_left (λ f '(v, q) x, 
      if x =? q then v else f q) 
      (vis s) (λ x, 0).


  Definition dijkstra (i : Node) (l : list Node) 
      (m : Node -> Node -> T) : Node -> T := 
    visited_to_map (dijkstra_aux i (List.length l) l m).
     

(* 
  This section contains proofs about 
  Dijkstra algorithm. 
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

  Lemma dijkstra_aux_iter_or_fix : 
    forall i k l m, 
    (dijkstra_aux i (S k) l m = dijkstra_aux i k l m) ∨
    (∃ v q, vis (dijkstra_aux i (S k) l m) = 
      ((v, q) :: vis (dijkstra_aux i k l m)) ∧
      (forall x y, List.In (x, y) 
        (pq (dijkstra_aux i k l m)) ->
      brel_lte_left eqT add v x = true)).
  Proof.
  Admitted.

  (* write our list membership for T * Node *)
   Lemma dijkstra_aux_lemma (i : Node) : 
    ∀ (k : nat) (pa : T) (j : Node)
      (m : Node -> Node -> T), 
      let r := (dijkstra_aux i k l m) in 
      List.In (pa, j) (vis r) -> 
      pa == I i j + 
      sum_fn 0 add  
        (fun '(w, q) => w * m q j) (vis r) = true.
  Proof.
    induction k.
    + simpl.
      intros ? ? ? [Ha | Ha].
      ++ 
        inversion Ha; subst; clear Ha.
        unfold sum_fn;
        simpl.
        admit.
      ++ tauto.
    + (* inducation case *)   
      intros ? ? ? ? Hb.
      (* 
        There are two cases here.
        1. (vis (dijkstra_one_step m (dijkstra_aux i k l m))) =
          vis (dijkstra_aux i k l m)) because 
          everything has been added to visited set and nothing left
          so we are home ! 
        2. (vis (dijkstra_one_step m (dijkstra_aux i k l m))) = 
          (ah, bh) :: vis (dijkstra_aux i k l m)) 
          and we know that 
          forall List.in (x, y) 
            (pq  vis (dijkstra_aux i k l m))) ->
            (ah, bh) <= (x, y).
      *)
      destruct (dijkstra_aux_iter_or_fix  i k l m) as [Hc | Hc].
      unfold r in * |- *.
      rewrite Hc in Hb.
      rewrite Hc.
      exact (IHk _ _ _ Hb).
      (* *)
      destruct Hc as (v & q & Hd & He).
      unfold r in * |- *.
      rewrite Hd.
      rewrite Hd in Hb.
      destruct Hb as [Hb | Hb].
      unfold sum_fn; simpl.
      inversion Hb; subst.
  Admitted.


  Lemma visited_simp : 
    forall i j ln m, 
      visited_to_map (initial_state i ln m) j == 
      (if i =? j then 1 else 0) = true.
  Admitted. 

  Lemma initial_state_2 : 
    forall i j ln m,
      sum_fn 0 add 
      (λ q : Node, 
        visited_to_map (initial_state i ln m) q * m q j) ln
      == 0 = true.
  Admitted. 

  Lemma dijkstra_more_gen (i : Node) :
    forall (k : nat) (j : Node)
    (ln : list Node) (m : Node -> Node -> T), 
    (visited_to_map (dijkstra_aux i k ln m) j ==
    I i j +
    sum_fn 0 add
      (λ q : Node, 
        visited_to_map (dijkstra_aux i k ln m) q * m q j) ln) =
    true.
  Proof.
    induction k.
    + simpl.
      intros until m.
      admit.
    + simpl.
      intros until m.
      unfold visited_to_map.
      
      
  Admitted.

  Lemma dijkstra_main_proof :
    forall (i : Node) 
      (ln : list Node)
      (m : Node -> Node -> T),
      let r := dijkstra i ln m in 
      forall j : Node, 
      List.In j ln -> 
      r j == I i j + 
      sum_fn 0 add  
        (fun q => r q * m q j) ln = true.
  Proof.
    intros until j. 
    intro Ha.
    unfold r, dijkstra.
    apply dijkstra_more_gen.
  Qed.




  
  
    




End Computation.


  




