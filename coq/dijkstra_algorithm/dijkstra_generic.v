(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat
  Vector Fin Utf8.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory.
Import ListNotations.

(* This section will move to another file
  after I finish the proof because right now
  I don't want to touch makefile to avoid 
  merge conflict.
*)
Section Finite.

  Lemma fin_inv_0 (i : Fin.t 0) : False.
  Proof. refine (match i with end). Defined.

  Lemma fin_inv_S {n : nat} (i : Fin.t (S n)) :
    (i = Fin.F1) + {i' | i = Fin.FS i'}.
  Proof.
    refine (match i with
            | Fin.F1 => _
            | Fin.FS _ => _
            end); eauto.
  Defined.

  (* How to write this function? 
    n = 0 => []
    n = 1 => [F1]
    n = 2 => [FS F1; F1]
    n = 3 => [FS (FS F1); FS F1; F1]
  
    I want to enumerate all the elements of Fin.t n into 
    a list.
  *)
  Fixpoint enum_fin {n : nat} : list (Fin.t n).
  Proof.
  Admitted.

End Finite.
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
    ssreflect formalisation 
    https://www.cl.cam.ac.uk/~tgg22/metarouting/rie-1.0.v
  *)
  Context
    {T : Type}
    {zero one : T}
    {add mul : T -> T -> T}
    {C : T -> T -> bool} (* comparision  *)
    {n : nat}. (* num of nodes and it is represented by Fin.t *)

   Context 
    (A : Fin.t n -> Fin.t n -> T)
    (i : Fin.t n). (* node i *)


  Declare Scope Dij_scope.
  Delimit Scope Dij_scope with T.
  Bind Scope Dij_scope with T.
  Local Open Scope Dij_scope.

  Local Infix "+" := add : Dij_scope.
  Local Infix "*" := mul : Dij_scope.
  Local Notation "0" := zero : Dij_scope.
  Local Notation "1" := one : Dij_scope.

  (* state captures all the information.  *)   
  Record state :=
    mk_state 
    {
      vis : list (Fin.t n); (* visited so far *)
      pq  : list (Fin.t n); (* priority_queue *)
      Ri  : Fin.t n -> T (* the ith row under consideration *)
    }.

  (* 
      Look for minimum element in Ri
      Some (qk, pq') := remove_min pq Ri
      new priority queue is pq'
      for every j in pq', relax the edges
      fun j : Fin.t n => (Ri j) + ((Ri qk) * (A qk j)) 
    *)

  (* we relax all the edges in pq from qk,
    i.e., every node in pq has a new (shortest) path from qk *)
  Definition relax_edges 
    (qk : Fin.t n) 
    (pq : list (Fin.t n))
    (Ri : Fin.t n -> T) : Fin.t n -> T :=
    fun (j : Fin.t n) =>
      match List.in_dec Fin.eq_dec j pq with 
      | left _ => (Ri j) + ((Ri qk) * (A qk j)) (* update if j is in pq *)
      | right _ => Ri j (* do nothing, if j in not in pq *)
      end.

  (* one iteration of Dijkstra. *)
  Definition dijkstra_one_step (s : state) : state :=
    match s with 
    |  mk_state vis pq Ri => 
      match @remove_min _ C n pq Ri with 
      | None => s 
      | Some (qk, pq') => 
          mk_state 
            (qk :: vis) (* add qk to visited set *)
            pq' (* new priority queue *)
            (relax_edges qk pq' Ri) (* relax the row *)
      end 
    end.


  Definition I := λ (i j : Fin.t n),
    if Fin.eq_dec i j then 1 else 0.
  (* 
    visisted is node i
    priority_queue is very other nodes, except i 
    Ri := fun j => I i j + A i j 
  *)
  (* I need to write enum_fin *)
  Definition initial_state : state :=
    (mk_state [i] (List.remove Fin.eq_dec i (@enum_fin n)) 
    (fun j => I i j + A i j)).


  (* it computes f^n (init_state) *)
  Definition dijkstra (m : nat) (s : state) : state :=
    Nat.iter m dijkstra_one_step s.
    
End Computation.

Section Proofs.
(* This section contains proofs about 
  Dijkstra algorithm. 
  
  Notes from Tim's slides:
  if we drop distributivity, then 
  Dijkstra algorithm computes for a given 
  source vertex i:
  ∀ j : V, R i j := I i j + (forall q : V, R i q * A q j)

  R := R * A + I 
  *)
  (* operators and assumptions that we going to have *)
  Context
    {T : Type}
    {zero one : T}
    {add mul : T -> T -> T}
    {eqT : brel T}
    {refT : brel_reflexive T eqT}
    {symT : brel_symmetric T eqT}
    {trnT : brel_transitive T eqT}.

  Declare Scope Dij_scope.
  Delimit Scope Dij_scope with T.
  Bind Scope Dij_scope with T.
  Local Open Scope Dij_scope.

  Local Infix "+" := add : Dij_scope.
  Local Infix "*" := mul : Dij_scope.
  Local Notation "0" := zero : Dij_scope.
  Local Notation "1" := one : Dij_scope.
  Local Infix "==" := eqT (at level 70) : Dij_scope.


  Context
    {associative : forall (a b c : T), (a + b + c == a + (b + c)) = true}
    {commutative : forall (a b : T), (a + b == b + a) = true}
    {zero_add_id : forall (a : T), (0 + a == a) = true}
    {one_mul_id : forall (a : T), (1 * a == a) = true}
    (* add_sel not used explicitly in the proofs *)
    {add_sel : forall (a b : T), ((a + b == a) = true) + ((a + b == b) = true)}
    {one_add_ann : forall (a : T), (1 + a == 1) = true}
    {add_mul_right_absorption : forall (a b : T), (a + (a * b) == a) = true}.
    (* a <=L a * b *)

  

  




End Proofs.
  




