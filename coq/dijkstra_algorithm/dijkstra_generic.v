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

  (* 
  Definition find_min 
    (n : nat) (f : nat -> U) : U * nat :=
    find_min_pair (f 0, 0) (get_list_of_nodes n f).
  *)

  Definition remove_min (vs : list nat) 
    (f : nat -> U) : 
    option (nat * list nat).
  Admitted.


End Priority.



Section Computation.

  Context 
    {U : Type} 
    {C : U -> U -> bool}
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
    (A : functional_matrix U)
    (i : nat). (* node i *)

  (* Everything is good upto here *)

  Definition zwf (xs ys : set nat) := 
    List.length xs < List.length ys.

  Lemma zwf_well_founded : well_founded zwf.
  Proof.
    exact (Wf_nat.well_founded_ltof _ 
      (fun xs => List.length xs)).
  Defined.


  
  Definition generic_dijkstra :
    set nat-> functional_matrix U ->
    functional_matrix U.
  Proof.
    intro vs. (* vs contains all the nodes 
    from 0, 1... n *)
    induction (zwf_well_founded vs) as [vs Hvs IHvs].
    intro R;
    unfold zwf in IHvs.
    (* 
      now find the qk which is minimum 
      remove_min vs (f : nat -> R) := Some (qk, vs')
      Also, prove that List.lenght vs' < List.length vs
      apply induction hypothesis.
    *)
    (* if vs is empty we have finished the iteration 
      upto k times, but if vs is not empty then I pick
      (qk, vs') := remove_minimum 
      IHvs vs' prf (vector_add (R i) 
        (vector_mul (R i) (fun j => A j qk) vs')
      
    refine(match remove_min vs with 
    | None => R 
    | Some (qk, vs') => 
      (* we are bulding one row*)
      IHvs vs' prf 
        (fun w j => if w = i thne plus (R i j) 
          (vector_mul_element (R i qk) (A qk)
      
    end *)
  Admitted.
   




  




