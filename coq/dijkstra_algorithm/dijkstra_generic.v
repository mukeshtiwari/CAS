(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat.
From CAS Require Import 
  coq.algorithms.matrix_definition.

Import ListNotations.
(* efficient priority queue. *)
Section Priority.

  Context 
    {U : Type} (* Type *)
    {C : U -> U -> bool}. (* Comparison operator *)


  

  (* This function returns the minimum node *)
  Fixpoint find_min_node
    (nund : U * nat)
    (ls : list (U * nat)) : nat :=
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
    (vs : list nat) (* list of nodes *)
    (f : nat -> U) :  (* one row *)
    option (nat * list nat) :=
  match vs with 
  | [] => None
  | h :: t => 
    let qk := 
      find_min_node (f h, h) 
        (List.map (fun x => (f x, x)) t) 
    in Some (qk, List.remove Nat.eq_dec qk vs)
  end.
  
  Lemma remove_min_decreases : 
    forall vs vs' qk (f : nat -> U), 
    Some (qk, vs') = remove_min vs f ->
    length vs' < length vs.
  Proof.
    induction vs. 
  Admitted.


End Priority.



Section Computation.

  Context 
    {U : Type} 
    {C : U -> U -> bool}
    {zero one : U}
    {plus mul : U -> U -> U}.
  

  Context 
    (A : functional_matrix U)
    (i : nat). (* node i *)


  Definition zwf (xs ys : set nat) := 
    List.length xs < List.length ys.

  Lemma zwf_well_founded : well_founded zwf.
  Proof.
    exact (Wf_nat.well_founded_ltof _ 
      (fun xs => List.length xs)).
  Defined.


  (* Idea:
    We start with set of all nodes vs.
    Using well founded induction, we show that this 
    function terminates. 
    Instead of looping (Line 3: for each k = 1, 2, ... |V|), 
    we use priority queue as the termination argument. 
    We find the node qk in vs for R(i, qk) is 
    <+ minimum (minimal element). We split the 
    (qk, vs') := remove_min vs (f : nat -> U) 
    (* f here is the row (R i) *)

    vs is basically V - Sk.
  *)
  
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
    refine(
      match remove_min vs (R i) as rm 
      return rm = remove_min vs (R i) -> _ 
      with 
      | None => fun Heq => R 
      | Some (qk, vs') => fun Heq => 
        IHvs vs' _ (fun w => 
          match Nat.eq_dec w i with 
          | left _ => 
            (fun j => 
              match List.in_dec Nat.eq_dec j vs' with 
              | left _ => plus 
                (R i j) (mul (R i qk) (A qk j)) (* if j is in vs' *)
              | right _ => R i j  (* if j is not in vs' *)
              end)
          | right _ => R w
          end)
      end eq_refl).
      eapply remove_min_decreases.
      exact Heq.
      Unshelve.
      exact C.
  Defined.
  





  




