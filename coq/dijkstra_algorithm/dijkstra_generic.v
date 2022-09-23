(* This file encodes Dijkstra Generic
  algorithm, shown in the figure 6, from the paper On the Forwarding
  Paths Produced by Internt Routing Algorithms 
*)
Require Import 
  List ListSet PeanoNat
  Vector Fin.

Section Computation.

  (* state captures all the information *)
  Record state :=
    mk_state 
    {
        

    }.

  Definition dijkstra_one_step : state -> state. 
  (* definition goes here *)

  (* it computes f^n (init_state) *)
  Definition dijkstra : state -> state :=
    iter n dijkstra_one_step initial_state. 


End Computation.

  




