
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.nat. 
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.sg.concat. 
Require Import CAS.coq.sg.product. 
Require Import CAS.coq.bs.product_product. 
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.max_min.
Require Import CAS.coq.bs.cast_up.

Definition bs_min_plus := bs_from_selective_presemiring selective_presemiring_min_plus. 
Definition bs_max_min := bs_from_selective_distributive_prelattice selective_distributive_prelattice_max_min.

Open Scope nat.

Definition bs1 := bs_product bs_min_plus bs_max_min.

Print bs1.

Eval hnf in bs1.

Eval cbv in bs_plus_certs bs1.

Eval cbv in bs_times_certs bs1. 

Eval cbv in bs_certs bs1. 

Definition plus := bs_plus bs1.

Eval cbv in plus (1, 2) (3, 4).

Definition times := bs_times bs1.

Eval cbv in times (1, 2) (3, 4).

(*
let bs_sigcomm2020_with_paths = 
   bs_add_one self (
          bs_min_set_union_lift_from_posg (
	      posg_extend_right (posg_from_bs_left bs_bw_times_sp) (sg_sequence (ti_pair ti_int ti_int))))
*)

Definition edge_paths := sg_concat (eqv_product eqv_eq_nat eqv_eq_nat).

Eval hnf in edge_paths. 
Eval cbv in sg_certs edge_paths. 

(* to do 

  1) posg_from_bs_left
  2) posg_extend_right
  3) finish bs_min_set_union_lift_from_posg

*) 