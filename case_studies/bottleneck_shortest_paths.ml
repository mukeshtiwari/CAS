(* This file attempts to use CAS to explore this paper. 

Bottleneck shortest paths
on a partially ordered scale
Jérôme Monnot and Olivier Spanjaard 
LAMSADE - Université Paris Dauphine, Place du Maréchal De Lattre de Tassigny,
75775 Paris Cedex 16, France.
(e-mail: {monnot, spanjaar}@lamsade.dauphine.fr)
Received: June 2002 / Revised version: March 2003

 *) 
open Cas;;
open Describe;;
open Matrix_solver;;

let bs_bw_x_sp =
  mcas_bs_add_zero
    (mcas_bs_product (mcas_bs_add_one mcas_max_min infinity) mcas_min_plus)
    infinity;;

let os_bw_x_sp = mcas_os_from_bs_left bs_bw_x_sp;;

let moo_bw_x_sp = mcas_minset_union_lift os_bw_x_sp;;

let test1 = mcas_os_from_bs_left moo_bw_x_sp;;
  
let test2 = mcas_minset_union_lift test1;;  
(*

mcas_bs_describe_fully test2;; 
Class : Dioid
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   [[inr((inr(0), 0))]].[[inr((inl(INF), 1))]] = [[inr((inr(0), 0))], [inr((inl(INF), 1))]]
Not Left Cancellative: 
   [[inr((inr(0), 0))], [inr((inl(INF), 1))]].[[inr((inr(0), 0))]] = [[inr((inl(INF), 1))], [inr((inr(0), 0))]]
   [[inr((inr(0), 0))], [inr((inl(INF), 1))]].[[inr((inl(INF), 1))]] = [[inr((inr(0), 0))], [inr((inl(INF), 1))]]
   [[inr((inr(0), 0))]] <> [[inr((inl(INF), 1))]]
Not Right Cancellative: 
   [[inr((inr(0), 0))]].[[inr((inr(0), 0))], [inr((inl(INF), 1))]] = [[inr((inr(0), 0))], [inr((inl(INF), 1))]]
   [[inr((inl(INF), 1))]].[[inr((inr(0), 0))], [inr((inl(INF), 1))]] = [[inr((inr(0), 0))], [inr((inl(INF), 1))]]
   [[inr((inr(0), 0))]] <> [[inr((inl(INF), 1))]]
Not Left Constant: 
   [].[[]] = [[]]
   [].[] = []
Not Right Constant: 
   [[]].[] = [[]]
   [].[] = []
Not Anti Left: 
   [].[] = []
Not Anti Right: 
   [].[] = []
Not Is Left: 
   [].[[]] = [[]]
Not Is Right: 
   [[]].[] = [[]]
Multiplicative properties:
-------------------------
Not Idempotent: 
   [[inr((inl(INF), 1))]].[[inr((inl(INF), 1))]] = [[inr((inl(INF), 2))]]
Commutative
Not Selective: 
   [[inr((inl(INF), 1))]].[[inr((inl(INF), 1))]] = [[inr((inl(INF), 2))]]
Not Left Cancellative: 
   [].[[]] = []
   [].[[inl(INF)]] = []
   [[]] <> [[inl(INF)]]
Not Right Cancellative: 
   [[]].[] = []
   [[inl(INF)]].[] = []
   [[]] <> [[inl(INF)]]
Not Left Constant: 
   [[]].[[]] = [[]]
   [[]].[] = []
Not Right Constant: 
   [[]].[[]] = [[]]
   [].[[]] = []
Not Anti Left: 
   [].[] = []
Not Anti Right: 
   [].[] = []
Not Is Left: 
   [[]].[] = []
Not Is Right: 
   [].[[]] = []
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Left_Right Absorptive 
Right_Left Absorptive
Right_Right Absorptive 

*) 
