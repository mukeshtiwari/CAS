(* This file attempts to use CAS to explore this paper. 

Bottleneck shortest paths on a partially ordered scale
Jérôme Monnot and Olivier Spanjaard 
LAMSADE - Université Paris Dauphine, Place du Maréchal De Lattre de Tassigny,
75775 Paris Cedex 16, France.
(e-mail: {monnot, spanjaar}@lamsade.dauphine.fr)
Received: June 2002 / Revised version: March 2003

Note: this is not an easy paper to read. 
I think this is a reasonable CAS encoding of 
the semiring described in Section 6. 

 *) 
open Cas;;
open Describe;;
open Matrix_solver;;

let or_max = mcas_left_order_from_sg mcas_sg_max;;   

let order_E = mcas_or_add_bottom (mcas_or_product or_max or_max) infinity;;

let maxset = mcas_sg_minset_union order_E;;

let os_maxset = mcas_os_from_sg_right maxset;;

(*  bottleneck_shortest_paths has OCaml type 
     (int * int) Cas.with_constant Cas.finite_set Cas.finite_set Cas.bs_mcas
*)   
let bottleneck_shortest_paths = mcas_minset_union_lift os_maxset;;

(*
 mcas_bs_describe_fully bottleneck_shortest_paths;; 
Class : Dioid
Carrier set:
(Ast_or_of_os : fix me) minimal_set
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   [[inr((1, 0))]].[[inr((0, 1))]] = [[inr((1, 0))], [inr((0, 1))]]
Not Left Cancellative: 
   [[inr((1, 0))], [inr((0, 1))]].[[inr((1, 0))]] = [[inr((0, 1))], [inr((1, 0))]]
   [[inr((1, 0))], [inr((0, 1))]].[[inr((0, 1))]] = [[inr((1, 0))], [inr((0, 1))]]
   [[inr((1, 0))]] <> [[inr((0, 1))]]
Not Right Cancellative: 
   [[inr((1, 0))]].[[inr((1, 0))], [inr((0, 1))]] = [[inr((1, 0))], [inr((0, 1))]]
   [[inr((0, 1))]].[[inr((1, 0))], [inr((0, 1))]] = [[inr((1, 0))], [inr((0, 1))]]
   [[inr((1, 0))]] <> [[inr((0, 1))]]
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
Identity = []
Annihilator = [[]]
Multiplicative properties:
-------------------------
Idempotent
Commutative
Not Selective: 
   [[inr((1, 0))]].[[inr((0, 1))]] = [[inr((1, 0)), inr((0, 1))]]
Not Left Cancellative: 
   [[inr((1, 0)), inr((0, 1))]].[[inr((1, 0))]] = [[inr((0, 1)), inr((1, 0))]]
   [[inr((1, 0)), inr((0, 1))]].[[inr((0, 1))]] = [[inr((1, 0)), inr((0, 1))]]
   [[inr((1, 0))]] <> [[inr((0, 1))]]
Not Right Cancellative: 
   [[inr((1, 0))]].[[inr((1, 0)), inr((0, 1))]] = [[inr((1, 0)), inr((0, 1))]]
   [[inr((0, 1))]].[[inr((1, 0)), inr((0, 1))]] = [[inr((1, 0)), inr((0, 1))]]
   [[inr((1, 0))]] <> [[inr((0, 1))]]
Not Left Constant: 
   [[]].[] = []
   [[]].[[]] = [[]]
Not Right Constant: 
   [].[[]] = []
   [[]].[[]] = [[]]
Not Anti Left: 
   [].[] = []
Not Anti Right: 
   [].[] = []
Not Is Left: 
   [[]].[] = []
Not Is Right: 
   [].[[]] = []
Identity = [[]]
Annihilator = []
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Left_Right Absorptive 
Right_Left Absorptive
Right_Right Absorptive 
*)   

let bsp_solver = instantiate_algorithm bottleneck_shortest_paths Matrix_power;; 

let bsp_solve_adj_list adjl =
  match bsp_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "bsp_solve_adj_list : internal error";; 

let mk_w b d = [[Inr (b, d)]] ;;

(*

This is Figure 3.1 from the paper. 
Node "s" is here 0, and node "t" is here 6. 
The values a < b < c have been replaced by 1, 2, 3. 

w(0,1) = (1, 3)
w(0,2) = (1, 1)
w(1,3) = (3, 1) 
w(2,3) = (2, 3) 
w(3,4) = (1, 1)
w(3,5) = (2, 2)
w(4,6) = (1, 1) 
w(5,6) = (3, 2) 

   1     4
  / \   / \
 /   \ /   \
0     3     6
 \   / \   /
  \ /   \ /
   2     5
*)

let plus =
  match bottleneck_shortest_paths with
  | BS_dioid d -> d.dioid_plus
  | _ -> error "plus: nope!" ;; 

let times =
  match bottleneck_shortest_paths with
  | BS_dioid d -> d.dioid_times
  | _ -> error "times: nope!" ;; 
  
let upper = [[Inr (1, 1); Inr(1,3); Inr(3,1)]];;
let lower = [[Inr(1, 1); Inr(2,3); Inr(2,2); Inr(3,2)]];; 

(* from example in Section 4.1.  
   This seems to work. 

plus upper lower;;
- : (int * int) Cas.with_constant Cas.finite_set Cas.finite_set =
[[Inr (1, 1); Inr (1, 3); Inr (3, 1)]]

 *) 

  
let figure_3_1 = 
  { adj_size = 7;
    adj_list = 
  [
    (0, [(1, mk_w 1 3); (2, mk_w 1 1)]);
    (1, [(3, mk_w 3 1)]);
    (2, [(3, mk_w 2 3)]);    
    (3, [(4, mk_w 1 1); (5, mk_w 2 2)]); 
    (4, [(6, mk_w 1 1)]);
    (5, [(6, mk_w 3 2)])
  ]};; 

let sol_1 = bsp_solve_adj_list figure_3_1;; 
(*

Note : the 0 to 6 value is not exactly 
what the paper seems to imply. 
This is because all paths are explored, not just 
the upper and lower paths. 

#print_length 1000;;
list_sq_matrix sol_1;; 

[(0, 0, [[]]); 
 (0, 1, [[Inr (1, 3)]]); 
 (0, 2, [[Inr (1, 1)]]);
 (0, 3, [[Inr (2, 3)]; [Inr (3, 1); Inr (1, 3)]]);
 (0, 4, [[Inr (2, 3)]; [Inr (3, 1); Inr (1, 3)]]);
 (0, 5, [[Inr (2, 3)]; [Inr (2, 2); Inr (3, 1); Inr (1, 3)]]);
 (0, 6, [[Inr (2, 3)]; [Inr (3, 1); Inr (1, 3)]]); 
 (1, 0, []); 
 (1, 1, [[]]);
 (1, 2, []); 
 (1, 3, [[Inr (3, 1)]]); 
 (1, 4, [[Inr (3, 1)]]);
 (1, 5, [[Inr (2, 2); Inr (3, 1)]]); 
 (1, 6, [[Inr (3, 1)]]); 
 (2, 0, []);
 (2, 1, []); 
 (2, 2, [[]]); 
 (2, 3, [[Inr (2, 3)]]); 
 (2, 4, [[Inr (2, 3)]]);
 (2, 5, [[Inr (2, 3)]]); 
 (2, 6, [[Inr (2, 3)]]); 
 (3, 0, []); 
 (3, 1, []);
 (3, 2, []); 
 (3, 3, [[]]); 
 (3, 4, [[Inr (1, 1)]]); 
 (3, 5, [[Inr (2, 2)]]);
 (3, 6, [[Inr (1, 1)]]); 
 (4, 0, []); 
 (4, 1, []); 
 (4, 2, []); 
 (4, 3, []);
 (4, 4, [[]]); 
 (4, 5, []); 
 (4, 6, [[Inr (1, 1)]]); 
 (5, 0, []); 
 (5, 1, []);
 (5, 2, []); 
 (5, 3, []); 
 (5, 4, []); 
 (5, 5, [[]]); 
 (5, 6, [[Inr (3, 2)]]);
 (6, 0, []); 
 (6, 1, []); 
 (6, 2, []); 
 (6, 3, []); 
 (6, 4, []); 
 (6, 5, []);
 (6, 6, [[]])]

  
 *) 

