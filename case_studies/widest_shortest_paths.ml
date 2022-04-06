
open Cas;;
open Describe;;
open Matrix_solver;; 

let widest_shortest_paths =
  mcas_bs_add_zero
    (mcas_bs_llex_product mcas_min_plus (mcas_bs_add_one mcas_max_min infinity))
    infinity;;
  
(* now, inspect this algebra 

mcas_bs_describe_fully widest_shortest_paths;;

Class : Selective Dioid
Carrier set:
{INF} + ((nat) * ({INF} + (nat)))
Additive properties:
--------------------
Idempotent
Commutative
Selective 
Not Left Cancellative: 
   inr((0, inl(INF))).inr((0, inl(INF))) = inr((0, inl(INF)))
   inr((0, inl(INF))).inl(INF) = inr((0, inl(INF)))
   inr((0, inl(INF))) <> inl(INF)
Not Right Cancellative: 
   inr((0, inl(INF))).inr((0, inl(INF))) = inr((0, inl(INF)))
   inl(INF).inr((0, inl(INF))) = inr((0, inl(INF)))
   inr((0, inl(INF))) <> inl(INF)
Not Left Constant: 
   inl(INF).inr((0, inl(INF))) = inr((0, inl(INF)))
   inl(INF).inl(INF) = inl(INF)
Not Right Constant: 
   inr((0, inl(INF))).inl(INF) = inr((0, inl(INF)))
   inl(INF).inl(INF) = inl(INF)
Not Anti Left: 
   inl(INF).inl(INF) = inl(INF)
Not Anti Right: 
   inl(INF).inl(INF) = inl(INF)
Not Is Left: 
   inl(INF).inr((0, inl(INF))) = inr((0, inl(INF)))
Not Is Right: 
   inr((0, inl(INF))).inl(INF) = inr((0, inl(INF)))
Identity = inl(INF)
Annihilator = inr((0, inl(INF)))
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr((1, inl(INF))).inr((1, inl(INF))) = inr((2, inl(INF)))
Commutative
Not Selective: 
   inr((0, inr(0))).inr((1, inl(INF))) = inr((1, inr(0)))
Not Left Cancellative: 
   inl(INF).inr((0, inl(INF))) = inl(INF)
   inl(INF).inr((1, inl(INF))) = inl(INF)
   inr((0, inl(INF))) <> inr((1, inl(INF)))
Not Right Cancellative: 
   inr((0, inl(INF))).inl(INF) = inl(INF)
   inr((1, inl(INF))).inl(INF) = inl(INF)
   inr((0, inl(INF))) <> inr((1, inl(INF)))
Not Left Constant: 
   inr((0, inl(INF))).inr((0, inl(INF))) = inr((0, inl(INF)))
   inr((0, inl(INF))).inl(INF) = inl(INF)
Not Right Constant: 
   inr((0, inl(INF))).inr((0, inl(INF))) = inr((0, inl(INF)))
   inl(INF).inr((0, inl(INF))) = inl(INF)
Not Anti Left: 
   inl(INF).inr((0, inl(INF))) = inl(INF)
Not Anti Right: 
   inr((0, inl(INF))).inl(INF) = inl(INF)
Not Is Left: 
   inr((0, inl(INF))).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr((0, inl(INF))) = inl(INF)
Identity = inr((0, inl(INF)))
Annihilator = inl(INF)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Left_Right Absorptive 
Right_Left Absorptive
Right_Right Absorptive 

*)

(* now, configure an adjacency matrix *)

let widest_shortest_paths_solver = instantiate_algorithm widest_shortest_paths Matrix_power;; 

let widest_shortest_paths_solve_adj_list adjl =
  match widest_shortest_paths_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "widest_shortest_paths_solve_adj_list : internal error";; 

(*     (1, 2) 
    0  ------  1 
      |       |
(1,1) |       | (1, 2)
      |       |
      2 ------ 3
       (1,1)
*) 
let adj_1 = { adj_size = 4;
	      adj_list = [
		          (0, [(1, Inr (1, Inr 2)); (2, Inr (1, Inr 1))]);
		          (1, [(0, Inr (1, Inr 2)); (3, Inr (1, Inr 2))]);
		          (2, [(0, Inr (1, Inr 1)); (3, Inr (1, Inr 1))]); 
			  (3, [(1, Inr (1, Inr 2)); (2, Inr (1, Inr 1))]) 
			 ]
	    } ;;
let sol_1 = widest_shortest_paths_solve_adj_list adj_1;; 
(*
list_sq_matrix sol_1;; 

- : (int * int * (int * int Cas.with_constant) Cas.with_constant) list =
[(0, 0,
  Inr
   (0,
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']}));
 (0, 1, Inr (1, Inr 2)); (0, 2, Inr (1, Inr 1)); (0, 3, Inr (2, Inr 2));
 (1, 0, Inr (1, Inr 2));
 (1, 1,
  Inr
   (0,
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']}));
 (1, 2, Inr (2, Inr 1)); (1, 3, Inr (1, Inr 2)); (2, 0, Inr (1, Inr 1));
 (2, 1, Inr (2, Inr 1));
 (2, 2,
  Inr
   (0,
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']}));
 (2, 3, Inr (1, Inr 1)); (3, 0, Inr (2, Inr 2)); (3, 1, Inr (1, Inr 2));
 (3, 2, Inr (1, Inr 1));
 (3, 3,
  Inr
   (0,
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']}))]
# 
*)



