
open Cas;;
open Describe;;
open Matrix_solver;; 

let widest_shortest_paths =
  mcas_bs_add_zero
    (mcas_bs_llex_product mcas_min_plus (mcas_bs_add_one mcas_max_min infinity))
    infinity;;
  
(* now, inspect this algebra 

mcas_bs_describe_fully widest_shortest_paths;;
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



