
open Cas;;
open Describe;;
open Matrix_solver;; 


(* we need to add a zero to min-plus *) 
let shortest_paths = mcas_bs_add_zero mcas_min_plus infinity;;
  
(* now, inspect this algebra 

mcas_bs_describe_fully shortest_paths;;
Class : Selective Dioid
Additive properties:
--------------------
Idempotent
Commutative
Selective 
Not Left Cancellative: 
   inr(0).inr(0) = inr(0)
   inr(0).inl(INF) = inr(0)
   inr(0) <> inl(INF)
Not Right Cancellative: 
   inr(0).inr(0) = inr(0)
   inl(INF).inr(0) = inr(0)
   inr(0) <> inl(INF)
Not Left Constant: 
   inl(INF).inr(0) = inr(0)
   inl(INF).inl(INF) = inl(INF)
Not Right Constant: 
   inr(0).inl(INF) = inr(0)
   inl(INF).inl(INF) = inl(INF)
Not Anti Left: 
   inl(INF).inl(INF) = inl(INF)
Not Anti Right: 
   inl(INF).inl(INF) = inl(INF)
Not Is Left: 
   inl(INF).inr(0) = inr(0)
Not Is Right: 
   inr(0).inl(INF) = inr(0)
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr(1).inr(1) = inr(2)
Commutative
Not Selective: 
   inr(1).inr(1) = inr(2)
Not Left Cancellative: 
   inl(INF).inr(0) = inl(INF)
   inl(INF).inr(1) = inl(INF)
   inr(0) <> inr(1)
Not Right Cancellative: 
   inr(0).inl(INF) = inl(INF)
   inr(1).inl(INF) = inl(INF)
   inr(0) <> inr(1)
Not Left Constant: 
   inr(0).inr(0) = inr(0)
   inr(0).inl(INF) = inl(INF)
Not Right Constant: 
   inr(0).inr(0) = inr(0)
   inl(INF).inr(0) = inl(INF)
Not Anti Left: 
   inl(INF).inr(0) = inl(INF)
Not Anti Right: 
   inr(0).inl(INF) = inl(INF)
Not Is Left: 
   inr(0).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr(0) = inl(INF)
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

let shortest_paths_solver = instantiate_algorithm shortest_paths Matrix_power;; 

let shortest_paths_solve_adj_list adjl =
  match shortest_paths_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "shortest_paths_solve_adj_list : internal error";; 

(*       2 
    0 ------> 1 
    |         |
  1 |         | 2
    |         |
    \/       \/
    2 ------> 3
         1
*) 
let adj_1 = { adj_size = 4;
	      adj_list = [
		          (0, [(1, Inr 2); (2, Inr 1)]);
		          (1, [(3, Inr 2)]);
		          (2, [(3, Inr 1)])
			 ]
	    } ;;
let mat_1 = square_matrix_from_adj_list shortest_paths adj_1;;
let sol_1 = shortest_paths_solve_adj_list adj_1;; 
(*
list_sq_matrix mat_1;; 

list_sq_matrix mat_1;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1);
 (0, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 1, Inr 0);
 (1, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 3, Inr 2);
 (2, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0); (2, 3, Inr 1);
 (3, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 3, Inr 0)]



list_sq_matrix sol_1;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1); (0, 3, Inr 2);
 (1, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 1, Inr 0);
 (1, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 3, Inr 2);
 (2, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0); (2, 3, Inr 1);
 (3, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 3, Inr 0)]
*)

  
(*       2 
    0 ------- 1 
    |         |
  1 |         | 2
    |         |
    2 ------- 3
         1
*) 
let adj_2 = { adj_size = 4;
	      adj_list = [
		          (0, [(1, Inr 2); (2, Inr 1)]);
		          (1, [(0, Inr 2); (3, Inr 2)]);
		          (2, [(0, Inr 1); (3, Inr 1)]);
		          (3, [(1, Inr 2); (2, Inr 1)])
			 ]
	    } ;;
let mat_2 = square_matrix_from_adj_list shortest_paths adj_2;;
let sol_2 = shortest_paths_solve_adj_list adj_2;;

(*
list_sq_matrix mat_2;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1);
 (0, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 0, Inr 2); (1, 1, Inr 0);
 (1, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 3, Inr 2); (2, 0, Inr 1);
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0); (2, 3, Inr 1);
 (3, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1, Inr 2); (3, 2, Inr 1); (3, 3, Inr 0)]

list_sq_matrix sol_2;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1); (0, 3, Inr 2); (1, 0, Inr 2);
 (1, 1, Inr 0); (1, 2, Inr 3); (1, 3, Inr 2); (2, 0, Inr 1); (2, 1, Inr 3);
 (2, 2, Inr 0); (2, 3, Inr 1); (3, 0, Inr 2); (3, 1, Inr 2); (3, 2, Inr 1);
 (3, 3, Inr 0)]

 *)   
