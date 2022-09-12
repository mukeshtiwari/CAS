
open Cas;;
open Describe;;
open Matrix_solver;;

(* MOO = Multi-Objective Optimization 

  Example taken from the SIGCOMM 2020 paper. 

*)   

let bs_bw_x_sp = mcas_bs_product
		   (mcas_bs_add_one mcas_max_min infinity)
		   (mcas_bs_add_zero mcas_min_plus infinity);;

let os_bw_x_sp = mcas_os_from_bs_left bs_bw_x_sp;;

let moo_bw_x_sp = mcas_minset_union_lift os_bw_x_sp;;

(*
mcas_bs_describe moo_bw_x_sp;; 

mcas_bs_describe_fully moo_bw_x_sp;; 

*)   

(* now, configure an adjacency matrix *)

let moo_bw_x_sp_solver = instantiate_algorithm moo_bw_x_sp Matrix_power;; 

let moo_bw_x_sp_solve_adj_list adjl =
  match moo_bw_x_sp_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "moo_bw_x_sp_solve_adj_list : internal error";; 

(*  

 ({INF} + (({INF} + int) * int )) set

 *)
let mk_w b d = [Inr (Inr b, d)] ;;

let sigcomm2020_with_paths_v2_figure_3 = 
  (* 0 = u, 1 = w, 2 = x, 3 = v*)
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mk_w 5 1); (3, mk_w 10 3)]);
    
    (1, [(2, mk_w 20 1)]);
    
    (3, [(1, mk_w 20 4); (2, mk_w 10 2)])
  ]};; 

let sol_1 = moo_bw_x_sp_solve_adj_list sigcomm2020_with_paths_v2_figure_3;; 
(*
list_sq_matrix sol_1;; 

[(0, 0,
  [Inr
    (Inl
      {constant_ascii = ['I'; 'N'; 'F'];
       constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
     0)]);
 (0, 1, [Inr (Inr 10, 7); Inr (Inr 5, 1)]);
 (0, 2, [Inr (Inr 10, 5); Inr (Inr 5, 2)]); (0, 3, [Inr (Inr 10, 3)]);
 (1, 0, []);
 (1, 1,
  [Inr
    (Inl
      {constant_ascii = ['I'; 'N'; 'F'];
       constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
     0)]);
 (1, 2, [Inr (Inr 20, 1)]); (1, 3, []); (2, 0, []); (2, 1, []);
 (2, 2,
  [Inr
    (Inl
      {constant_ascii = ['I'; 'N'; 'F'];
       constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
     0)]);
 (2, 3, []); (3, 0, []); (3, 1, [Inr (Inr 20, 4)]);
 (3, 2, [Inr (Inr 10, 2); Inr (Inr 20, 5)]);
 (3, 3,
  [Inr
    (Inl
      {constant_ascii = ['I'; 'N'; 'F'];
       constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
     0)])]


 *)

let empty = [];;
let v1 = [Inr (1, Inr 1)];;
let v2 = [Inr (100, Inr 100)];;   

let plus =
  match moo_bw_x_sp with
  | BS_dioid d -> d.dioid_plus
  | _ -> error "plus: nope!" ;; 

let times =
  match moo_bw_x_sp with
  | BS_dioid d -> d.dioid_times
  | _ -> error "times: nope!" ;; 
  
(* Now, attempt to add paths

let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;
let sg_path = mcas_sg_concat eqv_edge;; 
let sg_paths = mcas_sg_lift sg_path 
let os_paths = mcas_os_trivial_from_sg sg_paths
let os_bw_x_sp_lex_paths = mcas_os_left_lex os_bw_x_sp os_paths 
let moo_bw_x_sp_lex_paths = mcas_minset_union_lift os_bw_x_sp_lex_paths;;
 *) 
