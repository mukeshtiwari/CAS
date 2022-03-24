
open Cas;;
open Describe;;
open Matrix_solver;;

(* attempt to add paths to routes of moo1.ml 
*)

let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;

let sg_paths = mcas_sg_concat eqv_edge;;

let bs_paths = mcas_bs_union_lift sg_paths;;  (* +-id = {} = x-ann. x-id={[]}, no +-ann *)

(*

 *) 

  
(*
mcas_bs_describe_fully bs_paths;;;
Class : Semiring
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   {[]}.{[(0, 0)]} = {[], [(0, 0)]}
Not Left Cancellative: 
   {[], [(0, 0)]}.{[]} = {[(0, 0)], []}
   {[], [(0, 0)]}.{[(0, 0)]} = {[], [(0, 0)]}
   {[]} <> {[(0, 0)]}
Not Right Cancellative: 
   {[]}.{[], [(0, 0)]} = {[], [(0, 0)]}
   {[(0, 0)]}.{[], [(0, 0)]} = {[], [(0, 0)]}
   {[]} <> {[(0, 0)]}
Not Left Constant: 
   {}.{[]} = {[]}
   {}.{} = {}
Not Right Constant: 
   {[]}.{} = {[]}
   {}.{} = {}
Not Anti Left: 
   {[]}.{[]} = {[]}
Not Anti Right: 
   {[]}.{[]} = {[]}
Not Is Left: 
   {}.{[]} = {[]}
Not Is Right: 
   {[]}.{} = {[]}
Multiplicative properties:
-------------------------
Not Idempotent: 
   {[(0, 0)], [(1, 0)]}.{[(0, 0)], [(1, 0)]} = {[(0, 0), (0, 0)], [(0, 0), (1, 0)], [(1, 0), (0, 0)], [(1, 0), (1, 0)]}
Not Commutative: 
   {[(0, 0)]}.{[(1, 0)]} = {[(0, 0), (1, 0)]}
   {[(1, 0)]}.{[(0, 0)]} = {[(1, 0), (0, 0)]}
Not Selective: 
   {[(0, 0)]}.{[(0, 0)]} = {[(0, 0), (0, 0)]}
Not Left Cancellative: 
   {}.{[]} = {}
   {}.{[(0, 0)]} = {}
   {[]} <> {[(0, 0)]}
Not Right Cancellative: 
   {[]}.{} = {}
   {[(0, 0)]}.{} = {}
   {[]} <> {[(0, 0)]}
Not Left Constant: 
   {[]}.{[]} = {[]}
   {[]}.{} = {}
Not Right Constant: 
   {[]}.{[]} = {[]}
   {}.{[]} = {}
Not Anti Left: 
   {}.{} = {}
Not Anti Right: 
   {}.{} = {}
Not Is Left: 
   {[]}.{} = {}
Not Is Right: 
   {}.{[]} = {}
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Not Left left Absorptive: 
   a = {[]}
   b = {[(0, 0)]}
   a <> a + a*b = rhs: 
   a*b = {[(0, 0)]}
   rhs = {[], [(0, 0)]}
Not Left Right Absorptive: 
   a = {[]}
   b = {[(0, 0)]}
   a <> a + b*a = rhs: 
   b*a = {[(0, 0)]}
   rhs = {[], [(0, 0)]}
Not Right left Absorptive: 
   a = {[]}
   b = {[(0, 0)]}
   a <> a*b + a = rhs: 
   a*b = {[(0, 0)]}
   rhs = {[(0, 0)], []}
Not Right left Absorptive: 
   a = {[]}
   b = {[(0, 0)]}
   a <> b*a + a = rhs: 
   b*a = {[(0, 0)]}
   rhs = {[(0, 0)], []}



mcas_os_from_bs_left bs_paths;;
- : (int * int) list Cas.finite_set Cas.os_mcas =
OS_Error
 [['m'; 'c'; 'a'; 's'; '_'; 'p'; 'o'; 's'; 'g'; '_'; 'f'; 'r'; 'o'; 'm'; '_';
   'b'; 's'; '_'; 'l'; 'e'; 'f'; 't'; ' '; ':'; ' '; 't'; 'h'; 'i'; 's'; ' ';
   'c'; 'o'; 'm'; 'b'; 'i'; 'n'; 'a'; 't'; 'o'; 'r'; ' '; '('; 'c'; 'u'; 'r';
   'r'; 'e'; 'n'; 't'; 'l'; 'y'; ')'; ' '; 'r'; 'e'; 'q'; 'u'; 'i'; 'r'; 'e';
   's'; ' '; 'a'; ' '; 'd'; 'i'; 'o'; 'i'; 'd']]

WHY? WHY? WHY? WHY? WHY? 

 *) 


let bs_bw_x_sp = mcas_bs_product (mcas_bs_add_one mcas_max_min infinity) mcas_min_plus;; 

let bs_bw_x_sp_lex_paths = mcas_bs_llex_product bs_bw_x_sp bs_paths;;   (* BS_bs_CI *)

(*
mcas_bs_describe_fully bs_bw_x_sp_lex_paths;;
Class : Commuative and Idempotent Bi-semigroup
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   ((inr(0), 0), {[]}).((inl(INF), 1), {[]}) = ((inl(INF), 0), {})
Not Left Cancellative: 
   ((inl(INF), 0), {}).((inr(0), 0), {[]}) = ((inl(INF), 0), {})
   ((inl(INF), 0), {}).((inl(INF), 1), {[]}) = ((inl(INF), 0), {})
   ((inr(0), 0), {[]}) <> ((inl(INF), 1), {[]})
Not Right Cancellative: 
   ((inr(0), 0), {[]}).((inl(INF), 0), {}) = ((inl(INF), 0), {})
   ((inl(INF), 1), {[]}).((inl(INF), 0), {}) = ((inl(INF), 0), {})
   ((inr(0), 0), {[]}) <> ((inl(INF), 1), {[]})
Not Left Constant: 
   ((inr(0), 0), {[]}).((inl(INF), 0), {[]}) = ((inl(INF), 0), {[]})
   ((inr(0), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
Not Right Constant: 
   ((inl(INF), 0), {[]}).((inr(0), 0), {[]}) = ((inl(INF), 0), {[]})
   ((inr(0), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
Not Anti Left: 
   ((inl(INF), 0), {[]}).((inl(INF), 0), {[]}) = ((inl(INF), 0), {[]})
Not Anti Right: 
   ((inl(INF), 0), {[]}).((inl(INF), 0), {[]}) = ((inl(INF), 0), {[]})
Not Is Left: 
   ((inr(0), 0), {[]}).((inl(INF), 0), {[]}) = ((inl(INF), 0), {[]})
Not Is Right: 
   ((inl(INF), 0), {[]}).((inr(0), 0), {[]}) = ((inl(INF), 0), {[]})
Multiplicative properties:
-------------------------
Not Idempotent: 
   ((inl(INF), 1), {[]}).((inl(INF), 1), {[]}) = ((inl(INF), 2), {[]})
Not Commutative: 
   ((inl(INF), 0), {[(0, 0)]}).((inl(INF), 0), {[(1, 0)]}) = ((inl(INF), 0), {[(0, 0), (1, 0)]})
   ((inl(INF), 0), {[(1, 0)]}).((inl(INF), 0), {[(0, 0)]}) = ((inl(INF), 0), {[(1, 0), (0, 0)]})
Not Selective: 
   ((inl(INF), 0), {}).((inr(0), 0), {[]}) = ((inr(0), 0), {})
Not Left Cancellative: 
   ((inr(0), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
   ((inr(0), 0), {[]}).((inl(INF), 0), {[]}) = ((inr(0), 0), {[]})
   ((inr(0), 0), {[]}) <> ((inl(INF), 0), {[]})
Not Right Cancellative: 
   ((inr(0), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
   ((inl(INF), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
   ((inr(0), 0), {[]}) <> ((inl(INF), 0), {[]})
Not Left Constant: 
   ((inl(INF), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
   ((inl(INF), 0), {[]}).((inr(1), 0), {[]}) = ((inr(1), 0), {[]})
Not Right Constant: 
   ((inr(0), 0), {[]}).((inl(INF), 0), {[]}) = ((inr(0), 0), {[]})
   ((inr(1), 0), {[]}).((inl(INF), 0), {[]}) = ((inr(1), 0), {[]})
Not Anti Left: 
   ((inr(0), 0), {}).((inl(INF), 0), {}) = ((inr(0), 0), {})
Not Anti Right: 
   ((inl(INF), 0), {}).((inr(0), 0), {}) = ((inr(0), 0), {})
Not Is Left: 
   ((inl(INF), 0), {[]}).((inr(0), 0), {[]}) = ((inr(0), 0), {[]})
Not Is Right: 
   ((inr(0), 0), {[]}).((inl(INF), 0), {[]}) = ((inr(0), 0), {[]})
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Not Left Distributive:
   a = ((inr(0), 0), {[]})
   b = ((inr(0), 0), {[]})
   c = ((inl(INF), 0), {})
   lhs = a*(b + c) <> a*b + a*c = rhs: 
   b + c = ((inl(INF), 0), {})
   a*b = ((inr(0), 0), {[]})
   a*c = ((inr(0), 0), {})
   lhs = ((inr(0), 0), {})
   rhs = ((inr(0), 0), {[]})
Not Right Distributive: 
   a = ((inr(0), 0), {[]})
   b = ((inr(0), 0), {[]})
   c = ((inl(INF), 0), {})
   lhs = (b + c)*a <> b*a + c*a = rhs: 
   b + c = ((inl(INF), 0), {})
   b*a = ((inr(0), 0), {[]})
   c*a = ((inr(0), 0), {})
   lhs = ((inr(0), 0), {})
   rhs = ((inr(0), 0), {[]})
Not Left left Absorptive: 
   a = ((inr(0), 0), {[]})
   b = ((inl(INF), 0), {[(0, 0)]})
   a <> a + a*b = rhs: 
   a*b = ((inr(0), 0), {[(0, 0)]})
   rhs = ((inr(0), 0), {[], [(0, 0)]})
Not Left Right Absorptive: 
   a = ((inr(0), 0), {[]})
   b = ((inl(INF), 0), {[(0, 0)]})
   a <> a + b*a = rhs: 
   b*a = ((inr(0), 0), {[(0, 0)]})
   rhs = ((inr(0), 0), {[], [(0, 0)]})
Not Right left Absorptive: 
   a = ((inr(0), 0), {[]})
   b = ((inl(INF), 0), {[(0, 0)]})
   a <> a*b + a = rhs: 
   a*b = ((inr(0), 0), {[(0, 0)]})
   rhs = ((inr(0), 0), {[(0, 0)], []})
Not Right left Absorptive: 
   a = ((inr(0), 0), {[]})
   b = ((inl(INF), 0), {[(0, 0)]})
   a <> b*a + a = rhs: 
   b*a = ((inr(0), 0), {[(0, 0)]})
   rhs = ((inr(0), 0), {[(0, 0)], []})

 *)   

  

let bs_bw_x_sp =
  mcas_bs_add_zero
    (
    infinity;;

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
  
