open Cas;;
open Describe;;
open Matrix_solver;;
  
(* 
   This file contains the two examples from Section 4.8.1 
   of "Path Problems in Networks" by Baras and Theodorakopoulos. 

*) 
let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;

let bridges = mcas_bs_add_zero (mcas_bs_intersect_union eqv_edge) infinity;; 

(*
mcas_bs_describe_fully bridges ;; 

Class : Dioid
Carrier set:
{INF} + (((nat) * (nat)) set)
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   inr({(0, 0)}).inr({(1, 0)}) = inr({})
Not Left Cancellative: 
   inr({}).inr({(0, 0)}) = inr({})
   inr({}).inr({(1, 0)}) = inr({})
   inr({(0, 0)}) <> inr({(1, 0)})
Not Right Cancellative: 
   inr({(0, 0)}).inr({}) = inr({})
   inr({(1, 0)}).inr({}) = inr({})
   inr({(0, 0)}) <> inr({(1, 0)})
Not Left Constant: 
   inl(INF).inr({(0, 0)}) = inr({(0, 0)})
   inl(INF).inl(INF) = inl(INF)
Not Right Constant: 
   inr({(0, 0)}).inl(INF) = inr({(0, 0)})
   inl(INF).inl(INF) = inl(INF)
Not Anti Left: 
   inl(INF).inl(INF) = inl(INF)
Not Anti Right: 
   inl(INF).inl(INF) = inl(INF)
Not Is Left: 
   inl(INF).inr({(0, 0)}) = inr({(0, 0)})
Not Is Right: 
   inr({(0, 0)}).inl(INF) = inr({(0, 0)})
Identity = inl(INF)
Annihilator = inr({})
Multiplicative properties:
-------------------------
Idempotent
Commutative
Not Selective: 
   inr({(0, 0)}).inr({(1, 0)}) = inr({(0, 0), (1, 0)})
Not Left Cancellative: 
   inl(INF).inr({(0, 0)}) = inl(INF)
   inl(INF).inr({}) = inl(INF)
   inr({(0, 0)}) <> inr({})
Not Right Cancellative: 
   inr({(0, 0)}).inl(INF) = inl(INF)
   inr({}).inl(INF) = inl(INF)
   inr({(0, 0)}) <> inr({})
Not Left Constant: 
   inr({(0, 0)}).inr({(0, 0)}) = inr({(0, 0)})
   inr({(0, 0)}).inl(INF) = inl(INF)
Not Right Constant: 
   inr({(0, 0)}).inr({(0, 0)}) = inr({(0, 0)})
   inl(INF).inr({(0, 0)}) = inl(INF)
Not Anti Left: 
   inl(INF).inr({(0, 0)}) = inl(INF)
Not Anti Right: 
   inr({(0, 0)}).inl(INF) = inl(INF)
Not Is Left: 
   inr({(0, 0)}).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr({(0, 0)}) = inl(INF)
Identity = inr({})
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

let bridges_solver = instantiate_algorithm bridges Matrix_power;; 

let bridges_solve_adj_list adjl =
  match bridges_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "bridges_solve_adj_list : internal error";; 

let br_w i j = Inr [(i, j)] ;;

(*       
    0 ------> 3
    |      /  |
    |     /   | 
    |    /    |
    \/ \/    \/
     1 --- -> 2
         
*) 
  

let bridges_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, br_w 0 1); (3, br_w 0 3)]);
    
    (1, [(2, br_w 1 2)]);
    
    (3, [(1, br_w 3 1); (2, br_w 3 2)])
  ]};; 

let bridges_sol_1 = bridges_solve_adj_list bridges_adj_1;; 

  (*
list_sq_matrix bridges_sol_1;; 

Interpretation : if we remove link (0,3), then there is no path from 0 to 3. 
and if we remove link (1,2), then there is no path from 1 to 2. 

- : (int * int * (int * int) Cas.finite_set Cas.with_constant) list =
[(0, 0, Inr []); 
 (0, 1, Inr []); 
 (0, 2, Inr []); 
 (0, 3, Inr [(0, 3)]);
 (1, 0, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 1, Inr []); 
 (1, 2, Inr [(1, 2)]);
 (1, 3, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 0, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr []);
 (2, 3, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 0, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1, Inr [(3, 1)]); 
 (3, 2, Inr []); 
 (3, 3, Inr [])]

   *)

let vertex_cuts = mcas_bs_add_zero (mcas_bs_intersect_union mcas_eqv_eq_nat) infinity;; 

let vertex_cuts_solver = instantiate_algorithm vertex_cuts Matrix_power;; 

let vertex_cuts_solve_adj_list adjl =
  match vertex_cuts_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "vertex_cuts_solve_adj_list : internal error";; 

let vc_w i j = Inr [i; j] ;;

(*       
    0 ------> 3
    |      /  |
    |     /   | 
    |    /    |
    \/ \/    \/
     1 --- -> 2
         
*) 
  

let vertex_cuts_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, vc_w 0 1); (3, vc_w 0 3)]);
    
    (1, [(2, vc_w 1 2)]);
    
    (3, [(1, vc_w 3 1); (2, vc_w 3 2)])
  ]};; 

let vertex_cuts_sol_1 = vertex_cuts_solve_adj_list vertex_cuts_adj_1;; 

(*

Interpretation of  (1, 2, Inr [1; 2]) : if nodes 1 and 2 are deleted, then there will be no path from 1 to 2. 
OK, this is a boring network.... 

list_sq_matrix vertex_cuts_sol_1;; 
- : (int * int * int Cas.finite_set Cas.with_constant) list =
[(0, 0, Inr []); 
 (0, 1, Inr [0; 1]); 
 (0, 2, Inr [0; 2]); 
 (0, 3, Inr [0; 3]);
 (1, 0, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 1, Inr []); 
 (1, 2, Inr [1; 2]);
 (1, 3, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 0, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr []);
 (2, 3, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 0, Inl {constant_ascii = ['I'; 'N'; 'F']; constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1, Inr [3; 1]); 
 (3, 2, Inr [3; 2]); 
 (3, 3, Inr [])]   

*)   


(* let's try something a bit more interesting. 

    0 ------- 3 ------- 4 
    |                   |
    |                   | 
    |                   |
    |                   | 
    1 --------2         5
         
*) 
let vertex_cuts_adj_2 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, vc_w 0 1); (3, vc_w 0 3)]);
    (1, [(0, vc_w 1 0); (2, vc_w 1 2)]);
    (2, [(1, vc_w 2 1); (5, vc_w 2 5)]);    
    (3, [(0, vc_w 3 0); (4, vc_w 3 4)]);
    (4, [(3, vc_w 4 3); (5, vc_w 4 5)]);
    (5, [(4, vc_w 5 4)])            
  ]};; 

let vertex_cuts_sol_2 = vertex_cuts_solve_adj_list vertex_cuts_adj_2;; 
  
(* 

print_solution vertex_cuts vertex_cuts_sol_2;;
(0, 0): inr({})
(0, 1): inr({0, 1})
(0, 2): inr({0, 1, 2})
(0, 3): inr({0, 3})
(0, 4): inr({0, 4})
(0, 5): inr({0, 5})
(1, 0): inr({1, 0})
(1, 1): inr({})
(1, 2): inr({1, 2})
(1, 3): inr({1, 3})
(1, 4): inr({1, 4})
(1, 5): inr({1, 5})
(2, 0): inr({2, 0})
(2, 1): inr({2, 1})
(2, 2): inr({})
(2, 3): inr({2, 3})
(2, 4): inr({2, 4})
(2, 5): inr({2, 5})
(3, 0): inr({3, 0})
(3, 1): inr({3, 0, 1})
(3, 2): inr({3, 0, 1, 2})
(3, 3): inr({})
(3, 4): inr({3, 4})
(3, 5): inr({3, 5})
(4, 0): inr({4, 3, 0})
(4, 1): inr({4, 3, 0, 1})
(4, 2): inr({4, 3, 0, 1, 2})
(4, 3): inr({4, 3})
(4, 4): inr({})
(4, 5): inr({4, 5})
(5, 0): inr({5, 4, 3, 0})
(5, 1): inr({5, 4, 3, 0, 1})
(5, 2): inr({5, 4, 3, 0, 1, 2})
(5, 3): inr({5, 4, 3})
(5, 4): inr({5, 4})
(5, 5): inr({})

*) 
