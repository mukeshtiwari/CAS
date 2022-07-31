open Cas;;
open Describe;;
open Matrix_solver;;
  
(* 
   This file contains the two examples from Section 4.8.1 
   of "Path Problems in Networks" by Baras and Theodorakopoulos. 

   A*[i,j] = set of all arcs common to all paths from i to j 

*) 
let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;

let bridges = mcas_bs_add_zero (mcas_bs_intersect_union eqv_edge) infinity;;

let bridges_solver = bs_adj_list_solver bridges ;;   

(*
mcas_bs_describe_fully bridges ;; 

Class : Dioid
bs_describe_algebra_fully_aux: Not Yet!
(S_1, +_1, *_1) = bs_add_zero (S_0, +_0, *_0) INF
where
S_1 = {INF} + S_0
Inr(x) +_1 Inr(y) = Inr(x +_0 y)
Inl(INF) +_1 a = a
a +_1 Inl(INF) = a
Inr(x) *_1 Inr(y) = Inr(x *_0 y)
Inl(INF) *_1 _ = Inl(INF)
_ *_1 Inl(INF) = Inl(INF)
Additive properties:
--------------------
Identity = inl(INF)
Annihilator = inr({})
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
Multiplicative properties:
-------------------------
Identity = inr({})
Annihilator = inl(INF)
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
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Left_Right Absorptive 
Right_Left Absorptive
Right_Right Absorptive 

*)   

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

let bridges_sol_1 = bridges_solver bridges_adj_1;; 

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

let vertex_cuts_solver = bs_adj_list_solver vertex_cuts;; 

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

let vertex_cuts_sol_1 = vertex_cuts_solver vertex_cuts_adj_1;; 

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

let vertex_cuts_sol_2 = vertex_cuts_solver vertex_cuts_adj_2;; 
  
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

  (* ************************************* *)

let test =
  mcas_bs_add_zero
    (mcas_bs_llex_product
       mcas_min_plus
       (mcas_bs_product bridges vertex_cuts))
    infinity;;

let test_solver = bs_adj_list_solver test;;   

let t_w w i j = Inr (w, (br_w i j, vc_w i j));; 
  
  
(* 

    0 ------- 3 ------- 4 
    |         |         |
    |         |         | 
    |         |         |
    |         |         | 
    1 --------2 ------- 5
         
*) 
let test_adj_1 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, t_w 2 0 1); (3, t_w 1 0 3)]);
    (1, [(0, t_w 1 1 0); (2, t_w 3 1 2)]);
    (2, [(1, t_w 2 2 1); (2, t_w 2 2 3); (5, t_w 2 2 5)]);    
    (3, [(0, t_w 1 3 0); (2, t_w 1 3 2); (4, t_w 1 3 4)]);
    (4, [(3, t_w 2 4 3); (5, t_w 2 4 5)]);
    (5, [(2, t_w 2 5 2); (4, t_w 2 5 4)])            
  ]};; 

let print_adj alg adj = print_solution alg (square_matrix_from_adj_list alg adj);;

(* 
print_adj test test_adj_1;;
*)   

(* 
print_solution test (test_solver test_adj_1);;  
(0, 0): inr((0, (inr({}), inr({}))))
(0, 1): inr((2, (inr({(0, 1)}), inr({0, 1}))))
(0, 2): inr((2, (inr({(0, 3), (3, 2)}), inr({0, 3, 2}))))
(0, 3): inr((1, (inr({(0, 3)}), inr({0, 3}))))
(0, 4): inr((2, (inr({(0, 3), (3, 4)}), inr({0, 3, 4}))))
(0, 5): inr((4, (inr({(0, 3)}), inr({0, 3, 5}))))
(1, 0): inr((1, (inr({(1, 0)}), inr({1, 0}))))
(1, 1): inr((0, (inr({}), inr({}))))
(1, 2): inr((3, (inr({}), inr({1, 2}))))
(1, 3): inr((2, (inr({(1, 0), (0, 3)}), inr({1, 0, 3}))))
(1, 4): inr((3, (inr({(1, 0), (0, 3), (3, 4)}), inr({1, 0, 3, 4}))))
(1, 5): inr((5, (inr({}), inr({1, 5}))))
(2, 0): inr((3, (inr({(2, 1), (1, 0)}), inr({2, 1, 0}))))
(2, 1): inr((2, (inr({(2, 1)}), inr({2, 1}))))
(2, 2): inr((4, (inr({(2, 5), (5, 2)}), inr({5, 2}))))
(2, 3): inr((4, (inr({(2, 1), (1, 0), (0, 3)}), inr({2, 1, 0, 3}))))
(2, 4): inr((4, (inr({(2, 5), (5, 4)}), inr({2, 5, 4}))))
(2, 5): inr((2, (inr({(2, 5)}), inr({2, 5}))))
(3, 0): inr((1, (inr({(3, 0)}), inr({3, 0}))))
(3, 1): inr((3, (inr({}), inr({3, 1}))))
(3, 2): inr((1, (inr({(3, 2)}), inr({3, 2}))))
(3, 3): inr((0, (inr({}), inr({}))))
(3, 4): inr((1, (inr({(3, 4)}), inr({3, 4}))))
(3, 5): inr((3, (inr({}), inr({3, 5}))))
(4, 0): inr((3, (inr({(4, 3), (3, 0)}), inr({4, 3, 0}))))
(4, 1): inr((5, (inr({(4, 3)}), inr({4, 3, 1}))))
(4, 2): inr((3, (inr({(4, 3), (3, 2)}), inr({4, 3, 2}))))
(4, 3): inr((2, (inr({(4, 3)}), inr({4, 3}))))
(4, 4): inr((0, (inr({}), inr({}))))
(4, 5): inr((2, (inr({(4, 5)}), inr({4, 5}))))
(5, 0): inr((5, (inr({}), inr({5, 0}))))
(5, 1): inr((4, (inr({(5, 2), (2, 1)}), inr({5, 2, 1}))))
(5, 2): inr((2, (inr({(5, 2)}), inr({5, 2}))))
(5, 3): inr((4, (inr({(5, 4), (4, 3)}), inr({5, 4, 3}))))
(5, 4): inr((2, (inr({(5, 4)}), inr({5, 4}))))
(5, 5): inr((0, (inr({}), inr({}))))

 *) 


let test2 = mcas_bs_product bridges vertex_cuts;; 
let test2_solver = bs_adj_list_solver test2;;   

let t2_w i j = (br_w i j, vc_w i j);; 
  
  
(* 
    0 ------- 3 ------- 4 
    |         |         |
    |         |         | 
    |         |         |
    |         |         | 
    1 --------2 ------- 5
*) 
let test2_adj_1 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, t2_w 0 1); (3, t2_w 0 3)]);
    (1, [(0, t2_w 1 0); (2, t2_w 1 2)]);
    (2, [(1, t2_w 2 1); (2, t2_w 2 3); (5, t2_w 2 5)]);    
    (3, [(0, t2_w 3 0); (2, t2_w 3 2); (4, t2_w 3 4)]);
    (4, [(3, t2_w 4 3); (5, t2_w 4 5)]);
    (5, [(2, t2_w 5 2); (4, t2_w 5 4)])            
  ]};; 
  
(*
print_solution test2 (test2_solver test2_adj_1);;  
(0, 0): (inr({}), inr({}))
(0, 1): (inr({}), inr({0, 1}))
(0, 2): (inr({}), inr({0, 2}))
(0, 3): (inr({}), inr({0, 3}))
(0, 4): (inr({}), inr({0, 4}))
(0, 5): (inr({}), inr({0, 5}))
(1, 0): (inr({}), inr({1, 0}))
(1, 1): (inr({}), inr({}))
(1, 2): (inr({}), inr({1, 2}))
(1, 3): (inr({}), inr({1, 3}))
(1, 4): (inr({}), inr({1, 4}))
(1, 5): (inr({}), inr({1, 5}))
(2, 0): (inr({}), inr({2, 0}))
(2, 1): (inr({}), inr({2, 1}))
(2, 2): (inr({}), inr({2}))
(2, 3): (inr({}), inr({2, 3}))
(2, 4): (inr({}), inr({2, 4}))
(2, 5): (inr({}), inr({2, 5}))
(3, 0): (inr({}), inr({3, 0}))
(3, 1): (inr({}), inr({3, 1}))
(3, 2): (inr({}), inr({3, 2}))
(3, 3): (inr({}), inr({}))
(3, 4): (inr({}), inr({3, 4}))
(3, 5): (inr({}), inr({3, 5}))
(4, 0): (inr({}), inr({4, 0}))
(4, 1): (inr({}), inr({4, 1}))
(4, 2): (inr({}), inr({4, 2}))
(4, 3): (inr({}), inr({4, 3}))
(4, 4): (inr({}), inr({}))
(4, 5): (inr({}), inr({4, 5}))
(5, 0): (inr({}), inr({5, 0}))
(5, 1): (inr({}), inr({5, 1}))
(5, 2): (inr({}), inr({5, 2}))
(5, 3): (inr({}), inr({5, 3}))
(5, 4): (inr({}), inr({5, 4}))
(5, 5): (inr({}), inr({}))
- 

 *) 
