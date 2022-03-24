
open Cas;;
open Describe;;
open Matrix_solver;;

(* 

Experiments with a generalized Martelli combinator: 

   minset_lift_union (S, <=, (x)) = (P(S), (+), (x')) 
   where 
   (+)  = min(<=, lift(x)) 
   (x') = min(<=, union)
   NOTE: The construction (currently) requires (x) to be commutative, idempotent, and not selective. 

   That is, 
   X (+) Y = min(<=, {x (x) y | x in X, y in Y}
   X (x') Y = min(<=, X union Y)

A*[i,j] = (+)_{p in P(i,j)} w(p) 
        = (+)_{p in P(i,j)} min(<=, U_{e in p} w(e))
        = (+)_{p in {p_1, .... p_k}} min(<=, U_{e in p} w(e))
        = min(<=, U_{e in p_1} w(e)) (+) ... (+) min(<=, U_{e in p_k} w(e))
        = (U_{e in p_1} w(e)) (+) ... (+) (U_{e in p_k} w(e))
        = min(<=, {w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k})


   This is more general than Martelli's semiring where 
   A*[i,j] is the set of all minimal cut-sets that disconnect i and j. 

   To reconstruct martelli: 
   1) Note that A subset_eq B iff B = A union B (the right-order wrt union), 
      and A subset_eq B iff A = A intersect B (the left-order wrt intersect) 
      So, start with (P_f(S), intersect, union) 
      so, (+) = intersect, (x) = union. 
   2) construct an order-semigroup (os) as follows: 
       os_from_bs_left (P(S), intersect, union) = (P(S), subset_eq, union). 
   3) Let (P(P(S)), (+), (x')) = minset_lift_union (P(S), subset_eq, union)
   where 
   (+)  = min(subset_eq, lift(union)) 
   (x') = min(subset_eq, union)
   That is, 
   X (+) Y  = min(subset_eq, {x union y | x in X, y in Y}
   X (x') Y = min(subset_eq, X union Y)
   4) Finally, what is S?  It is S = E, the arc-set for the directed graph G = (V, E). 
      w(i, j) = ({(i, j)}}. 

From above 

A*[i,j] = min(<=, { w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k}
        = min(<=, { {{e_1}} union {{e_2}} ... union {{e_k}} | e_1 in p_1, ... e_k in p_k}
        = min(<=, { {{e_1, e_2, ... e_k}} | e_1 in p_1, ... e_k in p_k}
*)   



let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;
let bs_edge_sets_intersect_union = mcas_bs_add_zero (mcas_bs_intersect_union eqv_edge) infinity;;
let os_edge_sets_intersect_union = mcas_os_from_bs_left bs_edge_sets_intersect_union;;
let martelli = mcas_minset_lift_union os_edge_sets_intersect_union;;


let martelli_solver = instantiate_algorithm martelli Matrix_power;; 

let martelli_solve_adj_list adjl =
  match martelli_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "martelli_solve_adj_list : internal error";; 

let mt_w i j = [Inr [(i, j)]] ;;

(*       
    0 ------> 3
    |      /  |
    |     /   | 
    |    /    |
    \/ \/    \/
     1 --- -> 2
         
*) 
  

let martelli_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mt_w 0 1); (3, mt_w 0 3)]);
    
    (1, [(2, mt_w 1 2)]);
    
    (3, [(1, mt_w 3 1); (2, mt_w 3 2)])
  ]};; 

let martelli_sol_1 = martelli_solve_adj_list martelli_adj_1;; 

(*
list_sq_matrix martelli_sol_1;; 
- : (int * int * (int * int) Cas.finite_set Cas.with_constant Cas.finite_set)
    list
=
[(0, 0, []); 
 (0, 1, [Inr [(0, 1); (3, 1)]; Inr [(0, 1); (0, 3)]]);
 (0, 2, [Inr [(1, 2); (3, 2)]; Inr [(1, 2); (0, 3)]; Inr [(0, 1); (3, 1); (3, 2)]; Inr [(0, 1); (0, 3)]]);
 (0, 3, [Inr [(0, 3)]]); 
 (1, 0, [Inr []]); 
 (1, 1, []);
 (1, 2, [Inr [(1, 2)]]); 
 (1, 3, [Inr []]); 
 (2, 0, [Inr []]);
 (2, 1, [Inr []]); 
 (2, 2, []); 
 (2, 3, [Inr []]); 
 (3, 0, [Inr []]);
 (3, 1, [Inr [(3, 1)]]);
 (3, 2, [Inr [(1, 2); (3, 2)]; Inr [(3, 1); (3, 2)]]); 
 (3, 3, [])]
 *)   


(*       
    0 ------ 3
    |      /  |
    |     /   | 
    |    /    |
    |   /     |
    |  /      |	  
    1 ------- 2
*) 
  

let martelli_adj_2 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mt_w 0 1); (3, mt_w 0 3)]);
    
    (1, [(0, mt_w 1 0); (2, mt_w 1 2); (3, mt_w 1 3)]);

    (2, [(1, mt_w 2 1); (3, mt_w 2 3)]);    
    
    (3, [(0, mt_w 3 0); (1, mt_w 3 1); (2, mt_w 3 2)])
  ]};; 

let martelli_sol_2 = martelli_solve_adj_list martelli_adj_2;; 

(*

#print_length 100000;; 
# list_sq_matrix martelli_sol_2;; 
- : (int * int * (int * int) Cas.finite_set Cas.with_constant Cas.finite_set)
    list
=
[(0, 0, []);
 (0, 1, [Inr [(0, 1); (2, 1); (3, 1)]; 
         Inr [(0, 1); (3, 2); (3, 1)]; 
         Inr [(0, 1); (0, 3)]]);
 (0, 2, [Inr [(1, 2); (3, 2)]; 
         Inr [(1, 2); (1, 3); (0, 3)];
         Inr [(0, 1); (3, 1); (3, 2)]; 
         Inr [(0, 1); (0, 3)]]);
 (0, 3, [Inr [(2, 3); (1, 3); (0, 3)]; 
         Inr [(1, 2); (1, 3); (0, 3)];
         Inr [(0, 1); (0, 3)]]);
 (1, 0, [Inr [(1, 0); (3, 0)]; 
         Inr [(1, 0); (2, 3); (1, 3)];
         Inr [(1, 0); (1, 2); (1, 3)]]);
 (1, 1, []);
 (1, 2, [Inr [(1, 2); (3, 2)]; 
         Inr [(0, 3); (1, 2); (1, 3)];
         Inr [(1, 0); (1, 2); (1, 3)]]);
 (1, 3, [Inr [(0, 3); (2, 3); (1, 3)]; 
         Inr [(0, 3); (1, 2); (1, 3)]; 
         Inr [(1, 0); (2, 3); (1, 3)]; 
         Inr [(1, 0); (1, 2); (1, 3)]]); << 
 (2, 0,
  [Inr [(1, 0); (3, 0)]; Inr [(1, 3); (1, 0); (2, 3)];
   Inr [(2, 1); (3, 1); (3, 0)]; Inr [(2, 1); (2, 3)]]);
 (2, 1,
  [Inr [(0, 1); (2, 1); (3, 1)]; Inr [(3, 0); (2, 1); (3, 1)];
   Inr [(2, 1); (2, 3)]]);
 (2, 2, []);
 (2, 3,
  [Inr [(0, 3); (1, 3); (2, 3)]; Inr [(1, 0); (1, 3); (2, 3)];
   Inr [(2, 1); (2, 3)]]);
 (3, 0,
  [Inr [(1, 0); (3, 0)]; Inr [(2, 1); (3, 1); (3, 0)];
   Inr [(3, 2); (3, 1); (3, 0)]]);
 (3, 1,
  [Inr [(0, 1); (2, 1); (3, 1)]; Inr [(0, 1); (3, 2); (3, 1)];
   Inr [(3, 0); (2, 1); (3, 1)]; Inr [(3, 0); (3, 2); (3, 1)]]);
 (3, 2,
  [Inr [(1, 2); (3, 2)]; Inr [(0, 1); (3, 1); (3, 2)];
   Inr [(3, 0); (3, 1); (3, 2)]]);
 (3, 3, [])]

 *) 

(* Now, an experiment with a generalized version *)

let bs_bool_intersect_union = mcas_bs_add_zero (mcas_bs_intersect_union mcas_eqv_bool) infinity;;
let os_bool_sets_intersect_union = mcas_os_from_bs_left bs_bool_intersect_union;;
let bool_martelli = mcas_minset_lift_union os_bool_sets_intersect_union;;

let bool_martelli_solver = instantiate_algorithm bool_martelli Matrix_power;; 

let bool_martelli_solve_adj_list adjl =
  match bool_martelli_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "martelli_solve_adj_list : internal error";; 

let bmt_w i j b = [Inr [b]] ;;

(*       
    0 ------ 3
    |      /  |
    |     /   | 
    |    /    |
    |   /     |
    |  /      |	  
    1 ------- 2
*) 
  

let bool_martelli_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, bmt_w 0 1 true); (3, bmt_w 0 3 false)]);
    
    (1, [(0, bmt_w 1 0 true); (2, bmt_w 1 2 true); (3, bmt_w 1 3 false)]);

    (2, [(1, bmt_w 2 1 false); (3, bmt_w 2 3 true)]);    
    
    (3, [(0, bmt_w 3 0 true); (1, bmt_w 3 1 false); (2, bmt_w 3 2 true)])
  ]};; 

let bool_martelli_sol_1 = bool_martelli_solve_adj_list bool_martelli_adj_1;; 
  
(*
list_sq_matrix bool_martelli_sol_1;; 
- : (int * int * bool Cas.finite_set Cas.with_constant Cas.finite_set) list =
[(0, 0, []); 
 (0, 1, [Inr [true; false]]); 
 (0, 2, [Inr [true]]);
 (0, 3, [Inr [true; false]]); 

 (1, 0, [Inr [true]]); 
 (1, 1, []);
 (1, 2, [Inr [true]]); 
 (1, 3, [Inr [true; false]]); 

 (2, 0, [Inr [true]]);
 (2, 1, [Inr [false; true]]); 
 (2, 2, []); 
 (2, 3, [Inr [false; true]]);
 
 (3, 0, [Inr [true]]); 
 (3, 1, [Inr [true; false]]); 
 (3, 2, [Inr [true]]);
 (3, 3, [])]

 *)



let bool_martelli_adj_2 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, bmt_w 0 1 true); (3, bmt_w 0 3 false)]);
    
    (1, [(0, bmt_w 1 0 true); (2, bmt_w 1 2 false); (3, bmt_w 1 3 true)]);

    (2, [(1, bmt_w 2 1 false); (3, bmt_w 2 3 false)]);    
    
    (3, [(0, bmt_w 3 0 false); (1, bmt_w 3 1 false); (2, bmt_w 3 2 true)])
  ]};; 

let bool_martelli_sol_2 = bool_martelli_solve_adj_list bool_martelli_adj_2;; 
(*
list_sq_matrix bool_martelli_sol_2;;
list_sq_matrix bool_martelli_sol_2;;
- : (int * int * bool Cas.finite_set Cas.with_constant Cas.finite_set) list =
[(0, 0, []); 
 (0, 1, [Inr [true; false]]); 
 (0, 2, [Inr [true; false]]);
 (0, 3, [Inr [true; false]]); 
 (1, 0, [Inr [true; false]]); 
 (1, 1, []);
 (1, 2, [Inr [false; true]]); 
 (1, 3, [Inr [false; true]]);
 (2, 0, [Inr [false]]); 
 (2, 1, [Inr [false]]); 
 (2, 2, []);
 (2, 3, [Inr [false]]); 
 (3, 0, [Inr [false]]); 
 (3, 1, [Inr [false]]);
 (3, 2, [Inr [false; true]]); 
 (3, 3, [])]
 *)


(*  what if we start with  (P(S), intersect, lift(x))?
   NOTE : distributivity requires and INJECTIVE (x) ! 

   2) construct an order-semigroup (os) as follows: 
       os_from_bs_left (P(S), intersect, lift(x)) = (P(S), subset_eq, lift(x)). 
   3) Let (P(P(S)), (+), (x')) = minset_lift_union (P(S), subset_eq, lift(x)). 
   where 
   (+)  = min(subset_eq, lift(lift(x))) 
   (x') = min(subset_eq, union)
   That is, 
   X (+) Y  = min(subset_eq, {x lift(x) y | x in X, y in Y}
   X (x') Y = min(subset_eq, X union Y)

A*[i,j] = min(<=, {w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k})
        = min(<=, {w(e_1) lift(x) w(e_2) ... lift(x) w(e_k) | e_1 in p_1, ... e_k in p_k})
        = 
 *) 

(* Now, another experiment with a generalized version *) 


(* C + int *)   
let bs_bw = mcas_bs_add_one mcas_max_min infinity;; 

(* (C + int) x (C + int) *)     
let bs_bw_x_bw = mcas_bs_product bs_bw bs_bw ;; 

(* (C + int) x (C + int)  with <= = max x max *)       
let os_bw_x_bw = mcas_os_from_bs_left bs_bw_x_bw;;

(* (C + int) x (C + int) set *)       
let g_martelli_bw_x_bw = mcas_minset_lift_union os_bw_x_bw;;

(*
 A[i,j] = {w(i, j)} = {(w_1(i,j), w2(i,j))}

A*[i,j] = min(<=, {w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k}

        ?=? min(<=,  w (Martelli[i, j])   (by idempotence?) 
*)


(*
mcas_bs_describe_fully g_martelli_bw_x_bw;; 
Class : Dioid
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   [(inl(INF), inr(0))].[(inr(0), inl(INF))] = [(inr(0), inr(0))]
Not Left Cancellative: 
   [(inr(0), inr(0))].[(inl(INF), inr(0))] = [(inr(0), inr(0))]
   [(inr(0), inr(0))].[(inr(0), inl(INF))] = [(inr(0), inr(0))]
   [(inl(INF), inr(0))] <> [(inr(0), inl(INF))]
Not Right Cancellative: 
   [(inl(INF), inr(0))].[(inr(0), inr(0))] = [(inr(0), inr(0))]
   [(inr(0), inl(INF))].[(inr(0), inr(0))] = [(inr(0), inr(0))]
   [(inl(INF), inr(0))] <> [(inr(0), inl(INF))]
Not Left Constant: 
   [(inl(INF), inl(INF))].[] = []
   [(inl(INF), inl(INF))].[(inl(INF), inl(INF))] = [(inl(INF), inl(INF))]
Not Right Constant: 
   [].[(inl(INF), inl(INF))] = []
   [(inl(INF), inl(INF))].[(inl(INF), inl(INF))] = [(inl(INF), inl(INF))]
Not Anti Left: 
   [].[] = []
Not Anti Right: 
   [].[] = []
Not Is Left: 
   [(inl(INF), inl(INF))].[] = []
Not Is Right: 
   [].[(inl(INF), inl(INF))] = []
Multiplicative properties:
-------------------------
Idempotent
Commutative
Not Selective: 
   [(inr(0), inl(INF))].[(inl(INF), inr(0))] = [(inr(0), inl(INF)), (inl(INF), inr(0))]
Not Left Cancellative: 
   [(inr(0), inl(INF)), (inl(INF), inr(0))].[(inr(0), inl(INF))] = [(inl(INF), inr(0)), (inr(0), inl(INF))]
   [(inr(0), inl(INF)), (inl(INF), inr(0))].[(inl(INF), inr(0))] = [(inr(0), inl(INF)), (inl(INF), inr(0))]
   [(inr(0), inl(INF))] <> [(inl(INF), inr(0))]
Not Right Cancellative: 
   [(inr(0), inl(INF))].[(inr(0), inl(INF)), (inl(INF), inr(0))] = [(inr(0), inl(INF)), (inl(INF), inr(0))]
   [(inl(INF), inr(0))].[(inr(0), inl(INF)), (inl(INF), inr(0))] = [(inr(0), inl(INF)), (inl(INF), inr(0))]
   [(inr(0), inl(INF))] <> [(inl(INF), inr(0))]
Not Left Constant: 
   [].[(inl(INF), inl(INF))] = [(inl(INF), inl(INF))]
   [].[] = []
Not Right Constant: 
   [(inl(INF), inl(INF))].[] = [(inl(INF), inl(INF))]
   [].[] = []
Not Anti Left: 
   [].[] = []
Not Anti Right: 
   [].[] = []
Not Is Left: 
   [].[(inl(INF), inl(INF))] = [(inl(INF), inl(INF))]
Not Is Right: 
   [(inl(INF), inl(INF))].[] = [(inl(INF), inl(INF))]
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

let g_martelli_bw_x_bw_solver = instantiate_algorithm g_martelli_bw_x_bw Matrix_power;; 

let g_martelli_bw_x_bw_solve_adj_list adjl =
  match g_martelli_bw_x_bw_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "g_martelli_bw_x_bw_solve_adj_list : internal error";; 

let mk_w b1 b2 = [(Inr b1, Inr b2)] ;;

let adj_1 = 
  (* 0 = u, 1 = w, 2 = x, 3 = v*)
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mk_w 5 1); (3, mk_w 10 3)]);
    
    (1, [(2, mk_w 20 1)]);
    
    (3, [(1, mk_w 20 4); (2, mk_w 10 2)])
  ]};; 

let sol_1 = g_martelli_bw_x_bw_solve_adj_list adj_1;; 
(*

0->2 is only interesting case 
(0, 2, [(Inr 10, Inr 1)])

paths: 
p1 = 0,1,2
p2 = 0,3,2
p3 = 0,3,1,2

have to look at |p1| x |p2| x |p3| = 2 x 2 x 3 = 12 products 
then, take "max x max" minset. 

minimal cut-sets: 
 
   {(0,1), (0,3)} 
   {(1,2), (0,3)} 
   {(0,1), (3, 2), (0,3)} 
   {(1,2), (3, 2), (0,3)} 
   {(0,1), (0,3), (1, 2)} 

list_sq_matrix sol_1;; 
- : (int * int *
     (int Cas.with_constant * int Cas.with_constant) Cas.finite_set)
    list
=
[(0, 0, []); (0, 1, [(Inr 5, Inr 1)]); (0, 2, [(Inr 10, Inr 1)]);
 (0, 3, [(Inr 10, Inr 3)]);
 (1, 0,
  [(Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']})]);
 (1, 1, []); (1, 2, [(Inr 20, Inr 1)]);
 (1, 3,
  [(Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']})]);
 (2, 0,
  [(Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']})]);
 (2, 1,
  [(Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']})]);
 (2, 2, []);
 (2, 3,
  [(Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']})]);
 (3, 0,
  [(Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']},
    Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']})]);
 (3, 1, [(Inr 20, Inr 4)]); (3, 2, [(Inr 10, Inr 2)]); (3, 3, [])]


 *)
  
