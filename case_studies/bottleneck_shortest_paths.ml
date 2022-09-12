(*

This file attempts to use CAS to explore this paper. 

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

(*
    (a, b) <=_1 (c, d) iff (c <= a) and (d <= b) 

    (a, b) <_1 (c, d) iff ((a, b) <=_1 (c, d)) and not ((c, d) <=_1 (a, b))
                      iff ((c <= a) and (d <= b)) and not ((a <= c) and (b <= d))
                      iff ((c <= a) and (d <= b)) and (not (a <= c) or not(b <= d))
                      iff (((c <= a) and (d <= b)) and not (a <= c)) 
                          or
			  (((c <= a) and (d <= b)) and not (b <= d))
                      iff ((c < a) and (d <= b)) or ((c <= a) and (d < b)) 
   not (a, b) <_1 (c, d)
                      iff not (((c < a) and (d <= b)) or ((c <= a) and (d < b)))
                      iff (not(c < a) or not(d <= b)) and (not(c <= a) or not(d < b))
                      iff (not(c < a) and not(c <= a)) 
                          or 
                          (not(c < a) and not(d < b))
                          or 
                          (not(d <= b) and not(c <= a)) 
                          or 
                          (not(d <= b) and not(d < b))

 *)                
let order_E = mcas_or_add_bottom (mcas_or_product or_max or_max) infinity;;

(* P(<=_1, nat x nat), (x)_1) 

   X (x)_1 Y = min(<=_1, X union Y)  
             = {z in X union Y | for all w in (X union Y), not (w <_1 z)} 
             = {(c,d) in X union Y | for all (a,b) in (X union Y), not ((a,b) <_1 (c,d))} 
 *)   
let maxset = mcas_sg_minset_union order_E;;

(* (P(<=_1, nat x nat), <=_2, (x)_1)  with 

   X <=_2 Y iff Y = X (x)_1 Y
            iff Y = min(<=_1, X union Y)  
            iff for all x in X exists y in Y, y <=_1 x

 *)   
let os_maxset = mcas_os_from_sg_right maxset;;

(*  bottleneck_shortest_paths has OCaml type 
     (int * int) Cas.with_constant Cas.finite_set Cas.finite_set Cas.bs_mcas
 *)

(*
    minset_union_lift (P(<=_1, nat x nat), <=_2, (x)_1) 
    = (P(<=_2, P(<=_1, nat x nat)), (+)_2, (x)_2)

    XX (+)_2 YY = min(<=_2, XX union YY) 

    XX (x)_2 YY = min(<=_2, XX lift((x)_1) YY) 
                = min(<=_2, {X (x)_1 Y | X in XX, Y in YY}) 
                = min(<=_2, { min(<=_1, X union Y)  | X in XX, Y in YY}) 


   min(<=_1, X) <=_2 min(<=_1, Y) 
   iff 
   for all x in min(<=_1, X) exists y in min(<=_1, Y), y <=_1 x
   iff 
   for all x in {x in X | P(x)} exists y in {y in Y | Q(y)}, y <=_1 x
   iff 
   for all x in X, y in Y, P(x) * Q (y) -> y <=_1 x


   Note: minset_union_lift(S, <=, (x))  demands (currently) 
   that (x) is commutative and idempotent (a semilattice) 
   and that the order is left and right monotone and 
   left and right increasing. 

   so, 

   ∀ s t u : S, t <= u -> s (+) t <= s (+) u 
     ∀ s t : S, s <= s (+) t 

   Q : are there interesting such (S, <=, (x))
       where <= is a quasi-order? 

   Q : relationship between <= and <=_L? 
   s <=_L t === s = s (+) t 
   note that (+) is the glb wrt <=_L? 

   1) s <=_L t -> s <= s (+) t 




================================================

think about bottleneck as a general construction over (S, <=_1). 

1) P(<=_1, S), (x)_1) 

   X (x)_1 Y = min(<=_1, X union Y)  

2) (P(<=_1, S), <=_2, (x)_1)    (D in {L, R} ???) 

   X <=_2 Y iff Y = X (x)_1 Y
            iff Y = min(<=_1, X union Y)  
            iff for all x in X exists y in Y, y <=_1 x

3) minset_union_lift (P(<=_1, S), <=_2, (x)_1) 
    = (P(<=_2, P(<=_1, S)), (+)_2, (x)_2)

    XX (+)_2 YY = min(<=_2, XX union YY) 

    XX (x)_2 YY = min(<=_2, XX lift((x)_1) YY) 
                = min(<=_2, {X (x)_1 Y | X in XX, Y in YY}) 
                = min(<=_2, { min(<=_1, X union Y)  | X in XX, Y in YY})

how about: 
minset_union_lift(max_order_semigroup(minset_lift(S, <=_1))). 


A*[i,j] = (+)_2_{p in pi[i,j]} (x)_2(p)
        = min(<=_2, U_{p in pi[i,j]} min(<=_2, {lift(x)_1(p)}
        = min(<=_2, U_{p in pi[i,j]} {lift(x)_1(p)}
        = min(<=_2, U_{p in pi[i,j]} {min(<=_1, U_{e in p} w(e))}



--------------------
start with (max, min)

how to extend to partial orders?

Given (S, <=, (x))

construct 

X [+] Y = max(<=, X union Y)

X [x] Y = min(<=, X union Y) 	       

w(p) = min(<=, U_{e in p} w(e))

A*[i,j] = max(<=, U_{p in pi[i,j]} w(p))
        = max(<=, U_{p in pi[i,j]} min(<=, U_{e in p} w(e)))

Wait: this is not distributive.

lhs = X [x] (Y [+] Z)
rhs = (X [x] Y) [+]  (X [x] Z)

X = {1} 
Y = {0, 10} 
Z = {0, 10} 

lhs = {1} 
rhs = {10} 


-------------------


   minset_union_lift (T, <=, (x))n = ((P<=, T), [+], [x]) 
   X [+] Y = min(<=, X union Y) 
   X [x] Y = min(<=, {x (x) y | x in X, y in Y})

   A*[i,j] = [+]_{p in pi[i,j]} w(p) 
           = [+]_{p1, ... pk} w(p) 
           = w(p1) [+] ... [+] w(pk) 
           = min(<=, w(p1) union ... union w(pk)) 

   Now, suppose w(u,v) = {w'(u,v)} (a singleton).  then

             min(<=, w(p1) union ... union w(pk)) 
           = min(<=, {w'(p1)} union ... union {w'(pk)}) 
           = min(<=, {w'(p1), ..., w'(pk)}) 

------------------

   Now, suppose (T, <=, (x)) = os_from_sg_right (S, (x)) 
   t <= t' === t' = t (x) t'

     not (w'(pj) < w'(pi))
   = not( (w'(pi) = w(pj) (x) w(pi)) 
          and 
          not (w'(pj) = w(pj) (x) w(pi)))
   = not(w'(pi) = w(pj) (x) w(pi))
     or 
    (w'(pj) = w(pj) (x) w(pi))
  = (w'(pi) <= w'(pj)) or not(w'(pj) <= w'(pi))


             min(<=, {w'(p1), ..., w'(pk)}) 
           = min(<=, {w'(p1), ..., w'(pk)})  
           = {w'(pi) | for all w'(pj), not (w'(pj) < w'(pi)) }
           = {w'(pi) | for all w'(pj), (w'(pi) <= w'(pj)) or not(w'(pj) <= w'(pi))}

---------------
   Now, suppose (S, (x)) = minset_union(U, <=') 
   X (x) Y = min(<=', X union Y) 
   t <= t' === t' = t (x) t' === t' = min(<=', t union t') 
      iff forall a in t exists b in t' b <=' a 

   w'(p) = min(<=', {w'(e) | e in p}) 

   w'(pi) <= w'(pj) 
   iff  forall a in w'(pi) exists b in w'(pj) b <=' a 
   iff  forall a in min(<=', {w'(e) | e in pi}  
           exists b in min(<=', {w'(e) | e in pj} b <=' a 

             {w'(pi) | for all w'(pj), (w'(pi) <= w'(pj)) or not(w'(pj) <= w'(pi))}
           = ???

=================================================
 *) 
let bottleneck_shortest_paths = mcas_minset_union_lift os_maxset;;

(*
 mcas_bs_describe_fully bottleneck_shortest_paths;; 



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



(* 
   what would this look like in the direct style?  

   sg_minset_union_from_po_bounded      : 'a1 Cas.po_bounded     -> 'a1 Cas.finite_set Cas.sg_BCI 
   sg_minset_union_from_po_with_bottom  : 'a1 Cas.po_with_bottom -> 'a1 Cas.finite_set Cas.sg_BCI 
   
   os_from_sg_BCI_right                 : 'a1 Cas.sg_BCI -> 'a1 Cas.bounded_monotone_increasing_posg 

   minset_union_lift_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION;;
              : 'a1 Cas.bounded_monotone_increasing_posg -> 'a1 Cas.assert_not_selective -> 'a1 Cas.finite_set Cas.dioid

   minset_union_lift_from_bounded_monotone_increasing_posg_GUARDED_CNI_VERSION;;
              : 'a1 Cas.bounded_monotone_increasing_posg -> 'a1 Cas.assert_not_idempotent -> 'a1 Cas.finite_set Cas.dioid
    
= 


  will this work with pre-orders? 
*) 
let test order = mcas_minset_union_lift (mcas_os_from_sg_right (mcas_sg_minset_union order));;

(* test_lte_nat : (int * int) Cas.finite_set Cas.finite_set Cas.bs_mcas *) 
let test_lte_nat = test (mcas_left_order_from_sg (mcas_sg_product mcas_sg_min mcas_sg_min));;

let test_lte_nat_solver = bs_adj_list_solver test_lte_nat;; 

let w_test1 w = [[(w, 1)]];; 

let test_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, w_test1 10); (2, w_test1 9); (3, w_test1 100)]);
    (1, [(2, w_test1 1)]);
    (3, [(2, w_test1 9)])
  ]};; 

let sol1 = test_lte_nat_solver test_adj_1;;
(*
print_solution test_lte_nat sol1;;
(0, 0): [[]]
(0, 1): [[(10, 1)]]
(0, 2): [[(9, 1)]]
(0, 3): [[(100, 1)]]
(1, 0): []
(1, 1): [[]]
(1, 2): [[(1, 1)]]
(1, 3): []
(2, 0): []
(2, 1): []
(2, 2): [[]]
(2, 3): []
(3, 0): []
(3, 1): []
(3, 2): [[(9, 1)]]
(3, 3): [[]]
*) 

let max_min_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, Inr 10); (2, Inr 9); (3, Inr 100)]);
    (1, [(2, Inr 1)]);
    (3, [(2, Inr 9)])
  ]};; 

let max_min = mcas_bs_add_one mcas_max_min infinity;; 
(* 
print_solution max_min (bs_adj_list_solver max_min max_min_adj_1);;
(0, 0): inl(INF)
(0, 1): inr(10)
(0, 2): inr(9)
(0, 3): inr(100)
(1, 0): inr(0)
(1, 1): inl(INF)
(1, 2): inr(1)
(1, 3): inr(0)
(2, 0): inr(0)
(2, 1): inr(0)
(2, 2): inl(INF)
(2, 3): inr(0)
(3, 0): inr(0)
(3, 1): inr(0)
(3, 2): inr(9)
(3, 3): inl(INF)
*) 

let w_test2 w u = [[(w, u)]];; 

let test_adj_2 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, w_test2 10 2); (2, w_test2 9 5); (3, w_test2 100 2)]);
    (1, [(2, w_test2 1 10)]);
    (3, [(2, w_test2 9 20)])
  ]};; 

let sol2 = test_lte_nat_solver test_adj_2;;
(*
print_solution test_lte_nat sol2;;
(0, 0): [[]]
(0, 1): [[(10, 2)]]
(0, 2): [[(100, 2), (9, 20)], [(9, 5)]]
(0, 3): [[(100, 2)]]
(1, 0): []
(1, 1): [[]]
(1, 2): [[(1, 10)]]
(1, 3): []
(2, 0): []
(2, 1): []
(2, 2): [[]]
(2, 3): []
(3, 0): []
(3, 1): []
(3, 2): [[(9, 20)]]
(3, 3): [[]]

*) 

(*
*) 

let minimax = mcas_bs_add_zero mcas_min_max infinity;; 

(*

        3        2
     0 ------ 1 ---- 4
     |\  2           |
   1 | \----         | 1
     |      \        |
     2 ------ 3------5 
        1         3
*)    

let minimax_adj_1 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, Inr 3); (2, Inr 1); (3, Inr 2)]);
    (1, [(0, Inr 3); (4, Inr 2)]);
    (2, [(0, Inr 1); (3, Inr 1)]);
    (3, [(0, Inr 2); (2, Inr 1); (5, Inr 3)]);
    (4, [(1, Inr 2); (5, Inr 1)]);
    (5, [(3, Inr 3); (4, Inr 1)])
  ]};; 

(*
print_solution minimax (bs_adj_list_solver minimax minimax_adj_1);;
(0, 0): inr(0)
(0, 1): inr(3)
(0, 2): inr(1)
(0, 3): inr(1)
(0, 4): inr(3)
(0, 5): inr(3)
(1, 0): inr(3)
(1, 1): inr(0)
(1, 2): inr(3)
(1, 3): inr(3)
(1, 4): inr(2)
(1, 5): inr(2)
(2, 0): inr(1)
(2, 1): inr(3)
(2, 2): inr(0)
(2, 3): inr(1)
(2, 4): inr(3)
(2, 5): inr(3)
(3, 0): inr(1)
(3, 1): inr(3)
(3, 2): inr(1)
(3, 3): inr(0)
(3, 4): inr(3)
(3, 5): inr(3)
(4, 0): inr(3)
(4, 1): inr(2)
(4, 2): inr(3)
(4, 3): inr(3)
(4, 4): inr(0)
(4, 5): inr(1)
(5, 0): inr(3)
(5, 1): inr(2)
(5, 2): inr(3)
(5, 3): inr(3)
(5, 4): inr(1)
(5, 5): inr(0)

               3
              / \
             /   \
            /     2
           /     / \ 
          1     1   \ 
         /|\   /\   |
        0 2 3  4 5  1
*) 


let minimax_adj_2 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, Inr 3); (2, Inr 1); (3, Inr 2)]);
    (1, [(0, Inr 3); (4, Inr 1)]);
    (2, [(0, Inr 1); (3, Inr 1)]);
    (3, [(0, Inr 2); (2, Inr 1); (5, Inr 3)]);
    (4, [(1, Inr 1); (5, Inr 1)]);
    (5, [(3, Inr 3); (4, Inr 1)])
  ]};; 

(*
             only change 2->1 on link 1---4
        3        1
     0 ------ 1 ---- 4
     |\  2           |
   1 | \----         | 1
     |      \        |
     2 ------ 3------5 
        1         3
*)    

(*
print_solution minimax (bs_adj_list_solver minimax minimax_adj_2);;
(0, 0): inr(0)
(0, 1): inr(3)
(0, 2): inr(1)
(0, 3): inr(1)
(0, 4): inr(3)
(0, 5): inr(3)
(1, 0): inr(3)
(1, 1): inr(0)
(1, 2): inr(3)
(1, 3): inr(3)
(1, 4): inr(1)
(1, 5): inr(1)
(2, 0): inr(1)
(2, 1): inr(3)
(2, 2): inr(0)
(2, 3): inr(1)
(2, 4): inr(3)
(2, 5): inr(3)
(3, 0): inr(1)
(3, 1): inr(3)
(3, 2): inr(1)
(3, 3): inr(0)
(3, 4): inr(3)
(3, 5): inr(3)
(4, 0): inr(3)
(4, 1): inr(1)
(4, 2): inr(3)
(4, 3): inr(3)
(4, 4): inr(0)
(4, 5): inr(1)
(5, 0): inr(3)
(5, 1): inr(1)
(5, 2): inr(3)
(5, 3): inr(3)
(5, 4): inr(1)
(5, 5): inr(0)


               3
              / \
             /   \
            /     \
           /       \
          1         1 
         /|\       /|\
        0 2 3     4 5 1
*) 


let test_adj_1_and_2 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, w_test2 3 3); (2, w_test2 1 1); (3, w_test2 2 2)]);
    (1, [(0, w_test2 3 3); (4, w_test2 2 1)]);
    (2, [(0, w_test2 1 1); (3, w_test2 1 1)]);
    (3, [(0, w_test2 2 2); (2, w_test2 1 1); (5, w_test2 3 3)]);
    (4, [(1, w_test2 2 1); (5, w_test2 1 1)]);
    (5, [(3, w_test2 3 3); (4, w_test2 1 1)])
  ]};; 

(* 
print_solution test_lte_nat (test_lte_nat_solver test_adj_1_and_2);;
(0, 0): [[]]
(0, 1): [[(3, 3)]]
(0, 2): [[(1, 1)]]
(0, 3): [[(2, 2)]]
(0, 4): [[(2, 1)]]
(0, 5): [[(2, 2)]]
(1, 0): [[(3, 3)]]
(1, 1): [[]]
(1, 2): [[(1, 1)]]
(1, 3): [[(2, 2)]]
(1, 4): [[(2, 1)]]
(1, 5): [[(2, 2)]]
(2, 0): [[(1, 1)]]
(2, 1): [[(1, 1)]]
(2, 2): [[]]
(2, 3): [[(1, 1)]]
(2, 4): [[(1, 1)]]
(2, 5): [[(1, 1)]]
(3, 0): [[(2, 2)]]
(3, 1): [[(2, 2)]]
(3, 2): [[(1, 1)]]
(3, 3): [[]]
(3, 4): [[(2, 1)]]
(3, 5): [[(3, 3)]]
(4, 0): [[(2, 1)]]
(4, 1): [[(2, 1)]]
(4, 2): [[(1, 1)]]
(4, 3): [[(2, 1)]]
(4, 4): [[]]
(4, 5): [[(2, 1)]]
(5, 0): [[(2, 2)]]
(5, 1): [[(2, 2)]]
(5, 2): [[(1, 1)]]
(5, 3): [[(3, 3)]]
(5, 4): [[(2, 1)]]
(5, 5): [[]]
*) 

(* use max 

test_gte_nat :
  (int * int) Cas.with_constant Cas.finite_set Cas.finite_set Cas.bs_mcas =

*) 
let test_gte_nat = 
test (mcas_or_add_bottom (mcas_left_order_from_sg (mcas_sg_product mcas_sg_max mcas_sg_max)) infinity);;

let test_gte_nat_solver = bs_adj_list_solver test_gte_nat;; 

let w_test_gte w u = [[Inr (w, u)]];; 

let test_gte_adj_1_and_2 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, w_test_gte 3 3); (2, w_test_gte 1 1); (3, w_test_gte 2 2)]);
    (1, [(0, w_test_gte 3 3); (4, w_test_gte 2 1)]);
    (2, [(0, w_test_gte 1 1); (3, w_test_gte 1 1)]);
    (3, [(0, w_test_gte 2 2); (2, w_test_gte 1 1); (5, w_test_gte 3 3)]);
    (4, [(1, w_test_gte 2 1); (5, w_test_gte 1 1)]);
    (5, [(3, w_test_gte 3 3); (4, w_test_gte 1 1)])
  ]};; 
(* 
print_solution test_gte_nat (test_gte_nat_solver test_gte_adj_1_and_2);;

(0, 0): [[]]
(0, 1): [[inr((3, 3))]]
(0, 2): [[inr((1, 1))]]
(0, 3): [[inr((1, 1))]]
(0, 4): [[inr((3, 3))]]
(0, 5): [[inr((3, 3))]]
(1, 0): [[inr((3, 3))]]
(1, 1): [[]]
(1, 2): [[inr((3, 3))]]
(1, 3): [[inr((3, 3))]]
(1, 4): [[inr((2, 1))]]
(1, 5): [[inr((2, 1))]]
(2, 0): [[inr((1, 1))]]
(2, 1): [[inr((3, 3))]]
(2, 2): [[]]
(2, 3): [[inr((1, 1))]]
(2, 4): [[inr((3, 3))]]
(2, 5): [[inr((3, 3))]]
(3, 0): [[inr((1, 1))]]
(3, 1): [[inr((3, 3))]]
(3, 2): [[inr((1, 1))]]
(3, 3): [[]]
(3, 4): [[inr((3, 3))]]
(3, 5): [[inr((3, 3))]]
(4, 0): [[inr((3, 3))]]
(4, 1): [[inr((2, 1))]]
(4, 2): [[inr((3, 3))]]
(4, 3): [[inr((3, 3))]]
(4, 4): [[]]
(4, 5): [[inr((1, 1))]]
(5, 0): [[inr((3, 3))]]
(5, 1): [[inr((2, 1))]]
(5, 2): [[inr((3, 3))]]
(5, 3): [[inr((3, 3))]]
(5, 4): [[inr((1, 1))]]
(5, 5): [[]]
*) 


(*

        1        2
     0 ------ 1 ---- 4
     |\  2           |
   2 | \----         | 3
     |      \        |
     2 ------ 3------5 
        2         3
*)    

let minimax_adj_3 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, Inr 1); (2, Inr 2); (3, Inr 2)]);
    (1, [(0, Inr 1); (4, Inr 2)]);
    (2, [(0, Inr 2); (3, Inr 2)]);
    (3, [(0, Inr 2); (2, Inr 2); (5, Inr 3)]);
    (4, [(1, Inr 2); (5, Inr 3)]);
    (5, [(3, Inr 3); (4, Inr 3)])
  ]};; 

(*
print_solution minimax (bs_adj_list_solver minimax minimax_adj_3);;

(0, 0): inr(0)
(0, 1): inr(1)
(0, 2): inr(2)
(0, 3): inr(2)
(0, 4): inr(2)
(0, 5): inr(3)
(1, 0): inr(1)
(1, 1): inr(0)
(1, 2): inr(2)
(1, 3): inr(2)
(1, 4): inr(2)
(1, 5): inr(3)
(2, 0): inr(2)
(2, 1): inr(2)
(2, 2): inr(0)
(2, 3): inr(2)
(2, 4): inr(2)
(2, 5): inr(3)
(3, 0): inr(2)
(3, 1): inr(2)
(3, 2): inr(2)
(3, 3): inr(0)
(3, 4): inr(2)
(3, 5): inr(3)
(4, 0): inr(2)
(4, 1): inr(2)
(4, 2): inr(2)
(4, 3): inr(2)
(4, 4): inr(0)
(4, 5): inr(3)
(5, 0): inr(3)
(5, 1): inr(3)
(5, 2): inr(3)
(5, 3): inr(3)
(5, 4): inr(3)
(5, 5): inr(0)

   3 
   | \
   |  \
   |   \ 
   |    \ 
   |  -- 2
   | /  /| \ 
   | | | |  1 
   | | | |  | \
   5 2  3 4 0  1 
*)
  
let test_gte_adj_1_and_3 = 
  { adj_size = 6;
    adj_list = 
  [
    (0, [(1, w_test_gte 3 1); (2, w_test_gte 1 2); (3, w_test_gte 2 2)]);
    (1, [(0, w_test_gte 3 1); (4, w_test_gte 2 2)]);
    (2, [(0, w_test_gte 1 2); (3, w_test_gte 1 2)]);
    (3, [(0, w_test_gte 2 2); (2, w_test_gte 1 2); (5, w_test_gte 3 3)]);
    (4, [(1, w_test_gte 2 2); (5, w_test_gte 1 3)]);
    (5, [(3, w_test_gte 3 3); (4, w_test_gte 1 3)])
  ]};; 
(* 
print_solution test_gte_nat (test_gte_nat_solver test_gte_adj_1_and_3);;

(0, 0): [[]]
(0, 1): [[inr((3, 1))]]
(0, 2): [[inr((1, 2))]]
(0, 3): [[inr((1, 2))]]
(0, 4): [[inr((3, 1)), inr((2, 2))]]
(0, 5): [[inr((3, 1)), inr((2, 2)), inr((1, 3))]]
(1, 0): [[inr((3, 1))]]
(1, 1): [[]]
(1, 2): [[inr((3, 1)), inr((1, 2))]]
(1, 3): [[inr((3, 1)), inr((1, 2))]]
(1, 4): [[inr((2, 2))]]
(1, 5): [[inr((2, 2)), inr((1, 3))]]
(2, 0): [[inr((1, 2))]]
(2, 1): [[inr((1, 2)), inr((3, 1))]]
(2, 2): [[]]
(2, 3): [[inr((1, 2))]]
(2, 4): [[inr((3, 1)), inr((2, 2))]]
(2, 5): [[inr((3, 1)), inr((2, 2)), inr((1, 3))]]
(3, 0): [[inr((1, 2))]]
(3, 1): [[inr((1, 2)), inr((3, 1))]]
(3, 2): [[inr((1, 2))]]
(3, 3): [[]]
(3, 4): [[inr((3, 1)), inr((2, 2))]]
(3, 5): [[inr((3, 1)), inr((2, 2)), inr((1, 3))]]
(4, 0): [[inr((2, 2)), inr((3, 1))]]
(4, 1): [[inr((2, 2))]]
(4, 2): [[inr((2, 2)), inr((3, 1))]]
(4, 3): [[inr((2, 2)), inr((3, 1))]]
(4, 4): [[]]
(4, 5): [[inr((1, 3))]]
(5, 0): [[inr((1, 3)), inr((2, 2)), inr((3, 1))]]
(5, 1): [[inr((1, 3)), inr((2, 2))]]
(5, 2): [[inr((1, 3)), inr((2, 2)), inr((3, 1))]]
(5, 3): [[inr((1, 3)), inr((2, 2)), inr((3, 1))]]
(5, 4): [[inr((1, 3))]]
(5, 5): [[]]

Can this be viewed as some kind of combo of 


               3
              / \
             /   \
            /     2
           /     / \ 
          1     1   \ 
         /|\   /\   |
        0 2 3  4 5  1

and 

   3 
   | \
   |  \
   |   \ 
   |    \ 
   |  -- 2
   | /  /| \ 
   | | | |  1 
   | | | |  | \
   5 2  3 4 0  1 


*) 
