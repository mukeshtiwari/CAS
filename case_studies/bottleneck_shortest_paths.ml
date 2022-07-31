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
             = {(c,d) in X union Y | for all (a,b) in (X union Y), not ((a,b) <_1 (a,b))} 
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

-----

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

