
open Cas;;
open Describe;;
open Matrix_solver;; 

let widest_shortest_paths =
  mcas_bs_add_zero
    (mcas_bs_llex_product
       mcas_min_plus
       (mcas_bs_add_one
	  mcas_max_min
	  infinity))
    infinity;;

let widest_shortest_paths_solver = bs_adj_list_solver widest_shortest_paths;; 

  
(* now, inspect this algebra 
mcas_bs_describe_fully widest_shortest_paths;;

Class : Selective Dioid
(S_0, +_0, *_0) = min_plus
where
S_0 = nat
x +_0 y = x min y
x *_0 y = x + y
(S_1, +_1, *_1) = max_min
where
S_1 = nat
x +_1 y = x max y
x *_1 y = x min y
(S_2, +_2, *_2) = bs_add_one (S_1, +_1, *_1) INF
where
S_2 = {INF} + S_1
Inr(x) +_2 Inr(y) = Inr(x +_1 y)
Inl(INF) +_2 _ = Inl(INF)
_ +_2 Inl(INF) = Inl(INF)
Inr(x) *_2 Inr(y) = Inr(x *_1 y)
Inl(INF) *_2 a = a
a *_2 Inl(INF) = a
(S_3, +_3, *_3) = bs_llex_product (S_0, +_0, *_0) (S_2, +_2, *_2)
where
S_3 = S_0 * S_2
(a, b) +_3 (c, d) = (a, b +_2 d) (if a = a +_0 c = c)
(a, b) +_3 (c, d) = (a, b) (if a = a +_0 c <> c)
(a, b) +_3 (c, d) = (c, d) (if a <> a +_0 c = c)
(a, b) *_3 (c, d) = (a *_0 c, b *_2 d)
(S_4, +_4, *_4) = bs_add_zero (S_3, +_3, *_3) INF
where
S_4 = {INF} + S_3
Inr(x) +_4 Inr(y) = Inr(x +_3 y)
Inl(INF) +_4 a = a
a +_4 Inl(INF) = a
Inr(x) *_4 Inr(y) = Inr(x *_3 y)
Inl(INF) *_4 _ = Inl(INF)
_ *_4 Inl(INF) = Inl(INF)
Additive properties:
--------------------
Identity = inl(INF)
Annihilator = inr((0, inl(INF)))
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
Multiplicative properties:
-------------------------
Identity = inr((0, inl(INF)))
Annihilator = inl(INF)
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
let sol_1 = widest_shortest_paths_solver adj_1;; 
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



