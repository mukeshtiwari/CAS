open Cas;;
open Describe;;
open Matrix_solver;;
  
(* 
   This file contains an from Section 4.11.3 
   of "Path Problems in Networks" by Baras and Theodorakopoulos. 

   This is a good example of a semiring where (+) is not idempotent. 

   Here's the idea: 

   A*[i,j] should be (w, c), where w is the shortest path weight 
   from i to j, and c is the number of distinct paths of this weight. 

   The book claims to define a semiring, but it does not. 
   Here we fix that. But the resulting semiring is not 0-stable. 

 *)

(* Note that the book defines this as follows *)

let geodetic_not_correct =mcas_bs_llex_product ( mcas_bs_add_zero mcas_min_plus infinity) mcas_plus_times ;;

(*
Note: this has the additive and multiplicative ids as in the book. 
(+) Identity = (inl(INF), 0)
(x) Identity = (inr(0), 1)

However, it is not left or right distributive! 

mcas_bs_describe_fully geodetic_not_correct;;
Class : Bi-semigroup
Carrier set:
({INF} + (nat)) * (nat)
Additive properties:
--------------------
Not Idempotent: 
   (inl(INF), 1).(inl(INF), 1) = (inl(INF), 2)
Commutative
Not Selective: 
   (inl(INF), 1).(inl(INF), 1) = (inl(INF), 2)
Not Left Cancellative: 
   (inr(0), 0).(inl(INF), 0) = (inr(0), 0)
   (inr(0), 0).(inl(INF), 1) = (inr(0), 0)
   (inl(INF), 0) <> (inl(INF), 1)
Not Right Cancellative: 
   (inl(INF), 0).(inr(0), 0) = (inr(0), 0)
   (inl(INF), 1).(inr(0), 0) = (inr(0), 0)
   (inl(INF), 0) <> (inl(INF), 1)
Not Left Constant: 
   (inl(INF), 0).(inr(0), 0) = (inr(0), 0)
   (inl(INF), 0).(inr(0), 1) = (inr(0), 1)
Not Right Constant: 
   (inr(0), 0).(inl(INF), 0) = (inr(0), 0)
   (inr(0), 1).(inl(INF), 0) = (inr(0), 1)
Not Anti Left: 
   (inr(0), 0).(inl(INF), 0) = (inr(0), 0)
Not Anti Right: 
   (inl(INF), 0).(inr(0), 0) = (inr(0), 0)
Not Is Left: 
   (inl(INF), 0).(inr(0), 0) = (inr(0), 0)
Not Is Right: 
   (inr(0), 0).(inl(INF), 0) = (inr(0), 0)
Identity = (inl(INF), 0)
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   (inr(1), 0).(inr(1), 0) = (inr(2), 0)
Commutative
Not Selective: 
   (inr(0), 0).(inl(INF), 1) = (inl(INF), 0)
Not Left Cancellative: 
   (inl(INF), 0).(inr(0), 0) = (inl(INF), 0)
   (inl(INF), 0).(inr(1), 0) = (inl(INF), 0)
   (inr(0), 0) <> (inr(1), 0)
Not Right Cancellative: 
   (inr(0), 0).(inl(INF), 0) = (inl(INF), 0)
   (inr(1), 0).(inl(INF), 0) = (inl(INF), 0)
   (inr(0), 0) <> (inr(1), 0)
Not Left Constant: 
   (inr(0), 0).(inr(0), 0) = (inr(0), 0)
   (inr(0), 0).(inl(INF), 0) = (inl(INF), 0)
Not Right Constant: 
   (inr(0), 0).(inr(0), 0) = (inr(0), 0)
   (inl(INF), 0).(inr(0), 0) = (inl(INF), 0)
Not Anti Left: 
   (inl(INF), 0).(inr(0), 0) = (inl(INF), 0)
Not Anti Right: 
   (inr(0), 0).(inl(INF), 0) = (inl(INF), 0)
Not Is Left: 
   (inr(0), 0).(inl(INF), 0) = (inl(INF), 0)
Not Is Right: 
   (inl(INF), 0).(inr(0), 0) = (inl(INF), 0)
Identity = (inr(0), 1)
Annihilator = (inl(INF), 0)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Not Left Distributive:
   a = (inl(INF), 1)
   b = (inr(0), 0)
   c = (inr(1), 1)
   lhs = a*(b + c) <> a*b + a*c = rhs: 
   b + c = (inr(0), 0)
   a*b = (inl(INF), 0)
   a*c = (inl(INF), 1)
   lhs = (inl(INF), 0)
   rhs = (inl(INF), 1)
Not Right Distributive: 
   a = (inl(INF), 1)
   b = (inr(0), 0)
   c = (inr(1), 1)
   lhs = (b + c)*a <> b*a + c*a = rhs: 
   b + c = (inr(0), 0)
   b*a = (inl(INF), 0)
   c*a = (inl(INF), 1)
   lhs = (inl(INF), 0)
   rhs = (inl(INF), 1)
Not Left left Absorptive: 
   a = (inl(INF), 1)
   b = (inr(0), 1)
   a <> a + a*b = rhs: 
   a*b = (inl(INF), 1)
   rhs = (inl(INF), 2)
Not Left Right Absorptive: 
   a = (inl(INF), 1)
   b = (inr(0), 1)
   a <> a + b*a = rhs: 
   b*a = (inl(INF), 1)
   rhs = (inl(INF), 2)
Not Right left Absorptive: 
   a = (inl(INF), 1)
   b = (inr(0), 1)
   a <> a*b + a = rhs: 
   a*b = (inl(INF), 1)
   rhs = (inl(INF), 2)
Not Right left Absorptive: 
   a = (inl(INF), 1)
   b = (inr(0), 1)
   a <> b*a + a = rhs: 
   b*a = (inl(INF), 1)
   rhs = (inl(INF), 2)
- : unit = ()
# 

 *)   
  
(* now, let's fix the definition by postponing the addition of zero until the end. *) 
let geodetic = mcas_bs_add_zero (mcas_bs_llex_product mcas_min_plus mcas_plus_times) infinity;;

(*

mcas_bs_describe_fully geodetic;;
Class : Semiring
Carrier set:
{INF} + ((nat) * (nat))
Additive properties:
--------------------
Not Idempotent: 
   inr((0, 1)).inr((0, 1)) = inr((0, 2))
Commutative
Not Selective: 
   inr((0, 1)).inr((0, 1)) = inr((0, 2))
Not Left Cancellative: 
   inr((0, 0)).inr((1, 0)) = inr((0, 0))
   inr((0, 0)).inl(INF) = inr((0, 0))
   inr((1, 0)) <> inl(INF)
Not Right Cancellative: 
   inr((1, 0)).inr((0, 0)) = inr((0, 0))
   inl(INF).inr((0, 0)) = inr((0, 0))
   inr((1, 0)) <> inl(INF)
Not Left Constant: 
   inl(INF).inr((0, 0)) = inr((0, 0))
   inl(INF).inr((1, 0)) = inr((1, 0))
Not Right Constant: 
   inr((0, 0)).inl(INF) = inr((0, 0))
   inr((1, 0)).inl(INF) = inr((1, 0))
Not Anti Left: 
   inr((0, 0)).inl(INF) = inr((0, 0))
Not Anti Right: 
   inl(INF).inr((0, 0)) = inr((0, 0))
Not Is Left: 
   inl(INF).inr((0, 0)) = inr((0, 0))
Not Is Right: 
   inr((0, 0)).inl(INF) = inr((0, 0))
Identity = inl(INF)
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr((1, 0)).inr((1, 0)) = inr((2, 0))
Commutative
Not Selective: 
   inr((0, 0)).inr((1, 1)) = inr((1, 0))
Not Left Cancellative: 
   inl(INF).inr((0, 0)) = inl(INF)
   inl(INF).inr((1, 0)) = inl(INF)
   inr((0, 0)) <> inr((1, 0))
Not Right Cancellative: 
   inr((0, 0)).inl(INF) = inl(INF)
   inr((1, 0)).inl(INF) = inl(INF)
   inr((0, 0)) <> inr((1, 0))
Not Left Constant: 
   inr((0, 0)).inr((0, 0)) = inr((0, 0))
   inr((0, 0)).inl(INF) = inl(INF)
Not Right Constant: 
   inr((0, 0)).inr((0, 0)) = inr((0, 0))
   inl(INF).inr((0, 0)) = inl(INF)
Not Anti Left: 
   inl(INF).inr((0, 0)) = inl(INF)
Not Anti Right: 
   inr((0, 0)).inl(INF) = inl(INF)
Not Is Left: 
   inr((0, 0)).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr((0, 0)) = inl(INF)
Identity = inr((0, 1))
Annihilator = inl(INF)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Not Left left Absorptive: 
   a = inr((0, 1))
   b = inr((0, 1))
   a <> a + a*b = rhs: 
   a*b = inr((0, 1))
   rhs = inr((0, 2))
Not Left Right Absorptive: 
   a = inr((0, 1))
   b = inr((0, 1))
   a <> a + b*a = rhs: 
   b*a = inr((0, 1))
   rhs = inr((0, 2))
Not Right left Absorptive: 
   a = inr((0, 1))
   b = inr((0, 1))
   a <> a*b + a = rhs: 
   a*b = inr((0, 1))
   rhs = inr((0, 2))
Not Right left Absorptive: 
   a = inr((0, 1))
   b = inr((0, 1))
   a <> b*a + a = rhs: 
   b*a = inr((0, 1))
   rhs = inr((0, 2))
- : unit = ()
# 

 *)   


  
