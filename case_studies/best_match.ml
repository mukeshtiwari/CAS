open Cas;;
open Describe;;
open Matrix_solver;;
  
(* 
 *)

let bs_simulate_best_match = mcas_bs_add_zero (mcas_bs_llex_product (mcas_bs_right mcas_sg_max) mcas_min_plus) infinity;;

(*
mcas_bs_describe_fully bs_simulate_best_match;; 
Class : Commuative and Selective Bi-semigroup
Carrier set:
{INF} + ((nat) * (nat))
Additive properties:
--------------------
Idempotent
Commutative
Selective 
Not Left Cancellative: 
   inr((0, 0)).inr((0, 0)) = inr((0, 0))
   inr((0, 0)).inl(INF) = inr((0, 0))
   inr((0, 0)) <> inl(INF)
Not Right Cancellative: 
   inr((0, 0)).inr((0, 0)) = inr((0, 0))
   inl(INF).inr((0, 0)) = inr((0, 0))
   inr((0, 0)) <> inl(INF)
Not Left Constant: 
   inl(INF).inr((0, 0)) = inr((0, 0))
   inl(INF).inl(INF) = inl(INF)
Not Right Constant: 
   inr((0, 0)).inl(INF) = inr((0, 0))
   inl(INF).inl(INF) = inl(INF)
Not Anti Left: 
   inl(INF).inl(INF) = inl(INF)
Not Anti Right: 
   inl(INF).inl(INF) = inl(INF)
Not Is Left: 
   inl(INF).inr((0, 0)) = inr((0, 0))
Not Is Right: 
   inr((0, 0)).inl(INF) = inr((0, 0))
Identity = inl(INF)
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr((0, 1)).inr((0, 1)) = inr((0, 2))
Not Commutative: 
   inr((1, 0)).inr((0, 0)) = inr((0, 0))
   inr((0, 0)).inr((1, 0)) = inr((1, 0))
Not Selective: 
   inr((1, 1)).inr((0, 0)) = inr((0, 1))
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
No identity
Annihilator = inl(INF)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Not Right Distributive: 
   a = inr((0, 0))
   b = inr((0, 0))
   c = inr((1, 1))
   lhs = (b + c)*a <> b*a + c*a = rhs: 
   b + c = inr((1, 1))
   b*a = inr((0, 0))
   c*a = inr((0, 1))
   lhs = inr((0, 1))
   rhs = inr((0, 0))
Not Left left Absorptive: 
   a = inr((0, 0))
   b = inr((1, 0))
   a <> a + a*b = rhs: 
   a*b = inr((1, 0))
   rhs = inr((1, 0))
Left_Right Absorptive 
Not Right left Absorptive: 
   a = inr((0, 0))
   b = inr((1, 0))
   a <> a*b + a = rhs: 
   a*b = inr((1, 0))
   rhs = inr((1, 0))
Right_Right Absorptive 
	 *)    
