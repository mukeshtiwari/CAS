
open Cas;;
open Describe;;
open Matrix_solver;;

  (*
   This file contains an from Section 4.11.4
   of "Path Problems in Networks" by Baras and Theodorakopoulos. 

   A*[i,j] should be (w, X), where w is the shortest path weight 
   from i to j, and X is the set of all possible nodes these paths traverse. 

   The book defines a very complicated mess that we won't even attempt to implement. 
 *)   
let min_plus_with_node_sets = mcas_bs_add_zero (mcas_bs_llex_product mcas_min_plus (mcas_bs_union_union mcas_eqv_eq_nat)) infinity;;
(*

mcas_bs_describe pre_min_plus_with_node_sets;;
Class : Semiring
Carrier set:
{INF} + ((nat) * ((nat) set))
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   inr((0, {0})).inr((0, {1})) = inr((0, {0, 1}))
Identity = inl(INF)
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr((1, {0})).inr((1, {0})) = inr((2, {0}))
Commutative
Not Selective: 
   inr((0, {0})).inr((1, {})) = inr((1, {0}))
Identity = inr((0, {}))
Annihilator = inl(INF)
Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 



mcas_bs_describe_fully pre_min_plus_with_node_sets;;
Class : Semiring
Carrier set:
{INF} + ((nat) * ((nat) set))
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   inr((0, {0})).inr((0, {1})) = inr((0, {0, 1}))
Not Left Cancellative: 
   inr((0, {0})).inr((1, {0})) = inr((0, {0}))
   inr((0, {0})).inl(INF) = inr((0, {0}))
   inr((1, {0})) <> inl(INF)
Not Right Cancellative: 
   inr((1, {0})).inr((0, {0})) = inr((0, {0}))
   inl(INF).inr((0, {0})) = inr((0, {0}))
   inr((1, {0})) <> inl(INF)
Not Left Constant: 
   inl(INF).inr((0, {0})) = inr((0, {0}))
   inl(INF).inr((1, {0})) = inr((1, {0}))
Not Right Constant: 
   inr((0, {0})).inl(INF) = inr((0, {0}))
   inr((1, {0})).inl(INF) = inr((1, {0}))
Not Anti Left: 
   inr((0, {0})).inl(INF) = inr((0, {0}))
Not Anti Right: 
   inl(INF).inr((0, {0})) = inr((0, {0}))
Not Is Left: 
   inl(INF).inr((0, {0})) = inr((0, {0}))
Not Is Right: 
   inr((0, {0})).inl(INF) = inr((0, {0}))
Identity = inl(INF)
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr((1, {0})).inr((1, {0})) = inr((2, {0}))
Commutative
Not Selective: 
   inr((0, {0})).inr((1, {})) = inr((1, {0}))
Not Left Cancellative: 
   inl(INF).inr((0, {0})) = inl(INF)
   inl(INF).inr((1, {0})) = inl(INF)
   inr((0, {0})) <> inr((1, {0}))
Not Right Cancellative: 
   inr((0, {0})).inl(INF) = inl(INF)
   inr((1, {0})).inl(INF) = inl(INF)
   inr((0, {0})) <> inr((1, {0}))
Not Left Constant: 
   inr((0, {0})).inr((0, {0})) = inr((0, {0}))
   inr((0, {0})).inl(INF) = inl(INF)
Not Right Constant: 
   inr((0, {0})).inr((0, {0})) = inr((0, {0}))
   inl(INF).inr((0, {0})) = inl(INF)
Not Anti Left: 
   inl(INF).inr((0, {0})) = inl(INF)
Not Anti Right: 
   inr((0, {0})).inl(INF) = inl(INF)
Not Is Left: 
   inr((0, {0})).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr((0, {0})) = inl(INF)
Identity = inr((0, {}))
Annihilator = inl(INF)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Not Left left Absorptive: 
   a = inr((0, {}))
   b = inr((0, {0}))
   a <> a + a*b = rhs: 
   a*b = inr((0, {0}))
   rhs = inr((0, {0}))
Not Left Right Absorptive: 
   a = inr((0, {}))
   b = inr((0, {0}))
   a <> a + b*a = rhs: 
   b*a = inr((0, {0}))
   rhs = inr((0, {0}))
Not Right left Absorptive: 
   a = inr((0, {}))
   b = inr((0, {0}))
   a <> a*b + a = rhs: 
   a*b = inr((0, {0}))
   rhs = inr((0, {0}))
Not Right left Absorptive: 
   a = inr((0, {}))
   b = inr((0, {0}))
   a <> b*a + a = rhs: 
   b*a = inr((0, {0}))
   rhs = inr((0, {0}))

 *) 
