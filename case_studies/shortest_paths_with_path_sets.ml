open Cas;;
open Describe;;


let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;

let sg_paths = mcas_sg_concat eqv_edge;;

let bs_path_sets = mcas_bs_union_lift sg_paths;;

(*
mcas_bs_describe_fully bs_path_sets;; 

Class : Semiring
Carrier set:
(((nat) * (nat)) list) set
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
Identity = {}
No annihilator
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
Identity = {[]}
Annihilator = {}
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

*)   

let bs_min_plus_with_paths = mcas_bs_add_zero (mcas_bs_llex_product mcas_min_plus bs_path_sets) infinity;; 

(*
mcas_bs_describe_fully bs_min_plus_with_paths;;
Class : Semiring
Carrier set:
{INF} + ((nat) * ((((nat) * (nat)) list) set))
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   inr((0, {[]})).inr((0, {[(0, 0)]})) = inr((0, {[], [(0, 0)]}))
Not Left Cancellative: 
   inr((0, {[]})).inr((1, {[]})) = inr((0, {[]}))
   inr((0, {[]})).inl(INF) = inr((0, {[]}))
   inr((1, {[]})) <> inl(INF)
Not Right Cancellative: 
   inr((1, {[]})).inr((0, {[]})) = inr((0, {[]}))
   inl(INF).inr((0, {[]})) = inr((0, {[]}))
   inr((1, {[]})) <> inl(INF)
Not Left Constant: 
   inl(INF).inr((0, {[]})) = inr((0, {[]}))
   inl(INF).inr((1, {[]})) = inr((1, {[]}))
Not Right Constant: 
   inr((0, {[]})).inl(INF) = inr((0, {[]}))
   inr((1, {[]})).inl(INF) = inr((1, {[]}))
Not Anti Left: 
   inr((0, {[]})).inl(INF) = inr((0, {[]}))
Not Anti Right: 
   inl(INF).inr((0, {[]})) = inr((0, {[]}))
Not Is Left: 
   inl(INF).inr((0, {[]})) = inr((0, {[]}))
Not Is Right: 
   inr((0, {[]})).inl(INF) = inr((0, {[]}))
Identity = inl(INF)
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   inr((1, {[]})).inr((1, {[]})) = inr((2, {[]}))
Not Commutative: 
   inr((0, {[(0, 0)]})).inr((0, {[(1, 0)]})) = inr((0, {[(0, 0), (1, 0)]}))
   inr((0, {[(1, 0)]})).inr((0, {[(0, 0)]})) = inr((0, {[(1, 0), (0, 0)]}))
Not Selective: 
   inr((0, {})).inr((1, {[]})) = inr((1, {}))
Not Left Cancellative: 
   inl(INF).inr((0, {[]})) = inl(INF)
   inl(INF).inr((1, {[]})) = inl(INF)
   inr((0, {[]})) <> inr((1, {[]}))
Not Right Cancellative: 
   inr((0, {[]})).inl(INF) = inl(INF)
   inr((1, {[]})).inl(INF) = inl(INF)
   inr((0, {[]})) <> inr((1, {[]}))
Not Left Constant: 
   inr((0, {[]})).inr((0, {[]})) = inr((0, {[]}))
   inr((0, {[]})).inl(INF) = inl(INF)
Not Right Constant: 
   inr((0, {[]})).inr((0, {[]})) = inr((0, {[]}))
   inl(INF).inr((0, {[]})) = inl(INF)
Not Anti Left: 
   inl(INF).inr((0, {[]})) = inl(INF)
Not Anti Right: 
   inr((0, {[]})).inl(INF) = inl(INF)
Not Is Left: 
   inr((0, {[]})).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr((0, {[]})) = inl(INF)
Identity = inr((0, {[]}))
Annihilator = inl(INF)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Not Left left Absorptive: 
   a = inr((0, {[]}))
   b = inr((0, {[(0, 0)]}))
   a <> a + a*b = rhs: 
   a*b = inr((0, {[(0, 0)]}))
   rhs = inr((0, {[], [(0, 0)]}))
Not Left Right Absorptive: 
   a = inr((0, {[]}))
   b = inr((0, {[(0, 0)]}))
   a <> a + b*a = rhs: 
   b*a = inr((0, {[(0, 0)]}))
   rhs = inr((0, {[], [(0, 0)]}))
Not Right left Absorptive: 
   a = inr((0, {[]}))
   b = inr((0, {[(0, 0)]}))
   a <> a*b + a = rhs: 
   a*b = inr((0, {[(0, 0)]}))
   rhs = inr((0, {[(0, 0)], []}))
Not Right left Absorptive: 
   a = inr((0, {[]}))
   b = inr((0, {[(0, 0)]}))
   a <> b*a + a = rhs: 
   b*a = inr((0, {[(0, 0)]}))
   rhs = inr((0, {[(0, 0)], []}))

 *)   

let bs_min_plus_with_paths2 = mcas_bs_llex_product (mcas_bs_add_zero mcas_min_plus infinity) bs_path_sets ;; 

(*
mcas_bs_describe_fully bs_min_plus_with_paths2;;
Class : Commuative and Idempotent Bi-semigroup
Carrier set:
({INF} + (nat)) * ((((nat) * (nat)) list) set)
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   (inl(INF), {[]}).(inl(INF), {[(0, 0)]}) = (inl(INF), {[], [(0, 0)]})
Not Left Cancellative: 
   (inl(INF), {[], [(0, 0)]}).(inl(INF), {[]}) = (inl(INF), {[(0, 0)], []})
   (inl(INF), {[], [(0, 0)]}).(inl(INF), {[(0, 0)]}) = (inl(INF), {[], [(0, 0)]})
   (inl(INF), {[]}) <> (inl(INF), {[(0, 0)]})
Not Right Cancellative: 
   (inl(INF), {[]}).(inl(INF), {[], [(0, 0)]}) = (inl(INF), {[], [(0, 0)]})
   (inl(INF), {[(0, 0)]}).(inl(INF), {[], [(0, 0)]}) = (inl(INF), {[], [(0, 0)]})
   (inl(INF), {[]}) <> (inl(INF), {[(0, 0)]})
Not Left Constant: 
   (inl(INF), {[]}).(inr(0), {[]}) = (inr(0), {[]})
   (inl(INF), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
Not Right Constant: 
   (inr(0), {[]}).(inl(INF), {[]}) = (inr(0), {[]})
   (inl(INF), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
Not Anti Left: 
   (inl(INF), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
Not Anti Right: 
   (inl(INF), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
Not Is Left: 
   (inl(INF), {[]}).(inr(0), {[]}) = (inr(0), {[]})
Not Is Right: 
   (inr(0), {[]}).(inl(INF), {[]}) = (inr(0), {[]})
Identity = (inl(INF), {})
No annihilator
Multiplicative properties:
-------------------------
Not Idempotent: 
   (inr(1), {[]}).(inr(1), {[]}) = (inr(2), {[]})
Not Commutative: 
   (inl(INF), {[(0, 0)]}).(inl(INF), {[(1, 0)]}) = (inl(INF), {[(0, 0), (1, 0)]})
   (inl(INF), {[(1, 0)]}).(inl(INF), {[(0, 0)]}) = (inl(INF), {[(1, 0), (0, 0)]})
Not Selective: 
   (inr(0), {}).(inl(INF), {[]}) = (inl(INF), {})
Not Left Cancellative: 
   (inl(INF), {[]}).(inr(0), {[]}) = (inl(INF), {[]})
   (inl(INF), {[]}).(inr(1), {[]}) = (inl(INF), {[]})
   (inr(0), {[]}) <> (inr(1), {[]})
Not Right Cancellative: 
   (inr(0), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
   (inr(1), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
   (inr(0), {[]}) <> (inr(1), {[]})
Not Left Constant: 
   (inr(0), {[]}).(inr(0), {[]}) = (inr(0), {[]})
   (inr(0), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
Not Right Constant: 
   (inr(0), {[]}).(inr(0), {[]}) = (inr(0), {[]})
   (inl(INF), {[]}).(inr(0), {[]}) = (inl(INF), {[]})
Not Anti Left: 
   (inl(INF), {}).(inr(0), {}) = (inl(INF), {})
Not Anti Right: 
   (inr(0), {}).(inl(INF), {}) = (inl(INF), {})
Not Is Left: 
   (inr(0), {[]}).(inl(INF), {[]}) = (inl(INF), {[]})
Not Is Right: 
   (inl(INF), {[]}).(inr(0), {[]}) = (inl(INF), {[]})
Identity = (inr(0), {[]})
Annihilator = (inl(INF), {})
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Not Left Distributive:
   a = (inl(INF), {[]})
   b = (inr(0), {})
   c = (inr(1), {[]})
   lhs = a*(b + c) <> a*b + a*c = rhs: 
   b + c = (inr(0), {})
   a*b = (inl(INF), {})
   a*c = (inl(INF), {[]})
   lhs = (inl(INF), {})
   rhs = (inl(INF), {[]})
Not Right Distributive: 
   a = (inl(INF), {[]})
   b = (inr(0), {})
   c = (inr(1), {[]})
   lhs = (b + c)*a <> b*a + c*a = rhs: 
   b + c = (inr(0), {})
   b*a = (inl(INF), {})
   c*a = (inl(INF), {[]})
   lhs = (inl(INF), {})
   rhs = (inl(INF), {[]})
Not Left left Absorptive: 
   a = (inl(INF), {[]})
   b = (inr(0), {[(0, 0)]})
   a <> a + a*b = rhs: 
   a*b = (inl(INF), {[(0, 0)]})
   rhs = (inl(INF), {[], [(0, 0)]})
Not Left Right Absorptive: 
   a = (inl(INF), {[]})
   b = (inr(0), {[(0, 0)]})
   a <> a + b*a = rhs: 
   b*a = (inl(INF), {[(0, 0)]})
   rhs = (inl(INF), {[], [(0, 0)]})
Not Right left Absorptive: 
   a = (inl(INF), {[]})
   b = (inr(0), {[(0, 0)]})
   a <> a*b + a = rhs: 
   a*b = (inl(INF), {[(0, 0)]})
   rhs = (inl(INF), {[(0, 0)], []})
Not Right left Absorptive: 
   a = (inl(INF), {[]})
   b = (inr(0), {[(0, 0)]})
   a <> b*a + a = rhs: 
   b*a = (inl(INF), {[(0, 0)]})
   rhs = (inl(INF), {[(0, 0)], []})

   *) 
