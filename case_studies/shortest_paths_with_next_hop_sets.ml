
open Cas;;
open Describe;;

let next_hop_sets  = mcas_bs_union_lift (mcas_sg_left mcas_eqv_eq_nat);;
  
(* mcas_bs_describe_fully next_hop_sets;;

Class : Semiring
(S_0, *_0) = sg_left nat
S_0 = nat
x *_0 y = x
(S_1, +_1, *_1) = bs_union_lift (S_0, *_0)
S_1 = set(S_0)
X +_1 Y = X union Y
X *_1 Y = {x *_0 y | x in X, y in Y}
Additive properties:
--------------------
Identity = {}
No annihilator
Idempotent
Commutative
Not Selective: 
   {0}.{1} = {0, 1}
Not Left Cancellative: 
   {0, 1}.{0} = {1, 0}
   {0, 1}.{1} = {0, 1}
   {0} <> {1}
Not Right Cancellative: 
   {0}.{0, 1} = {0, 1}
   {1}.{0, 1} = {0, 1}
   {0} <> {1}
Not Left Constant: 
   {}.{0} = {0}
   {}.{} = {}
Not Right Constant: 
   {0}.{} = {0}
   {}.{} = {}
Not Anti Left: 
   {0}.{0} = {0}
Not Anti Right: 
   {0}.{0} = {0}
Not Is Left: 
   {}.{0} = {0}
Not Is Right: 
   {0}.{} = {0}
Multiplicative properties:
-------------------------
No identity
Annihilator = {}
Idempotent
Not Commutative: 
   {0}.{1} = {0}
   {1}.{0} = {1}
Selective 
Not Left Cancellative: 
   {}.{0} = {}
   {}.{1} = {}
   {0} <> {1}
Not Right Cancellative: 
   {0}.{} = {}
   {1}.{} = {}
   {0} <> {1}
Not Left Constant: 
   {0}.{0} = {0}
   {0}.{} = {}
Not Right Constant: 
   {0}.{0} = {0}
   {}.{0} = {}
Not Anti Left: 
   {}.{} = {}
Not Anti Right: 
   {}.{} = {}
Not Is Left: 
   {0}.{} = {}
Not Is Right: 
   {}.{0} = {}
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Not Left Right Absorptive: 
   a = {1}
   b = {0}
   a <> a + b*a = rhs: 
   b*a = {0}
   rhs = {1, 0}
Right_Left Absorptive
Not Right left Absorptive: 
   a = {1}
   b = {0}
   a <> b*a + a = rhs: 
   b*a = {0}
   rhs = {0, 1}

*)   

let pre_sp_with_nh_sets = mcas_bs_add_zero (mcas_bs_llex_product mcas_min_plus next_hop_sets) infinity;;

(* mcas_bs_describe_fully pre_sp_with_nh_sets;;

Class : Semiring
(S_0, +_0, *_0) = min_plus
where
S_0 = nat
x +_0 y = x min y
x *_0 y = x + y
(S_1, *_1) = sg_left nat
S_1 = nat
x *_1 y = x
(S_2, +_2, *_2) = bs_union_lift (S_1, *_1)
S_2 = set(S_1)
X +_2 Y = X union Y
X *_2 Y = {x *_1 y | x in X, y in Y}
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
No annihilator
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
Multiplicative properties:
-------------------------
No identity
Annihilator = inl(INF)
Not Idempotent: 
   inr((1, {0})).inr((1, {0})) = inr((2, {0}))
Not Commutative: 
   inr((0, {0})).inr((0, {1})) = inr((0, {0}))
   inr((0, {1})).inr((0, {0})) = inr((0, {1}))
Not Selective: 
   inr((0, {})).inr((1, {0})) = inr((1, {}))
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
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Not Left Right Absorptive: 
   a = inr((0, {1}))
   b = inr((0, {0}))
   a <> a + b*a = rhs: 
   b*a = inr((0, {0}))
   rhs = inr((0, {1, 0}))
Right_Left Absorptive
Not Right left Absorptive: 
   a = inr((0, {1}))
   b = inr((0, {0}))
   a <> b*a + a = rhs: 
   b*a = inr((0, {0}))
   rhs = inr((0, {0, 1}))

 *)

let sp_with_nh_sets = mcas_bs_add_one pre_sp_with_nh_sets self ;;

(* 
Note: A(i, j) has the form inr(inr((w, {j}))) or inr (inl infinity) 

mcas_bs_describe_fully sp_with_nh_sets;;
Class : Commuative and Idempotent Bi-semigroup
(S_0, +_0, *_0) = min_plus
where
S_0 = nat
x +_0 y = x min y
x *_0 y = x + y
(S_1, *_1) = sg_left nat
S_1 = nat
x *_1 y = x
(S_2, +_2, *_2) = bs_union_lift (S_1, *_1)
S_2 = set(S_1)
X +_2 Y = X union Y
X *_2 Y = {x *_1 y | x in X, y in Y}
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
(S_5, +_5, *_5) = bs_add_one (S_4, +_4, *_4) SELF
where
S_5 = {SELF} + S_4
Inr(x) +_5 Inr(y) = Inr(x +_4 y)
Inl(SELF) +_5 _ = Inl(SELF)
_ +_5 Inl(SELF) = Inl(SELF)
Inr(x) *_5 Inr(y) = Inr(x *_4 y)
Inl(SELF) *_5 a = a
a *_5 Inl(SELF) = a
Additive properties:
--------------------
Identity = inr(inl(INF))
Annihilator = inl(SELF)
Idempotent
Commutative
Not Selective: 
   inr(inr((0, {0}))).inr(inr((0, {1}))) = inr(inr((0, {0, 1})))
Not Left Cancellative: 
   inr(inr((0, {0, 1}))).inr(inr((0, {0}))) = inr(inr((0, {1, 0})))
   inr(inr((0, {0, 1}))).inr(inr((0, {1}))) = inr(inr((0, {0, 1})))
   inr(inr((0, {0}))) <> inr(inr((0, {1})))
Not Right Cancellative: 
   inr(inr((0, {0}))).inr(inr((0, {0, 1}))) = inr(inr((0, {0, 1})))
   inr(inr((0, {1}))).inr(inr((0, {0, 1}))) = inr(inr((0, {0, 1})))
   inr(inr((0, {0}))) <> inr(inr((0, {1})))
Not Left Constant: 
   inr(inl(INF)).inl(SELF) = inl(SELF)
   inr(inl(INF)).inr(inl(INF)) = inr(inl(INF))
Not Right Constant: 
   inl(SELF).inr(inl(INF)) = inl(SELF)
   inr(inl(INF)).inr(inl(INF)) = inr(inl(INF))
Not Anti Left: 
   inl(SELF).inl(SELF) = inl(SELF)
Not Anti Right: 
   inl(SELF).inl(SELF) = inl(SELF)
Not Is Left: 
   inr(inl(INF)).inl(SELF) = inl(SELF)
Not Is Right: 
   inl(SELF).inr(inl(INF)) = inl(SELF)
Multiplicative properties:
-------------------------
Identity = inl(SELF)
Annihilator = inr(inl(INF))
Not Idempotent: 
   inr(inr((1, {0}))).inr(inr((1, {0}))) = inr(inr((2, {0})))
Not Commutative: 
   inr(inr((0, {0}))).inr(inr((0, {1}))) = inr(inr((0, {0})))
   inr(inr((0, {1}))).inr(inr((0, {0}))) = inr(inr((0, {1})))
Not Selective: 
   inr(inr((0, {}))).inr(inr((1, {0}))) = inr(inr((1, {})))
Not Left Cancellative: 
   inr(inl(INF)).inr(inr((0, {0}))) = inr(inl(INF))
   inr(inl(INF)).inl(SELF) = inr(inl(INF))
   inr(inr((0, {0}))) <> inl(SELF)
Not Right Cancellative: 
   inr(inr((0, {0}))).inr(inl(INF)) = inr(inl(INF))
   inl(SELF).inr(inl(INF)) = inr(inl(INF))
   inr(inr((0, {0}))) <> inl(SELF)
Not Left Constant: 
   inl(SELF).inr(inl(INF)) = inr(inl(INF))
   inl(SELF).inr(inr((0, {0}))) = inr(inr((0, {0})))
Not Right Constant: 
   inr(inl(INF)).inl(SELF) = inr(inl(INF))
   inr(inr((0, {0}))).inl(SELF) = inr(inr((0, {0})))
Not Anti Left: 
   inr(inl(INF)).inl(SELF) = inr(inl(INF))
Not Anti Right: 
   inl(SELF).inr(inl(INF)) = inr(inl(INF))
Not Is Left: 
   inl(SELF).inr(inl(INF)) = inr(inl(INF))
Not Is Right: 
   inr(inl(INF)).inl(SELF) = inr(inl(INF))
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Not Right Distributive: 
   a = inr(inr((0, {1})))
   b = inl(SELF)
   c = inr(inr((0, {0})))
   lhs = (b + c)*a <> b*a + c*a = rhs: 
   b + c = inl(SELF)
   b*a = inr(inr((0, {1})))
   c*a = inr(inr((0, {0})))
   lhs = inr(inr((0, {1})))
   rhs = inr(inr((0, {1, 0})))
Left Left Absorptive
Not Left Right Absorptive: 
   a = inr(inr((0, {1})))
   b = inr(inr((0, {0})))
   a <> a + b*a = rhs: 
   b*a = inr(inr((0, {0})))
   rhs = inr(inr((0, {1, 0})))
Right_Left Absorptive
Not Right left Absorptive: 
   a = inr(inr((0, {1})))
   b = inr(inr((0, {0})))
   a <> b*a + a = rhs: 
   b*a = inr(inr((0, {0})))
   rhs = inr(inr((0, {0, 1})))

 *)   

(* Alternatives? 

let slt_min_plus_nhs = mcas_slt_llex_product 
                           mcas_slt_min_plus_one 
                           (mcas_slt_union_insert mcas_eqv_eq_nat)
 *) 

let union_insert = mcas_slt_union_insert mcas_eqv_eq_nat;; 
(*
mcas_slt_describe_fully union_insert;; 

Class : Selective Left Pre-Dioid
(L_0, S_0, +_0, *_0) = slt_union_insert nat
L_0 = nat
S_0 = set(nat)
X +_0 Y = X union Y
x |>_0 Y = {x} union Y
Special values:
Additive annihilator:
No Annihilator
Identity = {}
 No Annihilator
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   {0}.{1} = {0, 1}
Not Left Cancellative: 
   {0, 1}.{0} = {1, 0}
   {0, 1}.{1} = {0, 1}
   {0} <> {1}
Not Right Cancellative: 
   {0}.{0, 1} = {0, 1}
   {1}.{0, 1} = {0, 1}
   {0} <> {1}
Not Left Constant: 
   {}.{0} = {0}
   {}.{} = {}
Not Right Constant: 
   {0}.{} = {0}
   {}.{} = {}
Not Anti Left: 
   {0}.{0} = {0}
Not Anti Right: 
   {0}.{0} = {0}
Not Is Left: 
   {}.{0} = {0}
Not Is Right: 
   {0}.{} = {0}
Multiplicative properties:
-------------------------
Not Left Cancellative: 
   0.{} = {0}
   0.{0} = {0}
   {} <> {0}
Not Left Constant: 
   0|>{} = {0}
   0|>{1} = {0, 1}
Not Is Right: 
   0|>{} = {0}
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Not Absorptive: 
   x = {}
   l = 0
   x <> x + l|>x = rhs: 
   l|>x = {0}
   rhs = {0}
Not Strictly Absorptive (since not Absorptive): 
   x = {}
   l = 0
   x <> x + l|>x = rhs: 
   l|>x = {0}
   rhs = {0}


 *) 

let min_plus_one_llex_union_insert = mcas_slt_llex_product mcas_slt_min_plus_one union_insert;;
(*  
mcas_slt_describe_fully min_plus_one_llex_union_insert;; 

mcas_slt_describe_fully min_plus_one_llex_union_insert;; 
Class : Left Semigroup Transform
(S_0, +_0, *_0) = slt_min_plus_one
where
L_0 = nat
S_0 = nat
x +_0 y = x min y
x *_0 y = 1 + x + y
(L_1, S_1, +_1, *_1) = slt_union_insert nat
L_1 = nat
S_1 = set(nat)
X +_1 Y = X union Y
x |>_1 Y = {x} union Y
(L_2, S_2, +_2, *_2) = slt_llex_product (L_0, S_0, +_0, |>_0) (L_1, S_1, +_1, |>_1)
where
L_2 = L_0 * L_1
S_2 = S_0 * S_1
(a, b) +_2 (c, d) = (a, b +_1 d) (if a = a +_0 c = c)
(a, b) +_2 (c, d) = (a, b) (if a = a +_0 c <> c)
(a, b) +_2 (c, d) = (c, d) (if a <> a +_0 c = c)
(a, b) |>_2 (c, d) = (a |>_0 c, b |>_1 d)
Special values:
Additive annihilator:
No Annihilator
No Identity 
No Annihilator
Additive properties:
--------------------
Idempotent
Commutative
Not Selective: 
   (0, {0}).(0, {1}) = (0, {0, 1})
Not Left Cancellative: 
   (0, {0}).(1, {0}) = (0, {0})
   (0, {0}).(1, {}) = (0, {0})
   (1, {0}) <> (1, {})
Not Right Cancellative: 
   (1, {0}).(0, {0}) = (0, {0})
   (1, {}).(0, {0}) = (0, {0})
   (1, {0}) <> (1, {})
Not Left Constant: 
   (1, {0}).(0, {0}) = (0, {0})
   (1, {0}).(0, {}) = (0, {})
Not Right Constant: 
   (0, {0}).(1, {0}) = (0, {0})
   (0, {}).(1, {0}) = (0, {})
Not Anti Left: 
   (0, {0}).(1, {0}) = (0, {0})
Not Anti Right: 
   (1, {0}).(0, {0}) = (0, {0})
Not Is Left: 
   (1, {0}).(0, {0}) = (0, {0})
Not Is Right: 
   (0, {0}).(1, {0}) = (0, {0})
Multiplicative properties:
-------------------------
Not Left Cancellative: 
   (0, 0).(0, {}) = (1, {0})
   (0, 0).(0, {0}) = (1, {0})
   (0, {}) <> (0, {0})
Not Left Constant: 
   (0, 0)|>(0, {0}) = (1, {0})
   (0, 0)|>(1, {0}) = (2, {0})
Not Is Right: 
   (0, 0)|>(0, {0}) = (1, {0})
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Absorptive
Strictly Absorptive
*) 
