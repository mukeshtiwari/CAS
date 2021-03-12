
(*
From main directory 

./casml 

then 

#use "tests/mcas_demo.ml";; 

Or use Tuareg ... 

 *)

open Mcas;;

let e0 = eqv_nat;;
eqv_describe  e0;;   
let e1 = eqv_bool;;
eqv_describe  e1;; 
let e2 = eqv_product e0 e1;;
eqv_describe  e2;;
let e3 = eqv_sum e0 e2;;
eqv_describe  e3;;
let e4 = eqv_list e3;;
eqv_describe  e4;;
let e5 = eqv_set e4;;
eqv_describe  e5;;
(* should have a guard for n < 0 *)     
let e6 = eqv_nat_ceiling 7;;     
eqv_describe  e6;;
List.map (Cas.eqv_new e6) [0;1;2;3;4;5;6;7;8;9];;
let e7 = eqv_add_constant infinity e5;;  
eqv_describe  e7;;   
(* eqv_minset po ? *) 

    
let s1 =   sg_max;;
sg_describe_fully s1;;
let s2 =   sg_min;;    
sg_describe_fully s2;;
let s3 =   sg_and;;        
sg_describe_fully s3;;
let s4 =   sg_or;;        
sg_describe_fully s4;;
let s5 =   sg_plus;;        
sg_describe_fully s5;;
let s6 =   sg_times;;        
sg_describe_fully s6;;
let s7 =   sg_product s5 s6;;        
sg_describe_fully s7;;
let s9 =   sg_left e1;;        
sg_describe_fully s9;;                    
let s10 =   sg_right e1;;        
sg_describe_fully s10;;
let s11 =   sg_concat e1;;        
sg_describe_fully s11;;
let s12 =   sg_left_sum s7 s9;;        
sg_describe_fully s12;;    
let s13 = sg_add_id infinity sg_min;;
sg_describe_fully s13;;
let s14 = sg_add_ann infinity sg_plus;;
sg_describe_fully s14;;
let s15= sg_llex sg_max sg_min ;;
sg_describe_fully s15;;     
    
    
let sg_max_llex_min = sg_llex sg_max sg_min ;;
sg_describe_fully sg_max_llex_min;; 

let sg_min_llex_max = sg_llex sg_min sg_max ;;
sg_describe_fully sg_min_llex_max;; 
  
let sg1 = sg_and <*> sg_or <*> sg_min <*> sg_max <*> sg_times <*> sg_plus;; 
sg_describe_fully sg1;; 

let sg2 = sg_and <*> sg_or <*> sg_min <*> sg_max;; 
sg_describe_fully sg2;;

bs_describe_fully bs_min_plus;; (* no zero, 1 = 0 *)
bs_describe_fully bs_max_min;;  (* zero = 1, no 1 *)       
  
let bs_min_plus_llex_max_min = bs_min_plus <!**> bs_max_min;;
bs_describe_fully bs_min_plus_llex_max_min;;  (* no zero, no one *) 

let bs_min_plus_infinity  = bs_add_zero bs_min_plus infinity ;; 
bs_describe_fully  bs_min_plus_infinity;; 

let bs_max_min_self  = bs_add_one bs_max_min self ;; 
bs_describe_fully  bs_max_min_self;; 

let bs_min_plus_llex_max_min_v2 = bs_min_plus_infinity <!**>  bs_max_min_self;;
bs_describe_fully bs_min_plus_llex_max_min_v2;;  (* not distributive *) 

let bs_min_plus_llex_max_min_v3 = bs_min_plus <!**>  bs_max_min_self;;
bs_describe_fully bs_min_plus_llex_max_min_v3;;  (* distributive, no zero *) 
  
let bs_min_plus_llex_max_min_v4 = bs_add_zero bs_min_plus_llex_max_min_v3 infinity ;;
bs_describe_fully bs_min_plus_llex_max_min_v4;;  (* *) 

let bs_max_min_llex_min_plus = bs_max_min <!**> bs_min_plus;;
bs_describe_fully bs_max_min_llex_min_plus;;  (* not distributive, no 0, no 1 *) 

bs_describe_fully (bs_max_min <!++> bs_min_plus);; 

  (* **** *) 
let bs_union_lift_left  = bs_union_lift (sg_left (eqv_nat_ceiling 5));;  
let bs_union_lift_right = bs_union_lift (sg_right (eqv_nat_ceiling 5));;
(*
bs_describe_fully bs_union_lift_left;;
Carrier type :
([5 + 1]) set

Additive operation :
--------------------
union([5 + 1])
Idempotent
Commutative
Not Selective : 
   {0}.{1} = {0, 1}
Identity {}
Annihilator {6, 5, 4, 3, 2, 1, 0}

Multiplicative operation :
--------------------------
lift(left([5 + 1]))
Idempotent
Not Commutative : 
   {0}.{1} = {0}
   {1}.{0} = {1}
Selective 
No Identity
Annihilator {}

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 
plus id = times annihilator
times id <> plus annihilator


bs_describe_fully bs_union_lift_right;;
Carrier type :
([5 + 1]) set

Additive operation :
--------------------
union([5 + 1])
Idempotent
Commutative
Not Selective : 
   {0}.{1} = {0, 1}
Identity {}
Annihilator {6, 5, 4, 3, 2, 1, 0}

Multiplicative operation :
--------------------------
lift(right([5 + 1]))
Idempotent
Not Commutative : 
   {1}.{0} = {0}
   {0}.{1} = {1}
Selective 
No Identity
Annihilator {}

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 
plus id = times annihilator
times id <> plus annihilator
*)
  
let bs_sp_llex_union_lift_left  = bs_llex_product bs_min_plus bs_union_lift_left;;
let bs_sp_llex_union_lift_right = bs_llex_product bs_min_plus bs_union_lift_right;;
(*
bs_describe_fully bs_sp_llex_union_lift_left;;
Carrier type :
(int * ([5 + 1]) set)

Additive operation :
--------------------
llex(min, union([5 + 1]))
Idempotent
Commutative
Not Selective : 
   (0, {0}).(0, {1}) = (0, {0, 1})
No Identity
Annihilator (0, {6, 5, 4, 3, 2, 1, 0})

Multiplicative operation :
--------------------------
product(plus, lift(left([5 + 1])))
Not Idempotent : 
   (1, {0}).(1, {0}) = (2, {0})
Not Commutative : 
   (0, {0}).(0, {1}) = (0, {0})
   (0, {1}).(0, {0}) = (0, {1})
Not Selective : 
   (0, {}).(1, {0}) = (1, {})
No Identity
No Annihilator

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 
plus id <> times annihilator
times id <> plus annihilator



bs_describe_fully bs_sp_llex_union_lift_right;;
Carrier type :
(int * ([5 + 1]) set)

Additive operation :
--------------------
llex(min, union([5 + 1]))
Idempotent
Commutative
Not Selective : 
   (0, {0}).(0, {1}) = (0, {0, 1})
No Identity
Annihilator (0, {6, 5, 4, 3, 2, 1, 0})

Multiplicative operation :
--------------------------
product(plus, lift(right([5 + 1])))
Not Idempotent : 
   (1, {0}).(1, {0}) = (2, {0})
Not Commutative : 
   (0, {1}).(0, {0}) = (0, {0})
   (0, {0}).(0, {1}) = (0, {1})
Not Selective : 
   (0, {}).(1, {0}) = (1, {})
No Identity
No Annihilator

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 
plus id <> times annihilator
times id <> plus annihilator
  
*)
  
let bs_add_zero_sp_llex_union_lift_left  = bs_add_zero bs_sp_llex_union_lift_left infinity;; 
let bs_add_zero_sp_llex_union_lift_right = bs_add_zero bs_sp_llex_union_lift_right infinity;;
(*  
bs_describe_fully bs_add_zero_sp_llex_union_lift_left;;
Carrier type :
({INFINITY} + (int * ([5 + 1]) set))

Additive operation :
--------------------
add_id(INFINITY, llex(min, union([5 + 1])))
Idempotent
Commutative
Not Selective : 
   inr((0, {0})).inr((0, {1})) = inr((0, {0, 1}))
Identity inl(INFINITY)
Annihilator inr((0, {6, 5, 4, 3, 2, 1, 0}))

Multiplicative operation :
--------------------------
add_nn(INFINITY, product(plus, lift(left([5 + 1]))))
Not Idempotent : 
   inr((1, {0})).inr((1, {0})) = inr((2, {0}))
Not Commutative : 
   inr((0, {0})).inr((0, {1})) = inr((0, {0}))
   inr((0, {1})).inr((0, {0})) = inr((0, {1}))
Not Selective : 
   inr((0, {})).inr((1, {0})) = inr((1, {}))
No Identity
Annihilator inl(INFINITY)

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 
plus id = times annihilator
times id <> plus annihilator

 
bs_describe_fully bs_add_zero_sp_llex_union_lift_right;;
Carrier type :
({INFINITY} + (int * ([5 + 1]) set))

Additive operation :
--------------------
add_id(INFINITY, llex(min, union([5 + 1])))
Idempotent
Commutative
Not Selective : 
   inr((0, {0})).inr((0, {1})) = inr((0, {0, 1}))
Identity inl(INFINITY)
Annihilator inr((0, {6, 5, 4, 3, 2, 1, 0}))

Multiplicative operation :
--------------------------
add_nn(INFINITY, product(plus, lift(right([5 + 1]))))
Not Idempotent : 
   inr((1, {0})).inr((1, {0})) = inr((2, {0}))
Not Commutative : 
   inr((0, {1})).inr((0, {0})) = inr((0, {0}))
   inr((0, {0})).inr((0, {1})) = inr((0, {1}))
Not Selective : 
   inr((0, {})).inr((1, {0})) = inr((1, {}))
No Identity
Annihilator inl(INFINITY)

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Right Distributive 
plus id = times annihilator
times id <> plus annihilator

*)  

let bs_add_one_zero_sp_llex_union_lift_left  = bs_add_one bs_add_zero_sp_llex_union_lift_left self;; 
let bs_add_one_zero_sp_llex_union_lift_right = bs_add_one bs_add_zero_sp_llex_union_lift_right self;; 
(*  
bs_describe_fully bs_add_one_zero_sp_llex_union_lift_left;;
Carrier type :
({SELF} + ({INFINITY} + (int * ([5 + 1]) set)))

Additive operation :
--------------------
add_nn(SELF, add_id(INFINITY, llex(min, union([5 + 1]))))
Idempotent
Commutative
Not Selective : 
   inr(inr((0, {0}))).inr(inr((0, {1}))) = inr(inr((0, {0, 1})))
Identity inr(inl(INFINITY))
Annihilator inl(SELF)

Multiplicative operation :
--------------------------
add_id(SELF, add_nn(INFINITY, product(plus, lift(left([5 + 1])))))
Not Idempotent : 
   inr(inr((1, {0}))).inr(inr((1, {0}))) = inr(inr((2, {0})))
Not Commutative : 
   inr(inr((0, {0}))).inr(inr((0, {1}))) = inr(inr((0, {0})))
   inr(inr((0, {1}))).inr(inr((0, {0}))) = inr(inr((0, {1})))
Not Selective : 
   inr(inr((0, {}))).inr(inr((1, {0}))) = inr(inr((1, {})))
Identity inl(SELF)
Annihilator inr(inl(INFINITY))

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Left Distributive
Not Right Distributive : 
   a = inr(inr((0, {1})))
   b = inl(SELF)
   c = inr(inr((0, {0})))
   lhs = (b + c)*a <> b*a + c*a = rhs : 
   b + c = inl(SELF)
   b*a = inr(inr((0, {1})))
   c*a = inr(inr((0, {0})))
   lhs = inr(inr((0, {1})))
   rhs = inr(inr((0, {1, 0})))
plus id = times annihilator
times id = plus annihilator

  
bs_describe_fully bs_add_one_zero_sp_llex_union_lift_right;;
Carrier type :
({SELF} + ({INFINITY} + (int * ([5 + 1]) set)))

Additive operation :
--------------------
add_nn(SELF, add_id(INFINITY, llex(min, union([5 + 1]))))
Idempotent
Commutative
Not Selective : 
   inr(inr((0, {0}))).inr(inr((0, {1}))) = inr(inr((0, {0, 1})))
Identity inr(inl(INFINITY))
Annihilator inl(SELF)

Multiplicative operation :
--------------------------
add_id(SELF, add_nn(INFINITY, product(plus, lift(right([5 + 1])))))
Not Idempotent : 
   inr(inr((1, {0}))).inr(inr((1, {0}))) = inr(inr((2, {0})))
Not Commutative : 
   inr(inr((0, {1}))).inr(inr((0, {0}))) = inr(inr((0, {0})))
   inr(inr((0, {0}))).inr(inr((0, {1}))) = inr(inr((0, {1})))
Not Selective : 
   inr(inr((0, {}))).inr(inr((1, {0}))) = inr(inr((1, {})))
Identity inl(SELF)
Annihilator inr(inl(INFINITY))

Interaction of Additive and Multiplicative operations: 
-------------------------------------------------------
Not Left Distributive : 
   a = inr(inr((0, {1})))
   b = inl(SELF)
   c = inr(inr((0, {0})))
   lhs = a*(b + c) <> a*b + a*c = rhs : 
   b + c = inl(SELF)
   a*b = inr(inr((0, {1})))
   a*c = inr(inr((0, {0})))
   lhs = inr(inr((0, {1})))
   rhs = inr(inr((0, {1, 0})))
Right Distributive 
plus id = times annihilator
times id = plus annihilator

-----------------------------------------

Abstractly: for bs_add_zero_sp_llex_union_lift_right we have 

Left_Right Absorptive 
Not Right left Absorptive : 
   a = inr((0, {1}))
   b = inr((0, {0}))
   a <> a*b + a = rhs : 
   a*b = inr((0, {0}))
   rhs = inr((0, {0, 1}))

from which add_one constructs the left-dist counter example 

-----------------------------------------
Really want routes of form

infinity  or 
self      or 
(d, X), d <> 0

*)    
