
open Cas;;
open Describe;;

let next_hop_sets  = mcas_bs_union_lift (mcas_sg_left eqv_eq_nat);;
  
(* mcas_bs_describe_fully next_hop_sets;;

Class : Semiring
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

(*

mcas_bs_describe_fully pre_sp_with_nh_sets;;

Class : Semiring
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
Multiplicative properties:
-------------------------
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


take a look at zero and one: 

match pre_sp_with_nh_sets with | BS_semiring b -> b.semiring_id_ann_certs | _ -> complain "Blah";;
- : (int * int Cas.finite_set) Cas.with_constant Cas.pid_is_tann_certificates
=
{pid_is_tann_plus_times =
  Assert_Exists_Id_Ann_Equal
   (Inl
     {constant_ascii = ['I'; 'N'; 'F'];
      constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 pid_is_tann_times_plus_d = Id_Ann_Cert_None}

 *)

let sp_with_nh_sets = mcas_bs_add_one pre_sp_with_nh_sets self ;;

(* 
Note: A(i, j) has the form inr(inr((w, {j}))) or inr (inl infinity) 

mcas_bs_describe_fully sp_with_nh_sets;;

Class : Commuative and Idempotent Bi-semigroup
Additive properties:
--------------------
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

let next_hop_sets    = mcas_slt_union_singleton eqv_eq_nat;;
let slt_min_plus_nhs = mcas_slt_llex_product mcas_slt_min_plus_one next_hop_sets

 *) 

