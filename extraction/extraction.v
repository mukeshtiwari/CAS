Require Import CAS.coq.common.compute. 

Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.bool.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.eqv.set.
(*
Require Import CAS.coq.eqv.nat_ceiling.
Require Import CAS.coq.eqv.minset.


Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.
 *)

(*
Require Import CAS.coq.sg.times.
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.left.
Require Import CAS.coq.sg.right.
Require Import CAS.coq.sg.left_sum.
Require Import CAS.coq.sg.right_sum.
Require Import CAS.coq.sg.concat.

Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.sg.minset_union. 
Require Import CAS.coq.sg.lift.
(* Require Import CAS.coq.sg.minset_lift. *) 

Require Import CAS.coq.po.lte_nat. (* why is this not from_sg_left sg_min?*)
Require Import CAS.coq.po.trivial.
*) 
(*
Require Import CAS.coq.po.from_sg_left.
Require Import CAS.coq.po.from_sg_right.
Require Import CAS.coq.po.length.
Require Import CAS.coq.po.add_bottom.
Require Import CAS.coq.po.add_top.
Require Import CAS.coq.po.po_to_qo.
Require Import CAS.coq.po.product.
Require Import CAS.coq.po.llex.
Require Import CAS.coq.po.left_sum. 
Require Import CAS.coq.po.right_sum. 

Require Import CAS.coq.bs.cast_up.

*) 




Require Import CAS.coq.bs.max_min.
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.product.
Require Import CAS.coq.bs.add_zero.
Require Import CAS.coq.bs.add_one.
Require Import CAS.coq.bs.llex_product.

(*
Require Import CAS.coq.bs.min_max.
Require Import CAS.coq.bs.max_plus.
Require Import CAS.coq.bs.dual.
Require Import CAS.coq.bs.left_sum.
Require Import CAS.coq.bs.right_sum.
Require Import CAS.coq.bs.and_or.
Require Import CAS.coq.bs.or_and.
Require Import CAS.coq.bs.union_intersect.
Require Import CAS.coq.bs.intersect_union.
Require Import CAS.coq.bs.union_lift.
Require Import CAS.coq.bs.left.
Require Import CAS.coq.bs.right.
 *)
Require Extraction.


Cd "extraction".

(* Require Import Coq.ExtrOcamlString. *) (* why does this not work?? *) 

(* BEGIN from ExtrOcamlString.v  *)
Require Import Ascii String.

Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".

Extract Inlined Constant ascii_dec => "(=)".

Extract Inductive string => "char list" [ "[]" "(::)" ].



(* End from ExtrOcamlString.v *) 

(* Evaluation / Extraction /Testing  

Set Extraction Optimize. (* DEFAULT *) 
Unset Extraction Optimize.

Set Extraction KeepSingleton. 
Unset Extraction KeepSingleton. (* DEFAULT *) 

Set Extraction AutoInline. (* DEFAULT *) 
Unset Extraction AutoInline.

Extraction Inline qualid1 ... qualidn. 
Extraction NoInline qualid1 ... qualidn.
Print Extraction Inline. 
Reset Extraction Inline.

Extraction qualid.
Recursive Extraction qualid_1 ... qualid_n .
Extraction "file" qualid1 ... qualidn.
Extraction Library ident.

*) 


Set Extraction KeepSingleton. 
Unset Extraction Optimize.
Unset Extraction AutoInline.

(*
Extraction Inline 
   brel_eq_bool
   brel_eq_nat 
   bop_and
   bop_or
   bop_plus
   bop_times 
   bop_min 
   bop_max
   bop_concat
   . 
*)


Extraction Language OCaml. 
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option"  [ "Some" "None" ].
Extract Inductive nat => int [ "0" "succ" ] 
     "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Avoid name clashes *)
Extraction Blacklist List String Int.




(* Separate Extraction  *) 
Extraction "Cas.ml"
   make_constant 
   eqv_eq_nat
   eqv_product
   eqv_add_constant

   mcas_min_plus
   mcas_max_min   
   mcas_bs_product
   mcas_bs_llex_product   
   mcas_bs_add_zero
   mcas_bs_add_one. 

   
(*******************
   
(*   eqv_bool
   eqv_sum
   eqv_list
   eqv_set
   eqv_nat_ceiling
   eqv_minset_from_po
   eqv_minset_from_qo   *) 
(* semigroups 
   sg_C_times 
   sg_CS_and
   sg_CS_or   
*)
   sg_CS_max
   sg_CS_min
   sg_CK_plus
   sg_product
   sg_C_product      
   sg_CI_product
   sg_CK_product
   sg_llex            
   sg_C_llex         
   sg_CI_llex      
   sg_CS_llex
   sg_add_ann
   sg_C_add_ann
   sg_CI_add_ann
   sg_CS_add_ann            
   sg_add_id
   sg_C_add_id
   sg_CI_add_id
   sg_CS_add_id
   sg_left
   sg_right
   sg_concat
   sg_left_sum   
   sg_C_left_sum
   sg_CI_left_sum         
   sg_CS_left_sum      
   sg_right_sum
   sg_C_right_sum            
   sg_CI_right_sum         
   sg_CS_right_sum
   sg_CI_union 
   sg_CI_intersect
   sg_CI_minset_union_from_qo   
   sg_CI_minset_union_from_po
   sg_lift
   (* sg casting *)
   msg_from_sg   
   sg_from_sg_C
   sg_from_sg_CS
   sg_from_sg_CI
   sg_from_sg_CK
   sg_C_from_sg_CI
   sg_C_from_sg_CS
   sg_C_from_sg_CK
   sg_CI_from_sg_CS
   sg_C_option_from_sg
   sg_CI_option_from_sg
   sg_CK_option_from_sg
   sg_CS_option_from_sg 
   sg_CS_option_from_sg_C
   sg_CI_option_from_sg_C
   sg_CK_option_from_sg_C
   sg_CS_option_from_sg_CI
   (* order *)
   lte_nat
   wp_trivial 
(**
   po_add_bottom    
   to_bool 
   to_nat 
   po_dual 
   to_dual
   to_llte  
   to_rlte  
   po_llte  
   po_rlte  
   to_add_top
   to_add_bottom 
   po_add_top

**)   
   (* bi-semigroups *)
   selective_presemiring_max_plus 
   selective_presemiring_min_plus
   selective_distributive_prelattice_min_max
   selective_distributive_prelattice_max_min  
   selective_distributive_lattice_and_or
   selective_distributive_lattice_or_and
   bs_add_one
(* lattice_add_one
   distributive_lattice_add_one   *)
   bs_add_zero
(* semiring_add_zero 
   dioid_add_zero   
   lattice_add_zero
   distributive_lattice_add_zero 
   selective_distributive_lattice_add_zero   
   bs_product
   semiring_product
   dioid_product
*) 
(*   
   semiring_sg_left
   semiring_sg_right

   bs_left_sum
*)
(* bs_right_sum *) 
   bs_llex_product
   bs_CS_llex_product
   bs_CI_union_lift 
   distributive_prelattice_union_intersect
   distributive_prelattice_intersect_union 
   (* cast up *) 
   bs_from_bs_CI
   bs_from_semiring
   semiring_from_dioid
   bs_from_dioid 
   bs_from_selective_dioid  
   dioid_from_distributive_lattice
   bs_from_distributive_prelattice         
   bs_from_distributive_lattice 
   bs_from_selective_distributive_lattice
   bs_from_selective_distributive_prelattice
   bs_from_selective_presemiring   
   (* cast down *) 
   bs_CS_option_from_bs
   (* lattice duals *) 
   lattice_dual
   distributive_lattice_dual
   selective_distributive_lattice_dual
*******************)


