Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.construct_certs. 
Require Import CAS.code.cas_records.
Require Import CAS.code.cast. 
Require Import CAS.code.cas. 

(* Require Import Coq.ExtrOcamlString.v. *) (* why does this not work?? *) 

(* BEGIN from ExtrOcamlString.v *) 
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


Extraction Language Ocaml. 
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option"  [ "Some" "None" ].
Extract Inductive nat => int [ "0" "succ" ] 
     "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Avoid name clashes *)
Extraction Blacklist List String Int.

Cd "extraction".

Separate Extraction 

   (* eqv *) 
   eqv_eq_bool
   eqv_eq_nat
   eqv_add_constant
   eqv_list
   eqv_set 
   eqv_product
   eqv_sum

   (* sg *) 
   sg_times
   sg_plus
   sg_and
   sg_or 
   sg_min
   sg_max
   sg_concat
   sg_left
   sg_right
   sg_add_id
   sg_add_ann
   sg_left_sum
   sg_right_sum
   sg_product
   sg_llex
   sg_union
   sg_intersect 

   sg_C_times
   sg_C_add_ann
   sg_C_left_sum
   sg_C_right_sum
   sg_C_product
   sg_C_llex

   sg_CS_and
   sg_CS_or 
   sg_CS_min
   sg_CS_max
   sg_CS_add_id
   sg_CS_add_ann
   sg_CS_left_sum
   sg_CS_right_sum
   sg_CS_llex
   sg_CS_min_with_infinity
   sg_CS_max_with_infinity

   sg_CI_add_id
   sg_CI_add_ann
   sg_CI_left_sum
   sg_CI_right_sum
   sg_CI_product
   sg_CI_llex

   sg_CK_plus

   (* sg casts *) 
   sg_from_sg_C
   sg_C_from_sg_CI
   sg_CI_from_sg_CS
   sg_C_from_sg_CK
   sg_from_sg_CI
   sg_from_sg_CK
   sg_C_from_sg_CS
   sg_from_sg_CS
   sg_C_option_from_sg
   sg_CI_option_from_sg_C
   sg_CS_option_from_sg_CI
   sg_CK_option_from_sg_C
   sg_CI_option_from_sg
   sg_CK_option_from_sg
   sg_CS_option_from_sg_C
   sg_CS_option_from_sg

   (* bs *) 
   bs_and_or 
   bs_or_and 
   bs_min_max 
   bs_max_min
   bs_min_plus
   bs_max_plus

   bs_union_intersect 
   bs_intersect_union 

   bs_add_zero
   bs_add_one 
   bs_product

(*

   bs_min_times 
   bs_max_times 
   bs_llex
   bs_CS_llex
*)    .

