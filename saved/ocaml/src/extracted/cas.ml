open Datatypes
open Ast
open Basic_types
open Bop
open Brel
open Cas_records
open Construct_certs

(** val eqv_eq_bool : bool eqv **)

let eqv_eq_bool =
  { eqv_eq = brel_eq_bool; eqv_certs = eqv_certs_eq_bool; eqv_ast =
    Ast_eqv_bool }

(** val eqv_eq_nat : int eqv **)

let eqv_eq_nat =
  { eqv_eq = brel_eq_nat; eqv_certs = eqv_certs_eq_nat; eqv_ast =
    Ast_eqv_nat }

(** val eqv_add_constant :
    'a1 eqv -> cas_constant -> 'a1 with_constant eqv **)

let eqv_add_constant eqvS c =
  { eqv_eq = (brel_add_constant eqvS.eqv_eq c); eqv_certs =
    (eqv_certs_add_constant c eqvS.eqv_certs); eqv_ast =
    (Ast_eqv_add_constant (c,eqvS.eqv_ast)) }

(** val eqv_list : 'a1 eqv -> 'a1 list eqv **)

let eqv_list eqvS =
  { eqv_eq = (brel_list eqvS.eqv_eq); eqv_certs =
    (eqv_certs_brel_list eqvS.eqv_certs); eqv_ast = (Ast_eqv_list
    eqvS.eqv_ast) }

(** val eqv_set : 'a1 eqv -> 'a1 finite_set eqv **)

let eqv_set eqvS =
  { eqv_eq = (brel_set eqvS.eqv_eq); eqv_certs =
    (eqv_certs_brel_set eqvS.eqv_eq eqvS.eqv_certs); eqv_ast = (Ast_eqv_set
    eqvS.eqv_ast) }

(** val eqv_product : 'a1 eqv -> 'a2 eqv -> ('a1*'a2) eqv **)

let eqv_product eqvS eqvT =
  { eqv_eq = (brel_product eqvS.eqv_eq eqvT.eqv_eq); eqv_certs =
    (eqv_certs_product eqvS.eqv_certs eqvT.eqv_certs); eqv_ast =
    (Ast_eqv_product (eqvS.eqv_ast,eqvT.eqv_ast)) }

(** val eqv_sum : 'a1 eqv -> 'a2 eqv -> ('a1, 'a2) sum eqv **)

let eqv_sum eqvS eqvT =
  { eqv_eq = (brel_sum eqvS.eqv_eq eqvT.eqv_eq); eqv_certs =
    (eqv_certs_sum eqvS.eqv_certs eqvT.eqv_certs); eqv_ast = (Ast_eqv_sum
    (eqvS.eqv_ast,eqvT.eqv_ast)) }

(** val sg_C_times : int sg_C **)

let sg_C_times =
  { sg_C_eqv = eqv_eq_nat; sg_C_bop = bop_times; sg_C_certs =
    sg_C_certs_times; sg_C_ast = Ast_sg_C_times }

(** val sg_CK_plus : int sg_CK **)

let sg_CK_plus =
  { sg_CK_eqv = eqv_eq_nat; sg_CK_bop = bop_plus; sg_CK_certs =
    sg_CK_certs_plus; sg_CK_ast = Ast_sg_CK_plus }

(** val sg_CS_and : bool sg_CS **)

let sg_CS_and =
  { sg_CS_eqv = eqv_eq_bool; sg_CS_bop = bop_and; sg_CS_certs =
    sg_CS_certs_and; sg_CS_ast = Ast_sg_CS_and }

(** val sg_CS_or : bool sg_CS **)

let sg_CS_or =
  { sg_CS_eqv = eqv_eq_bool; sg_CS_bop = bop_or; sg_CS_certs =
    sg_CS_certs_or; sg_CS_ast = Ast_sg_CS_or }

(** val sg_CS_min : int sg_CS **)

let sg_CS_min =
  { sg_CS_eqv = eqv_eq_nat; sg_CS_bop = bop_min; sg_CS_certs =
    sg_CS_certs_min; sg_CS_ast = Ast_sg_CS_min }

(** val sg_CS_max : int sg_CS **)

let sg_CS_max =
  { sg_CS_eqv = eqv_eq_nat; sg_CS_bop = bop_max; sg_CS_certs =
    sg_CS_certs_max; sg_CS_ast = Ast_sg_CS_max }

(** val sg_concat : 'a1 eqv -> 'a1 list sg **)

let sg_concat eqvS =
  { sg_eq = (eqv_list eqvS); sg_bop = bop_concat; sg_certs =
    (sg_certs_concat eqvS.eqv_certs); sg_ast = (Ast_sg_concat eqvS.eqv_ast) }

(** val sg_left : 'a1 eqv -> 'a1 sg **)

let sg_left eqvS =
  { sg_eq = eqvS; sg_bop = bop_left; sg_certs =
    (sg_certs_left eqvS.eqv_certs); sg_ast = (Ast_sg_left eqvS.eqv_ast) }

(** val sg_right : 'a1 eqv -> 'a1 sg **)

let sg_right eqvS =
  { sg_eq = eqvS; sg_bop = bop_right; sg_certs =
    (sg_certs_right eqvS.eqv_certs); sg_ast = (Ast_sg_right eqvS.eqv_ast) }

(** val sg_add_id : cas_constant -> 'a1 sg -> 'a1 with_constant sg **)

let sg_add_id c sgS =
  { sg_eq = (eqv_add_constant sgS.sg_eq c); sg_bop =
    (bop_add_id sgS.sg_bop c); sg_certs =
    (sg_certs_add_id c sgS.sg_eq.eqv_certs sgS.sg_certs); sg_ast =
    (Ast_sg_add_id (c,sgS.sg_ast)) }

(** val sg_C_add_id : cas_constant -> 'a1 sg_C -> 'a1 with_constant sg_C **)

let sg_C_add_id c sgS =
  { sg_C_eqv = (eqv_add_constant sgS.sg_C_eqv c); sg_C_bop =
    (bop_add_id sgS.sg_C_bop c); sg_C_certs =
    (sg_C_certs_add_id c sgS.sg_C_eqv.eqv_certs sgS.sg_C_certs); sg_C_ast =
    (Ast_sg_C_add_id (c,sgS.sg_C_ast)) }

(** val sg_CI_add_id :
    cas_constant -> 'a1 sg_CI -> 'a1 with_constant sg_CI **)

let sg_CI_add_id c sgS =
  { sg_CI_eqv = (eqv_add_constant sgS.sg_CI_eqv c); sg_CI_bop =
    (bop_add_id sgS.sg_CI_bop c); sg_CI_certs =
    (sg_CI_certs_add_id c sgS.sg_CI_eqv.eqv_certs sgS.sg_CI_certs);
    sg_CI_ast = (Ast_sg_CI_add_id (c,sgS.sg_CI_ast)) }

(** val sg_CS_add_id :
    cas_constant -> 'a1 sg_CS -> 'a1 with_constant sg_CS **)

let sg_CS_add_id c sgS =
  { sg_CS_eqv = (eqv_add_constant sgS.sg_CS_eqv c); sg_CS_bop =
    (bop_add_id sgS.sg_CS_bop c); sg_CS_certs =
    (sg_CS_certs_add_id c sgS.sg_CS_eqv.eqv_certs sgS.sg_CS_certs);
    sg_CS_ast = (Ast_sg_CS_add_id (c,sgS.sg_CS_ast)) }

(** val sg_add_ann : cas_constant -> 'a1 sg -> 'a1 with_constant sg **)

let sg_add_ann c sgS =
  { sg_eq = (eqv_add_constant sgS.sg_eq c); sg_bop =
    (bop_add_ann sgS.sg_bop c); sg_certs =
    (sg_certs_add_ann c sgS.sg_eq.eqv_certs sgS.sg_certs); sg_ast =
    (Ast_sg_add_ann (c,sgS.sg_ast)) }

(** val sg_C_add_ann : cas_constant -> 'a1 sg_C -> 'a1 with_constant sg_C **)

let sg_C_add_ann c sgS =
  { sg_C_eqv = (eqv_add_constant sgS.sg_C_eqv c); sg_C_bop =
    (bop_add_ann sgS.sg_C_bop c); sg_C_certs =
    (sg_C_certs_add_ann c sgS.sg_C_eqv.eqv_certs sgS.sg_C_certs); sg_C_ast =
    (Ast_sg_C_add_ann (c,sgS.sg_C_ast)) }

(** val sg_CI_add_ann :
    cas_constant -> 'a1 sg_CI -> 'a1 with_constant sg_CI **)

let sg_CI_add_ann c sgS =
  { sg_CI_eqv = (eqv_add_constant sgS.sg_CI_eqv c); sg_CI_bop =
    (bop_add_ann sgS.sg_CI_bop c); sg_CI_certs =
    (sg_CI_certs_add_ann c sgS.sg_CI_eqv.eqv_certs sgS.sg_CI_certs);
    sg_CI_ast = (Ast_sg_CI_add_ann (c,sgS.sg_CI_ast)) }

(** val sg_CS_add_ann :
    cas_constant -> 'a1 sg_CS -> 'a1 with_constant sg_CS **)

let sg_CS_add_ann c sgS =
  { sg_CS_eqv = (eqv_add_constant sgS.sg_CS_eqv c); sg_CS_bop =
    (bop_add_ann sgS.sg_CS_bop c); sg_CS_certs =
    (sg_CS_certs_add_ann c sgS.sg_CS_eqv.eqv_certs sgS.sg_CS_certs);
    sg_CS_ast = (Ast_sg_CS_add_ann (c,sgS.sg_CS_ast)) }

(** val sg_product : 'a1 sg -> 'a2 sg -> ('a1*'a2) sg **)

let sg_product sgS sgT =
  { sg_eq = (eqv_product sgS.sg_eq sgT.sg_eq); sg_bop =
    (bop_product sgS.sg_bop sgT.sg_bop); sg_certs =
    (sg_certs_product sgS.sg_eq.eqv_certs sgT.sg_eq.eqv_certs sgS.sg_certs
      sgT.sg_certs); sg_ast = (Ast_sg_product (sgS.sg_ast,sgT.sg_ast)) }

(** val sg_product_new : 'a1 sg_new -> 'a2 sg_new -> ('a1*'a2) sg_new **)

let sg_product_new sgS sgT =
  { sgn_eq = (eqv_product sgS.sgn_eq sgT.sgn_eq); sgn_bop =
    (bop_product sgS.sgn_bop sgT.sgn_bop); sgn_certs =
    (sg_certs_product_new sgS.sgn_eq.eqv_certs sgT.sgn_eq.eqv_certs
      sgS.sgn_certs sgT.sgn_certs); sgn_ast = (Ast_sg_product
    (sgS.sgn_ast,sgT.sgn_ast)) }

(** val sg_C_product : 'a1 sg_C -> 'a2 sg_C -> ('a1*'a2) sg_C **)

let sg_C_product sgS sgT =
  { sg_C_eqv = (eqv_product sgS.sg_C_eqv sgT.sg_C_eqv); sg_C_bop =
    (bop_product sgS.sg_C_bop sgT.sg_C_bop); sg_C_certs =
    (sg_C_certs_product sgS.sg_C_eqv.eqv_eq sgT.sg_C_eqv.eqv_eq sgS.sg_C_bop
      sgT.sg_C_bop sgS.sg_C_eqv.eqv_certs sgT.sg_C_eqv.eqv_certs
      sgS.sg_C_certs sgT.sg_C_certs); sg_C_ast = (Ast_sg_C_product
    (sgS.sg_C_ast,sgT.sg_C_ast)) }

(** val sg_CI_product : 'a1 sg_CI -> 'a2 sg_CI -> ('a1*'a2) sg_CI **)

let sg_CI_product sgS sgT =
  { sg_CI_eqv = (eqv_product sgS.sg_CI_eqv sgT.sg_CI_eqv); sg_CI_bop =
    (bop_product sgS.sg_CI_bop sgT.sg_CI_bop); sg_CI_certs =
    (sg_CI_certs_product sgS.sg_CI_eqv.eqv_eq sgT.sg_CI_eqv.eqv_eq
      sgS.sg_CI_bop sgT.sg_CI_bop sgS.sg_CI_eqv.eqv_certs
      sgT.sg_CI_eqv.eqv_certs sgS.sg_CI_certs sgT.sg_CI_certs); sg_CI_ast =
    (Ast_sg_CI_product (sgS.sg_CI_ast,sgT.sg_CI_ast)) }

(** val sg_left_sum : 'a1 sg -> 'a2 sg -> ('a1, 'a2) sum sg **)

let sg_left_sum sgS sgT =
  { sg_eq = (eqv_sum sgS.sg_eq sgT.sg_eq); sg_bop =
    (bop_left_sum sgS.sg_bop sgT.sg_bop); sg_certs =
    (sg_certs_left_sum sgS.sg_eq.eqv_certs sgT.sg_eq.eqv_certs sgS.sg_certs
      sgT.sg_certs); sg_ast = (Ast_sg_left_sum (sgS.sg_ast,sgT.sg_ast)) }

(** val sg_right_sum : 'a1 sg -> 'a2 sg -> ('a1, 'a2) sum sg **)

let sg_right_sum sgS sgT =
  { sg_eq = (eqv_sum sgS.sg_eq sgT.sg_eq); sg_bop =
    (bop_right_sum sgS.sg_bop sgT.sg_bop); sg_certs =
    (sg_certs_right_sum sgS.sg_eq.eqv_certs sgT.sg_eq.eqv_certs sgS.sg_certs
      sgT.sg_certs); sg_ast = (Ast_sg_right_sum (sgS.sg_ast,sgT.sg_ast)) }

(** val sg_C_left_sum : 'a1 sg_C -> 'a2 sg_C -> ('a1, 'a2) sum sg_C **)

let sg_C_left_sum sgS sgT =
  { sg_C_eqv = (eqv_sum sgS.sg_C_eqv sgT.sg_C_eqv); sg_C_bop =
    (bop_left_sum sgS.sg_C_bop sgT.sg_C_bop); sg_C_certs =
    (sg_C_certs_left_sum sgS.sg_C_eqv.eqv_certs sgT.sg_C_eqv.eqv_certs
      sgS.sg_C_certs sgT.sg_C_certs); sg_C_ast = (Ast_sg_C_left_sum
    (sgS.sg_C_ast,sgT.sg_C_ast)) }

(** val sg_C_right_sum : 'a1 sg_C -> 'a2 sg_C -> ('a1, 'a2) sum sg_C **)

let sg_C_right_sum sgS sgT =
  { sg_C_eqv = (eqv_sum sgS.sg_C_eqv sgT.sg_C_eqv); sg_C_bop =
    (bop_right_sum sgS.sg_C_bop sgT.sg_C_bop); sg_C_certs =
    (sg_C_certs_right_sum sgS.sg_C_eqv.eqv_certs sgT.sg_C_eqv.eqv_certs
      sgS.sg_C_certs sgT.sg_C_certs); sg_C_ast = (Ast_sg_C_right_sum
    (sgS.sg_C_ast,sgT.sg_C_ast)) }

(** val sg_CI_left_sum : 'a1 sg_CI -> 'a2 sg_CI -> ('a1, 'a2) sum sg_CI **)

let sg_CI_left_sum sgS sgT =
  { sg_CI_eqv = (eqv_sum sgS.sg_CI_eqv sgT.sg_CI_eqv); sg_CI_bop =
    (bop_left_sum sgS.sg_CI_bop sgT.sg_CI_bop); sg_CI_certs =
    (sg_CI_certs_left_sum sgS.sg_CI_eqv.eqv_certs sgT.sg_CI_eqv.eqv_certs
      sgS.sg_CI_certs sgT.sg_CI_certs); sg_CI_ast = (Ast_sg_CI_left_sum
    (sgS.sg_CI_ast,sgT.sg_CI_ast)) }

(** val sg_CI_right_sum : 'a1 sg_CI -> 'a2 sg_CI -> ('a1, 'a2) sum sg_CI **)

let sg_CI_right_sum sgS sgT =
  { sg_CI_eqv = (eqv_sum sgS.sg_CI_eqv sgT.sg_CI_eqv); sg_CI_bop =
    (bop_right_sum sgS.sg_CI_bop sgT.sg_CI_bop); sg_CI_certs =
    (sg_CI_certs_right_sum sgS.sg_CI_eqv.eqv_certs sgT.sg_CI_eqv.eqv_certs
      sgS.sg_CI_certs sgT.sg_CI_certs); sg_CI_ast = (Ast_sg_CI_right_sum
    (sgS.sg_CI_ast,sgT.sg_CI_ast)) }

(** val sg_CS_left_sum : 'a1 sg_CS -> 'a2 sg_CS -> ('a1, 'a2) sum sg_CS **)

let sg_CS_left_sum sgS sgT =
  { sg_CS_eqv = (eqv_sum sgS.sg_CS_eqv sgT.sg_CS_eqv); sg_CS_bop =
    (bop_left_sum sgS.sg_CS_bop sgT.sg_CS_bop); sg_CS_certs =
    (sg_CS_certs_left_sum sgS.sg_CS_eqv.eqv_certs sgT.sg_CS_eqv.eqv_certs
      sgS.sg_CS_certs sgT.sg_CS_certs); sg_CS_ast = (Ast_sg_CS_left_sum
    (sgS.sg_CS_ast,sgT.sg_CS_ast)) }

(** val sg_CS_right_sum : 'a1 sg_CS -> 'a2 sg_CS -> ('a1, 'a2) sum sg_CS **)

let sg_CS_right_sum sgS sgT =
  { sg_CS_eqv = (eqv_sum sgS.sg_CS_eqv sgT.sg_CS_eqv); sg_CS_bop =
    (bop_right_sum sgS.sg_CS_bop sgT.sg_CS_bop); sg_CS_certs =
    (sg_CS_certs_right_sum sgS.sg_CS_eqv.eqv_certs sgT.sg_CS_eqv.eqv_certs
      sgS.sg_CS_certs sgT.sg_CS_certs); sg_CS_ast = (Ast_sg_CS_right_sum
    (sgS.sg_CS_ast,sgT.sg_CS_ast)) }

(** val sg_llex : 'a1 sg_CS -> 'a2 sg -> ('a1*'a2) sg **)

let sg_llex sgS sgT =
  { sg_eq = (eqv_product sgS.sg_CS_eqv sgT.sg_eq); sg_bop =
    (bop_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop sgT.sg_bop); sg_certs =
    (sg_certs_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop sgS.sg_CS_eqv.eqv_certs
      sgT.sg_eq.eqv_certs sgS.sg_CS_certs sgT.sg_certs); sg_ast =
    (Ast_sg_llex (sgS.sg_CS_ast,sgT.sg_ast)) }

(** val sg_C_llex : 'a1 sg_CS -> 'a2 sg_C -> ('a1*'a2) sg_C **)

let sg_C_llex sgS sgT =
  { sg_C_eqv = (eqv_product sgS.sg_CS_eqv sgT.sg_C_eqv); sg_C_bop =
    (bop_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop sgT.sg_C_bop); sg_C_certs =
    (sg_C_certs_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop
      sgS.sg_CS_eqv.eqv_certs sgT.sg_C_eqv.eqv_certs sgS.sg_CS_certs
      sgT.sg_C_certs); sg_C_ast = (Ast_sg_C_llex
    (sgS.sg_CS_ast,sgT.sg_C_ast)) }

(** val sg_CI_llex : 'a1 sg_CS -> 'a2 sg_CI -> ('a1*'a2) sg_CI **)

let sg_CI_llex sgS sgT =
  { sg_CI_eqv = (eqv_product sgS.sg_CS_eqv sgT.sg_CI_eqv); sg_CI_bop =
    (bop_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop sgT.sg_CI_bop);
    sg_CI_certs =
    (sg_CI_certs_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop
      sgS.sg_CS_eqv.eqv_certs sgT.sg_CI_eqv.eqv_certs sgS.sg_CS_certs
      sgT.sg_CI_certs); sg_CI_ast = (Ast_sg_CI_llex
    (sgS.sg_CS_ast,sgT.sg_CI_ast)) }

(** val sg_CS_llex : 'a1 sg_CS -> 'a2 sg_CS -> ('a1*'a2) sg_CS **)

let sg_CS_llex sgS sgT =
  { sg_CS_eqv = (eqv_product sgS.sg_CS_eqv sgT.sg_CS_eqv); sg_CS_bop =
    (bop_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop sgT.sg_CS_bop);
    sg_CS_certs =
    (sg_CS_certs_llex sgS.sg_CS_eqv.eqv_eq sgS.sg_CS_bop
      sgS.sg_CS_eqv.eqv_certs sgT.sg_CS_eqv.eqv_certs sgS.sg_CS_certs
      sgT.sg_CS_certs); sg_CS_ast = (Ast_sg_CS_llex
    (sgS.sg_CS_ast,sgT.sg_CS_ast)) }

(** val sg_CI_union_with_ann :
    cas_constant -> 'a1 eqv -> 'a1 finite_set with_constant sg_CI **)

let sg_CI_union_with_ann c eqvS =
  { sg_CI_eqv = (eqv_add_constant (eqv_set eqvS) c); sg_CI_bop =
    (bop_add_ann (bop_union eqvS.eqv_eq) c); sg_CI_certs =
    (sg_CI_certs_union_with_ann c eqvS.eqv_certs); sg_CI_ast =
    (Ast_sg_CI_union_with_ann (c,eqvS.eqv_ast)) }

(** val sg_CI_intersect_with_id :
    cas_constant -> 'a1 eqv -> 'a1 finite_set with_constant sg_CI **)

let sg_CI_intersect_with_id c eqvS =
  { sg_CI_eqv = (eqv_add_constant (eqv_set eqvS) c); sg_CI_bop =
    (bop_add_id (bop_intersect eqvS.eqv_eq) c); sg_CI_certs =
    (sg_CI_certs_intersect_with_id c eqvS.eqv_certs); sg_CI_ast =
    (Ast_sg_CI_intersect_with_id (c,eqvS.eqv_ast)) }

(** val sg_CS_min_with_infinity : int with_constant sg_CS **)

let sg_CS_min_with_infinity =
  sg_CS_add_id cas_infinity sg_CS_min

(** val sg_CS_max_with_infinity : int with_constant sg_CS **)

let sg_CS_max_with_infinity =
  sg_CS_add_ann cas_infinity sg_CS_max

(** val sg_sg_add_zero :
    'a1 sg_sg -> cas_constant -> 'a1 with_constant sg_sg **)

let sg_sg_add_zero sg_sgS c =
  { sg_sg_eqv = (eqv_add_constant sg_sgS.sg_sg_eqv c); sg_sg_plus =
    (bop_add_id sg_sgS.sg_sg_plus c); sg_sg_times =
    (bop_add_ann sg_sgS.sg_sg_times c); sg_sg_plus_certs =
    (sg_certs_add_id c sg_sgS.sg_sg_eqv.eqv_certs sg_sgS.sg_sg_plus_certs);
    sg_sg_times_certs =
    (sg_certs_add_ann c sg_sgS.sg_sg_eqv.eqv_certs sg_sgS.sg_sg_times_certs);
    sg_sg_certs =
    (sg_sg_certs_add_zero sg_sgS.sg_sg_eqv.eqv_certs sg_sgS.sg_sg_certs);
    sg_sg_ast = (Ast_sg_sg_add_zero (c,sg_sgS.sg_sg_ast)) }

(** val sg_C_sg_add_one :
    'a1 sg_C_sg -> cas_constant -> 'a1 with_constant sg_C_sg **)

let sg_C_sg_add_one sg_sgS c =
  { sg_C_sg_eqv = (eqv_add_constant sg_sgS.sg_C_sg_eqv c); sg_C_sg_plus =
    (bop_add_ann sg_sgS.sg_C_sg_plus c); sg_C_sg_times =
    (bop_add_id sg_sgS.sg_C_sg_times c); sg_C_sg_plus_certs =
    (sg_C_certs_add_ann c sg_sgS.sg_C_sg_eqv.eqv_certs
      sg_sgS.sg_C_sg_plus_certs); sg_C_sg_times_certs =
    (sg_certs_add_id c sg_sgS.sg_C_sg_eqv.eqv_certs
      sg_sgS.sg_C_sg_times_certs); sg_C_sg_certs =
    (sg_sg_certs_add_one c sg_sgS.sg_C_sg_eqv.eqv_certs
      sg_sgS.sg_C_sg_plus_certs sg_sgS.sg_C_sg_certs); sg_C_sg_ast =
    (Ast_sg_C_sg_add_one (c,sg_sgS.sg_C_sg_ast)) }

(** val sg_sg_product : 'a1 sg_sg -> 'a2 sg_sg -> ('a1*'a2) sg_sg **)

let sg_sg_product sg_sgS sg_sgT =
  { sg_sg_eqv = (eqv_product sg_sgS.sg_sg_eqv sg_sgT.sg_sg_eqv); sg_sg_plus =
    (bop_product sg_sgS.sg_sg_plus sg_sgT.sg_sg_plus); sg_sg_times =
    (bop_product sg_sgS.sg_sg_times sg_sgT.sg_sg_times); sg_sg_plus_certs =
    (sg_certs_product sg_sgS.sg_sg_eqv.eqv_certs sg_sgT.sg_sg_eqv.eqv_certs
      sg_sgS.sg_sg_plus_certs sg_sgT.sg_sg_plus_certs); sg_sg_times_certs =
    (sg_certs_product sg_sgS.sg_sg_eqv.eqv_certs sg_sgT.sg_sg_eqv.eqv_certs
      sg_sgS.sg_sg_times_certs sg_sgT.sg_sg_times_certs); sg_sg_certs =
    (sg_sg_certs_product sg_sgS.sg_sg_eqv.eqv_certs
      sg_sgT.sg_sg_eqv.eqv_certs sg_sgS.sg_sg_certs sg_sgT.sg_sg_certs);
    sg_sg_ast = (Ast_sg_sg_product (sg_sgS.sg_sg_ast,sg_sgT.sg_sg_ast)) }

(** val sg_C_sg_llex : 'a1 sg_CS_sg -> 'a2 sg_C_sg -> ('a1*'a2) sg_C_sg **)

let sg_C_sg_llex sg_sgS sg_sgT =
  { sg_C_sg_eqv = (eqv_product sg_sgS.sg_CS_sg_eqv sg_sgT.sg_C_sg_eqv);
    sg_C_sg_plus =
    (bop_llex sg_sgS.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus
      sg_sgT.sg_C_sg_plus); sg_C_sg_times =
    (bop_product sg_sgS.sg_CS_sg_times sg_sgT.sg_C_sg_times);
    sg_C_sg_plus_certs =
    (sg_C_certs_llex sg_sgS.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus
      sg_sgS.sg_CS_sg_eqv.eqv_certs sg_sgT.sg_C_sg_eqv.eqv_certs
      sg_sgS.sg_CS_sg_plus_certs sg_sgT.sg_C_sg_plus_certs);
    sg_C_sg_times_certs =
    (sg_certs_product sg_sgS.sg_CS_sg_eqv.eqv_certs
      sg_sgT.sg_C_sg_eqv.eqv_certs sg_sgS.sg_CS_sg_times_certs
      sg_sgT.sg_C_sg_times_certs); sg_C_sg_certs =
    (sg_sg_certs_llex_product sg_sgS.sg_CS_sg_eqv.eqv_eq
      sg_sgT.sg_C_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus sg_sgT.sg_C_sg_plus
      sg_sgT.sg_C_sg_times sg_sgS.sg_CS_sg_eqv.eqv_certs
      sg_sgT.sg_C_sg_eqv.eqv_certs sg_sgS.sg_CS_sg_times_certs
      sg_sgT.sg_C_sg_times_certs sg_sgS.sg_CS_sg_certs sg_sgT.sg_C_sg_certs);
    sg_C_sg_ast = (Ast_sg_C_sg_llex
    (sg_sgS.sg_CS_sg_ast,sg_sgT.sg_C_sg_ast)) }

(** val sg_CS_sg_llex :
    'a1 sg_CS_sg -> 'a2 sg_CS_sg -> ('a1*'a2) sg_CS_sg **)

let sg_CS_sg_llex sg_sgS sg_sgT =
  { sg_CS_sg_eqv = (eqv_product sg_sgS.sg_CS_sg_eqv sg_sgT.sg_CS_sg_eqv);
    sg_CS_sg_plus =
    (bop_llex sg_sgS.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus
      sg_sgT.sg_CS_sg_plus); sg_CS_sg_times =
    (bop_product sg_sgS.sg_CS_sg_times sg_sgT.sg_CS_sg_times);
    sg_CS_sg_plus_certs =
    (sg_CS_certs_llex sg_sgS.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus
      sg_sgS.sg_CS_sg_eqv.eqv_certs sg_sgT.sg_CS_sg_eqv.eqv_certs
      sg_sgS.sg_CS_sg_plus_certs sg_sgT.sg_CS_sg_plus_certs);
    sg_CS_sg_times_certs =
    (sg_certs_product sg_sgS.sg_CS_sg_eqv.eqv_certs
      sg_sgT.sg_CS_sg_eqv.eqv_certs sg_sgS.sg_CS_sg_times_certs
      sg_sgT.sg_CS_sg_times_certs); sg_CS_sg_certs =
    (sg_sg_certs_llex_product sg_sgS.sg_CS_sg_eqv.eqv_eq
      sg_sgT.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus sg_sgT.sg_CS_sg_plus
      sg_sgT.sg_CS_sg_times sg_sgS.sg_CS_sg_eqv.eqv_certs
      sg_sgT.sg_CS_sg_eqv.eqv_certs sg_sgS.sg_CS_sg_times_certs
      sg_sgT.sg_CS_sg_times_certs sg_sgS.sg_CS_sg_certs
      sg_sgT.sg_CS_sg_certs); sg_CS_sg_ast = (Ast_sg_CS_sg_llex
    (sg_sgS.sg_CS_sg_ast,sg_sgT.sg_CS_sg_ast)) }

(** val sg_CI_sg_llex :
    'a1 sg_CS_sg -> 'a2 sg_CI_sg -> ('a1*'a2) sg_CI_sg **)

let sg_CI_sg_llex sg_sgS sg_sgT =
  { sg_CI_sg_eqv = (eqv_product sg_sgS.sg_CS_sg_eqv sg_sgT.sg_CI_sg_eqv);
    sg_CI_sg_plus =
    (bop_llex sg_sgS.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus
      sg_sgT.sg_CI_sg_plus); sg_CI_sg_times =
    (bop_product sg_sgS.sg_CS_sg_times sg_sgT.sg_CI_sg_times);
    sg_CI_sg_plus_certs =
    (sg_CI_certs_llex sg_sgS.sg_CS_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus
      sg_sgS.sg_CS_sg_eqv.eqv_certs sg_sgT.sg_CI_sg_eqv.eqv_certs
      sg_sgS.sg_CS_sg_plus_certs sg_sgT.sg_CI_sg_plus_certs);
    sg_CI_sg_times_certs =
    (sg_certs_product sg_sgS.sg_CS_sg_eqv.eqv_certs
      sg_sgT.sg_CI_sg_eqv.eqv_certs sg_sgS.sg_CS_sg_times_certs
      sg_sgT.sg_CI_sg_times_certs); sg_CI_sg_certs =
    (sg_sg_certs_llex_product sg_sgS.sg_CS_sg_eqv.eqv_eq
      sg_sgT.sg_CI_sg_eqv.eqv_eq sg_sgS.sg_CS_sg_plus sg_sgT.sg_CI_sg_plus
      sg_sgT.sg_CI_sg_times sg_sgS.sg_CS_sg_eqv.eqv_certs
      sg_sgT.sg_CI_sg_eqv.eqv_certs sg_sgS.sg_CS_sg_times_certs
      sg_sgT.sg_CI_sg_times_certs sg_sgS.sg_CS_sg_certs
      sg_sgT.sg_CI_sg_certs); sg_CI_sg_ast = (Ast_sg_CI_sg_llex
    (sg_sgS.sg_CS_sg_ast,sg_sgT.sg_CI_sg_ast)) }

