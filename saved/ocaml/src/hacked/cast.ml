(*open Ast
open Basic_types
open Cas_records
open Cef
open Cert_records
open Certificates
*) 

(** val sg_certs_from_sg_C_certs :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a1
    sg_C_certificates -> 'a1 sg_certificates **)

let sg_certs_from_sg_C_certs r b eqvS sgS =
  let ntS = eqvS.eqv_nontrivial in
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Negate f = ntS.certify_nontrivial_negate in
  { sg_commutative_d = Certify_Commutative; sg_selective_d =
  sgS.sg_C_selective_d; sg_idempotent_d = sgS.sg_C_idempotent_d;
  sg_exists_id_d = sgS.sg_C_exists_id_d; sg_exists_ann_d =
  sgS.sg_C_exists_ann_d; sg_is_left_d = (Certify_Not_Is_Left
  (cef_commutative_implies_not_is_left r b s f)); sg_is_right_d =
  (Certify_Not_Is_Right (cef_commutative_implies_not_is_right r b s f));
  sg_left_cancel_d = sgS.sg_C_left_cancel_d; sg_right_cancel_d =
  sgS.sg_C_right_cancel_d; sg_left_constant_d = sgS.sg_C_left_constant_d;
  sg_right_constant_d = sgS.sg_C_right_constant_d; sg_anti_left_d =
  sgS.sg_C_anti_left_d; sg_anti_right_d = sgS.sg_C_anti_right_d }

(** val sg_from_sg_C : 'a1 sg_C -> 'a1 sg **)

let sg_from_sg_C sg_CS0 =
  { sg_eq = sg_CS0.sg_C_eqv; sg_bop = sg_CS0.sg_C_bop; sg_certs =
    (sg_certs_from_sg_C_certs sg_CS0.sg_C_eqv.eqv_eq sg_CS0.sg_C_bop
      sg_CS0.sg_C_eqv.eqv_certs sg_CS0.sg_C_certs); sg_ast =
    (Ast_sg_from_sg_C sg_CS0.sg_C_ast) }

(** val sg_C_certs_from_sg_CI_certs :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a1
    sg_CI_certificates -> 'a1 sg_C_certificates **)

let sg_C_certs_from_sg_CI_certs r b eqvS sgS =
  let ntS = eqvS.eqv_nontrivial in
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Negate f = ntS.certify_nontrivial_negate in
  { sg_C_selective_d = sgS.sg_CI_selective_d; sg_C_idempotent_d =
  Certify_Idempotent; sg_C_exists_id_d = sgS.sg_CI_exists_id_d;
  sg_C_exists_ann_d = sgS.sg_CI_exists_ann_d; sg_C_left_cancel_d =
  (Certify_Not_Left_Cancellative
  (match sgS.sg_CI_selective_d with
   | Certify_Selective ->
     cef_selective_and_commutative_imply_not_left_cancellative r b s f
   | Certify_Not_Selective p ->
     let s1,s2 = p in
     cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative
       b s1 s2)); sg_C_right_cancel_d = (Certify_Not_Right_Cancellative
  (match sgS.sg_CI_selective_d with
   | Certify_Selective ->
     cef_selective_and_commutative_imply_not_right_cancellative r b s f
   | Certify_Not_Selective p ->
     let s1,s2 = p in
     cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative
       b s1 s2)); sg_C_left_constant_d = (Certify_Not_Left_Constant
  (cef_idempotent_and_commutative_imply_not_left_constant r b s f));
  sg_C_right_constant_d = (Certify_Not_Right_Constant
  (cef_idempotent_and_commutative_imply_not_right_constant r b s f));
  sg_C_anti_left_d = (Certify_Not_Anti_Left
  (cef_idempotent_implies_not_anti_left s)); sg_C_anti_right_d =
  (Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s)) }

(** val sg_C_from_sg_CI : 'a1 sg_CI -> 'a1 sg_C **)

let sg_C_from_sg_CI sgS =
  { sg_C_eqv = sgS.sg_CI_eqv; sg_C_bop = sgS.sg_CI_bop; sg_C_certs =
    (sg_C_certs_from_sg_CI_certs sgS.sg_CI_eqv.eqv_eq sgS.sg_CI_bop
      sgS.sg_CI_eqv.eqv_certs sgS.sg_CI_certs); sg_C_ast =
    (Ast_sg_C_from_sg_CI sgS.sg_CI_ast) }

(** val sg_CI_certs_from_sg_CS_certs :
    'a1 sg_CS_certificates -> 'a1 sg_CI_certificates **)

let sg_CI_certs_from_sg_CS_certs sgS =
  { sg_CI_selective_d = Certify_Selective; sg_CI_exists_id_d =
    sgS.sg_CS_exists_id_d; sg_CI_exists_ann_d = sgS.sg_CS_exists_ann_d }

(** val sg_CI_from_sg_CS : 'a1 sg_CS -> 'a1 sg_CI **)

let sg_CI_from_sg_CS sgS =
  { sg_CI_eqv = sgS.sg_CS_eqv; sg_CI_bop = sgS.sg_CS_bop; sg_CI_certs =
    (sg_CI_certs_from_sg_CS_certs sgS.sg_CS_certs); sg_CI_ast =
    (Ast_sg_CI_from_sg_CS sgS.sg_CS_ast) }

(** val sg_C_certs_from_sg_CK_certs :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a1
    sg_CK_certificates -> 'a1 sg_C_certificates **)

let sg_C_certs_from_sg_CK_certs r b eqvS sgS =
  let ntS = eqvS.eqv_nontrivial in
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Negate f = ntS.certify_nontrivial_negate in
  let ni =
    match sgS.sg_CK_exists_id_d with
    | Certify_Exists_Id i ->
      cef_cancellative_and_exists_id_imply_not_idempotent r s i f
    | Certify_Not_Exists_Id -> s
  in
  { sg_C_selective_d = (Certify_Not_Selective
  (cef_not_idempotent_implies_not_selective ni)); sg_C_idempotent_d =
  (Certify_Not_Idempotent ni); sg_C_exists_id_d = sgS.sg_CK_exists_id_d;
  sg_C_exists_ann_d = Certify_Not_Exists_Ann; sg_C_left_cancel_d =
  Certify_Left_Cancellative; sg_C_right_cancel_d =
  Certify_Right_Cancellative; sg_C_left_constant_d =
  (Certify_Not_Left_Constant
  (cef_left_cancellative_implies_not_left_constant s f));
  sg_C_right_constant_d = (Certify_Not_Right_Constant
  (cef_right_cancellative_implies_not_right_constant s f));
  sg_C_anti_left_d = sgS.sg_CK_anti_left_d; sg_C_anti_right_d =
  sgS.sg_CK_anti_right_d }

(** val sg_C_from_sg_CK : 'a1 sg_CK -> 'a1 sg_C **)

let sg_C_from_sg_CK sg0 =
  { sg_C_eqv = sg0.sg_CK_eqv; sg_C_bop = sg0.sg_CK_bop; sg_C_certs =
    (sg_C_certs_from_sg_CK_certs sg0.sg_CK_eqv.eqv_eq sg0.sg_CK_bop
      sg0.sg_CK_eqv.eqv_certs sg0.sg_CK_certs); sg_C_ast =
    (Ast_sg_C_from_sg_CK sg0.sg_CK_ast) }

(** val sg_from_sg_CI : 'a1 sg_CI -> 'a1 sg **)

let sg_from_sg_CI sgS =
  sg_from_sg_C (sg_C_from_sg_CI sgS)

(** val sg_from_sg_CK : 'a1 sg_CK -> 'a1 sg **)

let sg_from_sg_CK sgS =
  sg_from_sg_C (sg_C_from_sg_CK sgS)

(** val sg_C_from_sg_CS : 'a1 sg_CS -> 'a1 sg_C **)

let sg_C_from_sg_CS sgS =
  sg_C_from_sg_CI (sg_CI_from_sg_CS sgS)

(** val sg_from_sg_CS : 'a1 sg_CS -> 'a1 sg **)

let sg_from_sg_CS sgS =
  sg_from_sg_C (sg_C_from_sg_CS sgS)

(** val sg_C_certs_option_from_sg_certs :
    'a1 sg_certificates -> 'a1 sg_C_certificates option **)

let sg_C_certs_option_from_sg_certs sgS =
  match sgS.sg_commutative_d with
  | Certify_Commutative ->
    Some { sg_C_selective_d = sgS.sg_selective_d; sg_C_idempotent_d =
      sgS.sg_idempotent_d; sg_C_exists_id_d = sgS.sg_exists_id_d;
      sg_C_exists_ann_d = sgS.sg_exists_ann_d; sg_C_left_cancel_d =
      sgS.sg_left_cancel_d; sg_C_right_cancel_d = sgS.sg_right_cancel_d;
      sg_C_left_constant_d = sgS.sg_left_constant_d; sg_C_right_constant_d =
      sgS.sg_right_constant_d; sg_C_anti_left_d = sgS.sg_anti_left_d;
      sg_C_anti_right_d = sgS.sg_anti_right_d }
  | Certify_Not_Commutative p -> None

(** val sg_C_option_from_sg : 'a1 sg -> 'a1 sg_C option **)

let sg_C_option_from_sg sgS =
  match sg_C_certs_option_from_sg_certs sgS.sg_certs with
  | Some c ->
    Some { sg_C_eqv = sgS.sg_eq; sg_C_bop = sgS.sg_bop; sg_C_certs = c;
      sg_C_ast = (Ast_sg_C_from_sg sgS.sg_ast) }
  | None -> None

(** val sg_CI_certs_option_from_sg_C_certs :
    'a1 sg_C_certificates -> 'a1 sg_CI_certificates option **)

let sg_CI_certs_option_from_sg_C_certs sg_CS0 =
  match sg_CS0.sg_C_idempotent_d with
  | Certify_Idempotent ->
    Some { sg_CI_selective_d = sg_CS0.sg_C_selective_d; sg_CI_exists_id_d =
      sg_CS0.sg_C_exists_id_d; sg_CI_exists_ann_d =
      sg_CS0.sg_C_exists_ann_d }
  | Certify_Not_Idempotent s -> None

(** val sg_CI_option_from_sg_C : 'a1 sg_C -> 'a1 sg_CI option **)

let sg_CI_option_from_sg_C sg_CS0 =
  match sg_CI_certs_option_from_sg_C_certs sg_CS0.sg_C_certs with
  | Some certs ->
    Some { sg_CI_eqv = sg_CS0.sg_C_eqv; sg_CI_bop = sg_CS0.sg_C_bop;
      sg_CI_certs = certs; sg_CI_ast = (Ast_sg_CI_from_sg_C
      sg_CS0.sg_C_ast) }
  | None -> None

(** val sg_CS_certs_option_from_sg_CI_certs :
    'a1 sg_CI_certificates -> 'a1 sg_CS_certificates option **)

let sg_CS_certs_option_from_sg_CI_certs sg_CIS =
  match sg_CIS.sg_CI_selective_d with
  | Certify_Selective ->
    Some { sg_CS_exists_id_d = sg_CIS.sg_CI_exists_id_d; sg_CS_exists_ann_d =
      sg_CIS.sg_CI_exists_ann_d }
  | Certify_Not_Selective p -> None

(** val sg_CS_option_from_sg_CI : 'a1 sg_CI -> 'a1 sg_CS option **)

let sg_CS_option_from_sg_CI sg_CIS =
  match sg_CS_certs_option_from_sg_CI_certs sg_CIS.sg_CI_certs with
  | Some certs ->
    Some { sg_CS_eqv = sg_CIS.sg_CI_eqv; sg_CS_bop = sg_CIS.sg_CI_bop;
      sg_CS_certs = certs; sg_CS_ast = (Ast_sg_CS_from_sg_CI
      sg_CIS.sg_CI_ast) }
  | None -> None

(** val sg_CK_certs_option_from_sg_C_certs :
    'a1 sg_C_certificates -> 'a1 sg_CK_certificates option **)

let sg_CK_certs_option_from_sg_C_certs sgS =
  match sgS.sg_C_left_cancel_d with
  | Certify_Left_Cancellative ->
    Some { sg_CK_exists_id_d = sgS.sg_C_exists_id_d; sg_CK_anti_left_d =
      sgS.sg_C_anti_left_d; sg_CK_anti_right_d = sgS.sg_C_anti_right_d }
  | Certify_Not_Left_Cancellative p -> None

(** val sg_CK_option_from_sg_C : 'a1 sg_C -> 'a1 sg_CK option **)

let sg_CK_option_from_sg_C sgS =
  match sg_CK_certs_option_from_sg_C_certs sgS.sg_C_certs with
  | Some c ->
    Some { sg_CK_eqv = sgS.sg_C_eqv; sg_CK_bop = sgS.sg_C_bop; sg_CK_certs =
      c; sg_CK_ast = (Ast_sg_CK_from_sg_C sgS.sg_C_ast) }
  | None -> None

(** val sg_CI_option_from_sg : 'a1 sg -> 'a1 sg_CI option **)

let sg_CI_option_from_sg sgS =
  match sg_C_option_from_sg sgS with
  | Some sgS0 -> sg_CI_option_from_sg_C sgS0
  | None -> None

(** val sg_CK_option_from_sg : 'a1 sg -> 'a1 sg_CK option **)

let sg_CK_option_from_sg sgS =
  match sg_C_option_from_sg sgS with
  | Some sgS0 -> sg_CK_option_from_sg_C sgS0
  | None -> None

(** val sg_CS_option_from_sg_C : 'a1 sg_C -> 'a1 sg_CS option **)

let sg_CS_option_from_sg_C sgS =
  match sg_CI_option_from_sg_C sgS with
  | Some sgS0 -> sg_CS_option_from_sg_CI sgS0
  | None -> None

(** val sg_CS_option_from_sg : 'a1 sg -> 'a1 sg_CS option **)

let sg_CS_option_from_sg sgS =
  match sg_CI_option_from_sg sgS with
  | Some sgS0 -> sg_CS_option_from_sg_CI sgS0
  | None -> None

