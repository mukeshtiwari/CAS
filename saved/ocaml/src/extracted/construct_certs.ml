open Datatypes
open Basic_types
open Brel
open Cef
open Cert_records
open Certificates
open Check

(** val eqv_certs_eq_bool : bool eqv_certificates **)

let eqv_certs_eq_bool =
  { eqv_nontrivial = { certify_nontrivial_witness = (Certify_Witness true);
    certify_nontrivial_negate = (Certify_Negate negb) } }

(** val eqv_certs_eq_nat : int eqv_certificates **)

let eqv_certs_eq_nat =
  { eqv_nontrivial = { certify_nontrivial_witness = (Certify_Witness 0);
    certify_nontrivial_negate = (Certify_Negate (fun i -> succ i)) } }

(** val eqv_certs_add_constant :
    cas_constant -> 'a1 eqv_certificates -> 'a1 with_constant
    eqv_certificates **)

let eqv_certs_add_constant c eqvS =
  let w = nontrivial_witness eqvS.eqv_nontrivial in
  { eqv_nontrivial = { certify_nontrivial_witness = (Certify_Witness (Coq_inr
  w)); certify_nontrivial_negate = (Certify_Negate (fun d ->
  match d with
  | Coq_inl c0 -> Coq_inr w
  | Coq_inr s -> Coq_inl c)) } }

(** val eqv_certs_brel_list :
    'a1 eqv_certificates -> 'a1 list eqv_certificates **)

let eqv_certs_brel_list eqvS =
  let w = nontrivial_witness eqvS.eqv_nontrivial in
  { eqv_nontrivial = { certify_nontrivial_witness = (Certify_Witness []);
  certify_nontrivial_negate = (Certify_Negate (fun l -> w::l)) } }

(** val eqv_certs_brel_set :
    'a1 brel -> 'a1 eqv_certificates -> 'a1 finite_set eqv_certificates **)

let eqv_certs_brel_set r eqvS =
  let s = nontrivial_witness eqvS.eqv_nontrivial in
  { eqv_nontrivial = { certify_nontrivial_witness = (Certify_Witness []);
  certify_nontrivial_negate = (Certify_Negate (fun l ->
  if brel_set r [] l then s::[] else [])) } }

(** val assert_product_nontrivial :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> ('a1*'a2)
    assert_nontrivial **)

let assert_product_nontrivial ntS ntT =
  let Certify_Negate f = ntS.certify_nontrivial_negate in
  let Certify_Negate g = ntT.certify_nontrivial_negate in
  { certify_nontrivial_witness = (Certify_Witness
  ((nontrivial_witness ntS),(nontrivial_witness ntT)));
  certify_nontrivial_negate = (Certify_Negate (fun p ->
  let x,y = p in (f x),(g y))) }

(** val eqv_certs_product :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> ('a1*'a2)
    eqv_certificates **)

let eqv_certs_product eqvS eqvT =
  { eqv_nontrivial =
    (assert_product_nontrivial eqvS.eqv_nontrivial eqvT.eqv_nontrivial) }

(** val eqv_certs_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> ('a1, 'a2) sum
    eqv_certificates **)

let eqv_certs_sum eqvS eqvT =
  let wS = nontrivial_witness eqvS.eqv_nontrivial in
  let wT = nontrivial_witness eqvT.eqv_nontrivial in
  { eqv_nontrivial = { certify_nontrivial_witness = (Certify_Witness (Coq_inl
  wS)); certify_nontrivial_negate = (Certify_Negate (fun d ->
  match d with
  | Coq_inl s -> Coq_inr wT
  | Coq_inr t -> Coq_inl wS)) } }

(** val sg_CS_certs_and : bool sg_CS_certificates **)

let sg_CS_certs_and =
  { sg_CS_exists_id_d = (Certify_Exists_Id true); sg_CS_exists_ann_d =
    (Certify_Exists_Ann false) }

(** val sg_CS_certs_or : bool sg_CS_certificates **)

let sg_CS_certs_or =
  { sg_CS_exists_id_d = (Certify_Exists_Id false); sg_CS_exists_ann_d =
    (Certify_Exists_Ann true) }

(** val sg_CS_certs_min : int sg_CS_certificates **)

let sg_CS_certs_min =
  { sg_CS_exists_id_d = Certify_Not_Exists_Id; sg_CS_exists_ann_d =
    (Certify_Exists_Ann 0) }

(** val sg_CS_certs_max : int sg_CS_certificates **)

let sg_CS_certs_max =
  { sg_CS_exists_id_d = (Certify_Exists_Id 0); sg_CS_exists_ann_d =
    Certify_Not_Exists_Ann }

(** val sg_CK_certs_plus : int sg_CK_certificates **)

let sg_CK_certs_plus =
  { sg_CK_exists_id_d = (Certify_Exists_Id 0); sg_CK_anti_left_d =
    (Certify_Not_Anti_Left (0,0)); sg_CK_anti_right_d =
    (Certify_Not_Anti_Right (0,0)) }

(** val sg_C_certs_times : int sg_C_certificates **)

let sg_C_certs_times =
  { sg_C_selective_d = (Certify_Not_Selective ((succ (succ 0)),(succ (succ
    0)))); sg_C_idempotent_d = (Certify_Not_Idempotent (succ (succ 0)));
    sg_C_exists_id_d = (Certify_Exists_Id (succ 0)); sg_C_exists_ann_d =
    (Certify_Exists_Ann 0); sg_C_left_cancel_d =
    (Certify_Not_Left_Cancellative (0,(0,(succ 0)))); sg_C_right_cancel_d =
    (Certify_Not_Right_Cancellative (0,(0,(succ 0)))); sg_C_left_constant_d =
    (Certify_Not_Left_Constant ((succ 0),(0,(succ 0))));
    sg_C_right_constant_d = (Certify_Not_Right_Constant ((succ 0),(0,(succ
    0)))); sg_C_anti_left_d = (Certify_Not_Anti_Left (0,0));
    sg_C_anti_right_d = (Certify_Not_Anti_Right (0,0)) }

(** val sg_certs_concat :
    'a1 eqv_certificates -> 'a1 list sg_certificates **)

let sg_certs_concat eqvS =
  let s,t = nontrivial_pair eqvS.eqv_nontrivial in
  { sg_commutative_d = (Certify_Not_Commutative ((s::[]),(t::[])));
  sg_selective_d = (Certify_Not_Selective ((s::[]),(t::[])));
  sg_idempotent_d = (Certify_Not_Idempotent (s::[])); sg_exists_id_d =
  (Certify_Exists_Id []); sg_exists_ann_d = Certify_Not_Exists_Ann;
  sg_is_left_d = (Certify_Not_Is_Left ([],(s::[]))); sg_is_right_d =
  (Certify_Not_Is_Right ((s::[]),[])); sg_left_cancel_d =
  Certify_Left_Cancellative; sg_right_cancel_d = Certify_Right_Cancellative;
  sg_left_constant_d = (Certify_Not_Left_Constant ([],([],(s::[]))));
  sg_right_constant_d = (Certify_Not_Right_Constant ([],([],(s::[]))));
  sg_anti_left_d = (Certify_Not_Anti_Left ((s::[]),[])); sg_anti_right_d =
  (Certify_Not_Anti_Right ((s::[]),[])) }

(** val sg_certs_left : 'a1 eqv_certificates -> 'a1 sg_certificates **)

let sg_certs_left eqvS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  let t = f s in
  { sg_commutative_d = (Certify_Not_Commutative (s,t)); sg_selective_d =
  Certify_Selective; sg_idempotent_d = Certify_Idempotent; sg_exists_id_d =
  Certify_Not_Exists_Id; sg_exists_ann_d = Certify_Not_Exists_Ann;
  sg_is_left_d = Certify_Is_Left; sg_is_right_d = (Certify_Not_Is_Right
  (s,t)); sg_left_cancel_d = (Certify_Not_Left_Cancellative (s,(s,t)));
  sg_right_cancel_d = Certify_Right_Cancellative; sg_left_constant_d =
  Certify_Left_Constant; sg_right_constant_d = (Certify_Not_Right_Constant
  (s,(s,t))); sg_anti_left_d = (Certify_Not_Anti_Left (s,s));
  sg_anti_right_d = (Certify_Not_Anti_Right (s,s)) }

(** val sg_certs_right : 'a1 eqv_certificates -> 'a1 sg_certificates **)

let sg_certs_right eqvS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  let t = f s in
  { sg_commutative_d = (Certify_Not_Commutative (t,s)); sg_selective_d =
  Certify_Selective; sg_idempotent_d = Certify_Idempotent; sg_exists_id_d =
  Certify_Not_Exists_Id; sg_exists_ann_d = Certify_Not_Exists_Ann;
  sg_is_left_d = (Certify_Not_Is_Left (t,s)); sg_is_right_d =
  Certify_Is_Right; sg_left_cancel_d = Certify_Left_Cancellative;
  sg_right_cancel_d = (Certify_Not_Right_Cancellative (s,(s,t)));
  sg_left_constant_d = (Certify_Not_Left_Constant (s,(s,t)));
  sg_right_constant_d = Certify_Right_Constant; sg_anti_left_d =
  (Certify_Not_Anti_Left (s,s)); sg_anti_right_d = (Certify_Not_Anti_Right
  (s,s)) }

(** val sg_certs_add_id :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_certificates -> 'a1
    with_constant sg_certificates **)

let sg_certs_add_id c eqvS sgS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_commutative_d = (bop_add_id_commutative_check sgS.sg_commutative_d);
  sg_selective_d = (bop_add_id_selective_check sgS.sg_selective_d);
  sg_idempotent_d = (bop_add_id_idempotent_check sgS.sg_idempotent_d);
  sg_exists_id_d = (Certify_Exists_Id (Coq_inl c)); sg_exists_ann_d =
  (bop_add_id_exists_ann_check sgS.sg_exists_ann_d); sg_is_left_d =
  (bop_add_id_not_is_left_check c
    eqvS.eqv_nontrivial.certify_nontrivial_witness); sg_is_right_d =
  (bop_add_id_not_is_right_check c
    eqvS.eqv_nontrivial.certify_nontrivial_witness); sg_left_cancel_d =
  (bop_add_id_left_cancellative_check c sgS.sg_anti_left_d
    sgS.sg_left_cancel_d); sg_right_cancel_d =
  (bop_add_id_right_cancellative_check c sgS.sg_anti_right_d
    sgS.sg_right_cancel_d); sg_left_constant_d = (Certify_Not_Left_Constant
  ((Coq_inl c),((Coq_inr s),(Coq_inr (f s))))); sg_right_constant_d =
  (Certify_Not_Right_Constant ((Coq_inl c),((Coq_inr s),(Coq_inr (f s)))));
  sg_anti_left_d = (Certify_Not_Anti_Left ((Coq_inr s),(Coq_inl c)));
  sg_anti_right_d = (Certify_Not_Anti_Right ((Coq_inr s),(Coq_inl c))) }

(** val sg_C_certs_add_id :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_C_certificates -> 'a1
    with_constant sg_C_certificates **)

let sg_C_certs_add_id c eqvS sgS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_C_selective_d = (bop_add_id_selective_check sgS.sg_C_selective_d);
  sg_C_idempotent_d = (bop_add_id_idempotent_check sgS.sg_C_idempotent_d);
  sg_C_exists_id_d = (Certify_Exists_Id (Coq_inl c)); sg_C_exists_ann_d =
  (bop_add_id_exists_ann_check sgS.sg_C_exists_ann_d); sg_C_left_cancel_d =
  (bop_add_id_left_cancellative_check c sgS.sg_C_anti_left_d
    sgS.sg_C_left_cancel_d); sg_C_right_cancel_d =
  (bop_add_id_right_cancellative_check c sgS.sg_C_anti_right_d
    sgS.sg_C_right_cancel_d); sg_C_left_constant_d =
  (Certify_Not_Left_Constant ((Coq_inl c),((Coq_inr s),(Coq_inr (f s)))));
  sg_C_right_constant_d = (Certify_Not_Right_Constant ((Coq_inl c),((Coq_inr
  s),(Coq_inr (f s))))); sg_C_anti_left_d = (Certify_Not_Anti_Left ((Coq_inr
  s),(Coq_inl c))); sg_C_anti_right_d = (Certify_Not_Anti_Right ((Coq_inr
  s),(Coq_inl c))) }

(** val sg_CI_certs_add_id :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CI_certificates -> 'a1
    with_constant sg_CI_certificates **)

let sg_CI_certs_add_id c eqvS sgS =
  let wS = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Witness s = wS in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_CI_selective_d = (bop_add_id_selective_check sgS.sg_CI_selective_d);
  sg_CI_exists_id_d = (Certify_Exists_Id (Coq_inl c)); sg_CI_exists_ann_d =
  (bop_add_id_exists_ann_check sgS.sg_CI_exists_ann_d) }

(** val sg_CS_certs_add_id :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CS_certificates -> 'a1
    with_constant sg_CS_certificates **)

let sg_CS_certs_add_id c eqvS sg =
  let wS = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Witness s = wS in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_CS_exists_id_d = (Certify_Exists_Id (Coq_inl c)); sg_CS_exists_ann_d =
  (bop_add_id_exists_ann_check sg.sg_CS_exists_ann_d) }

(** val sg_certs_add_ann :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_certificates -> 'a1
    with_constant sg_certificates **)

let sg_certs_add_ann c eqvS sgS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_commutative_d = (bop_add_ann_commutative_check sgS.sg_commutative_d);
  sg_selective_d = (bop_add_ann_selective_check sgS.sg_selective_d);
  sg_idempotent_d = (bop_add_ann_idempotent_check sgS.sg_idempotent_d);
  sg_exists_id_d = (bop_add_ann_exists_id_check sgS.sg_exists_id_d);
  sg_exists_ann_d = (Certify_Exists_Ann (Coq_inl c)); sg_is_left_d =
  (bop_add_ann_not_is_left_check c
    eqvS.eqv_nontrivial.certify_nontrivial_witness); sg_is_right_d =
  (bop_add_ann_not_is_right_check c
    eqvS.eqv_nontrivial.certify_nontrivial_witness); sg_left_cancel_d =
  (Certify_Not_Left_Cancellative ((Coq_inl c),((Coq_inr s),(Coq_inr
  (f s))))); sg_right_cancel_d = (Certify_Not_Right_Cancellative ((Coq_inl
  c),((Coq_inr s),(Coq_inr (f s))))); sg_left_constant_d =
  (Certify_Not_Left_Constant ((Coq_inr s),((Coq_inr s),(Coq_inl c))));
  sg_right_constant_d = (Certify_Not_Right_Constant ((Coq_inr s),((Coq_inr
  s),(Coq_inl c)))); sg_anti_left_d = (Certify_Not_Anti_Left ((Coq_inl
  c),(Coq_inr s))); sg_anti_right_d = (Certify_Not_Anti_Right ((Coq_inl
  c),(Coq_inr s))) }

(** val sg_C_certs_add_ann :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_C_certificates -> 'a1
    with_constant sg_C_certificates **)

let sg_C_certs_add_ann c eqvS sgS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_C_selective_d = (bop_add_ann_selective_check sgS.sg_C_selective_d);
  sg_C_idempotent_d = (bop_add_ann_idempotent_check sgS.sg_C_idempotent_d);
  sg_C_exists_id_d = (bop_add_ann_exists_id_check sgS.sg_C_exists_id_d);
  sg_C_exists_ann_d = (Certify_Exists_Ann (Coq_inl c)); sg_C_left_cancel_d =
  (Certify_Not_Left_Cancellative ((Coq_inl c),((Coq_inr s),(Coq_inr
  (f s))))); sg_C_right_cancel_d = (Certify_Not_Right_Cancellative ((Coq_inl
  c),((Coq_inr s),(Coq_inr (f s))))); sg_C_left_constant_d =
  (Certify_Not_Left_Constant ((Coq_inr s),((Coq_inr s),(Coq_inl c))));
  sg_C_right_constant_d = (Certify_Not_Right_Constant ((Coq_inr s),((Coq_inr
  s),(Coq_inl c)))); sg_C_anti_left_d = (Certify_Not_Anti_Left ((Coq_inl
  c),(Coq_inr s))); sg_C_anti_right_d = (Certify_Not_Anti_Right ((Coq_inl
  c),(Coq_inr s))) }

(** val sg_CI_certs_add_ann :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CI_certificates -> 'a1
    with_constant sg_CI_certificates **)

let sg_CI_certs_add_ann c eqvS sgS =
  let wS = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Witness s = wS in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_CI_selective_d = (bop_add_ann_selective_check sgS.sg_CI_selective_d);
  sg_CI_exists_id_d = (bop_add_ann_exists_id_check sgS.sg_CI_exists_id_d);
  sg_CI_exists_ann_d = (Certify_Exists_Ann (Coq_inl c)) }

(** val sg_CS_certs_add_ann :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_CS_certificates -> 'a1
    with_constant sg_CS_certificates **)

let sg_CS_certs_add_ann c eqvS sg =
  let wS = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Witness s = wS in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_CS_exists_id_d = (bop_add_ann_exists_id_check sg.sg_CS_exists_id_d);
  sg_CS_exists_ann_d = (Certify_Exists_Ann (Coq_inl c)) }

(** val sg_certs_left_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates ->
    'a2 sg_certificates -> ('a1, 'a2) sum sg_certificates **)

let sg_certs_left_sum eS eT cS cT =
  let s = nontrivial_witness eS.eqv_nontrivial in
  let f = nontrivial_negate eS.eqv_nontrivial in
  let t = nontrivial_witness eT.eqv_nontrivial in
  let g = nontrivial_negate eT.eqv_nontrivial in
  { sg_commutative_d =
  (check_commutative_sum cS.sg_commutative_d cT.sg_commutative_d);
  sg_selective_d = (check_selective_sum cS.sg_selective_d cT.sg_selective_d);
  sg_idempotent_d =
  (check_idempotent_sum cS.sg_idempotent_d cT.sg_idempotent_d);
  sg_exists_id_d = (check_exists_id_left_sum cT.sg_exists_id_d);
  sg_exists_ann_d = (check_exists_ann_left_sum cS.sg_exists_ann_d);
  sg_is_left_d = (Certify_Not_Is_Left ((Coq_inr t),(Coq_inl s)));
  sg_is_right_d = (Certify_Not_Is_Right ((Coq_inl s),(Coq_inr t)));
  sg_left_cancel_d = (Certify_Not_Left_Cancellative ((Coq_inl s),((Coq_inr
  t),(Coq_inr (g t))))); sg_right_cancel_d = (Certify_Not_Right_Cancellative
  ((Coq_inl s),((Coq_inr t),(Coq_inr (g t))))); sg_left_constant_d =
  (Certify_Not_Left_Constant ((Coq_inr t),((Coq_inl s),(Coq_inl (f s)))));
  sg_right_constant_d = (Certify_Not_Right_Constant ((Coq_inr t),((Coq_inl
  s),(Coq_inl (f s))))); sg_anti_left_d = (Certify_Not_Anti_Left ((Coq_inl
  s),(Coq_inr t))); sg_anti_right_d = (Certify_Not_Anti_Right ((Coq_inl
  s),(Coq_inr t))) }

(** val sg_certs_right_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates ->
    'a2 sg_certificates -> ('a1, 'a2) sum sg_certificates **)

let sg_certs_right_sum eS eT cS cT =
  let s = nontrivial_witness eS.eqv_nontrivial in
  let f = nontrivial_negate eS.eqv_nontrivial in
  let t = nontrivial_witness eT.eqv_nontrivial in
  let g = nontrivial_negate eT.eqv_nontrivial in
  { sg_commutative_d =
  (check_commutative_sum cS.sg_commutative_d cT.sg_commutative_d);
  sg_selective_d = (check_selective_sum cS.sg_selective_d cT.sg_selective_d);
  sg_idempotent_d =
  (check_idempotent_sum cS.sg_idempotent_d cT.sg_idempotent_d);
  sg_exists_id_d = (check_exists_id_right_sum cS.sg_exists_id_d);
  sg_exists_ann_d = (check_exists_ann_right_sum cT.sg_exists_ann_d);
  sg_is_left_d = (Certify_Not_Is_Left ((Coq_inl s),(Coq_inr t)));
  sg_is_right_d = (Certify_Not_Is_Right ((Coq_inr t),(Coq_inl s)));
  sg_left_cancel_d = (Certify_Not_Left_Cancellative ((Coq_inr t),((Coq_inl
  s),(Coq_inl (f s))))); sg_right_cancel_d = (Certify_Not_Right_Cancellative
  ((Coq_inr t),((Coq_inl s),(Coq_inl (f s))))); sg_left_constant_d =
  (Certify_Not_Left_Constant ((Coq_inl s),((Coq_inr t),(Coq_inr (g t)))));
  sg_right_constant_d = (Certify_Not_Right_Constant ((Coq_inl s),((Coq_inr
  t),(Coq_inr (g t))))); sg_anti_left_d = (Certify_Not_Anti_Left ((Coq_inr
  t),(Coq_inl s))); sg_anti_right_d = (Certify_Not_Anti_Right ((Coq_inr
  t),(Coq_inl s))) }

(** val sg_C_certs_left_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_C_certificates ->
    'a2 sg_C_certificates -> ('a1, 'a2) sum sg_C_certificates **)

let sg_C_certs_left_sum eS eT cS cT =
  let s = nontrivial_witness eS.eqv_nontrivial in
  let f = nontrivial_negate eS.eqv_nontrivial in
  let t = nontrivial_witness eT.eqv_nontrivial in
  let g = nontrivial_negate eT.eqv_nontrivial in
  { sg_C_selective_d =
  (check_selective_sum cS.sg_C_selective_d cT.sg_C_selective_d);
  sg_C_idempotent_d =
  (check_idempotent_sum cS.sg_C_idempotent_d cT.sg_C_idempotent_d);
  sg_C_exists_id_d = (check_exists_id_left_sum cT.sg_C_exists_id_d);
  sg_C_exists_ann_d = (check_exists_ann_left_sum cS.sg_C_exists_ann_d);
  sg_C_left_cancel_d = (Certify_Not_Left_Cancellative ((Coq_inl s),((Coq_inr
  t),(Coq_inr (g t))))); sg_C_right_cancel_d =
  (Certify_Not_Right_Cancellative ((Coq_inl s),((Coq_inr t),(Coq_inr
  (g t))))); sg_C_left_constant_d = (Certify_Not_Left_Constant ((Coq_inr
  t),((Coq_inl s),(Coq_inl (f s))))); sg_C_right_constant_d =
  (Certify_Not_Right_Constant ((Coq_inr t),((Coq_inl s),(Coq_inl (f s)))));
  sg_C_anti_left_d = (Certify_Not_Anti_Left ((Coq_inl s),(Coq_inr t)));
  sg_C_anti_right_d = (Certify_Not_Anti_Right ((Coq_inl s),(Coq_inr t))) }

(** val sg_C_certs_right_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_C_certificates ->
    'a2 sg_C_certificates -> ('a1, 'a2) sum sg_C_certificates **)

let sg_C_certs_right_sum eS eT cS cT =
  let s = nontrivial_witness eS.eqv_nontrivial in
  let f = nontrivial_negate eS.eqv_nontrivial in
  let t = nontrivial_witness eT.eqv_nontrivial in
  let g = nontrivial_negate eT.eqv_nontrivial in
  { sg_C_selective_d =
  (check_selective_sum cS.sg_C_selective_d cT.sg_C_selective_d);
  sg_C_idempotent_d =
  (check_idempotent_sum cS.sg_C_idempotent_d cT.sg_C_idempotent_d);
  sg_C_exists_id_d = (check_exists_id_right_sum cS.sg_C_exists_id_d);
  sg_C_exists_ann_d = (check_exists_ann_right_sum cT.sg_C_exists_ann_d);
  sg_C_left_cancel_d = (Certify_Not_Left_Cancellative ((Coq_inr t),((Coq_inl
  s),(Coq_inl (f s))))); sg_C_right_cancel_d =
  (Certify_Not_Right_Cancellative ((Coq_inr t),((Coq_inl s),(Coq_inl
  (f s))))); sg_C_left_constant_d = (Certify_Not_Left_Constant ((Coq_inl
  s),((Coq_inr t),(Coq_inr (g t))))); sg_C_right_constant_d =
  (Certify_Not_Right_Constant ((Coq_inl s),((Coq_inr t),(Coq_inr (g t)))));
  sg_C_anti_left_d = (Certify_Not_Anti_Left ((Coq_inr t),(Coq_inl s)));
  sg_C_anti_right_d = (Certify_Not_Anti_Right ((Coq_inr t),(Coq_inl s))) }

(** val sg_CI_certs_left_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CI_certificates ->
    'a2 sg_CI_certificates -> ('a1, 'a2) sum sg_CI_certificates **)

let sg_CI_certs_left_sum eS eT cS cT =
  { sg_CI_selective_d =
    (check_selective_sum cS.sg_CI_selective_d cT.sg_CI_selective_d);
    sg_CI_exists_id_d = (check_exists_id_left_sum cT.sg_CI_exists_id_d);
    sg_CI_exists_ann_d = (check_exists_ann_left_sum cS.sg_CI_exists_ann_d) }

(** val sg_CI_certs_right_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CI_certificates ->
    'a2 sg_CI_certificates -> ('a1, 'a2) sum sg_CI_certificates **)

let sg_CI_certs_right_sum eS eT cS cT =
  { sg_CI_selective_d =
    (check_selective_sum cS.sg_CI_selective_d cT.sg_CI_selective_d);
    sg_CI_exists_id_d = (check_exists_id_right_sum cS.sg_CI_exists_id_d);
    sg_CI_exists_ann_d = (check_exists_ann_right_sum cT.sg_CI_exists_ann_d) }

(** val sg_CS_certs_left_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CS_certificates ->
    'a2 sg_CS_certificates -> ('a1, 'a2) sum sg_CS_certificates **)

let sg_CS_certs_left_sum eS eT cS cT =
  { sg_CS_exists_id_d = (check_exists_id_left_sum cT.sg_CS_exists_id_d);
    sg_CS_exists_ann_d = (check_exists_ann_left_sum cS.sg_CS_exists_ann_d) }

(** val sg_CS_certs_right_sum :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CS_certificates ->
    'a2 sg_CS_certificates -> ('a1, 'a2) sum sg_CS_certificates **)

let sg_CS_certs_right_sum eS eT cS cT =
  { sg_CS_exists_id_d = (check_exists_id_right_sum cS.sg_CS_exists_id_d);
    sg_CS_exists_ann_d = (check_exists_ann_right_sum cT.sg_CS_exists_ann_d) }

(** val sg_certs_product :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates ->
    'a2 sg_certificates -> ('a1*'a2) sg_certificates **)

let sg_certs_product eS eT cS cT =
  let wS = eS.eqv_nontrivial in
  let wT = eT.eqv_nontrivial in
  { sg_commutative_d =
  (check_commutative_product wS wT cS.sg_commutative_d cT.sg_commutative_d);
  sg_selective_d =
  (check_selective_product wS wT cS.sg_is_left_d cT.sg_is_left_d
    cS.sg_is_right_d cT.sg_is_right_d); sg_idempotent_d =
  (check_idempotent_product wS wT cS.sg_idempotent_d cT.sg_idempotent_d);
  sg_exists_id_d =
  (check_exists_id_product cS.sg_exists_id_d cT.sg_exists_id_d);
  sg_exists_ann_d =
  (check_exists_ann_product cS.sg_exists_ann_d cT.sg_exists_ann_d);
  sg_is_left_d =
  (check_is_left_product wS wT cS.sg_is_left_d cT.sg_is_left_d);
  sg_is_right_d =
  (check_is_right_product wS wT cS.sg_is_right_d cT.sg_is_right_d);
  sg_left_cancel_d =
  (check_left_cancellative_product wS wT cS.sg_left_cancel_d
    cT.sg_left_cancel_d); sg_right_cancel_d =
  (check_right_cancellative_product wS wT cS.sg_right_cancel_d
    cT.sg_right_cancel_d); sg_left_constant_d =
  (check_left_constant_product wS wT cS.sg_left_constant_d
    cT.sg_left_constant_d); sg_right_constant_d =
  (check_right_constant_product wS wT cS.sg_right_constant_d
    cT.sg_right_constant_d); sg_anti_left_d =
  (check_anti_left_product cS.sg_anti_left_d cT.sg_anti_left_d);
  sg_anti_right_d =
  (check_anti_right_product cS.sg_anti_right_d cT.sg_anti_right_d) }

(** val sg_certs_product_new :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates_new
    -> 'a2 sg_certificates_new -> ('a1*'a2) sg_certificates_new **)

let sg_certs_product_new eS eT cS cT =
  let wS = nontrivial_witness eS.eqv_nontrivial in
  let wT = nontrivial_witness eT.eqv_nontrivial in
  { sgn_commutative_d =
  (check_commutative_product_new wS wT cS.sgn_commutative_d
    cT.sgn_commutative_d); sgn_selective_d =
  (check_selective_product_new wS wT cS.sgn_is_left_d cT.sgn_is_left_d
    cS.sgn_is_right_d cT.sgn_is_right_d); sgn_idempotent_d =
  (check_idempotent_product_new wS wT cS.sgn_idempotent_d
    cT.sgn_idempotent_d); sgn_exists_id_d =
  (check_exists_id_product_new cS.sgn_exists_id_d cT.sgn_exists_id_d);
  sgn_exists_ann_d =
  (check_exists_ann_product_new cS.sgn_exists_ann_d cT.sgn_exists_ann_d);
  sgn_is_left_d =
  (check_is_left_product_new wS wT cS.sgn_is_left_d cT.sgn_is_left_d);
  sgn_is_right_d =
  (check_is_right_product_new wS wT cS.sgn_is_right_d cT.sgn_is_right_d);
  sgn_left_cancel_d =
  (check_left_cancellative_product_new wS wT cS.sgn_left_cancel_d
    cT.sgn_left_cancel_d); sgn_right_cancel_d =
  (check_right_cancellative_product_new wS wT cS.sgn_right_cancel_d
    cT.sgn_right_cancel_d); sgn_left_constant_d =
  (check_left_constant_product_new wS wT cS.sgn_left_constant_d
    cT.sgn_left_constant_d); sgn_right_constant_d =
  (check_right_constant_product_new wS wT cS.sgn_right_constant_d
    cT.sgn_right_constant_d); sgn_anti_left_d =
  (check_anti_left_product_new cS.sgn_anti_left_d cT.sgn_anti_left_d);
  sgn_anti_right_d =
  (check_anti_right_product_new cS.sgn_anti_right_d cT.sgn_anti_right_d) }

(** val sg_C_certs_product :
    'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a1
    eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_C_certificates -> 'a2
    sg_C_certificates -> ('a1*'a2) sg_C_certificates **)

let sg_C_certs_product rS rT bS bT eS eT cS cT =
  let wS = eS.eqv_nontrivial in
  let wT = eT.eqv_nontrivial in
  let s = nontrivial_witness wS in
  let f = nontrivial_negate wS in
  let t = nontrivial_witness wT in
  let g = nontrivial_negate wT in
  { sg_C_selective_d =
  (check_selective_product wS wT (Certify_Not_Is_Left
    (cef_commutative_implies_not_is_left rS bS s f)) (Certify_Not_Is_Left
    (cef_commutative_implies_not_is_left rT bT t g)) (Certify_Not_Is_Right
    (cef_commutative_implies_not_is_right rS bS s f)) (Certify_Not_Is_Right
    (cef_commutative_implies_not_is_right rT bT t g))); sg_C_idempotent_d =
  (check_idempotent_product wS wT cS.sg_C_idempotent_d cT.sg_C_idempotent_d);
  sg_C_exists_id_d =
  (check_exists_id_product cS.sg_C_exists_id_d cT.sg_C_exists_id_d);
  sg_C_exists_ann_d =
  (check_exists_ann_product cS.sg_C_exists_ann_d cT.sg_C_exists_ann_d);
  sg_C_left_cancel_d =
  (check_left_cancellative_product wS wT cS.sg_C_left_cancel_d
    cT.sg_C_left_cancel_d); sg_C_right_cancel_d =
  (check_right_cancellative_product wS wT cS.sg_C_right_cancel_d
    cT.sg_C_right_cancel_d); sg_C_left_constant_d =
  (check_left_constant_product wS wT cS.sg_C_left_constant_d
    cT.sg_C_left_constant_d); sg_C_right_constant_d =
  (check_right_constant_product wS wT cS.sg_C_right_constant_d
    cT.sg_C_right_constant_d); sg_C_anti_left_d =
  (check_anti_left_product cS.sg_C_anti_left_d cT.sg_C_anti_left_d);
  sg_C_anti_right_d =
  (check_anti_right_product cS.sg_C_anti_right_d cT.sg_C_anti_right_d) }

(** val sg_CI_certs_product :
    'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a1
    eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_CI_certificates -> 'a2
    sg_CI_certificates -> ('a1*'a2) sg_CI_certificates **)

let sg_CI_certs_product rS rT bS bT eS eT cS cT =
  let wS = eS.eqv_nontrivial in
  let wT = eT.eqv_nontrivial in
  let s = nontrivial_witness wS in
  let f = nontrivial_negate wS in
  let t = nontrivial_witness wT in
  let g = nontrivial_negate wT in
  { sg_CI_selective_d =
  (check_selective_product wS wT (Certify_Not_Is_Left
    (cef_commutative_implies_not_is_left rS bS s f)) (Certify_Not_Is_Left
    (cef_commutative_implies_not_is_left rT bT t g)) (Certify_Not_Is_Right
    (cef_commutative_implies_not_is_right rS bS s f)) (Certify_Not_Is_Right
    (cef_commutative_implies_not_is_right rT bT t g))); sg_CI_exists_id_d =
  (check_exists_id_product cS.sg_CI_exists_id_d cT.sg_CI_exists_id_d);
  sg_CI_exists_ann_d =
  (check_exists_ann_product cS.sg_CI_exists_ann_d cT.sg_CI_exists_ann_d) }

(** val sg_certs_llex :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
    -> 'a1 sg_CS_certificates -> 'a2 sg_certificates -> ('a1*'a2)
    sg_certificates **)

let sg_certs_llex rS bS eS eT cS cT =
  let wS = eS.eqv_nontrivial in
  let wT = eT.eqv_nontrivial in
  let s = nontrivial_witness wS in
  let t = nontrivial_witness wT in
  let f = nontrivial_negate wS in
  let g = nontrivial_negate wT in
  { sg_commutative_d = (check_commutative_llex wS cT.sg_commutative_d);
  sg_selective_d = (check_selective_llex wS cT.sg_selective_d);
  sg_idempotent_d = (check_idempotent_llex wS cT.sg_idempotent_d);
  sg_exists_id_d =
  (check_exists_id_llex cS.sg_CS_exists_id_d cT.sg_exists_id_d);
  sg_exists_ann_d =
  (check_exists_ann_llex cS.sg_CS_exists_ann_d cT.sg_exists_ann_d);
  sg_is_left_d = (Certify_Not_Is_Left
  (cef_bop_llex_not_is_left rS bS s f t)); sg_is_right_d =
  (Certify_Not_Is_Right (cef_bop_llex_not_is_right rS bS s f t));
  sg_left_cancel_d = (Certify_Not_Left_Cancellative
  (cef_bop_llex_not_cancellative rS bS s f t g)); sg_right_cancel_d =
  (Certify_Not_Right_Cancellative
  (cef_bop_llex_not_cancellative rS bS s f t g)); sg_left_constant_d =
  (Certify_Not_Left_Constant (cef_bop_llex_not_constant rS bS s f t g));
  sg_right_constant_d = (Certify_Not_Right_Constant
  (cef_bop_llex_not_constant rS bS s f t g)); sg_anti_left_d =
  (Certify_Not_Anti_Left (cef_bop_llex_not_anti_left rS bS s f t));
  sg_anti_right_d = (Certify_Not_Anti_Right
  (cef_bop_llex_not_anti_right rS bS s f t)) }

(** val sg_C_certs_llex :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
    -> 'a1 sg_CS_certificates -> 'a2 sg_C_certificates -> ('a1*'a2)
    sg_C_certificates **)

let sg_C_certs_llex rS bS eS eT cS cT =
  let wS = eS.eqv_nontrivial in
  let wT = eT.eqv_nontrivial in
  let s = nontrivial_witness wS in
  let t = nontrivial_witness wT in
  let f = nontrivial_negate wS in
  let g = nontrivial_negate wT in
  { sg_C_selective_d = (check_selective_llex wS cT.sg_C_selective_d);
  sg_C_idempotent_d = (check_idempotent_llex wS cT.sg_C_idempotent_d);
  sg_C_exists_id_d =
  (check_exists_id_llex cS.sg_CS_exists_id_d cT.sg_C_exists_id_d);
  sg_C_exists_ann_d =
  (check_exists_ann_llex cS.sg_CS_exists_ann_d cT.sg_C_exists_ann_d);
  sg_C_left_cancel_d = (Certify_Not_Left_Cancellative
  (cef_bop_llex_not_cancellative rS bS s f t g)); sg_C_right_cancel_d =
  (Certify_Not_Right_Cancellative
  (cef_bop_llex_not_cancellative rS bS s f t g)); sg_C_left_constant_d =
  (Certify_Not_Left_Constant (cef_bop_llex_not_constant rS bS s f t g));
  sg_C_right_constant_d = (Certify_Not_Right_Constant
  (cef_bop_llex_not_constant rS bS s f t g)); sg_C_anti_left_d =
  (Certify_Not_Anti_Left (cef_bop_llex_not_anti_left rS bS s f t));
  sg_C_anti_right_d = (Certify_Not_Anti_Right
  (cef_bop_llex_not_anti_right rS bS s f t)) }

(** val sg_CI_certs_llex :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
    -> 'a1 sg_CS_certificates -> 'a2 sg_CI_certificates -> ('a1*'a2)
    sg_CI_certificates **)

let sg_CI_certs_llex rS bS eS eT cS cT =
  { sg_CI_selective_d =
    (check_selective_llex eS.eqv_nontrivial cT.sg_CI_selective_d);
    sg_CI_exists_id_d =
    (check_exists_id_llex cS.sg_CS_exists_id_d cT.sg_CI_exists_id_d);
    sg_CI_exists_ann_d =
    (check_exists_ann_llex cS.sg_CS_exists_ann_d cT.sg_CI_exists_ann_d) }

(** val sg_CS_certs_llex :
    'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a2 eqv_certificates
    -> 'a1 sg_CS_certificates -> 'a2 sg_CS_certificates -> ('a1*'a2)
    sg_CS_certificates **)

let sg_CS_certs_llex rS bS eS eT cS cT =
  { sg_CS_exists_id_d =
    (check_exists_id_llex cS.sg_CS_exists_id_d cT.sg_CS_exists_id_d);
    sg_CS_exists_ann_d =
    (check_exists_ann_llex cS.sg_CS_exists_ann_d cT.sg_CS_exists_ann_d) }

(** val sg_CI_certs_union_with_ann :
    cas_constant -> 'a1 eqv_certificates -> 'a1 finite_set with_constant
    sg_CI_certificates **)

let sg_CI_certs_union_with_ann c eqvS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_CI_selective_d = (Certify_Not_Selective ((Coq_inr (s::[])),(Coq_inr
  ((f s)::[])))); sg_CI_exists_id_d = (Certify_Exists_Id (Coq_inr []));
  sg_CI_exists_ann_d = (Certify_Exists_Ann (Coq_inl c)) }

(** val sg_CI_certs_intersect_with_id :
    cas_constant -> 'a1 eqv_certificates -> 'a1 finite_set with_constant
    sg_CI_certificates **)

let sg_CI_certs_intersect_with_id c eqvS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Negate f = eqvS.eqv_nontrivial.certify_nontrivial_negate in
  { sg_CI_selective_d = (Certify_Not_Selective ((Coq_inr (s::[])),(Coq_inr
  ((f s)::[])))); sg_CI_exists_id_d = (Certify_Exists_Id (Coq_inl c));
  sg_CI_exists_ann_d = (Certify_Exists_Ann (Coq_inr [])) }

(** val sg_sg_certs_add_zero :
    'a1 eqv_certificates -> 'a1 sg_sg_certificates -> 'a1 with_constant
    sg_sg_certificates **)

let sg_sg_certs_add_zero eqvS pS =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  { sg_sg_left_distributive_d =
  (bops_add_zero_left_distributive_check pS.sg_sg_left_distributive_d);
  sg_sg_right_distributive_d =
  (bops_add_zero_right_distributive_check pS.sg_sg_right_distributive_d);
  sg_sg_plus_id_is_times_ann_d = Certify_Plus_Id_Equals_Times_Ann;
  sg_sg_times_id_is_plus_ann_d =
  (match pS.sg_sg_times_id_is_plus_ann_d with
   | Certify_Times_Id_Equals_Plus_Ann -> Certify_Times_Id_Equals_Plus_Ann
   | Certify_Not_Times_Id_Equals_Plus_Ann ->
     Certify_Not_Times_Id_Equals_Plus_Ann); sg_sg_left_absorptive_d =
  (bops_add_zero_left_absorptive_check s pS.sg_sg_left_absorptive_d);
  sg_sg_right_absorptive_d =
  (bops_add_zero_right_absorptive_check s pS.sg_sg_right_absorptive_d) }

(** val bops_add_one_left_distributive_check :
    cas_constant -> 'a1 check_idempotent -> 'a1 check_left_absorptive -> 'a1
    check_left_distributive -> 'a1 with_constant check_left_distributive **)

let bops_add_one_left_distributive_check c idemS_d laS_d = function
| Certify_Left_Distributive ->
  (match laS_d with
   | Certify_Left_Absorptive ->
     (match idemS_d with
      | Certify_Idempotent -> Certify_Left_Distributive
      | Certify_Not_Idempotent s ->
        Certify_Not_Left_Distributive ((Coq_inr s),((Coq_inl c),(Coq_inl c))))
   | Certify_Not_Left_Absorptive p ->
     let s1,s2 = p in
     Certify_Not_Left_Distributive ((Coq_inr s1),((Coq_inl c),(Coq_inr s2))))
| Certify_Not_Left_Distributive p ->
  let s1,p0 = p in
  let s2,s3 = p0 in
  Certify_Not_Left_Distributive ((Coq_inr s1),((Coq_inr s2),(Coq_inr s3)))

(** val bops_add_one_right_distributive_check :
    cas_constant -> 'a1 check_idempotent -> 'a1 check_right_absorptive -> 'a1
    check_right_distributive -> 'a1 with_constant check_right_distributive **)

let bops_add_one_right_distributive_check c idemS_d laS_d = function
| Certify_Right_Distributive ->
  (match laS_d with
   | Certify_Right_Absorptive ->
     (match idemS_d with
      | Certify_Idempotent -> Certify_Right_Distributive
      | Certify_Not_Idempotent s ->
        Certify_Not_Right_Distributive ((Coq_inr s),((Coq_inl c),(Coq_inl
          c))))
   | Certify_Not_Right_Absorptive p ->
     let s1,s2 = p in
     Certify_Not_Right_Distributive ((Coq_inr s1),((Coq_inl c),(Coq_inr s2))))
| Certify_Not_Right_Distributive p ->
  let s1,p0 = p in
  let s2,s3 = p0 in
  Certify_Not_Right_Distributive ((Coq_inr s1),((Coq_inr s2),(Coq_inr s3)))

(** val bops_add_one_left_absorptive_check :
    cas_constant -> 'a1 check_idempotent -> 'a1 check_left_absorptive -> 'a1
    with_constant check_left_absorptive **)

let bops_add_one_left_absorptive_check c idemS_d = function
| Certify_Left_Absorptive ->
  (match idemS_d with
   | Certify_Idempotent -> Certify_Left_Absorptive
   | Certify_Not_Idempotent s ->
     Certify_Not_Left_Absorptive ((Coq_inr s),(Coq_inl c)))
| Certify_Not_Left_Absorptive p ->
  let s1,s2 = p in Certify_Not_Left_Absorptive ((Coq_inr s1),(Coq_inr s2))

(** val bops_add_one_right_absorptive_check :
    cas_constant -> 'a1 check_idempotent -> 'a1 check_right_absorptive -> 'a1
    with_constant check_right_absorptive **)

let bops_add_one_right_absorptive_check c idemS_d = function
| Certify_Right_Absorptive ->
  (match idemS_d with
   | Certify_Idempotent -> Certify_Right_Absorptive
   | Certify_Not_Idempotent s ->
     Certify_Not_Right_Absorptive ((Coq_inr s),(Coq_inl c)))
| Certify_Not_Right_Absorptive p ->
  let s1,s2 = p in Certify_Not_Right_Absorptive ((Coq_inr s1),(Coq_inr s2))

(** val sg_sg_certs_add_one :
    cas_constant -> 'a1 eqv_certificates -> 'a1 sg_C_certificates -> 'a1
    sg_sg_certificates -> 'a1 with_constant sg_sg_certificates **)

let sg_sg_certs_add_one c eqvS ppS pS =
  { sg_sg_left_distributive_d =
    (bops_add_one_left_distributive_check c ppS.sg_C_idempotent_d
      pS.sg_sg_left_absorptive_d pS.sg_sg_left_distributive_d);
    sg_sg_right_distributive_d =
    (bops_add_one_right_distributive_check c ppS.sg_C_idempotent_d
      pS.sg_sg_right_absorptive_d pS.sg_sg_right_distributive_d);
    sg_sg_plus_id_is_times_ann_d =
    (match pS.sg_sg_plus_id_is_times_ann_d with
     | Certify_Plus_Id_Equals_Times_Ann -> Certify_Plus_Id_Equals_Times_Ann
     | Certify_Not_Plus_Id_Equals_Times_Ann ->
       Certify_Not_Plus_Id_Equals_Times_Ann); sg_sg_times_id_is_plus_ann_d =
    Certify_Times_Id_Equals_Plus_Ann; sg_sg_left_absorptive_d =
    (bops_add_one_left_absorptive_check c ppS.sg_C_idempotent_d
      pS.sg_sg_left_absorptive_d); sg_sg_right_absorptive_d =
    (bops_add_one_right_absorptive_check c ppS.sg_C_idempotent_d
      pS.sg_sg_right_absorptive_d) }

(** val sg_sg_certs_product :
    'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_sg_certificates ->
    'a2 sg_sg_certificates -> ('a1*'a2) sg_sg_certificates **)

let sg_sg_certs_product eqvS eqvT sg_sgS sg_sgT =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Witness t = eqvT.eqv_nontrivial.certify_nontrivial_witness in
  { sg_sg_left_distributive_d =
  (bop_product_left_distributive_check eqvS.eqv_nontrivial
    eqvT.eqv_nontrivial sg_sgS.sg_sg_left_distributive_d
    sg_sgT.sg_sg_left_distributive_d); sg_sg_right_distributive_d =
  (bop_product_right_distributive_check eqvS.eqv_nontrivial
    eqvT.eqv_nontrivial sg_sgS.sg_sg_right_distributive_d
    sg_sgT.sg_sg_right_distributive_d); sg_sg_plus_id_is_times_ann_d =
  (bop_product_plus_id_is_times_ann_check sg_sgS.sg_sg_plus_id_is_times_ann_d
    sg_sgT.sg_sg_plus_id_is_times_ann_d); sg_sg_times_id_is_plus_ann_d =
  (bop_product_times_id_equals_plus_ann_check
    sg_sgS.sg_sg_times_id_is_plus_ann_d sg_sgT.sg_sg_times_id_is_plus_ann_d);
  sg_sg_left_absorptive_d =
  (bop_product_left_absorptive_check s t sg_sgS.sg_sg_left_absorptive_d
    sg_sgT.sg_sg_left_absorptive_d); sg_sg_right_absorptive_d =
  (bop_product_right_absorptive_check s t sg_sgS.sg_sg_right_absorptive_d
    sg_sgT.sg_sg_right_absorptive_d) }

(** val sg_sg_certs_llex_product :
    'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a2 binary_op
    -> 'a1 eqv_certificates -> 'a2 eqv_certificates -> 'a1 sg_certificates ->
    'a2 sg_certificates -> 'a1 sg_sg_certificates -> 'a2 sg_sg_certificates
    -> ('a1*'a2) sg_sg_certificates **)

let sg_sg_certs_llex_product rS rT addS addT mulT eqvS eqvT sg_timesS sg_timesT sg_sgS sg_sgT =
  let Certify_Witness s = eqvS.eqv_nontrivial.certify_nontrivial_witness in
  let Certify_Witness t = eqvT.eqv_nontrivial.certify_nontrivial_witness in
  { sg_sg_left_distributive_d =
  (bops_llex_product_left_distributive_check rS rT addS addT mulT
    eqvS.eqv_nontrivial eqvT.eqv_nontrivial sg_timesS.sg_left_cancel_d
    sg_timesT.sg_left_constant_d sg_sgS.sg_sg_left_distributive_d
    sg_sgT.sg_sg_left_distributive_d); sg_sg_right_distributive_d =
  (bops_llex_product_right_distributive_check rS rT addS addT mulT
    eqvS.eqv_nontrivial eqvT.eqv_nontrivial sg_timesS.sg_right_cancel_d
    sg_timesT.sg_right_constant_d sg_sgS.sg_sg_right_distributive_d
    sg_sgT.sg_sg_right_distributive_d); sg_sg_plus_id_is_times_ann_d =
  (bops_llex_product_plus_id_is_times_ann_check
    sg_sgS.sg_sg_plus_id_is_times_ann_d sg_sgT.sg_sg_plus_id_is_times_ann_d);
  sg_sg_times_id_is_plus_ann_d =
  (bops_llex_product_times_id_equals_plus_ann_check
    sg_sgS.sg_sg_times_id_is_plus_ann_d sg_sgT.sg_sg_times_id_is_plus_ann_d);
  sg_sg_left_absorptive_d =
  (bops_llex_product_left_absorptive_check t sg_sgS.sg_sg_left_absorptive_d
    sg_sgT.sg_sg_left_absorptive_d sg_timesS.sg_anti_left_d);
  sg_sg_right_absorptive_d =
  (bops_llex_product_right_absorptive_check t sg_sgS.sg_sg_right_absorptive_d
    sg_sgT.sg_sg_right_absorptive_d sg_timesS.sg_anti_right_d) }

