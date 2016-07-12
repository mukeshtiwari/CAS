(*open Datatypes
open Certificates
*) 
type 's eqv_certificates = { eqv_nontrivial : 's assert_nontrivial }

(** val eqv_nontrivial : 'a1 eqv_certificates -> 'a1 assert_nontrivial **)

let eqv_nontrivial x = x.eqv_nontrivial

type 's sg_certificates = { sg_commutative_d : 's check_commutative;
                            sg_selective_d : 's check_selective;
                            sg_idempotent_d : 's check_idempotent;
                            sg_exists_id_d : 's check_exists_id;
                            sg_exists_ann_d : 's check_exists_ann;
                            sg_is_left_d : 's check_is_left;
                            sg_is_right_d : 's check_is_right;
                            sg_left_cancel_d : 's check_left_cancellative;
                            sg_right_cancel_d : 's check_right_cancellative;
                            sg_left_constant_d : 's check_left_constant;
                            sg_right_constant_d : 's check_right_constant;
                            sg_anti_left_d : 's check_anti_left;
                            sg_anti_right_d : 's check_anti_right }

(** val sg_commutative_d : 'a1 sg_certificates -> 'a1 check_commutative **)

let sg_commutative_d x = x.sg_commutative_d

(** val sg_selective_d : 'a1 sg_certificates -> 'a1 check_selective **)

let sg_selective_d x = x.sg_selective_d

(** val sg_idempotent_d : 'a1 sg_certificates -> 'a1 check_idempotent **)

let sg_idempotent_d x = x.sg_idempotent_d

(** val sg_exists_id_d : 'a1 sg_certificates -> 'a1 check_exists_id **)

let sg_exists_id_d x = x.sg_exists_id_d

(** val sg_exists_ann_d : 'a1 sg_certificates -> 'a1 check_exists_ann **)

let sg_exists_ann_d x = x.sg_exists_ann_d

(** val sg_is_left_d : 'a1 sg_certificates -> 'a1 check_is_left **)

let sg_is_left_d x = x.sg_is_left_d

(** val sg_is_right_d : 'a1 sg_certificates -> 'a1 check_is_right **)

let sg_is_right_d x = x.sg_is_right_d

(** val sg_left_cancel_d :
    'a1 sg_certificates -> 'a1 check_left_cancellative **)

let sg_left_cancel_d x = x.sg_left_cancel_d

(** val sg_right_cancel_d :
    'a1 sg_certificates -> 'a1 check_right_cancellative **)

let sg_right_cancel_d x = x.sg_right_cancel_d

(** val sg_left_constant_d :
    'a1 sg_certificates -> 'a1 check_left_constant **)

let sg_left_constant_d x = x.sg_left_constant_d

(** val sg_right_constant_d :
    'a1 sg_certificates -> 'a1 check_right_constant **)

let sg_right_constant_d x = x.sg_right_constant_d

(** val sg_anti_left_d : 'a1 sg_certificates -> 'a1 check_anti_left **)

let sg_anti_left_d x = x.sg_anti_left_d

(** val sg_anti_right_d : 'a1 sg_certificates -> 'a1 check_anti_right **)

let sg_anti_right_d x = x.sg_anti_right_d

type 's sg_certificates_new = { sgn_commutative_d : (unit, 's*'s) sum;
                                sgn_selective_d : (unit, 's*'s) sum;
                                sgn_idempotent_d : (unit, 's) sum;
                                sgn_exists_id_d : ('s, unit) sum;
                                sgn_exists_ann_d : ('s, unit) sum;
                                sgn_is_left_d : (unit, 's*'s) sum;
                                sgn_is_right_d : (unit, 's*'s) sum;
                                sgn_left_cancel_d : (unit, 's*('s*'s)) sum;
                                sgn_right_cancel_d : (unit, 's*('s*'s)) sum;
                                sgn_left_constant_d : (unit, 's*('s*'s)) sum;
                                sgn_right_constant_d : (unit, 's*('s*'s)) sum;
                                sgn_anti_left_d : (unit, 's*'s) sum;
                                sgn_anti_right_d : (unit, 's*'s) sum }

(** val sgn_commutative_d :
    'a1 sg_certificates_new -> (unit, 'a1*'a1) sum **)

let sgn_commutative_d x = x.sgn_commutative_d

(** val sgn_idempotent_d : 'a1 sg_certificates_new -> (unit, 'a1) sum **)

let sgn_idempotent_d x = x.sgn_idempotent_d

(** val sgn_exists_id_d : 'a1 sg_certificates_new -> ('a1, unit) sum **)

let sgn_exists_id_d x = x.sgn_exists_id_d

(** val sgn_exists_ann_d : 'a1 sg_certificates_new -> ('a1, unit) sum **)

let sgn_exists_ann_d x = x.sgn_exists_ann_d

(** val sgn_is_left_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum **)

let sgn_is_left_d x = x.sgn_is_left_d

(** val sgn_is_right_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum **)

let sgn_is_right_d x = x.sgn_is_right_d

(** val sgn_left_cancel_d :
    'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum **)

let sgn_left_cancel_d x = x.sgn_left_cancel_d

(** val sgn_right_cancel_d :
    'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum **)

let sgn_right_cancel_d x = x.sgn_right_cancel_d

(** val sgn_left_constant_d :
    'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum **)

let sgn_left_constant_d x = x.sgn_left_constant_d

(** val sgn_right_constant_d :
    'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum **)

let sgn_right_constant_d x = x.sgn_right_constant_d

(** val sgn_anti_left_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum **)

let sgn_anti_left_d x = x.sgn_anti_left_d

(** val sgn_anti_right_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum **)

let sgn_anti_right_d x = x.sgn_anti_right_d

type 's sg_C_certificates = { sg_C_selective_d : 's check_selective;
                              sg_C_idempotent_d : 's check_idempotent;
                              sg_C_exists_id_d : 's check_exists_id;
                              sg_C_exists_ann_d : 's check_exists_ann;
                              sg_C_left_cancel_d : 's check_left_cancellative;
                              sg_C_right_cancel_d : 's
                                                    check_right_cancellative;
                              sg_C_left_constant_d : 's check_left_constant;
                              sg_C_right_constant_d : 's check_right_constant;
                              sg_C_anti_left_d : 's check_anti_left;
                              sg_C_anti_right_d : 's check_anti_right }

(** val sg_C_selective_d : 'a1 sg_C_certificates -> 'a1 check_selective **)

let sg_C_selective_d x = x.sg_C_selective_d

(** val sg_C_idempotent_d : 'a1 sg_C_certificates -> 'a1 check_idempotent **)

let sg_C_idempotent_d x = x.sg_C_idempotent_d

(** val sg_C_exists_id_d : 'a1 sg_C_certificates -> 'a1 check_exists_id **)

let sg_C_exists_id_d x = x.sg_C_exists_id_d

(** val sg_C_exists_ann_d : 'a1 sg_C_certificates -> 'a1 check_exists_ann **)

let sg_C_exists_ann_d x = x.sg_C_exists_ann_d

(** val sg_C_left_cancel_d :
    'a1 sg_C_certificates -> 'a1 check_left_cancellative **)

let sg_C_left_cancel_d x = x.sg_C_left_cancel_d

(** val sg_C_right_cancel_d :
    'a1 sg_C_certificates -> 'a1 check_right_cancellative **)

let sg_C_right_cancel_d x = x.sg_C_right_cancel_d

(** val sg_C_left_constant_d :
    'a1 sg_C_certificates -> 'a1 check_left_constant **)

let sg_C_left_constant_d x = x.sg_C_left_constant_d

(** val sg_C_right_constant_d :
    'a1 sg_C_certificates -> 'a1 check_right_constant **)

let sg_C_right_constant_d x = x.sg_C_right_constant_d

(** val sg_C_anti_left_d : 'a1 sg_C_certificates -> 'a1 check_anti_left **)

let sg_C_anti_left_d x = x.sg_C_anti_left_d

(** val sg_C_anti_right_d : 'a1 sg_C_certificates -> 'a1 check_anti_right **)

let sg_C_anti_right_d x = x.sg_C_anti_right_d

type 's sg_CS_certificates = { sg_CS_exists_id_d : 's check_exists_id;
                               sg_CS_exists_ann_d : 's check_exists_ann }

(** val sg_CS_exists_id_d : 'a1 sg_CS_certificates -> 'a1 check_exists_id **)

let sg_CS_exists_id_d x = x.sg_CS_exists_id_d

(** val sg_CS_exists_ann_d :
    'a1 sg_CS_certificates -> 'a1 check_exists_ann **)

let sg_CS_exists_ann_d x = x.sg_CS_exists_ann_d

type 's sg_CI_certificates = { sg_CI_selective_d : 's check_selective;
                               sg_CI_exists_id_d : 's check_exists_id;
                               sg_CI_exists_ann_d : 's check_exists_ann }

(** val sg_CI_selective_d : 'a1 sg_CI_certificates -> 'a1 check_selective **)

let sg_CI_selective_d x = x.sg_CI_selective_d

(** val sg_CI_exists_id_d : 'a1 sg_CI_certificates -> 'a1 check_exists_id **)

let sg_CI_exists_id_d x = x.sg_CI_exists_id_d

(** val sg_CI_exists_ann_d :
    'a1 sg_CI_certificates -> 'a1 check_exists_ann **)

let sg_CI_exists_ann_d x = x.sg_CI_exists_ann_d

type 's sg_CK_certificates = { sg_CK_exists_id_d : 's check_exists_id;
                               sg_CK_anti_left_d : 's check_anti_left;
                               sg_CK_anti_right_d : 's check_anti_right }

(** val sg_CK_exists_id_d : 'a1 sg_CK_certificates -> 'a1 check_exists_id **)

let sg_CK_exists_id_d x = x.sg_CK_exists_id_d

(** val sg_CK_anti_left_d : 'a1 sg_CK_certificates -> 'a1 check_anti_left **)

let sg_CK_anti_left_d x = x.sg_CK_anti_left_d

(** val sg_CK_anti_right_d :
    'a1 sg_CK_certificates -> 'a1 check_anti_right **)

let sg_CK_anti_right_d x = x.sg_CK_anti_right_d

type 's sg_sg_certificates = { sg_sg_left_distributive_d : 's
                                                           check_left_distributive;
                               sg_sg_right_distributive_d : 's
                                                            check_right_distributive;
                               sg_sg_plus_id_is_times_ann_d : 's
                                                              check_plus_id_equals_times_ann;
                               sg_sg_times_id_is_plus_ann_d : 's
                                                              check_times_id_equals_plus_ann;
                               sg_sg_left_absorptive_d : 's
                                                         check_left_absorptive;
                               sg_sg_right_absorptive_d : 's
                                                          check_right_absorptive }

(** val sg_sg_left_distributive_d :
    'a1 sg_sg_certificates -> 'a1 check_left_distributive **)

let sg_sg_left_distributive_d x = x.sg_sg_left_distributive_d

(** val sg_sg_right_distributive_d :
    'a1 sg_sg_certificates -> 'a1 check_right_distributive **)

let sg_sg_right_distributive_d x = x.sg_sg_right_distributive_d

(** val sg_sg_plus_id_is_times_ann_d :
    'a1 sg_sg_certificates -> 'a1 check_plus_id_equals_times_ann **)

let sg_sg_plus_id_is_times_ann_d x = x.sg_sg_plus_id_is_times_ann_d

(** val sg_sg_times_id_is_plus_ann_d :
    'a1 sg_sg_certificates -> 'a1 check_times_id_equals_plus_ann **)

let sg_sg_times_id_is_plus_ann_d x = x.sg_sg_times_id_is_plus_ann_d

(** val sg_sg_left_absorptive_d :
    'a1 sg_sg_certificates -> 'a1 check_left_absorptive **)

let sg_sg_left_absorptive_d x = x.sg_sg_left_absorptive_d

(** val sg_sg_right_absorptive_d :
    'a1 sg_sg_certificates -> 'a1 check_right_absorptive **)

let sg_sg_right_absorptive_d x = x.sg_sg_right_absorptive_d

