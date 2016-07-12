open Datatypes
open Certificates

type 's eqv_certificates = { eqv_nontrivial : 's assert_nontrivial }

val eqv_nontrivial : 'a1 eqv_certificates -> 'a1 assert_nontrivial

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

val sg_commutative_d : 'a1 sg_certificates -> 'a1 check_commutative

val sg_selective_d : 'a1 sg_certificates -> 'a1 check_selective

val sg_idempotent_d : 'a1 sg_certificates -> 'a1 check_idempotent

val sg_exists_id_d : 'a1 sg_certificates -> 'a1 check_exists_id

val sg_exists_ann_d : 'a1 sg_certificates -> 'a1 check_exists_ann

val sg_is_left_d : 'a1 sg_certificates -> 'a1 check_is_left

val sg_is_right_d : 'a1 sg_certificates -> 'a1 check_is_right

val sg_left_cancel_d : 'a1 sg_certificates -> 'a1 check_left_cancellative

val sg_right_cancel_d : 'a1 sg_certificates -> 'a1 check_right_cancellative

val sg_left_constant_d : 'a1 sg_certificates -> 'a1 check_left_constant

val sg_right_constant_d : 'a1 sg_certificates -> 'a1 check_right_constant

val sg_anti_left_d : 'a1 sg_certificates -> 'a1 check_anti_left

val sg_anti_right_d : 'a1 sg_certificates -> 'a1 check_anti_right

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

val sgn_commutative_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum

val sgn_idempotent_d : 'a1 sg_certificates_new -> (unit, 'a1) sum

val sgn_exists_id_d : 'a1 sg_certificates_new -> ('a1, unit) sum

val sgn_exists_ann_d : 'a1 sg_certificates_new -> ('a1, unit) sum

val sgn_is_left_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum

val sgn_is_right_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum

val sgn_left_cancel_d : 'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum

val sgn_right_cancel_d : 'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum

val sgn_left_constant_d :
  'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum

val sgn_right_constant_d :
  'a1 sg_certificates_new -> (unit, 'a1*('a1*'a1)) sum

val sgn_anti_left_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum

val sgn_anti_right_d : 'a1 sg_certificates_new -> (unit, 'a1*'a1) sum

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

val sg_C_selective_d : 'a1 sg_C_certificates -> 'a1 check_selective

val sg_C_idempotent_d : 'a1 sg_C_certificates -> 'a1 check_idempotent

val sg_C_exists_id_d : 'a1 sg_C_certificates -> 'a1 check_exists_id

val sg_C_exists_ann_d : 'a1 sg_C_certificates -> 'a1 check_exists_ann

val sg_C_left_cancel_d : 'a1 sg_C_certificates -> 'a1 check_left_cancellative

val sg_C_right_cancel_d :
  'a1 sg_C_certificates -> 'a1 check_right_cancellative

val sg_C_left_constant_d : 'a1 sg_C_certificates -> 'a1 check_left_constant

val sg_C_right_constant_d : 'a1 sg_C_certificates -> 'a1 check_right_constant

val sg_C_anti_left_d : 'a1 sg_C_certificates -> 'a1 check_anti_left

val sg_C_anti_right_d : 'a1 sg_C_certificates -> 'a1 check_anti_right

type 's sg_CS_certificates = { sg_CS_exists_id_d : 's check_exists_id;
                               sg_CS_exists_ann_d : 's check_exists_ann }

val sg_CS_exists_id_d : 'a1 sg_CS_certificates -> 'a1 check_exists_id

val sg_CS_exists_ann_d : 'a1 sg_CS_certificates -> 'a1 check_exists_ann

type 's sg_CI_certificates = { sg_CI_selective_d : 's check_selective;
                               sg_CI_exists_id_d : 's check_exists_id;
                               sg_CI_exists_ann_d : 's check_exists_ann }

val sg_CI_selective_d : 'a1 sg_CI_certificates -> 'a1 check_selective

val sg_CI_exists_id_d : 'a1 sg_CI_certificates -> 'a1 check_exists_id

val sg_CI_exists_ann_d : 'a1 sg_CI_certificates -> 'a1 check_exists_ann

type 's sg_CK_certificates = { sg_CK_exists_id_d : 's check_exists_id;
                               sg_CK_anti_left_d : 's check_anti_left;
                               sg_CK_anti_right_d : 's check_anti_right }

val sg_CK_exists_id_d : 'a1 sg_CK_certificates -> 'a1 check_exists_id

val sg_CK_anti_left_d : 'a1 sg_CK_certificates -> 'a1 check_anti_left

val sg_CK_anti_right_d : 'a1 sg_CK_certificates -> 'a1 check_anti_right

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

val sg_sg_left_distributive_d :
  'a1 sg_sg_certificates -> 'a1 check_left_distributive

val sg_sg_right_distributive_d :
  'a1 sg_sg_certificates -> 'a1 check_right_distributive

val sg_sg_plus_id_is_times_ann_d :
  'a1 sg_sg_certificates -> 'a1 check_plus_id_equals_times_ann

val sg_sg_times_id_is_plus_ann_d :
  'a1 sg_sg_certificates -> 'a1 check_times_id_equals_plus_ann

val sg_sg_left_absorptive_d :
  'a1 sg_sg_certificates -> 'a1 check_left_absorptive

val sg_sg_right_absorptive_d :
  'a1 sg_sg_certificates -> 'a1 check_right_absorptive

