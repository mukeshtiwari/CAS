open Basic_types

type ast_eqv =
| Ast_eqv_bool
| Ast_eqv_nat
| Ast_eqv_list of ast_eqv
| Ast_eqv_set of ast_eqv
| Ast_eqv_product of (ast_eqv*ast_eqv)
| Ast_eqv_sum of (ast_eqv*ast_eqv)
| Ast_eqv_add_constant of (cas_constant*ast_eqv)

type ast_sg =
| Ast_sg_concat of ast_eqv
| Ast_sg_left of ast_eqv
| Ast_sg_right of ast_eqv
| Ast_sg_left_sum of (ast_sg*ast_sg)
| Ast_sg_right_sum of (ast_sg*ast_sg)
| Ast_sg_product of (ast_sg*ast_sg)
| Ast_sg_llex of (ast_sg_CS*ast_sg)
| Ast_sg_add_id of (cas_constant*ast_sg)
| Ast_sg_add_ann of (cas_constant*ast_sg)
| Ast_sg_from_sg_C of ast_sg_C
and ast_sg_C =
| Ast_sg_C_times
| Ast_sg_C_add_id of (cas_constant*ast_sg_C)
| Ast_sg_C_add_ann of (cas_constant*ast_sg_C)
| Ast_sg_C_product of (ast_sg_C*ast_sg_C)
| Ast_sg_C_left_sum of (ast_sg_C*ast_sg_C)
| Ast_sg_C_right_sum of (ast_sg_C*ast_sg_C)
| Ast_sg_C_llex of (ast_sg_CS*ast_sg_C)
| Ast_sg_C_from_sg_CI of ast_sg_CI
| Ast_sg_C_from_sg_CK of ast_sg_CK
| Ast_sg_C_from_sg of ast_sg
and ast_sg_CK =
| Ast_sg_CK_plus
| Ast_sg_CK_product of (ast_sg_CK*ast_sg_CK)
| Ast_sg_CK_from_sg of ast_sg
| Ast_sg_CK_from_sg_C of ast_sg_C
and ast_sg_CI =
| Ast_sg_CI_union_with_ann of (cas_constant*ast_eqv)
| Ast_sg_CI_intersect_with_id of (cas_constant*ast_eqv)
| Ast_sg_CI_add_id of (cas_constant*ast_sg_CI)
| Ast_sg_CI_add_ann of (cas_constant*ast_sg_CI)
| Ast_sg_CI_left_sum of (ast_sg_CI*ast_sg_CI)
| Ast_sg_CI_right_sum of (ast_sg_CI*ast_sg_CI)
| Ast_sg_CI_product of (ast_sg_CI*ast_sg_CI)
| Ast_sg_CI_llex of (ast_sg_CS*ast_sg_CI)
| Ast_sg_CI_from_sg_CS of ast_sg_CS
| Ast_sg_CI_from_sg_C of ast_sg_C
and ast_sg_CS =
| Ast_sg_CS_and
| Ast_sg_CS_or
| Ast_sg_CS_min
| Ast_sg_CS_max
| Ast_sg_CS_add_id of (cas_constant*ast_sg_CS)
| Ast_sg_CS_add_ann of (cas_constant*ast_sg_CS)
| Ast_sg_CS_left_sum of (ast_sg_CS*ast_sg_CS)
| Ast_sg_CS_right_sum of (ast_sg_CS*ast_sg_CS)
| Ast_sg_CS_llex of (ast_sg_CS*ast_sg_CS)
| Ast_sg_CS_from_sg_CI of ast_sg_CI
and ast_po =
| Ast_po_llte_from_sg_CI of ast_sg_CI
| Ast_po_product of (ast_po*ast_po)
and ast_to =
| Ast_to_llex of (ast_to*ast_to)

type ast_sg_sg =
| Ast_sg_sg_product of (ast_sg_sg*ast_sg_sg)
| Ast_sg_sg_add_zero of (cas_constant*ast_sg_sg)
and ast_sg_CS_sg =
| Ast_sg_CS_sg_product of (ast_sg_CS_sg*ast_sg_CS_sg)
| Ast_sg_CS_sg_llex of (ast_sg_CS_sg*ast_sg_CS_sg)
and ast_sg_CI_sg =
| Ast_sg_CI_sg_product of (ast_sg_CI_sg*ast_sg_CI_sg)
| Ast_sg_CI_sg_llex of (ast_sg_CS_sg*ast_sg_CI_sg)
and ast_sg_C_sg =
| Ast_sg_C_sg_llex of (ast_sg_CS_sg*ast_sg_C_sg)
| Ast_sg_C_sg_add_one of (cas_constant*ast_sg_C_sg)
| Ast_sg_C_sg_product of (ast_sg_C_sg*ast_sg_C_sg)

