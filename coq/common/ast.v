Require Import CAS.coq.common.compute.

  
Inductive cas_eqv_ast : Type :=
   | Ast_eqv_ascii         : cas_eqv_ast
   | Ast_eqv_bool          : cas_eqv_ast
   | Ast_eqv_nat           : cas_eqv_ast
   | Ast_eqv_list          : cas_eqv_ast → cas_eqv_ast
   | Ast_eqv_set           : cas_eqv_ast → cas_eqv_ast
   | Ast_eqv_product       : cas_eqv_ast * cas_eqv_ast → cas_eqv_ast
   | Ast_eqv_sum           : cas_eqv_ast * cas_eqv_ast → cas_eqv_ast
   | Ast_eqv_add_constant  : cas_constant * cas_eqv_ast → cas_eqv_ast
   | Ast_eqv_nat_ceiling   : nat → cas_eqv_ast   
   | Ast_eqv_minset        : cas_or_ast → cas_eqv_ast
   | Ast_eqv_of_or         : cas_or_ast → cas_eqv_ast
   | Ast_eqv_of_sg         : cas_sg_ast → cas_eqv_ast
   | Ast_eqv_of_bs         : cas_bs_ast → cas_eqv_ast
   | Ast_eqv_of_os         : cas_os_ast → cas_eqv_ast
with cas_or_ast : Type :=
   | Ast_or_nat           : cas_or_ast
   | Ast_or_bool          : cas_or_ast
   | Ast_or_add_bottom    : cas_constant * cas_or_ast → cas_or_ast
   | Ast_or_add_top       : cas_constant * cas_or_ast → cas_or_ast    
   | Ast_or_dual          : cas_or_ast → cas_or_ast      
   | Ast_or_llte          : cas_sg_ast → cas_or_ast
   | Ast_or_rlte          : cas_sg_ast → cas_or_ast
   | Ast_or_length        : cas_eqv_ast → cas_or_ast
   | Ast_or_llex          : cas_or_ast * cas_or_ast → cas_or_ast
   | Ast_or_product       : cas_or_ast * cas_or_ast → cas_or_ast    
   | Ast_or_subset        : cas_eqv_ast → cas_or_ast
   | Ast_or_set           : cas_eqv_ast → cas_or_ast
   | Ast_or_left_sum      : cas_or_ast * cas_or_ast → cas_or_ast
   | Ast_or_right_sum     : cas_or_ast * cas_or_ast → cas_or_ast
   | Ast_or_trivial       : cas_eqv_ast → cas_or_ast
   | Ast_or_of_os         : cas_os_ast → cas_or_ast                                               
with cas_sg_ast : Type :=
   | Ast_sg_times        : cas_sg_ast
   | Ast_sg_plus         : cas_sg_ast
   | Ast_sg_or           : cas_sg_ast
   | Ast_sg_and          : cas_sg_ast                              
   | Ast_sg_min          : cas_sg_ast 
   | Ast_sg_max          : cas_sg_ast
   | Ast_sg_add_id       : cas_constant * cas_sg_ast → cas_sg_ast
   | Ast_sg_add_ann      : cas_constant * cas_sg_ast → cas_sg_ast    
   | Ast_sg_concat       : cas_eqv_ast → cas_sg_ast         
   | Ast_sg_union        : cas_eqv_ast → cas_sg_ast
   | Ast_sg_intersect    : cas_eqv_ast → cas_sg_ast  
   | Ast_sg_left         : cas_eqv_ast → cas_sg_ast
   | Ast_sg_right        : cas_eqv_ast → cas_sg_ast
   | Ast_sg_left_sum     : cas_sg_ast * cas_sg_ast → cas_sg_ast
   | Ast_sg_right_sum    : cas_sg_ast * cas_sg_ast → cas_sg_ast
   | Ast_sg_lift         : cas_sg_ast → cas_sg_ast
   | Ast_sg_llex         : cas_sg_ast * cas_sg_ast → cas_sg_ast
   | Ast_sg_product      : cas_sg_ast * cas_sg_ast → cas_sg_ast
   | Ast_sg_minset_lift  : cas_os_ast → cas_sg_ast   
   | Ast_sg_minset_union : cas_or_ast → cas_sg_ast
   | Ast_sg_plus_of_bs   : cas_bs_ast → cas_sg_ast
   | Ast_sg_times_of_bs  : cas_bs_ast → cas_sg_ast
   | Ast_sg_times_of_os  : cas_os_ast → cas_sg_ast
with cas_bs_ast : Type :=
   | Ast_min_plus : cas_bs_ast
   | Ast_max_plus : cas_bs_ast
   | Ast_and_or   : cas_bs_ast
   | Ast_or_and   : cas_bs_ast                      
   | Ast_max_min   : cas_bs_ast
   | Ast_min_max   : cas_bs_ast                      
   | Ast_bs_add_zero   : cas_constant * cas_bs_ast → cas_bs_ast
   | Ast_bs_add_one    : cas_constant * cas_bs_ast → cas_bs_ast  
   | Ast_bs_product    : cas_bs_ast * cas_bs_ast → cas_bs_ast
   | Ast_bs_llex_product       : cas_bs_ast * cas_bs_ast → cas_bs_ast
   | Ast_bs_union_lift : cas_sg_ast → cas_bs_ast
   | Ast_bs_left_sum_right_sum   : cas_bs_ast * cas_bs_ast → cas_bs_ast
   | Ast_bs_right_sum_left_sum  : cas_bs_ast * cas_bs_ast → cas_bs_ast 
   | Ast_bs_left   : cas_sg_ast  → cas_bs_ast
   | Ast_bs_right  : cas_sg_ast  → cas_bs_ast      
   | Ast_union_intersect : cas_eqv_ast → cas_bs_ast
   | Ast_intersect_union : cas_eqv_ast → cas_bs_ast    
   | Ast_bs_dual : cas_bs_ast → cas_bs_ast   
   | Ast_minset_lift_union : cas_os_ast → cas_bs_ast    
   | Ast_minset_union_lift : cas_os_ast → cas_bs_ast
   | Ast_lift_union : cas_sg_ast → cas_bs_ast    
   | Ast_union_lift : cas_sg_ast → cas_bs_ast                          
with cas_os_ast : Type :=
   | Ast_os_from_bs_left : cas_bs_ast  → cas_os_ast
   | Ast_os_from_bs_right : cas_bs_ast  → cas_os_ast
   | Ast_os_llex_product : cas_os_ast * cas_os_ast  → cas_os_ast
   | Ast_os_product : cas_os_ast * cas_os_ast  → cas_os_ast
   | Ast_os_add_bottom_id : cas_constant * cas_os_ast → cas_os_ast
   | Ast_os_add_top_ann : cas_constant * cas_os_ast → cas_os_ast 
with cas_ltr_ast : Type :=
   | Ast_ltr_cons          : cas_eqv_ast            → cas_ltr_ast    
   | Ast_ltr_product       : cas_ltr_ast * cas_ltr_ast  → cas_ltr_ast
   | Ast_ltr_left_sum      : cas_ltr_ast * cas_ltr_ast  → cas_ltr_ast
   | Ast_ltr_right_sum     : cas_ltr_ast * cas_ltr_ast  → cas_ltr_ast
   | Ast_ltr_lift          : cas_ltr_ast            → cas_ltr_ast
   | Ast_ltr_from_sg       : cas_ltr_ast             → cas_ltr_ast
   | Ast_ltr_with_policy   : cas_ltr_ast            → cas_ltr_ast
with cas_lstr_ast : Type :=
| Ast_lstr_product         : cas_lstr_ast * cas_lstr_ast  → cas_lstr_ast
| Ast_lstr_llex_product    : cas_lstr_ast * cas_lstr_ast  → cas_lstr_ast
with cas_lotr_ast : Type :=
| Ast_lotr_length_cons     : cas_eqv_ast  → cas_lotr_ast  
| Ast_lotr_product         : cas_lotr_ast * cas_lotr_ast  → cas_lotr_ast
| Ast_lotr_llex_product    : cas_lotr_ast * cas_lotr_ast  → cas_lotr_ast
.
