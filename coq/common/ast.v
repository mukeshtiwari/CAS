Require Import CAS.coq.common.compute.

Inductive cas_ast : Type :=
   | Ast_eqv_bool          : cas_ast
   | Ast_eqv_nat           : cas_ast
   | Ast_eqv_list          : cas_ast → cas_ast
   | Ast_eqv_set           : cas_ast → cas_ast
   | Ast_eqv_product       : cas_ast * cas_ast → cas_ast
   | Ast_eqv_sum           : cas_ast * cas_ast → cas_ast
   | Ast_eqv_add_constant  : cas_constant * cas_ast → cas_ast
   | Ast_eqv_nat_ceiling   : nat → cas_ast   
   | Ast_eqv_minset        : cas_ast → cas_ast

   | Ast_po_subset        : cas_ast → cas_ast
   | Ast_po_dual          : cas_ast → cas_ast
   | Ast_po_product       : cas_ast * cas_ast → cas_ast
   | Ast_po_left_sum      : cas_ast * cas_ast → cas_ast
   | Ast_po_right_sum     : cas_ast * cas_ast → cas_ast
   | Ast_po_add_bottom    : cas_constant * cas_ast → cas_ast
   | Ast_po_add_top       : cas_constant * cas_ast → cas_ast
   | Ast_po_from_qo       : cas_ast → cas_ast
   | Ast_po_from_to       : cas_ast → cas_ast
   | Ast_po_llte          : cas_ast → cas_ast
   | Ast_po_rlte          : cas_ast → cas_ast
   | Ast_qo_trivial       : cas_ast → cas_ast
   | Ast_qo_length        : cas_ast → cas_ast                                                                                   

   | Ast_to_nat           : cas_ast
   | Ast_to_bool          : cas_ast
   | Ast_to_from_po       : cas_ast → cas_ast
   | Ast_to_llte          : cas_ast → cas_ast
   | Ast_to_rlte          : cas_ast → cas_ast

   | Ast_sg_times        : cas_ast
   | Ast_sg_plus         : cas_ast
   | Ast_sg_and          : cas_ast 
   | Ast_sg_or           : cas_ast 
   | Ast_sg_min          : cas_ast 
   | Ast_sg_max          : cas_ast
   | Ast_sg_union        : cas_ast → cas_ast
   | Ast_sg_intersect    : cas_ast → cas_ast                             
   | Ast_sg_concat       : cas_ast → cas_ast                                
   | Ast_sg_left         : cas_ast → cas_ast
   | Ast_sg_right        : cas_ast → cas_ast

   | Ast_sg_product        : cas_ast * cas_ast → cas_ast
   | Ast_sg_llex           : cas_ast * cas_ast → cas_ast
   | Ast_sg_add_id         : cas_constant * cas_ast → cas_ast
   | Ast_sg_add_ann        : cas_constant * cas_ast → cas_ast                                                   
   | Ast_sg_left_sum       : cas_ast * cas_ast → cas_ast
   | Ast_sg_right_sum      : cas_ast * cas_ast → cas_ast
   | Ast_sg_lift           : cas_ast → cas_ast      
   | Ast_sg_minset_union   : cas_ast → cas_ast                                                
   | Ast_sg_minset_lift    : cas_ast → cas_ast                                          

   | Ast_sg_from_sg_C      : cas_ast → cas_ast                                                
   | Ast_sg_C_from_sg_CI   : cas_ast → cas_ast
   | Ast_sg_C_from_sg_CK   : cas_ast → cas_ast
   | Ast_sg_C_from_sg      : cas_ast → cas_ast
   | Ast_sg_CK_from_sg     : cas_ast → cas_ast
   | Ast_sg_CK_from_sg_C   : cas_ast → cas_ast
   | Ast_sg_CI_from_sg_CS  : cas_ast → cas_ast
   | Ast_sg_CI_from_sg_C   : cas_ast → cas_ast
   | Ast_sg_CS_from_sg_CI  : cas_ast → cas_ast
   | Ast_sg_CS_from_sg_C   : cas_ast → cas_ast                             
   | Ast_asg_from_sg        : cas_ast → cas_ast
   | Ast_msg_from_sg        : cas_ast → cas_ast 


   | Ast_min_plus : cas_ast
   | Ast_max_plus : cas_ast
   | Ast_and_or   : cas_ast                                                                           
   | Ast_union_intersect : cas_ast → cas_ast
   | Ast_max_min   : cas_ast
   | Ast_min_max   : cas_ast
                                        
   | Ast_bs_product    : cas_ast * cas_ast → cas_ast
   | Ast_bs_left_sum   : cas_ast * cas_ast → cas_ast
   | Ast_bs_right_sum  : cas_ast * cas_ast → cas_ast     
   | Ast_bs_add_zero   : cas_constant * cas_ast → cas_ast
   | Ast_bs_add_one    : cas_constant * cas_ast → cas_ast
   | Ast_bs_llex       : cas_ast * cas_ast → cas_ast                                                   
   | Ast_bs_union_lift : cas_ast → cas_ast
   | Ast_bs_dual : cas_ast → cas_ast                                     

   | Ast_bs_CI_from_bs       : cas_ast → cas_ast
   | Ast_bs_CI_from_bs_CS    : cas_ast → cas_ast                                          
   | Ast_bs_CI_from_lattice  : cas_ast → cas_ast                                       
   | Ast_bs_CS_from_bs_CI   : cas_ast  → cas_ast
   | Ast_bs_CS_from_bs      : cas_ast  → cas_ast                                       
   | Ast_bs_from_bs_CI       : cas_ast → cas_ast                                       
   | Ast_bs_from_presemiring : cas_ast → cas_ast

   | Ast_presemiring_product     : cas_ast * cas_ast → cas_ast
   | Ast_mposg_from_bs                    : cas_ast → cas_ast                                            
   | Ast_presemiring_from_bs                    : cas_ast → cas_ast                                                                      
   | Ast_presemiring_from_semiring              : cas_ast → cas_ast
| Ast_presemiring_from_selective_presemiring : cas_ast → cas_ast
| Ast_presemiring_from_distributive_prelattice : cas_ast → cas_ast
| Ast_presemiring_from_selective_distributive_prelattice : cas_ast → cas_ast                                          
| Ast_selective_presemiring_from_presemiring  : cas_ast → cas_ast                                                            
| Ast_semiring_from_presemiring  : cas_ast → cas_ast                                                            
| Ast_semiring_from_dioid        : cas_ast → cas_ast
| Ast_semiring_from_selective_semiring  : cas_ast → cas_ast 
| Ast_selective_semiring_from_semiring  : cas_ast → cas_ast                                                            
| Ast_dioid_from_semiring             : cas_ast → cas_ast                                        
| Ast_dioid_from_distributive_lattice : cas_ast → cas_ast
| Ast_dioid_from_selective_dioid      : cas_ast → cas_ast
| Ast_selective_dioid_from_dioid                           : cas_ast → cas_ast
| Ast_selective_dioid_from_selective_distributive_lattice  : cas_ast → cas_ast                                       
| Ast_distributive_lattice_from_dioid                           : cas_ast → cas_ast
| Ast_distributive_lattice_from_lattice                         : cas_ast → cas_ast
| Ast_distributive_lattice_from_selective_distributive_lattice  : cas_ast → cas_ast
| Ast_selective_distributive_lattice_from_selective_dioid       : cas_ast → cas_ast
| Ast_selective_distributive_lattice_from_distributive_lattice  : cas_ast → cas_ast
  | Ast_lattice_from_bs_CI                  : cas_ast → cas_ast                                                          
  | Ast_lattice_from_distributive_lattice   : cas_ast → cas_ast
| Ast_distributive_prelattice_from_selective_distributive_prelattice  : cas_ast → cas_ast

| Ast_po_from_sg_left : cas_ast → cas_ast
| Ast_po_from_sg_right : cas_ast → cas_ast                              
| Ast_os_from_bs_left : cas_ast → cas_ast
| Ast_os_from_bs_right : cas_ast → cas_ast                                     

   | Ast_ltr_cons          : cas_ast            → cas_ast    
   | Ast_ltr_right         : cas_ast * cas_ast  → cas_ast
   | Ast_ltr_product       : cas_ast * cas_ast  → cas_ast
   | Ast_ltr_left_sum      : cas_ast * cas_ast  → cas_ast
   | Ast_ltr_right_sum     : cas_ast * cas_ast  → cas_ast
   | Ast_ltr_lift          : cas_ast            → cas_ast
   | Ast_ltr_lift_all      : cas_ast            → cas_ast
   | Ast_ltr_with_policy   : cas_ast            → cas_ast                                                     
   | Ast_ltr_from_sg       : cas_ast             → cas_ast
   | Ast_ltr_from_sg_C     : cas_ast           → cas_ast
   | Ast_ltr_from_sg_CI    : cas_ast          → cas_ast
   | Ast_ltr_from_sg_CS    : cas_ast          → cas_ast
   | Ast_ltr_from_sg_CK    : cas_ast          → cas_ast   

.