Require Import CAS.code.basic_types. 

Inductive ast_eqv : Type := 
   | Ast_eqv_bool          : ast_eqv
   | Ast_eqv_nat           : ast_eqv
   | Ast_eqv_list          : ast_eqv → ast_eqv
   | Ast_eqv_set           : ast_eqv → ast_eqv
   | Ast_eqv_product       : ast_eqv * ast_eqv → ast_eqv
   | Ast_eqv_sum           : ast_eqv * ast_eqv → ast_eqv
   | Ast_eqv_add_constant  : cas_constant * ast_eqv → ast_eqv
   . 

Inductive ast_qo : Type := 
   | Ast_qo_dual          : ast_qo → ast_qo
   | Ast_qo_list          : ast_eqv → ast_qo
   | Ast_qo_set           : ast_eqv → ast_qo
   | Ast_qo_product       : ast_qo * ast_qo → ast_qo
   | Ast_qo_left_sum      : ast_qo * ast_qo → ast_qo
   | Ast_qo_right_sum     : ast_qo * ast_qo → ast_qo
   | Ast_qo_add_bottom    : cas_constant * ast_qo → ast_qo
   | Ast_qo_add_top       : cas_constant * ast_qo → ast_qo
   | Ast_qo_from_po       : ast_po → ast_qo

with ast_po : Type := 
   | Ast_po_subset        : ast_eqv → ast_po
   | Ast_po_dual          : ast_po → ast_po
   | Ast_po_product       : ast_po * ast_po → ast_po
   | Ast_po_left_sum      : ast_po * ast_po → ast_po
   | Ast_po_right_sum     : ast_po * ast_po → ast_po
   | Ast_po_add_bottom    : cas_constant * ast_po → ast_po
   | Ast_po_add_top       : cas_constant * ast_po → ast_po
   | Ast_po_from_qo       : ast_qo → ast_po
   | Ast_po_from_to       : ast_to → ast_po
   | Ast_po_llte          : ast_sg_CI → ast_po
   | Ast_po_rlte          : ast_sg_CI → ast_po

with ast_to : Type := 
   | Ast_to_nat           : ast_to
   | Ast_to_bool          : ast_to
   | Ast_to_dual          : ast_to → ast_to
   | Ast_to_left_sum      : ast_to * ast_to → ast_to
   | Ast_to_right_sum     : ast_to * ast_to → ast_to
   | Ast_to_add_bottom    : cas_constant * ast_to → ast_to
   | Ast_to_add_top       : cas_constant * ast_to → ast_to
   | Ast_to_from_po       : ast_po → ast_to
   | Ast_to_llte          : ast_sg_CS → ast_to
   | Ast_to_rlte          : ast_sg_CS → ast_to


with ast_sg :=
   | Ast_sg_concat         : ast_eqv → ast_sg
   | Ast_sg_left           : ast_eqv → ast_sg
   | Ast_sg_right          : ast_eqv → ast_sg
   | Ast_sg_plus           : ast_sg
   | Ast_sg_times          : ast_sg
   | Ast_sg_or             : ast_sg
   | Ast_sg_and            : ast_sg
   | Ast_sg_min            : ast_sg
   | Ast_sg_max            : ast_sg

   | Ast_sg_union          : cas_constant * ast_eqv → ast_sg
   | Ast_sg_intersect      : cas_constant * ast_eqv → ast_sg

   | Ast_sg_left_sum       : ast_sg * ast_sg → ast_sg
   | Ast_sg_right_sum      : ast_sg * ast_sg → ast_sg
   | Ast_sg_product        : ast_sg * ast_sg → ast_sg
   | Ast_sg_llex           : ast_sg_CS * ast_sg → ast_sg
   | Ast_sg_add_id         : cas_constant * ast_sg → ast_sg
   | Ast_sg_add_ann        : cas_constant * ast_sg → ast_sg
   | Ast_sg_from_sg_C      : ast_sg_C → ast_sg


with ast_sg_C :=
   | Ast_sg_C_times          : ast_sg_C 
   | Ast_sg_C_add_id         : cas_constant * ast_sg_C → ast_sg_C
   | Ast_sg_C_add_ann        : cas_constant * ast_sg_C → ast_sg_C
   | Ast_sg_C_product        : ast_sg_C * ast_sg_C → ast_sg_C
   | Ast_sg_C_left_sum       : ast_sg_C * ast_sg_C → ast_sg_C
   | Ast_sg_C_right_sum      : ast_sg_C * ast_sg_C → ast_sg_C
   | Ast_sg_C_llex           : ast_sg_CS * ast_sg_C → ast_sg_C
   | Ast_sg_C_from_sg_CI     : ast_sg_CI → ast_sg_C
   | Ast_sg_C_from_sg_CK     : ast_sg_CK → ast_sg_C
   | Ast_sg_C_from_sg        : ast_sg → ast_sg_C

with ast_sg_CK :=
   | Ast_sg_CK_plus          : ast_sg_CK 
   | Ast_sg_CK_product       : ast_sg_CK * ast_sg_CK → ast_sg_CK
   | Ast_sg_CK_from_sg       : ast_sg → ast_sg_CK
   | Ast_sg_CK_from_sg_C     : ast_sg_C → ast_sg_CK
   
with ast_sg_CI :=
   | Ast_sg_CI_add_id             : cas_constant * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_add_ann            : cas_constant * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_left_sum           : ast_sg_CI * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_right_sum          : ast_sg_CI * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_product            : ast_sg_CI * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_llex               : ast_sg_CS * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_union_with_ann     : cas_constant * ast_eqv → ast_sg_CI
   | Ast_sg_CI_intersect_with_id  : cas_constant * ast_eqv → ast_sg_CI
   | Ast_sg_CI_from_sg_CS         : ast_sg_CS → ast_sg_CI
   | Ast_sg_CI_from_sg_C          : ast_sg_C → ast_sg_CI

with ast_sg_CS :=
   | Ast_sg_CS_and          : ast_sg_CS 
   | Ast_sg_CS_or           : ast_sg_CS 
   | Ast_sg_CS_min          : ast_sg_CS 
   | Ast_sg_CS_max          : ast_sg_CS 
   | Ast_sg_CS_add_id       : cas_constant * ast_sg_CS → ast_sg_CS
   | Ast_sg_CS_add_ann      : cas_constant * ast_sg_CS → ast_sg_CS
   | Ast_sg_CS_left_sum     : ast_sg_CS * ast_sg_CS → ast_sg_CS
   | Ast_sg_CS_right_sum    : ast_sg_CS * ast_sg_CS → ast_sg_CS
   | Ast_sg_CS_llex         : ast_sg_CS * ast_sg_CS → ast_sg_CS
   | Ast_sg_CS_from_sg_CI   : ast_sg_CI → ast_sg_CS
   . 

Inductive ast_bs :=
   | Ast_bs_min_max   : ast_bs 
   | Ast_bs_max_min   : ast_bs 
   | Ast_bs_and_or    : ast_bs 
   | Ast_bs_or_and    : ast_bs 
   | Ast_bs_min_plus  : ast_bs 
   | Ast_bs_max_plus  : ast_bs 
   | Ast_bs_min_times : ast_bs 
   | Ast_bs_max_times : ast_bs 

   | Ast_bs_product    : ast_bs * ast_bs → ast_bs
   | Ast_bs_left_sum    : ast_bs * ast_bs → ast_bs                                             
   | Ast_bs_add_zero   : cas_constant * ast_bs → ast_bs
   | Ast_bs_add_one    : cas_constant * ast_bs → ast_bs

   | Ast_bs_from_bs_CS : ast_bs_CS → ast_bs
   | Ast_bs_from_bs_C  : ast_bs_C → ast_bs
   | Ast_bs_from_lattice : ast_lattice → ast_bs
                                        
with ast_bs_CS :=
   | Ast_bs_CS_product   : ast_bs_CS * ast_bs_CS → ast_bs_CS
   | Ast_bs_CS_add_zero  : cas_constant * ast_bs_CS → ast_bs_CS
   | Ast_bs_CS_add_one   : cas_constant * ast_bs_CS → ast_bs_CS
   | Ast_bs_CS_llex      : ast_bs_CS * ast_bs_CS → ast_bs_CS
   | Ast_bs_CS_from_bs   : ast_bs  → ast_bs_CS

with ast_bs_C :=
   | Ast_bs_C_product   : ast_bs_C * ast_bs_C → ast_bs_C
   | Ast_bs_C_add_zero  : cas_constant * ast_bs_C → ast_bs_C
   | Ast_bs_C_add_one   : cas_constant * ast_bs_C → ast_bs_C
   | Ast_bs_C_llex      : ast_bs_CS * ast_bs_C → ast_bs_C
   | Ast_bs_C_from_bs   : ast_bs  → ast_bs_C
   | Ast_bs_C_from_semiring  : ast_semiring → ast_bs_C

with  ast_semiring :=
| Ast_semiring_add_zero   : cas_constant * ast_semiring → ast_semiring
| Ast_semiring_product    : ast_semiring * ast_semiring → ast_semiring
| Ast_semiring_from_dioid  : ast_dioid → ast_semiring                                                            

with ast_dioid :=
| Ast_dioid_min_plus : ast_dioid
| Ast_dioid_max_plus : ast_dioid
| Ast_dioid_add_zero  : cas_constant * ast_dioid → ast_dioid
| Ast_dioid_product   : ast_dioid * ast_dioid → ast_dioid
| Ast_dioid_from_distributive_lattice_left : ast_distributive_lattice → ast_dioid
| Ast_dioid_from_distributive_lattice_right : ast_distributive_lattice → ast_dioid
| Ast_dioid_from_distributive_lattice  : ast_distributive_lattice → ast_dioid
                                                                          
with ast_distributive_lattice :=
| Ast_distributive_lattice_min_max  : ast_distributive_lattice
| Ast_distributive_lattice_and_or   : ast_distributive_lattice
| Ast_distributive_lattice_add_one  : cas_constant * ast_distributive_lattice → ast_distributive_lattice
| Ast_distributive_lattice_add_zero : cas_constant * ast_distributive_lattice → ast_distributive_lattice
| Ast_distributive_lattice_product  : ast_distributive_lattice * ast_distributive_lattice → ast_distributive_lattice
| Ast_distributive_lattice_left_sum : ast_distributive_lattice * ast_distributive_lattice → ast_distributive_lattice                      
| Ast_distributive_lattice_dual     : ast_distributive_lattice → ast_distributive_lattice
| Ast_distributive_lattice_intersect_union : cas_constant * ast_eqv → ast_distributive_lattice
| Ast_distributive_lattice_union_intersect : cas_constant * ast_eqv → ast_distributive_lattice
                                                                   

with ast_lattice :=
  | Ast_lattice_dual : ast_lattice → ast_lattice     
  | Ast_lattice_add_zero  : cas_constant * ast_lattice → ast_lattice
  | Ast_lattice_add_one  : cas_constant * ast_lattice → ast_lattice
  | Ast_lattice_product   : ast_lattice * ast_lattice → ast_lattice
  | Ast_lattice_left_sum   : ast_lattice * ast_lattice → ast_lattice                                                          
  | Ast_lattice_from_distributive_lattice   : ast_distributive_lattice → ast_lattice                                                          
  .
  

Inductive ast_os :=
   | Ast_os_from_bs_CS : ast_bs_CS → ast_os
  .

  
