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

Inductive ast_sg :=
   | Ast_sg_concat         : ast_eqv → ast_sg
   | Ast_sg_left           : ast_eqv → ast_sg
   | Ast_sg_right          : ast_eqv → ast_sg
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
   | Ast_sg_CI_union_with_ann     : cas_constant * ast_eqv → ast_sg_CI
   | Ast_sg_CI_intersect_with_id  : cas_constant * ast_eqv → ast_sg_CI

   | Ast_sg_CI_add_id             : cas_constant * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_add_ann            : cas_constant * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_left_sum           : ast_sg_CI * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_right_sum          : ast_sg_CI * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_product            : ast_sg_CI * ast_sg_CI → ast_sg_CI
   | Ast_sg_CI_llex               : ast_sg_CS * ast_sg_CI → ast_sg_CI
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

with ast_po :=
   | Ast_po_llte_from_sg_CI : ast_sg_CI  → ast_po 
   | Ast_po_product         : ast_po * ast_po → ast_po

with ast_to :=
   | Ast_to_llex           : ast_to * ast_to → ast_to
   . 


(*

theory/bops_product_product.v

   | Ast_sg_C_sg_llex_product   : ast_sg_CS_sg * ast_sg_C_sg → ast_sg_C_sg

   | Ast_sg_CI_sg_llex_product  : ast_sg_CS_sg * ast_sg_CI_sg → ast_sg_CI_sg
   | Ast_sg_CS_sg_llex_product  : ast_sg_CS_sg * ast_sg_CS_sg → ast_sg_CS_sg

   | Ast_sg_CI_sg_BD_llex_product  : ast_sg_CS_sg_CK_BD * ast_sg_CI_sg_BD → ast_sg_CI_sg_BD
   | Ast_sg_CI_sg_BD_llex_product  : ast_sg_CS_sg_CK_BD * ast_sg_?C_sg_BD → ast_sg_CI_sg_BD


theory/bops_llex_product.v
theory/bops_left_sum_left_sum.v
theory/bops_left_sum_right_sum.v
theory/bops_add_ann_add_id.v
theory/bops_add_id_add_ann.v

theory/bops_max_min.v
theory/bops_min_max.v
theory/bops_min_plus.v
theory/bops_or_and.v
theory/bops_and_or.v
theory/bops_intersect_union.v
theory/bops_union_intersect.v
*) 
Inductive ast_sg_sg :=
   | Ast_sg_sg_product   : ast_sg_sg * ast_sg_sg → ast_sg_sg
   | Ast_sg_sg_add_zero  : cas_constant * ast_sg_sg → ast_sg_sg
   | Ast_sg_sg_add_one   : cas_constant * ast_sg_sg → ast_sg_sg
   | Ast_sg_sg_from_sg_C_sg : ast_sg_C_sg → ast_sg_sg

with ast_sg_CS_sg :=
   | Ast_sg_CS_sg_product : ast_sg_CS_sg * ast_sg_CS_sg → ast_sg_CS_sg
   | Ast_sg_CS_sg_add_zero  : cas_constant * ast_sg_CS_sg → ast_sg_CS_sg
   | Ast_sg_CS_sg_add_one  : cas_constant * ast_sg_CS_sg → ast_sg_CS_sg
   | Ast_sg_CS_sg_llex : ast_sg_CS_sg * ast_sg_CS_sg → ast_sg_CS_sg
   | Ast_sg_CS_sg_from_sg_CS_sg_CK_AD : ast_sg_CS_sg_CK_AD → ast_sg_CS_sg
   | Ast_sg_CS_sg_from_sg_CS_sg_CS_AD : ast_sg_CS_sg_CS_AD → ast_sg_CS_sg

with ast_sg_CI_sg :=
   | Ast_sg_CI_sg_product : ast_sg_CI_sg * ast_sg_CI_sg → ast_sg_CI_sg
   | Ast_sg_CI_sg_llex : ast_sg_CS_sg * ast_sg_CI_sg → ast_sg_CI_sg

with ast_sg_C_sg :=
   | Ast_sg_C_sg_llex    : ast_sg_CS_sg * ast_sg_C_sg → ast_sg_C_sg
   | Ast_sg_C_sg_add_one : cas_constant * ast_sg_C_sg → ast_sg_C_sg
   | Ast_sg_C_sg_product : ast_sg_C_sg * ast_sg_C_sg → ast_sg_C_sg
   | Ast_sg_C_sg_from_sg_CS_sg : ast_sg_CS_sg → ast_sg_C_sg 
   | Ast_sg_C_sg_from_sg_CS_sg_CS_AD : ast_sg_CS_sg_CS_AD → ast_sg_C_sg 
with ast_sg_CS_sg_CS_AD :=
   | Ast_sg_CS_sg_CS_AD_and_or  : ast_sg_CS_sg_CS_AD 
   | Ast_sg_CS_sg_CS_AD_or_and  : ast_sg_CS_sg_CS_AD 
   | Ast_sg_CS_sg_CS_AD_max_min : ast_sg_CS_sg_CS_AD 
   | Ast_sg_CS_sg_CS_AD_min_max : ast_sg_CS_sg_CS_AD 
with ast_sg_CS_sg_CK_AD :=
   | Ast_sg_CS_sg_CK_AD_min_plus  : ast_sg_CS_sg_CK_AD
with  ast_sg_CS_sg_CK_D :=
   | Ast_sg_CS_sg_CK_D_max_plus  : ast_sg_CS_sg_CK_D 
   . 
 
Inductive ast_sg_sg_D :=
   | Ast_sg_sg_D_product  : ast_sg_sg_D * ast_sg_sg_D → ast_sg_sg_D
   . 

Inductive ast_sg_CI_sg_D :=
   | Ast_sg_CI_sg_D_product : ast_sg_CI_sg_D * ast_sg_CI_sg_D → ast_sg_CI_sg_D
   . 

Inductive ast_sg_CI_sg_BD :=
   | Ast_sg_CI_sg_BD_product : ast_sg_CI_sg_BD * ast_sg_CI_sg_BD → ast_sg_CI_sg_BD
   . 

Inductive ast_sg_CS_sg_D :=
   | Ast_sg_CS_sg_D_product : ast_sg_CS_sg_D * ast_sg_CS_sg_D → ast_sg_CS_sg_D
   . 

Inductive ast_sg_CS_sg_BD :=
   | Ast_sg_CS_sg_BD_product : ast_sg_CS_sg_BD * ast_sg_CS_sg_BD → ast_sg_CS_sg_BD
   . 

Inductive ast_sg_CS_sg_CS_A :=
   | Ast_sg_CS_sg_CS_AD_unkown : ast_sg_CS_sg_CS_A
   . 

Inductive ast_sg_CI_sg_CI_A :=
   | Ast_sg_CI_sg_CI_A_product : ast_sg_CI_sg_CI_A * ast_sg_CI_sg_CI_A → ast_sg_CI_sg_CI_A
   . 

Inductive ast_sg_CI_sg_CI_AD :=
   | Ast_sg_CI_sg_CI_AD_product : ast_sg_CI_sg_CI_AD * ast_sg_CI_sg_CI_AD → ast_sg_CI_sg_CI_AD
   . 





