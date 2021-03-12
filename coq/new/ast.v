Require Import CAS.coq.common.compute.


Inductive ast_eqv : Type := 
   | Ast_eqv_bool          : ast_eqv
   | Ast_eqv_nat           : ast_eqv
   | Ast_eqv_list          : ast_eqv → ast_eqv
   | Ast_eqv_set           : ast_eqv → ast_eqv
   | Ast_eqv_product       : ast_eqv * ast_eqv → ast_eqv
   | Ast_eqv_sum           : ast_eqv * ast_eqv → ast_eqv
   | Ast_eqv_add_constant  : cas_constant * ast_eqv → ast_eqv
(*    | Ast_eqv_nat_ceiling   : nat → ast_eqv   
   | Ast_eqv_minset        : ast_po → ast_eqv   *)
   .


Inductive  ast_sg :=
   | Ast_sg_times          : ast_sg
   | Ast_sg_plus           : ast_sg
   | Ast_sg_min            : ast_sg
   | Ast_sg_max            : ast_sg                      
   | Ast_sg_concat         : ast_eqv → ast_sg
   | Ast_sg_left           : ast_eqv → ast_sg
   | Ast_sg_right          : ast_eqv → ast_sg
   | Ast_sg_left_sum       : ast_sg * ast_sg → ast_sg
   | Ast_sg_right_sum      : ast_sg * ast_sg → ast_sg
   | Ast_sg_product        : ast_sg * ast_sg → ast_sg
   | Ast_sg_llex           : ast_sg * ast_sg → ast_sg
   | Ast_sg_add_id         : cas_constant * ast_sg → ast_sg
   | Ast_sg_add_ann        : cas_constant * ast_sg → ast_sg
   | Ast_sg_lift           : ast_sg → ast_sg
   | Ast_sg_CI_union       : ast_eqv → ast_sg
   | Ast_sg_CI_intersect   : ast_eqv → ast_sg
(*                                         
   | Ast_sg_CI_minset_union  : ast_po → ast_sg           
*)
   .