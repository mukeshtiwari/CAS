
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.bool.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.eqv.list. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.add_constant. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.lte_nat. 
Require Import CAS.coq.po.product. 
Require Import CAS.coq.po.from_sg. 


Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up. 

(* base semigroups *) 
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.max. 
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.times.

(* unary combinators *) 
(* these take an eqv as an argument *) 
Require Import CAS.coq.sg.concat.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.sg.left.
Require Import CAS.coq.sg.right. 
(* these take a semigroup as an argument *) 
Require Import CAS.coq.sg.add_ann.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.lift. 

(* binary combinators over semigroups *)
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.left_sum.
Require Import CAS.coq.sg.right_sum.

(* *)
Require Import CAS.coq.sg.minset_union. 
Require Import CAS.coq.sg.minset_lift.

Open Scope nat_scope.

Definition infinity :=
{|
  constant_ascii := "INF"
; constant_latex := "\\infty"
|}.

Print A_eqv.
Print eqv. 
Print eqv_proofs. 
Print brel_not_trivial.
Print eqv_eq_nat.
Print A_eqv_nat.
Print eqv_proofs_eq_nat.
Print brel_eq_nat_transitive.

Print A2C_eqv.

Print A_eqv_product.
Print eqv_proofs_product. 
Print brel_product_reflexive. 

Print eqv_product.

Print A_sg.
Print bop_exists_id_decidable. 
Print bop_not_exists_id.
Print bop_not_is_id.
Print sg_proofs. 

Print sg.
Print check_exists_id.
Print  sg_certificates.
Print check_commutative. 


Print A_sg_product.
Print bop_product_exists_id_decide. 

Print sg_product.
Print sg_certs_product.
Print check_selective_product. 
Print bop_product.
Print check_exists_id_product. 


Eval cbv in mcas_sg_certs (mcas_sg_llex mcas_sg_max mcas_sg_min).

Eval cbv in mcas_sg_certs (sg_mcas_cast_up _ (mcas_sg_llex mcas_sg_max mcas_sg_min)). 

Eval cbv in mcas_sg_certs (mcas_sg_llex mcas_sg_max mcas_sg_plus).

Eval cbv in mcas_sg_certs (mcas_sg_llex mcas_sg_max (mcas_sg_concat eqv_eq_nat)).

Definition N :=
{|
  constant_ascii := "N"
; constant_latex := "\\NN"
|}.

Eval cbv in mcas_sg_certs (mcas_sg_llex (mcas_sg_union N eqv_eq_nat) mcas_sg_max).

Eval cbv in mcas_sg_certs (mcas_sg_llex (mcas_sg_union N eqv_eq_nat) (mcas_sg_add_id infinity mcas_sg_min)).


Eval cbv in mcas_sg_certs (mcas_sg_add_id infinity (mcas_sg_product mcas_sg_max mcas_sg_min)).


Eval cbv in mcas_sg_certs (sg_mcas_cast_up _ (mcas_sg_llex mcas_sg_max mcas_sg_min)). 





Eval cbv in mcas_sg_certs (mcas_sg_llex (mcas_sg_union N eqv_eq_nat) mcas_sg_min).

Eval cbv in mcas_sg_certs (mcas_sg_llex (mcas_sg_concat eqv_eq_nat) mcas_sg_min). 





Check mcas_sg_minset_union_from_po. 
Print mcas_sg_minset_union_from_po. 
Check eqv_minset_from_po.
Check eqv_minset_from_qo. 
Check minset_lift. 
