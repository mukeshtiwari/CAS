Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 

Require Import CAS.a_code.a_cas_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.bs_certificates.
Require Import CAS.code.bs_cert_records.
Require Import CAS.code.bs_records.

Require Import CAS.theory.bs_properties.
Require Import CAS.theory.facts.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.bs.dual.
Require Import CAS.coq.bs.min_max.


Section Theory.

Lemma bops_max_min_left_distributive  : 
     bop_left_distributive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bop_left_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_right_distributive  : 
     bop_right_distributive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bop_right_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_reflexive. 
Qed. 


Lemma bops_max_min_left_left_absorptive  : 
     bops_left_left_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. unfold bops_left_left_absorptive.
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma bops_max_min_left_right_absorptive  : 
       bops_left_right_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. apply bops_left_left_absorptive_implies_left_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_max_congruence. 
       apply bop_min_commutative. 
       apply bops_max_min_left_left_absorptive. 
Qed. 


Lemma bops_max_min_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_max_congruence. 
       apply bop_max_commutative. 
       apply bop_min_commutative. 
       apply bops_max_min_left_right_absorptive. 
Qed. 


Lemma bops_max_min_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_max bop_min. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_max_congruence. 
       apply bop_min_commutative. 
       apply bops_max_min_right_left_absorptive. 
Qed. 

End Theory.

Section ACAS.

Definition A_distributive_lattice_max_min : A_distributive_lattice nat := A_distributive_lattice_dual nat A_distributive_lattice_min_max. 

End ACAS.

Section CAS.

Definition distributive_lattice_max_min : @distributive_lattice nat := distributive_lattice_dual distributive_lattice_min_max.   

End CAS.

Section Verify.
 
End Verify.   
  