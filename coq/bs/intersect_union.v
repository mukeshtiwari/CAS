Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.sum.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.bs.union_intersect.
Require Import CAS.coq.bs.dual.

Section Theory.

  (* see CAS.coq.bs.union_intersect for theory *) 
  
End Theory.

Section ACAS.

Definition A_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv : A_eqv S) := 
              A_distributive_lattice_dual _ (A_bs_union_intersect_with_one S c eqv). 

End ACAS.

Section AMCAS.

Definition A_mcas_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv : A_eqv S) :=
    A_BS_distributive_lattice _ (A_bs_intersect_union_with_zero S c eqv).

End AMCAS.


Section CAS.
Definition bs_intersect_union_with_zero {S : Type} (c : cas_constant) (eqv : @eqv S) := 
               distributive_lattice_dual (bs_union_intersect_with_one c eqv).   
End CAS.


Section MCAS.

Definition mcas_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv : @eqv S) :=
    BS_distributive_lattice (bs_intersect_union_with_zero c eqv).

End MCAS.


Section Verify.

Theorem correct_intersect_union (S : Type) (c : cas_constant) (eqv: A_eqv S) : 
    bs_intersect_union_with_zero c (A2C_eqv S eqv)
    =
    A2C_distributive_lattice _ (A_bs_intersect_union_with_zero S c eqv). 
Proof. unfold bs_intersect_union_with_zero, A_bs_intersect_union_with_zero.
       rewrite <- correct_distributive_lattice_dual.
       rewrite correct_union_intersect_with_one.       
       reflexivity.
Qed. 

Theorem bop_mcas_intersect_union_correct (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
         mcas_bs_intersect_union_with_zero _ c (A2C_eqv S eqvS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_intersect_union_with_zero _ c eqvS). 
Proof. unfold mcas_bs_intersect_union_with_zero, A_mcas_bs_intersect_union_with_zero, A2C_mcas_bs. 
       rewrite correct_intersect_union. 
       reflexivity. 
Qed.  


End Verify.   
  
