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

(* see bs/union_intersect.v and bs/dual.v for theory 

   need an mcas_bs_dual, so some of the functionality below 
   will move there ... 
*) 


  
End Theory.

Section ACAS.

Definition A_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv : A_eqv S) := 
              A_distributive_lattice_dual _ (A_bs_union_intersect_with_one S c eqv). 

Definition A_bs_intersect_union (S : Type) (eqv : A_eqv S) := 
              A_distributive_prelattice_dual _ (A_bs_union_intersect S eqv). 

End ACAS.

Section AMCAS.

Definition A_mcas_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv : @A_mcas_eqv S) :=
match eqv with
| A_EQV_Error sl => A_BS_Error _ sl
| A_EQV_eqv eqv' => A_BS_distributive_lattice _ (A_bs_intersect_union_with_zero S c eqv')                                 
end.     

Definition A_mcas_bs_intersect_union (S : Type) (eqv : @A_mcas_eqv S) :=
match eqv with
| A_EQV_Error sl => A_BS_Error _ sl
| A_EQV_eqv eqv' => A_bs_classify _ (A_BS_distributive_prelattice _ (A_bs_intersect_union S eqv'))
end.

End AMCAS.


Section CAS.

Definition bs_intersect_union_with_zero {S : Type} (c : cas_constant) (eqv : @eqv S) := 
               distributive_lattice_dual (bs_union_intersect_with_one c eqv).   

Definition bs_intersect_union {S : Type} (eqv : @eqv S) := 
               distributive_prelattice_dual (bs_union_intersect eqv).   
End CAS.


Section MCAS.

Definition mcas_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv : @mcas_eqv S) :=
match eqv with
| EQV_Error sl => BS_Error sl
| EQV_eqv eqv' => BS_distributive_lattice (bs_intersect_union_with_zero c eqv')
end.                                             


Definition mcas_bs_intersect_union (S : Type) (eqv : @mcas_eqv S) :=
match eqv with
| EQV_Error sl => BS_Error sl
| EQV_eqv eqv' => bs_classify (BS_distributive_prelattice (bs_intersect_union eqv'))
end.

End MCAS.


Section Verify.

Theorem correct_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv: A_eqv S) : 
    bs_intersect_union_with_zero c (A2C_eqv S eqv)
    =
    A2C_distributive_lattice _ (A_bs_intersect_union_with_zero S c eqv). 
Proof. unfold bs_intersect_union_with_zero, A_bs_intersect_union_with_zero.
       rewrite <- correct_distributive_lattice_dual.
       rewrite correct_union_intersect_with_one.       
       reflexivity.
Qed. 


Theorem correct_intersect_union (S : Type) (eqv: A_eqv S) : 
    bs_intersect_union (A2C_eqv S eqv)
    =
    A2C_distributive_prelattice _ (A_bs_intersect_union S eqv). 
Proof. unfold bs_intersect_union, A_bs_intersect_union.
       rewrite <- correct_distributive_prelattice_dual.
       rewrite correct_union_intersect.       
       reflexivity.
Qed. 

Theorem correct_mcas_intersect_union_with_zero (S : Type) (c : cas_constant) (eqvS : @A_mcas_eqv S): 
         mcas_bs_intersect_union_with_zero _ c (A2C_mcas_eqv S eqvS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_intersect_union_with_zero S c eqvS). 
Proof. destruct eqvS.
       + compute; reflexivity. 
       + unfold mcas_bs_intersect_union_with_zero, A_mcas_bs_intersect_union_with_zero, A2C_mcas_eqv. 
         rewrite correct_intersect_union_with_zero.  unfold A2C_mcas_bs. 
         reflexivity. 
Qed.  

Theorem correct_mcas_intersect_union (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_bs_intersect_union _ (A2C_mcas_eqv S eqvS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_intersect_union  S eqvS). 
Proof. destruct eqvS.
       + compute; reflexivity. 
       + unfold mcas_bs_intersect_union, A_mcas_bs_intersect_union, A2C_mcas_eqv. 
         rewrite correct_intersect_union.
         unfold bs_classify, A_bs_classify. 
         rewrite correct_bs_classify_distributive_prelattice. 
         reflexivity. 
Qed.
                                            
End Verify.   
  
