Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties.
Require Import CAS.theory.bop.left_sum.
Require Import CAS.theory.bop.right_sum.

(*
This is an experiment.  The results seem to show that 
this combination of opperations may not be very useful. 
*) 



Variable S T : Type.
Variable rS : brel S.
Variable rT : brel T.
Variable addS  mulS : binary_op S.
Variable addT mulT : binary_op T. 

Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS. 

Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT. 


Lemma bop_left_sum_left_sum_left_distributive : 
      bop_idempotent S rS addS → 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
         bop_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT).
Proof. intros idemS ldS ldT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply ldS. 
       admit.      (* s1 * s2 =  (s1 * s2) + s1        s1 * s2 =  s1 * (s2 + id) = (s1 * s2) + s1 * id =?=  (s1 * s2) + s1 *) 
       admit.      (* s1 * s3 =  s1 + (s1 * s3)   *)
       rewrite symS. reflexivity. apply idemS. 
       apply refS.
       apply refS.
       apply refS.
       apply ldT.        
Admitted. 



Lemma bop_left_sum_left_sum_right_distributive :  
      bop_idempotent S rS addS → 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
         bop_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros idemS rdS rdT [s1 | t1] [s2 | t2] [s3 | t3]; compute. 
       apply rdS.
       admit.      (* s2 * s1 = (s2 * s1) + s1 *) 
       admit.      (* s3 * s1 = s1 + (s3 * s1) *) 
       apply symS. apply idemS. 
       apply refS.
       apply refS.
       apply refS.
       apply rdT. 
Admitted. 


Lemma bop_left_sum_left_sum_not_id_equals_ann : 
         bops_not_id_equals_ann (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT).
Proof. intros [s1 | t1] [s2 | t2] I A.
       compute. admit. 
       compute. reflexivity. 
       compute. reflexivity.
       compute. admit. 
Admitted.


Lemma bop_left_sum_left_sum_not_id_equals_ann_dual : 
         bops_not_id_equals_ann (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ mulS mulT)
             (bop_left_sum _ _ addS addT). 
Proof. intros [s1 | t1] [s2 | t2] I A.
       compute. admit. 
       compute. reflexivity. 
       compute. reflexivity.
       compute. admit. 
Admitted. 


Lemma bop_left_sum_left_sum_not_left_left_absorptive (s : S) (t : T) : 
         bops_not_left_left_absorptive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. exists (inr t, inl s). compute. reflexivity. Defined. 

Lemma bop_left_sum_left_sum_not_left_right_absorptive (s : S) (t : T) : 
         bops_not_left_right_absorptive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. exists (inr t, inl s). compute. reflexivity. Defined. 

Lemma bop_left_sum_left_sum_not_right_right_absorptive (s : S) (t : T) : 
         bops_not_right_right_absorptive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. exists (inr t, inl s). compute. reflexivity. Defined. 

Lemma bop_left_sum_left_sum_not_right_left_absorptive (s : S) (t : T) : 
         bops_not_right_left_absorptive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. exists (inr t, inl s). compute. reflexivity. Defined. 

