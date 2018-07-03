
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.brel.sum. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties.
Require Import CAS.theory.bop.left_sum.
Require Import CAS.theory.bop.right_sum.
Require Import CAS.theory.facts. 

Section RightSumLeftSum. 


(*  
    (inl a) + (inl b) = inl (a +_S b) 
    (inr a) + (inr b) = inr (a +_T b) 
    (inr a) + (inl b) = inr a 
    (inl a) + (inr b) = inr b 

    (inl a) * (inl b) = inl (a *_S b) 
    (inr a) * (inr b) = inr (a *_T b) 
    (inl a) * (inr b) = inl a
    (inr a) * (inl b) = inl b 

      
*) 


Variable S T : Type.
Variable rS : brel S.
Variable rT : brel T.

Variable wS : S.
Variable wT : T.

Variable addS  mulS : binary_op S.
Variable addT mulT : binary_op T. 
 
Variable congS: brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS. 

Variable congT: brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT. 
Variable tranT : brel_transitive T rT.

Notation "x [+] y"  := (brel_sum x y) (at level 15).
Notation "x <+] y"  := (bop_left_sum x y) (at level 15).
Notation "x [+> y"  := (bop_right_sum x y) (at level 15).

Lemma bop_right_sum_left_sum_left_distributive : 
  bop_idempotent S rS addS →
  bop_left_distributive S rS addS mulS → 
  bop_left_distributive T rT addT mulT →
  bops_left_left_absorptive S rS addS mulS →
  bops_right_left_absorptive S rS addS mulS →              
         bop_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros idemS ldS ldT llaS rlaS [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply ldS.
       apply rlaS.
       apply llaS.
       apply symS. apply idemS.       
       apply refS.
       apply refT.       
       apply refT.
       apply ldT.
Qed.

Lemma bop_right_sum_left_sum_not_left_distributive_v1 ( t : T) : 
  bop_not_idempotent S rS addS →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [s Ps]. exists ((inl s), (inr t, inr t)). compute.
       rewrite (sym_as_rewrite symS). exact Ps. 
Defined. 


Lemma bop_right_sum_left_sum_not_left_distributive_v2 : 
  bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Qed.        

Lemma bop_right_sum_left_sum_not_left_distributive_v3 : 
  bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Qed.        

Lemma bop_right_sum_left_sum_not_left_distributive_v4 (t : T) : 
  bops_not_left_left_absorptive S rS addS mulS →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [ [s1 s2] Ps]. exists ((inl s1), (inr t, inl s2)). compute. assumption. Qed.        


Lemma bop_right_sum_left_sum_not_left_distributive_v5 (t : T) : 
  bops_not_right_left_absorptive S rS addS mulS →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [ [s1 s2] Ps]. exists ((inl s1), (inl s2, inr t)). compute. assumption. Qed.        


Definition bop_right_sum_left_sum_left_distributive_decide :
  bop_idempotent_decidable S rS addS →
  bop_left_distributive_decidable S rS addS mulS → 
  bop_left_distributive_decidable T rT addT mulT →
  bops_left_left_absorptive_decidable S rS addS mulS →
  bops_right_left_absorptive_decidable S rS addS mulS →              
         bop_left_distributive_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d ldS_d ldT_d lla_d rla_d,
match idm_d with                                                                                  
| inl idm  => match ldS_d with
              | inl ldS  => match ldT_d with
                            | inl ldT  => match lla_d with
                                          | inl lla  => match rla_d with
                                                        | inl rla   => inl _ (bop_right_sum_left_sum_left_distributive idm ldS ldT lla rla)
                                                        | inr nrla  => inr _ (bop_right_sum_left_sum_not_left_distributive_v5 wT nrla)
                                                        end 
                                          | inr nlla => inr _ (bop_right_sum_left_sum_not_left_distributive_v4 wT nlla)
                                          end 
                            | inr nldT => inr _ (bop_right_sum_left_sum_not_left_distributive_v3 nldT)
                            end 
              | inr nldS => inr _ (bop_right_sum_left_sum_not_left_distributive_v2 nldS)
              end 
| inr nidm => inr _ (bop_right_sum_left_sum_not_left_distributive_v1 wT nidm)
end. 

Lemma bop_right_sum_left_sum_right_distributive : 
  bop_idempotent S rS addS →
  bop_right_distributive S rS addS mulS → 
  bop_right_distributive T rT addT mulT →
  bops_left_right_absorptive S rS addS mulS →
  bops_right_right_absorptive S rS addS mulS →              
         bop_right_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros idemS rdS rdT lraS rraS [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply rdS.
       apply rraS.
       apply lraS.
       apply symS. apply idemS.       
       apply refS.
       apply refT.       
       apply refT.
       apply rdT.        
Qed. 


Lemma bop_right_sum_left_sum_not_right_distributive_v1 ( t : T ) : 
  bop_not_idempotent S rS addS →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [s Ps]. exists ((inl s), (inr t, inr t)). compute.
       rewrite (sym_as_rewrite symS). assumption.
Defined. 


Lemma bop_right_sum_left_sum_not_right_distributive_v2 : 
  bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Defined. 

Lemma bop_right_sum_left_sum_not_right_distributive_v3 : 
  bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Defined. 

Lemma bop_right_sum_left_sum_not_right_distributive_v4 (t : T) : 
  bops_not_left_right_absorptive S rS addS mulS →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [ [s1 s2] Pt]. exists ((inl s1), (inr t, inl s2)). compute. assumption. Defined. 


Lemma bop_right_sum_left_sum_not_right_distributive_v5 (t : T) : 
  bops_not_right_right_absorptive S rS addS mulS →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [ [s1 s2] Pt]. exists ((inl s1), (inl s2, inr t)). compute. assumption. Defined.    



Definition bop_right_sum_left_sum_right_distributive_decide :
  bop_idempotent_decidable S rS addS →
  bop_right_distributive_decidable S rS addS mulS → 
  bop_right_distributive_decidable T rT addT mulT →
  bops_left_right_absorptive_decidable S rS addS mulS →
  bops_right_right_absorptive_decidable S rS addS mulS →              
         bop_right_distributive_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d ldS_d ldT_d lla_d rla_d,
match idm_d with                                                                                  
| inl idm  => match ldS_d with
              | inl ldS  => match ldT_d with
                            | inl ldT  => match lla_d with
                                          | inl lla  => match rla_d with
                                                        | inl rla   => inl _ (bop_right_sum_left_sum_right_distributive idm ldS ldT lla rla)
                                                        | inr nrla  => inr _ (bop_right_sum_left_sum_not_right_distributive_v5 wT nrla)
                                                        end 
                                          | inr nlla => inr _ (bop_right_sum_left_sum_not_right_distributive_v4 wT nlla)
                                          end 
                            | inr nldT => inr _ (bop_right_sum_left_sum_not_right_distributive_v3 nldT)
                            end 
              | inr nldS => inr _ (bop_right_sum_left_sum_not_right_distributive_v2 nldS)
              end 
| inr nidm => inr _ (bop_right_sum_left_sum_not_right_distributive_v1 wT nidm)
end. 


Lemma bop_right_sum_left_sum_left_left_absorptive :
  bop_idempotent S rS addS →   
  bops_left_left_absorptive S rS addS mulS →   
  bops_left_left_absorptive T rT addT mulT →    
         bops_left_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros idemS llaS llaT. unfold bops_left_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply llaS. apply symS. apply idemS. apply refT. apply llaT.
Qed. 


Lemma bop_right_sum_left_sum_not_left_left_absorptive_v1 (t : T) :
  bop_not_idempotent S rS addS →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [s Ps]. exists (inl s, inr t). compute. rewrite (sym_as_rewrite symS). assumption. Defined. 

Lemma bop_right_sum_left_sum_not_left_left_absorptive_v2 :
  bops_not_left_left_absorptive S rS addS mulS →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_right_sum_left_sum_not_left_left_absorptive_v3 :
  bops_not_left_left_absorptive T rT addT mulT →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 


Definition bop_right_sum_left_sum_left_left_absorptive_decide :
  bop_idempotent_decidable S rS addS →
  bops_left_left_absorptive_decidable S rS addS mulS →   
  bops_left_left_absorptive_decidable T rT addT mulT →    
         bops_left_left_absorptive_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (bop_right_sum_left_sum_left_left_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (bop_right_sum_left_sum_not_left_left_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (bop_right_sum_left_sum_not_left_left_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (bop_right_sum_left_sum_not_left_left_absorptive_v1 wT nidm)
end. 




Lemma bop_right_sum_left_sum_left_right_absorptive :
  bop_idempotent S rS addS →   
  bops_left_right_absorptive S rS addS mulS →   
  bops_left_right_absorptive T rT addT mulT →      
         bops_left_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros idemS lraS lraT. unfold bops_left_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply lraS. apply symS. apply idemS. apply refT. apply lraT.
Qed.        

Lemma bop_right_sum_left_sum_not_left_right_absorptive_v1 (t : T) :
  bop_not_idempotent S rS addS →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [s Ps]. exists (inl s, inr t). compute. rewrite (sym_as_rewrite symS). assumption. Defined. 

Lemma bop_right_sum_left_sum_not_left_right_absorptive_v2 :
  bops_not_left_right_absorptive S rS addS mulS →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma bop_right_sum_left_sum_not_left_right_absorptive_v3 :
  bops_not_left_right_absorptive T rT addT mulT →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 

Definition bop_right_sum_left_sum_left_right_absorptive_decide :
  bop_idempotent_decidable S rS addS →
  bops_left_right_absorptive_decidable S rS addS mulS →   
  bops_left_right_absorptive_decidable T rT addT mulT →    
         bops_left_right_absorptive_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (bop_right_sum_left_sum_left_right_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (bop_right_sum_left_sum_not_left_right_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (bop_right_sum_left_sum_not_left_right_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (bop_right_sum_left_sum_not_left_right_absorptive_v1 wT nidm)
end. 





Lemma bop_right_sum_left_sum_right_left_absorptive :
  bop_idempotent S rS addS →   
  bops_right_left_absorptive S rS addS mulS →   
  bops_right_left_absorptive T rT addT mulT →      
         bops_right_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros idemS rlaS rlaT. unfold bops_right_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply rlaS. apply symS. apply idemS. apply refT. apply rlaT.
Qed.

Lemma bop_right_sum_left_sum_not_right_left_absorptive_v1 (t : T) :
  bop_not_idempotent S rS addS →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [s Ps]. exists (inl s, inr t). compute. rewrite (sym_as_rewrite symS). assumption. Defined. 

Lemma bop_right_sum_left_sum_not_right_left_absorptive_v2 :
  bops_not_right_left_absorptive S rS addS mulS →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma bop_right_sum_left_sum_not_right_left_absorptive_v3 :
  bops_not_right_left_absorptive T rT addT mulT →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 


Definition bop_right_sum_left_sum_right_left_absorptive_decide :
  bop_idempotent_decidable S rS addS →
  bops_right_left_absorptive_decidable S rS addS mulS →   
  bops_right_left_absorptive_decidable T rT addT mulT →    
         bops_right_left_absorptive_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (bop_right_sum_left_sum_right_left_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (bop_right_sum_left_sum_not_right_left_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (bop_right_sum_left_sum_not_right_left_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (bop_right_sum_left_sum_not_right_left_absorptive_v1 wT nidm)
end. 


Lemma bop_right_sum_left_sum_right_right_absorptive :
  bop_idempotent S rS addS →   
  bops_right_right_absorptive S rS addS mulS →   
  bops_right_right_absorptive T rT addT mulT →      
         bops_right_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros idemS rraS rraT. unfold bops_right_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply rraS. apply symS. apply idemS. apply refT. apply rraT.
Qed.        

Lemma bop_right_sum_left_sum_not_right_right_absorptive_v1 (t : T) :
  bop_not_idempotent S rS addS →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [s Ps]. exists (inl s, inr t). compute. rewrite (sym_as_rewrite symS). assumption. Defined. 


Lemma bop_right_sum_left_sum_not_right_right_absorptive_v2 :
  bops_not_right_right_absorptive S rS addS mulS →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma bop_right_sum_left_sum_not_right_right_absorptive_v3 :
  bops_not_right_right_absorptive T rT addT mulT →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 


Definition bop_right_sum_left_sum_right_right_absorptive_decide :
  bop_idempotent_decidable S rS addS →
  bops_right_right_absorptive_decidable S rS addS mulS →   
  bops_right_right_absorptive_decidable T rT addT mulT →    
         bops_right_right_absorptive_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (bop_right_sum_left_sum_right_right_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (bop_right_sum_left_sum_not_right_right_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (bop_right_sum_left_sum_not_right_right_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (bop_right_sum_left_sum_not_right_right_absorptive_v1 wT nidm)
end. 

(*


*) 

Lemma bop_right_sum_left_sum_id_equals_ann :
  bops_id_equals_ann S rS addS mulS →
         bops_id_equals_ann (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [i [I A]]. exists (inl _ i). split.
       apply bop_right_sum_is_id; auto. 
       apply bop_left_sum_is_ann; auto. 
Defined.

Lemma bop_right_sum_left_sum_not_id_equals_ann (s' : S) :
  bops_not_id_equals_ann S rS addS mulS →
  bops_not_id_equals_ann (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros H [s | t]. destruct (H s) as [ [s'' [L | R]] | [s'' [L | R]] ] .
       left. exists (inl _ s''). compute. rewrite L. left. reflexivity. 
       left. exists (inl _ s''). compute. rewrite R. right. reflexivity. 
       right. exists (inl _ s''). compute. rewrite L. left. reflexivity. 
       right. exists (inl _ s''). compute. rewrite R. right. reflexivity. 
       destruct (H s') as [ [s'' [L | R]] | [s'' [L | R]] ] .
       left. exists (inl _ s''). compute. left. reflexivity.        
       left. exists (inl _ s''). compute. right. reflexivity.               
       right. exists (inl _ s''). compute. left. reflexivity.        
       right. exists (inl _ s''). compute. right. reflexivity.
Defined.        

Definition bop_right_sum_left_sum_id_equals_ann_decide :
  bops_id_equals_ann_decidable S rS addS mulS →
         bops_id_equals_ann_decidable (S + T) (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ ia_d,
match ia_d with                                                                                  
| inl ia  => inl _ (bop_right_sum_left_sum_id_equals_ann ia)  
| inr nia => inr _ (bop_right_sum_left_sum_not_id_equals_ann wS nia)
end. 


(*
Lemma bop_right_sum_left_sum_id_equals_ann_dual :
  bops_id_equals_ann T rT mulT addT →
             bops_id_equals_ann (S + T) (rS [+] rT) (mulS <+] mulT) (addS [+> addT).
Proof. intros [a [I A]]. exists (inr _ a). split.
       apply bop_left_sum_is_id; auto. 
       apply bop_right_sum_is_ann; auto. 
Defined.
*) 

End RightSumLeftSum.