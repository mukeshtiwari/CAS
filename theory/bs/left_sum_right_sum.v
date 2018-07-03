
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

Section LeftSumRightSum. 


(*  
    (inl a) + (inl b) = inl (a +_S b) 
    (inr a) + (inr b) = inr (a +_T b) 
    (inl a) + (inr b) = inl a
    (inr a) + (inl b) = inl b 

    (inl a) * (inl b) = inl (a *_S b) 
    (inr a) * (inr b) = inr (a *_T b) 
    (inr a) * (inl b) = inr a 
    (inl a) * (inr b) = inr b 

compare to 

     (a, b) |> inl c = inl (a *_S c) 
     (a, b) |> inr c = inr (b *_T c) 

or to (with different +) 

     (inl c) |> (a, b)  = (c * _S a, b) 
     (inr c) |> (a, b)  = (a, c * _T b) 

which is a sub-algebra of product 
      
     (c, id) x (a, b)  = (c * _S a, b) 
     (id, c) x (a, b)  = (a, c * _T b) 

Think of scoped product: 

     (inl (c, d)) |> (a, b)  = (c * _S a, d) = (c * _S a, d left b) 
     (inr c) |> (a, b)       = (a, c * _T b) = (c right a, c * _T b) =  (id *_S a, c * _T b) =  

Generalize scoped product: 

     (inl (c, d)) |> (a, b)  = (c * _S a, d) = (c * _S a, d left b) 
     (inr (c, d)) |> (a, b)  = (c * _S a, d *_T b) 
      
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

Lemma bop_left_sum_right_sum_left_distributive : 
  bop_idempotent T rT addT →
  bop_left_distributive S rS addS mulS → 
  bop_left_distributive T rT addT mulT →
  bops_left_left_absorptive T rT addT mulT →
  bops_right_left_absorptive T rT addT mulT →              
         bop_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros idemT ldS ldT llaT rlaT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply ldS. apply refS. apply refS. apply refT. apply symT. apply idemT. apply llaT. apply rlaT. apply ldT. Qed.

Lemma bop_left_sum_right_sum_not_left_distributive_v1 ( s : S) : 
  bop_not_idempotent T rT addT →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [t Pt]. exists ((inr t), (inl s, inl s)). compute.
       rewrite (sym_as_rewrite symT). assumption.
Qed.        


Lemma bop_left_sum_right_sum_not_left_distributive_v2 : 
  bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_left_distributive_v3 : 
  bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_left_distributive_v4 : 
  bops_not_left_left_absorptive T rT addT mulT →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inl wS, inr t2)). compute. assumption. Qed.        


Lemma bop_left_sum_right_sum_not_left_distributive_v5 : 
  bops_not_right_left_absorptive T rT addT mulT →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inr t2, inl wS)). compute. assumption. Qed.        


Definition bop_left_sum_right_sum_left_distributive_decide :
  bop_idempotent_decidable T rT addT →
  bop_left_distributive_decidable S rS addS mulS → 
  bop_left_distributive_decidable T rT addT mulT →
  bops_left_left_absorptive_decidable T rT addT mulT →
  bops_right_left_absorptive_decidable T rT addT mulT →              
         bop_left_distributive_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d ldS_d ldT_d lla_d rla_d,
match idm_d with                                                                                  
| inl idm  => match ldS_d with
              | inl ldS  => match ldT_d with
                            | inl ldT  => match lla_d with
                                          | inl lla  => match rla_d with
                                                        | inl rla   => inl _ (bop_left_sum_right_sum_left_distributive idm ldS ldT lla rla)
                                                        | inr nrla  => inr _ (bop_left_sum_right_sum_not_left_distributive_v5 nrla)
                                                        end 
                                          | inr nlla => inr _ (bop_left_sum_right_sum_not_left_distributive_v4 nlla)
                                          end 
                            | inr nldT => inr _ (bop_left_sum_right_sum_not_left_distributive_v3 nldT)
                            end 
              | inr nldS => inr _ (bop_left_sum_right_sum_not_left_distributive_v2 nldS)
              end 
| inr nidm => inr _ (bop_left_sum_right_sum_not_left_distributive_v1 wS nidm)
end. 


Lemma bop_left_sum_right_sum_right_distributive : 
  bop_idempotent T rT addT →
  bop_right_distributive S rS addS mulS → 
  bop_right_distributive T rT addT mulT →
  bops_left_right_absorptive T rT addT mulT →
  bops_right_right_absorptive T rT addT mulT →              
         bop_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros idemT rdS rdT lraT rraT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply rdS. apply refS. apply refS. apply refT.
       apply symT. apply idemT. apply lraT. apply rraT. apply rdT.        
Qed. 


Lemma bop_left_sum_right_sum_not_right_distributive_v1 : 
  bop_not_idempotent T rT addT →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [t Pt]. exists ((inr t), (inl wS, inl wS)). compute.
       rewrite (sym_as_rewrite symT). assumption.
Qed.        


Lemma bop_left_sum_right_sum_not_right_distributive_v2 : 
  bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_right_distributive_v3 : 
  bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_right_distributive_v4 : 
  bops_not_left_right_absorptive T rT addT mulT →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inl wS, inr t2)). compute. assumption. Qed.        


Lemma bop_left_sum_right_sum_not_right_distributive_v5 : 
  bops_not_right_right_absorptive T rT addT mulT →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inr t2, inl wS)). compute. assumption. Qed.        


Definition bop_left_sum_right_sum_right_distributive_decide :
  bop_idempotent_decidable T rT addT →
  bop_right_distributive_decidable S rS addS mulS → 
  bop_right_distributive_decidable T rT addT mulT →
  bops_left_right_absorptive_decidable T rT addT mulT →
  bops_right_right_absorptive_decidable T rT addT mulT →              
         bop_right_distributive_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d ldS_d ldT_d lla_d rla_d,
match idm_d with                                                                                  
| inl idm  => match ldS_d with
              | inl ldS  => match ldT_d with
                            | inl ldT  => match lla_d with
                                          | inl lla  => match rla_d with
                                                        | inl rla   => inl _ (bop_left_sum_right_sum_right_distributive idm ldS ldT lla rla)
                                                        | inr nrla  => inr _ (bop_left_sum_right_sum_not_right_distributive_v5 nrla)
                                                        end 
                                          | inr nlla => inr _ (bop_left_sum_right_sum_not_right_distributive_v4 nlla)
                                          end 
                            | inr nldT => inr _ (bop_left_sum_right_sum_not_right_distributive_v3 nldT)
                            end 
              | inr nldS => inr _ (bop_left_sum_right_sum_not_right_distributive_v2 nldS)
              end 
| inr nidm => inr _ (bop_left_sum_right_sum_not_right_distributive_v1 nidm)
end. 

Lemma bop_left_sum_right_sum_left_left_absorptive :
  bop_idempotent T rT addT →   
  bops_left_left_absorptive S rS addS mulS →   
  bops_left_left_absorptive T rT addT mulT →    
         bops_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT llaS llaT. unfold bops_left_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply llaS. apply refS. apply symT. apply idemT. apply llaT.
Qed. 

Lemma bop_left_sum_right_sum_not_left_left_absorptive_v1 :
  bop_not_idempotent T rT addT →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl wS). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_left_absorptive_v2 :
  bops_not_left_left_absorptive S rS addS mulS →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_left_absorptive_v3 :
  bops_not_left_left_absorptive T rT addT mulT →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 


Definition bop_left_sum_right_sum_left_left_absorptive_decide :
  bop_idempotent_decidable T rT addT →
  bops_left_left_absorptive_decidable S rS addS mulS →   
  bops_left_left_absorptive_decidable T rT addT mulT →    
         bops_left_left_absorptive_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (bop_left_sum_right_sum_left_left_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (bop_left_sum_right_sum_not_left_left_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (bop_left_sum_right_sum_not_left_left_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (bop_left_sum_right_sum_not_left_left_absorptive_v1 nidm)
end. 


Lemma bop_left_sum_right_sum_left_right_absorptive :
  bop_idempotent T rT addT →   
  bops_left_right_absorptive S rS addS mulS →   
  bops_left_right_absorptive T rT addT mulT →      
         bops_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT lraS lraT. unfold bops_left_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply lraS. apply refS. apply symT. apply idemT. apply lraT.
Qed.        

Lemma bop_left_sum_right_sum_not_left_right_absorptive_v1 :
  bop_not_idempotent T rT addT →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl wS). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_right_absorptive_v2 :
  bops_not_left_right_absorptive S rS addS mulS →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_right_absorptive_v3 :
  bops_not_left_right_absorptive T rT addT mulT →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 


Definition bop_left_sum_right_sum_left_right_absorptive_decide :
  bop_idempotent_decidable T rT addT →
  bops_left_right_absorptive_decidable S rS addS mulS →   
  bops_left_right_absorptive_decidable T rT addT mulT →    
         bops_left_right_absorptive_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d lraS_d lraT_d,
match idm_d with                                                                                  
| inl idm  => match lraS_d with
              | inl lraS  => match lraT_d with
                            | inl lraT  => inl _ (bop_left_sum_right_sum_left_right_absorptive idm lraS lraT)
                            | inr nlraT => inr _ (bop_left_sum_right_sum_not_left_right_absorptive_v3 nlraT)
                            end 
              | inr nlraS => inr _ (bop_left_sum_right_sum_not_left_right_absorptive_v2 nlraS)
              end 
| inr nidm => inr _ (bop_left_sum_right_sum_not_left_right_absorptive_v1 nidm)
end. 


Lemma bop_left_sum_right_sum_right_left_absorptive :
  bop_idempotent T rT addT →   
  bops_right_left_absorptive S rS addS mulS →   
  bops_right_left_absorptive T rT addT mulT →      
         bops_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT rlaS rlaT. unfold bops_right_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply rlaS. apply refS. apply symT. apply idemT. apply rlaT.
Qed.

Lemma bop_left_sum_right_sum_not_right_left_absorptive_v1 :
  bop_not_idempotent T rT addT →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl wS). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 

Lemma bop_left_sum_right_sum_not_right_left_absorptive_v2 :
  bops_not_right_left_absorptive S rS addS mulS →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_right_left_absorptive_v3 :
  bops_not_right_left_absorptive T rT addT mulT →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 


Definition bop_left_sum_right_sum_right_left_absorptive_decide :
  bop_idempotent_decidable T rT addT →
  bops_right_left_absorptive_decidable S rS addS mulS →   
  bops_right_left_absorptive_decidable T rT addT mulT →    
         bops_right_left_absorptive_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d rlaS_d rlaT_d,
match idm_d with                                                                                  
| inl idm  => match rlaS_d with
              | inl rlaS  => match rlaT_d with
                            | inl rlaT  => inl _ (bop_left_sum_right_sum_right_left_absorptive idm rlaS rlaT)
                            | inr nrlaT => inr _ (bop_left_sum_right_sum_not_right_left_absorptive_v3 nrlaT)
                            end 
              | inr nrlaS => inr _ (bop_left_sum_right_sum_not_right_left_absorptive_v2 nrlaS)
              end 
| inr nidm => inr _ (bop_left_sum_right_sum_not_right_left_absorptive_v1 nidm)
end. 

Lemma bop_left_sum_right_sum_right_right_absorptive :
  bop_idempotent T rT addT →   
  bops_right_right_absorptive S rS addS mulS →   
  bops_right_right_absorptive T rT addT mulT →      
         bops_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT rraS rraT. unfold bops_right_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply rraS. apply refS. apply symT. apply idemT. apply rraT.
Qed.        

Lemma bop_left_sum_right_sum_not_right_right_absorptive_v1 :
  bop_not_idempotent T rT addT →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl wS). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 


Lemma bop_left_sum_right_sum_not_right_right_absorptive_v2 :
  bops_not_right_right_absorptive S rS addS mulS →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_right_right_absorptive_v3 :
  bops_not_right_right_absorptive T rT addT mulT →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed.


Definition bop_left_sum_right_sum_right_right_absorptive_decide :
  bop_idempotent_decidable T rT addT →
  bops_right_right_absorptive_decidable S rS addS mulS →   
  bops_right_right_absorptive_decidable T rT addT mulT →    
         bops_right_right_absorptive_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d rraS_d rraT_d,
match idm_d with                                                                                  
| inl idm  => match rraS_d with
              | inl rraS  => match rraT_d with
                            | inl rraT  => inl _ (bop_left_sum_right_sum_right_right_absorptive idm rraS rraT)
                            | inr nrraT => inr _ (bop_left_sum_right_sum_not_right_right_absorptive_v3 nrraT)
                            end 
              | inr nrraS => inr _ (bop_left_sum_right_sum_not_right_right_absorptive_v2 nrraS)
              end 
| inr nidm => inr _ (bop_left_sum_right_sum_not_right_right_absorptive_v1 nidm)
end. 


Lemma bop_left_sum_right_sum_id_equals_ann :
  bops_id_equals_ann T rT addT mulT →
         bops_id_equals_ann (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [i [I A]]. exists (inr _ i). split.
       apply bop_left_sum_is_id; auto. 
       apply bop_right_sum_is_ann; auto. 
Defined. 

Lemma bop_left_sum_right_sum_not_id_equals_ann :
  bops_not_id_equals_ann T rT addT mulT →
  bops_not_id_equals_ann (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros H [s | t]. destruct (H wT) as [ [t'' [L | R]] | [t'' [L | R]] ] .
       left. exists (inr _ t''). compute. left. reflexivity. 
       left. exists (inr _ t''). compute. left. reflexivity. 
       right. exists (inr _ t''). compute. left. reflexivity.
       right. exists (inr _ t''). compute. left. reflexivity.
       destruct (H t) as [ [t'' [L | R]] | [t'' [L | R]] ] .
       left. exists (inr _ t''). compute. rewrite L. left. reflexivity.        
       left. exists (inr _ t''). compute. rewrite R. right. reflexivity.               
       right. exists (inr _ t''). compute. rewrite L. left. reflexivity.        
       right. exists (inr _ t''). compute. rewrite R. right. reflexivity.
Defined.

Definition bop_left_sum_right_sum_id_equals_ann_decide :
  bops_id_equals_ann_decidable T rT addT mulT →
         bops_id_equals_ann_decidable (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ ia_d,
match ia_d with                                                                                  
| inl ia  => inl _ (bop_left_sum_right_sum_id_equals_ann ia)  
| inr nia => inr _ (bop_left_sum_right_sum_not_id_equals_ann nia)
end. 

                                                                           
End LeftSumRightSum. 