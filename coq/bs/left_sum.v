Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.sg.left_sum.
Require Import CAS.coq.sg.right_sum. 

Section Theory.

Section LeftRight. 
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
End LeftRight.

Section RightLeft.


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


End RightLeft.                                                                            

End Theory.

Section ACAS.
                                                                             

Definition bs_proofs_left_sum : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT ->
     sg_proofs T rT plusT ->      
     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 
        bs_proofs (S + T) 
           (brel_sum rS rT) 
           (bop_left_sum plusS plusT)
           (bop_right_sum timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT s t eqvS eqvT sgT pS pT, 
{|
  A_bs_left_distributive_d :=
    bop_left_sum_right_sum_left_distributive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_left_distributive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d T rT plusT timesT pT)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)        

; A_bs_right_distributive_d := 
    bop_left_sum_right_sum_right_distributive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_right_distributive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d T rT plusT timesT pT)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)
        (A_bs_right_right_absorptive_d T rT plusT timesT pT)        

; A_bs_left_left_absorptive_d := 
    bop_left_sum_right_sum_left_left_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)        

; A_bs_left_right_absorptive_d := 
    bop_left_sum_right_sum_left_right_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)        

; A_bs_right_left_absorptive_d :=
    bop_left_sum_right_sum_right_left_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)        
    
; A_bs_right_right_absorptive_d := 
    bop_left_sum_right_sum_right_right_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_idempotent_d T rT plusT sgT)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d T rT plusT timesT pT)        

; A_bs_plus_id_is_times_ann_d :=
    bop_left_sum_right_sum_id_equals_ann_decide S T rS rT t plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)        

; A_bs_times_id_is_plus_ann_d :=  
    bop_right_sum_left_sum_id_equals_ann_decide S T rS rT s timesS plusS timesT plusT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)        
|}.



Definition lattice_proofs_left_sum : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT ->
    sg_CI_proofs S rS mulS ->             
    sg_CI_proofs T rT addT ->     
    lattice_proofs S rS addS mulS ->
    lattice_proofs T rT addT mulT ->     
        lattice_proofs (S + T) (brel_sum rS rT) (bop_left_sum addS addT) (bop_right_sum mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT p_mulS p_addT srS srT, 
{|
  A_lattice_absorptive        := 
    bop_left_sum_right_sum_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric T rT eqvT)
        (A_sg_CI_idempotent T rT addT p_addT)                                          
        (A_lattice_absorptive S rS addS mulS srS)
        (A_lattice_absorptive T rT addT mulT srT)
                                     
; A_lattice_absorptive_dual   :=
    bop_right_sum_left_sum_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_sg_CI_idempotent S rS mulS p_mulS)                                          
        (A_lattice_absorptive_dual S rS addS mulS srS)
        (A_lattice_absorptive_dual T rT addT mulT srT)

; A_lattice_distributive_d        :=
  bop_left_sum_right_sum_left_distributive_decide S T rS rT s addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_eqv_symmetric T rT eqvT)
        (inl _ (A_sg_CI_idempotent T rT addT p_addT))                                        
        (A_lattice_distributive_d S rS addS mulS srS)
        (A_lattice_distributive_d T rT addT mulT  srT)
        (inl _ (A_lattice_absorptive T rT addT mulT srT))
        (inl _ (bops_left_left_absorptive_implies_right_left T rT addT mulT
                  (A_eqv_transitive T rT eqvT)
                  (A_sg_CI_commutative T rT addT p_addT)
                  (A_lattice_absorptive T rT addT mulT srT)
               )
        )

; A_lattice_distributive_dual_d        :=
  bop_right_sum_left_sum_left_distributive_decide S T rS rT t mulS addS mulT addT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (inl _ (A_sg_CI_idempotent S rS mulS p_mulS))                                        
        (A_lattice_distributive_dual_d S rS addS mulS srS)
        (A_lattice_distributive_dual_d T rT addT mulT  srT)
        (inl _ (A_lattice_absorptive_dual S rS addS mulS srS))
        (inl _ (bops_left_left_absorptive_implies_right_left S rS mulS addS 
                  (A_eqv_transitive S rS eqvS)
                  (A_sg_CI_commutative S rS mulS p_mulS)
                  (A_lattice_absorptive_dual S rS addS mulS srS)
               )
        )
        
|}.

Definition distributive_lattice_proofs_left_sum : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T), 
    eqv_proofs S rS ->
    eqv_proofs T rT ->
    sg_CI_proofs S rS mulS ->             
    sg_CI_proofs T rT addT ->     
    distributive_lattice_proofs S rS addS mulS ->
    distributive_lattice_proofs T rT addT mulT ->     
        distributive_lattice_proofs (S + T) (brel_sum rS rT) (bop_left_sum addS addT) (bop_right_sum mulS mulT)
:= λ S T rS rT addS mulS addT mulT eqvS eqvT p_mulS p_addT srS srT, 
{|
  A_distributive_lattice_absorptive        := 
    bop_left_sum_right_sum_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric T rT eqvT)
        (A_sg_CI_idempotent T rT addT p_addT)                                          
        (A_distributive_lattice_absorptive S rS addS mulS srS)
        (A_distributive_lattice_absorptive T rT addT mulT srT)
                                     
; A_distributive_lattice_absorptive_dual   :=
    bop_right_sum_left_sum_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_sg_CI_idempotent S rS mulS p_mulS)                                          
        (A_distributive_lattice_absorptive_dual S rS addS mulS srS)
        (A_distributive_lattice_absorptive_dual T rT addT mulT srT)
    
; A_distributive_lattice_distributive        :=
  bop_left_sum_right_sum_left_distributive S T rS rT addS mulS addT mulT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_eqv_symmetric T rT eqvT)
        (A_sg_CI_idempotent T rT addT p_addT)
        (A_distributive_lattice_distributive S rS addS mulS srS)
        (A_distributive_lattice_distributive T rT addT mulT  srT)
        (A_distributive_lattice_absorptive T rT addT mulT srT)
        (bops_left_left_absorptive_implies_right_left T rT addT mulT
            (A_eqv_transitive T rT eqvT)
            (A_sg_CI_commutative T rT addT p_addT)
            (A_distributive_lattice_absorptive T rT addT mulT srT)
        )
|}.


Definition A_bs_left_sum : ∀ (S T : Type),  A_bs S -> A_bs T -> A_bs (S + T) 
:= λ S T bsS bsT, 
let eqvS   := A_bs_eqv S bsS   in
let eqvT   := A_bs_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_bs_plus S bsS  in 
let plusT  := A_bs_plus T bsT  in
let timesS := A_bs_times S bsS in 
let timesT := A_bs_times T bsT in 
{| 
     A_bs_eqv        := A_eqv_sum S T eqvS eqvT 
   ; A_bs_plus       := bop_left_sum plusS plusT 
   ; A_bs_times       := bop_right_sum timesS timesT 
   ; A_bs_plus_proofs := sg_proofs_left_sum S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := sg_proofs_right_sum S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_proofs S bsS) 
                           (A_bs_times_proofs T bsT) 
   ; A_bs_proofs    := bs_proofs_left_sum S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_plus_proofs T bsT)                            
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT) 
   ; A_bs_ast        := Ast_bs_left_sum(A_bs_ast S bsS, A_bs_ast T bsT)
|}. 


Definition A_lattice_left_sum : ∀ (S T : Type),  A_lattice S ->  A_lattice T -> A_lattice (S + T) 
:= λ S T sr1 sr2,
let eqvS   := A_lattice_eqv S sr1   in
let eqvT   := A_lattice_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let t      := A_eqv_witness T eqvT in
let joinS  := A_lattice_join S sr1  in 
let joinT  := A_lattice_join T sr2  in
let meetS  := A_lattice_meet S sr1 in 
let meetT  := A_lattice_meet T sr2 in 
{| 
     A_lattice_eqv          := A_eqv_sum S T eqvS eqvT
   ; A_lattice_join         := bop_left_sum joinS joinT
   ; A_lattice_meet         := bop_right_sum meetS meetT 
   ; A_lattice_join_proofs  := sg_CI_proofs_left_sum S T rS rT joinS joinT s t peqvS peqvT 
                                (A_lattice_join_proofs S sr1)
                                (A_lattice_join_proofs T sr2)                                 
   ; A_lattice_meet_proofs := sg_CI_proofs_right_sum S T rS rT meetS meetT s t peqvS peqvT 
                                (A_lattice_meet_proofs S sr1)
                                (A_lattice_meet_proofs T sr2)                                 
   ; A_lattice_proofs  := lattice_proofs_left_sum S T rS rT joinS meetS joinT meetT s t peqvS peqvT 
                                   (A_lattice_meet_proofs S sr1)
                                   (A_lattice_join_proofs T sr2)                                                                      
                                   (A_lattice_proofs S sr1)
                                   (A_lattice_proofs T sr2)                                   
   ; A_lattice_ast  := Ast_lattice_left_sum (A_lattice_ast S sr1, A_lattice_ast T sr2)
|}.


Definition A_distributive_lattice_left_sum : ∀ (S T : Type),  A_distributive_lattice S ->  A_distributive_lattice T -> A_distributive_lattice (S + T) 
:= λ S T sr1 sr2,
let eqvS   := A_distributive_lattice_eqv S sr1   in
let eqvT   := A_distributive_lattice_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let t      := A_eqv_witness T eqvT in
let joinS  := A_distributive_lattice_join S sr1  in 
let joinT  := A_distributive_lattice_join T sr2  in
let meetS  := A_distributive_lattice_meet S sr1 in 
let meetT  := A_distributive_lattice_meet T sr2 in 
{| 
     A_distributive_lattice_eqv          := A_eqv_sum S T eqvS eqvT
   ; A_distributive_lattice_join         := bop_left_sum joinS joinT
   ; A_distributive_lattice_meet        := bop_right_sum meetS meetT 
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_left_sum S T rS rT joinS joinT s t peqvS peqvT 
                                (A_distributive_lattice_join_proofs S sr1)
                                (A_distributive_lattice_join_proofs T sr2)                                 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_right_sum S T rS rT meetS meetT s t peqvS peqvT 
                                (A_distributive_lattice_meet_proofs S sr1)
                                (A_distributive_lattice_meet_proofs T sr2)                                 
   ; A_distributive_lattice_proofs  := distributive_lattice_proofs_left_sum S T rS rT joinS meetS joinT meetT peqvS peqvT 
                                   (A_distributive_lattice_meet_proofs S sr1)
                                   (A_distributive_lattice_join_proofs T sr2)                                                                      
                                   (A_distributive_lattice_proofs S sr1)
                                   (A_distributive_lattice_proofs T sr2)                                   
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_left_sum (A_distributive_lattice_ast S sr1, A_distributive_lattice_ast T sr2)
|}.

                                   
End ACAS.

Section CAS.

End CAS.

Section Verify.

  
 
End Verify.   
  