Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.bop.product. 

Section ProductProduct. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.
Variable wS : S.
Variable wT : T.
Variable addS  mulS : binary_op S. 
Variable addT mulT : binary_op T. 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).



(* note : should be able to abstract away and universally quantfied predicate .... *) 

Lemma bop_product_left_distributive : 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
         bop_left_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2] [s3 t3]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma bop_product_right_distributive : 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
         bop_right_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros lrS lrT [s1 t1] [s2 t2] [s3 t3]. simpl. rewrite lrS, lrT.  simpl. reflexivity. Defined. 

Lemma bop_product_not_left_distributive_left : 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl.        
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_distributive_right : 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 

Lemma bop_product_not_right_distributive_left : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_distributive_right : 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 

(* *********************************** *) 


Lemma bop_product_id_equals_ann : 
      bops_id_equals_ann S rS addS mulS → 
      bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT). split.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
Defined. 

Lemma bop_product_not_id_equals_ann_left : 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H s) as [ [s' [L | R]] | [s' [L | R]]].
          left. exists (s', t). left. compute. rewrite L. reflexivity. 
          left. exists (s', t). right. compute. rewrite R. reflexivity.           
          right. exists (s', t). left. compute. rewrite L. reflexivity. 
          right. exists (s', t). right. compute. rewrite R. reflexivity.           
Defined. 

Lemma bop_product_not_id_equals_ann_right : 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H t) as [ [t' [L | R]] | [t' [L | R]]].
          left. exists (s, t'). left. compute. rewrite L. case_eq( rS (s +S s) s); intro K; reflexivity. 
          left. exists (s, t'). right. compute. rewrite R. case_eq( rS (s +S s) s); intro K; reflexivity.           
          right. exists (s, t'). left. compute. rewrite L. case_eq( rS (s *S s) s); intro K; reflexivity. 
          right. exists (s, t'). right. compute. rewrite R. case_eq( rS (s *S s) s); intro K; reflexivity.           
Defined. 


(* left left *) 
Lemma bop_product_left_left_absorptive : 
      bops_left_left_absorptive S rS addS mulS → 
      bops_left_left_absorptive T rT addT mulT → 
         bops_left_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma bop_product_not_left_left_absorptive_left : 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_left_left_absorptive_right : 
      bops_not_left_left_absorptive T rT addT mulT → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


(* left right *) 
Lemma bop_product_left_right_absorptive : 
      bops_left_right_absorptive S rS addS mulS → 
      bops_left_right_absorptive T rT addT mulT → 
         bops_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 

Lemma bop_product_not_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_left_right_absorptive_right : 
      bops_not_left_right_absorptive T rT addT mulT → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 

(* right left *) 
Lemma bop_product_right_left_absorptive : 
      bops_right_left_absorptive S rS addS mulS → 
      bops_right_left_absorptive T rT addT mulT → 
         bops_right_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 

Lemma bop_product_not_right_left_absorptive_left : 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_right_left_absorptive_right : 
      bops_not_right_left_absorptive T rT addT mulT → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ].  exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


(* right right *) 
Lemma bop_product_right_right_absorptive : 
      bops_right_right_absorptive S rS addS mulS → 
      bops_right_right_absorptive T rT addT mulT → 
         bops_right_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma bop_product_not_right_right_absorptive_left : 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_right_right_absorptive_right : 
      bops_not_right_right_absorptive T rT addT mulT → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined.


Definition bop_product_left_distributive_decide : 
     bop_left_distributive_decidable S rS addS mulS -> bop_left_distributive_decidable T rT addT mulT -> 
        bop_left_distributive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (bop_product_left_distributive ldS ldT)
     | inr nldT => inr _ (bop_product_not_left_distributive_right nldT)
     end 
   | inr nldS   => inr _ (bop_product_not_left_distributive_left nldS)
   end. 

Definition bop_product_right_distributive_decide : 
     bop_right_distributive_decidable S rS addS mulS -> bop_right_distributive_decidable T rT addT mulT -> 
       bop_right_distributive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (bop_product_right_distributive ldS ldT)
     | inr nldT => inr _ (bop_product_not_right_distributive_right nldT)
     end 
   | inr nldS   => inr _ (bop_product_not_right_distributive_left nldS)
   end. 
       
Definition bop_product_id_equals_ann_decide : 
      bops_id_equals_ann_decidable S rS addS mulS → bops_id_equals_ann_decidable T rT addT mulT →  
        bops_id_equals_ann_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bop_product_id_equals_ann ieaS ieaT)
     | inr nieaT => inr _ (bop_product_not_id_equals_ann_right nieaT)
     end 
   | inr nieaS   => inr _ (bop_product_not_id_equals_ann_left nieaS)
   end. 


Definition bops_product_left_left_absorptive_decide : 
      bops_left_left_absorptive_decidable S rS addS mulS → bops_left_left_absorptive_decidable T rT addT mulT → 
         bops_left_left_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     => inl _ (bop_product_left_left_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_left_left_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_left_left_absorptive_left not_laS ) 
end. 


Definition bops_product_left_right_absorptive_decide : 
      bops_left_right_absorptive_decidable S rS addS mulS → bops_left_right_absorptive_decidable T rT addT mulT → 
         bops_left_right_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     => inl _ (bop_product_left_right_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_left_right_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_left_right_absorptive_left not_laS ) 
end. 

Definition bops_product_right_left_absorptive_decide : 
      bops_right_left_absorptive_decidable S rS addS mulS → bops_right_left_absorptive_decidable T rT addT mulT → 
         bops_right_left_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  inl _ (bop_product_right_left_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_right_left_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_right_left_absorptive_left not_laS ) 
end. 


Definition bops_product_right_right_absorptive_decide : 
      bops_right_right_absorptive_decidable S rS addS mulS → bops_right_right_absorptive_decidable T rT addT mulT → 
         bops_right_right_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  inl _ (bop_product_right_right_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_right_right_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_right_right_absorptive_left not_laS ) 
end.


End ProductProduct. 



