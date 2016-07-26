Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.bop.product. 


(* note : should be able to abstract away and universally quantfied predicate .... *) 

Lemma bop_product_left_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
         bop_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT ldS ldT [s1 t1] [s2 t2] [s3 t3].
       simpl. rewrite ldS, ldT.  simpl. reflexivity. 
Defined. 


Lemma bop_product_right_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
         bop_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT lrS lrT [s1 t1] [s2 t2] [s3 t3].
       simpl. rewrite lrS, lrT.  simpl. reflexivity. 
Defined. 



Lemma bop_product_not_left_distributive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t tP] [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, t), ((s2, t), (s3, t))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_distributive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s sP] [ [t1 [t2 t3 ] ] nd ].
       exists ((s, t1), ((s, t2), (s, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 


Lemma bop_product_not_right_distributive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT  [t tP] [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, t), ((s2, t), (s3, t))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_distributive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT  [s sP] [ [t1 [t2 t3] ] nd ].
       exists ((s, t1), ((s, t2), (s, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 


(* *********************************** *) 


Lemma bop_product_id_equals_ann : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_id_equals_ann S rS addS mulS → 
      bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT 
       [[iS piS] [[aS paS] pS]] [[iT piT] [[aT paT] pT]]. simpl in pS, pT. 
       unfold bops_id_equals_ann. 
       exists (existT _ (iS, iT) (bop_product_is_id S T rS rT addS addT iS iT piS piT)). 
       exists (existT _ (aS, aT) (bop_product_is_ann S T rS rT mulS mulT aS aT paS paT)). 
       simpl. rewrite pS, pT; auto. 
Defined. 

Lemma bop_product_not_id_equals_ann_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_id_left S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_ann_left S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. reflexivity. 
Defined. 

Lemma bop_product_not_id_equals_ann_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_id_right S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_ann_right S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. apply andb_comm. 
Defined. 



Lemma bop_product_id_equals_id : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_id_equals_id S rS addS mulS → 
      bops_id_equals_id T rT addT mulT → 
         bops_id_equals_id (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT 
       [[iS piS] [[aS paS] pS]] [[iT piT] [[aT paT] pT]]. simpl in pS, pT. 
       unfold bops_id_equals_id. 
       exists (existT _ (iS, iT) (bop_product_is_id S T rS rT addS addT iS iT piS piT)). 
       exists (existT _ (aS, aT) (bop_product_is_id S T rS rT mulS mulT aS aT paS paT)). 
       simpl. rewrite pS, pT; auto. 
Defined. 



Lemma bop_product_not_id_equals_id_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_id S rS addS mulS → 
         bops_not_id_equals_id (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_id_left S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_id_left S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. reflexivity. 
Defined. 


Lemma bop_product_not_id_equals_id_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_id T rT addT mulT → 
         bops_not_id_equals_id (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_id_right S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_id_right S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. apply andb_comm. 
Defined. 



Lemma bop_product_ann_equals_ann : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_ann_equals_ann S rS addS mulS → 
      bops_ann_equals_ann T rT addT mulT → 
         bops_ann_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT 
       [[iS piS] [[aS paS] pS]] [[iT piT] [[aT paT] pT]]. simpl in pS, pT. 
       unfold bops_ann_equals_ann. 
       exists (existT _ (iS, iT) (bop_product_is_ann S T rS rT addS addT iS iT piS piT)). 
       exists (existT _ (aS, aT) (bop_product_is_ann S T rS rT mulS mulT aS aT paS paT)). 
       simpl. rewrite pS, pT; auto. 
Defined. 



Lemma bop_product_not_ann_equals_ann_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_ann_equals_ann S rS addS mulS → 
         bops_not_ann_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_ann_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_ann_left S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_ann_left S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. reflexivity. 
Defined. 


Lemma bop_product_not_ann_equals_ann_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_ann_equals_ann T rT addT mulT → 
         bops_not_ann_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_ann_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_ann_right S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_ann_right S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. apply andb_comm. 
Defined. 


(* *************************** *) 


(* left left *) 
Lemma bop_product_left_left_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_left_left_absorptive S rS addS mulS → 
      bops_left_left_absorptive T rT addT mulT → 
         bops_left_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT ldS ldT [s1 t1] [s2 t2].
       simpl. rewrite ldS, ldT.  simpl. reflexivity. 
Defined. 


Lemma bop_product_not_left_left_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_left_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      bops_not_left_left_absorptive T rT addT mulT → 
         bops_not_left_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s [ [t1 t2] P ]. 
       exists ((s, t1), (s, t2)). simpl. rewrite P. simpl. 
       apply andb_comm.  
Defined. 



(* left right *) 
Lemma bop_product_left_right_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_left_right_absorptive S rS addS mulS → 
      bops_left_right_absorptive T rT addT mulT → 
         bops_left_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT ldS ldT [s1 t1] [s2 t2].
       simpl. rewrite ldS, ldT.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_right_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_right_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      bops_not_left_right_absorptive T rT addT mulT → 
         bops_not_left_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s [ [t1 t2] P ]. 
       exists ((s, t1), (s, t2)). simpl. rewrite P. simpl. 
       apply andb_comm.  
Defined. 


(* right left *) 
Lemma bop_product_right_left_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_right_left_absorptive S rS addS mulS → 
      bops_right_left_absorptive T rT addT mulT → 
         bops_right_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT ldS ldT [s1 t1] [s2 t2].
       simpl. rewrite ldS, ldT.  simpl. reflexivity. 
Defined. 


Lemma bop_product_not_right_left_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_left_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      bops_not_right_left_absorptive T rT addT mulT → 
         bops_not_right_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s [ [t1 t2] P ]. 
       exists ((s, t1), (s, t2)). simpl. rewrite P. simpl. 
       apply andb_comm.  
Defined. 



(* right right *) 
Lemma bop_product_right_right_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_right_right_absorptive S rS addS mulS → 
      bops_right_right_absorptive T rT addT mulT → 
         bops_right_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT ldS ldT [s1 t1] [s2 t2].
       simpl. rewrite ldS, ldT.  simpl. reflexivity. 
Defined. 


Lemma bop_product_not_right_right_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_right_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (s : S), 
      bops_not_right_right_absorptive T rT addT mulT → 
         bops_not_right_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT s [ [t1 t2] P ]. 
       exists ((s, t1), (s, t2)). simpl. rewrite P. simpl. 
       apply andb_comm.  
Defined. 



(* *************************** *) 




