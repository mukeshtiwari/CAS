Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.bop_left_sum. 


???????????????????



Lemma bop_left_sum_left_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      bop_idempotent S rS addS → 
      bops_left_constant S rS addS mulS → 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
         bop_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refS symS idemS lcS ldS ldT 
            [s1 | t1] [s2 | t2] [s3 | t3]; compute; auto. 
       admit. 
       assert (fact := lcS s1 s3 s1). 

       s1 * s2 = (s1 * s2) + s1
      rS (mulS s1 s2) (addS (mulS s1 s2) s1) = true
       s1 * s3 = s1 + (s1 * s3)
       rS (mulS s1 s3) (addS s1 (mulS s1 s3)) = true

       r (b2 s t) (b2 s (b1 t u)) = true.      


Defined. 


Lemma bop_left_sum_right_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
         bop_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT lrS lrT [s1 t1] [s2 t2] [s3 t3].
       simpl. rewrite lrS, lrT.  simpl. reflexivity. 
Defined. 



Lemma bop_left_sum_not_left_distributive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t tP] [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, t), ((s2, t), (s3, t))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_left_sum_not_left_distributive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s sP] [ [t1 [t2 t3 ] ] nd ].
       exists ((s, t1), ((s, t2), (s, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 


Lemma bop_left_sum_not_right_distributive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT  [t tP] [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, t), ((s2, t), (s3, t))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_left_sum_not_right_distributive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT  [s sP] [ [t1 [t2 t3] ] nd ].
       exists ((s, t1), ((s, t2), (s, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 



Lemma bop_id_unique : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (p : bop_exists_id S r b)        
                        (q : bop_exists_id S r b), r (projT1 p) (projT1 q) = true.             
Proof. intros S r symS trnS b [s1 P] [s2 Q]. simpl.  
       destruct (Q s1) as [_ R1]. destruct (P s2) as [L2 _]. 
       apply symS in R1. apply (trnS _ _ _ R1 L2). 
Defined.                         

Lemma bop_is_id_equal : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (x : S )
                        (y : S )
                        (p : bop_is_id S r b x)        
                        (q : bop_is_id S r b y), r x y = true.             
Proof. intros S r symS trnS b x y p q. 
       destruct (q x) as [_ R1]. destruct (p y) as [L2 _]. 
       apply symS in R1. apply (trnS _ _ _ R1 L2). 
Defined.                         


Lemma bop_ann_unique : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (p : bop_exists_ann S r b)        
                        (q : bop_exists_ann S r b), r (projT1 p) (projT1 q) = true.             
Proof. intros S r symS trnS b [s1 P] [s2 Q]. simpl.  
       destruct (Q s1) as [_ R1]. destruct (P s2) as [L2 _]. 
       apply symS in L2. apply (trnS _ _ _ L2 R1). 
Defined.                         

Lemma bop_is_ann_equal : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (x : S )
                        (y : S )
                        (p : bop_is_ann S r b x)        
                        (q : bop_is_ann S r b y), r x y = true.             
Proof. intros S r symS trnS b x y p q.  
       destruct (q x) as [_ R1]. destruct (p y) as [L2 _]. 
       apply symS in L2. apply (trnS _ _ _ L2 R1). 
Defined.                         


Lemma bop_left_sum_is_id_left : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_id (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT) (s, t))
       ->  bop_is_id S rS bS s.  
Proof. intros S T rS rT bS bT s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_left_sum_is_id_right : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_id (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT) (s, t))
       ->  bop_is_id T rT bT t.  
Proof. intros S T rS rT bS bT s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.                         


Lemma bop_left_sum_is_ann_left : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_ann (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT) (s, t))
       ->  bop_is_ann S rS bS s.  
Proof. intros S T rS rT bS bT s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_left_sum_is_ann_right : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_ann (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT) (s, t))
       ->  bop_is_ann T rT bT t.  
Proof. intros S T rS rT bS bT s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.                         


Lemma bop_left_sum_id_equals_ann : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS → brel_transitive S rS → 
      brel_symmetric T rT → brel_transitive T rT → 
      bops_id_equals_ann S rS addS mulS → 
      bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS symT transT [eIS [eAS pS]] [eIT [eAT pT]]. 
       assert (addIST := bop_left_sum_exists_id S T rS rT addS addT eIS eIT). 
       assert (mulAST := bop_left_sum_exists_ann S T rS rT mulS mulT eAS eAT). 
       unfold bops_id_equals_ann. 
       exists addIST; exists mulAST. 
       destruct eIS as [iS piS]. 
       destruct eAS as [aS paS]. 
       destruct eIT as [iT piT]. 
       destruct eAT as [aT paT].       
       destruct addIST as [[iS2 iT2] piST].  
       destruct mulAST as [[aS2 aT2] paST].  
       simpl. simpl in pS, pT. 
       assert (fact_iS2 := bop_left_sum_is_id_left S T rS rT addS addT iS2 iT2 piST). 
       assert (fact_iT2 := bop_left_sum_is_id_right S T rS rT addS addT iS2 iT2 piST). 
       assert (fact_aS2 := bop_left_sum_is_ann_left S T rS rT mulS mulT aS2 aT2 paST). 
       assert (fact_aT2 := bop_left_sum_is_ann_right S T rS rT mulS mulT aS2 aT2 paST).
       assert (fact1 :=  bop_is_id_equal S rS symS transS addS iS iS2 piS fact_iS2). 
       assert (fact2 :=  bop_is_id_equal T rT symT transT addT iT iT2 piT fact_iT2). 
       assert (fact3 :=  bop_is_ann_equal S rS symS transS mulS aS aS2 paS fact_aS2). 
       assert (fact4 :=  bop_is_ann_equal T rT symT transT mulT aT aT2 paT fact_aT2). 
       apply symS in fact1.        
       assert (fact5 := transS _ _ _ fact1 pS).  
       assert (fact6 := transS _ _ _ fact5 fact3).  
       apply symT in fact2.        
       assert (fact7 := transT _ _ _ fact2 pT).  
       assert (fact9 := transT _ _ _ fact7 fact4).  
       rewrite fact6, fact9. 
       simpl. reflexivity. 
Defined. 


Lemma bop_left_sum_not_id_equals_ann_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_left_sum_is_id_left S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_left_sum_is_ann_left S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. reflexivity. 
Defined. 

Lemma bop_left_sum_not_id_equals_ann_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_left_sum_is_id_right S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_left_sum_is_ann_right S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. apply andb_comm. 
Defined. 

Lemma bops_left_sum_left_sum_left_constant_ : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
       bops_left_constant S rS addS mulS → 
       bops_left_constant T rT addT mulT → 
         bops_left_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT lcS lcT [s1 t1] [s2 t2] [s3 t3]. 
       compute. rewrite lcS. apply lcT. 
Defined. 

Lemma bops_left_sum_left_sum_not_left_constant_left : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
       brel_witness T rT → 
       bops_not_left_constant S rS addS mulS → 
         bops_not_left_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t Pt] [ [s1 [s2 s3]] F]. 
       exists ((s1, t), ((s2, t), (s3, t))); compute. rewrite F. reflexivity. 
Defined. 

Lemma bops_left_sum_left_sum_not_left_constant_right : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
       brel_witness S rS → 
       bops_not_left_constant T rT addT mulT → 
         bops_not_left_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s Ps] [ [t1 [t2 t3]] F]. 
       exists ((s, t1), ((s, t2), (s, t3))); compute. rewrite F. 
       case(rS (mulS s s) (mulS s (addS s s))); reflexivity. 
Defined. 
       



Lemma bops_left_sum_left_sum_right_constant_ : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
       bops_right_constant S rS addS mulS → 
       bops_right_constant T rT addT mulT → 
         bops_right_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT lcS lcT [s1 t1] [s2 t2] [s3 t3]. 
       compute. rewrite lcS. apply lcT. 
Defined. 

Lemma bops_left_sum_left_sum_not_right_constant_left : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
       brel_witness T rT → 
       bops_not_right_constant S rS addS mulS → 
         bops_not_right_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t Pt] [ [s1 [s2 s3]] F]. 
       exists ((s1, t), ((s2, t), (s3, t))); compute. rewrite F. reflexivity. 
Defined. 

Lemma bops_left_sum_left_sum_not_right_constant_right : 
   ∀ (S T: Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
       brel_witness S rS → 
       bops_not_right_constant T rT addT mulT → 
         bops_not_right_constant (S + T) 
             (brel_sum _ _ rS rT) 
             (bop_left_sum _ _ addS addT)
             (bop_left_sum _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s Ps] [ [t1 [t2 t3]] F]. 
       exists ((s, t1), ((s, t2), (s, t3))); compute. rewrite F. 
       case(rS (mulS s s) (mulS (addS s s) s)); reflexivity. 
Defined. 
       


