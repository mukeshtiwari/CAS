Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.cef. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.llte. 
Require Import CAS.theory.bop.llex.
Require Import CAS.theory.bop.product. 


Lemma bop_llex_product_left_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS -> 
      brel_symmetric S rS -> 
      brel_transitive S rS -> 
      bop_congruence S rS mulS -> 
      brel_reflexive T rT -> 
      brel_transitive T rT -> 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
      ((bop_left_cancellative S rS mulS) + (bop_left_constant T rT mulT)) → 
         bop_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refS symS transS b_congS refT transT ldS ldT D 
           [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       case_eq(rS s2 s3); intro H1; 
       case_eq(rS s2 (addS s2 s3)); intro H2; 
       case_eq(rS (mulS s1 s2) (mulS s1 s3)); intro H3; 
       case_eq(rS (mulS s1 s2) (addS (mulS s1 s2) (mulS s1 s3))); intro H4; simpl. 
          apply ldT. 
          apply ldT. 
          assert(fact := b_congS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          assert(fact := b_congS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          apply ldT. 
          apply ldT. 
          assert(fact := b_congS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          assert(fact := b_congS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (addT t2 t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (addT t2 t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          apply refT. 

          assert (fact1 := ldS s1 s2 s3). 
          assert (fact2 := b_congS _ _ _ _ (refS s1) H2).
          assert (fact3 := transS _ _ _ fact2 fact1). 
          rewrite fact3 in H4. discriminate. 

          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (addT t2 t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (addT t2 t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). apply symS in fact1. 
             assert (fact2 := transS _ _ _ H4 fact1). 
             apply C in fact2. 
             rewrite fact2 in H2. discriminate. 
             apply K. (* "direct" use of K *) 
          apply refT. 
Defined. 


Lemma bop_llex_product_not_left_distributive_v1 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t Pt] [ [s1 [s2 s3 ] ] nld ].
       exists ((s1, t), ((s2, t), (s3, t))); simpl. 
       rewrite nld. simpl. reflexivity. 
Defined. 


Lemma bop_llex_product_not_left_distributive_v2 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      brel_reflexive S rS → 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s Ps] refS [ [t1 [t2 t3 ] ] nld ].
       exists ((s, t1), ((s, t2), (s, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS s). rewrite (refS (mulS s s)). 
       assumption. 
Defined. 

(*  

   Assume 

   bop_not_cancellative : s1 * s2 = s1 * s3, s2 <> s3 
   bop_not_constant     : t1 * t2 <> t1 * t3 

   find ((s1, a), (s2, b), (s3, c)) that violates LD 

   case 1 :  s2 < s3 

      LHS : (s1, a) * ( (s2, b) + (s3, c))      = (s1, a) * (s2, b) = (s1 * s2, a * b) 
      RHS : (s1 * s2, a * b) + (s1 * s3, a * c) = (s1 * s2, (a * b) + (a * c)) 

      Need a * b <> (a * b) + (a * c) 
      
      case 1.1 : t1 * t2  = (t1 * t2) + (t1 * t3) 
           so    t1 * t3 <> (t1 * t2) + (t1 * t3) ={commT}=  (t1 * t3) + (t1 * t2)
           use   a    b                                       a     b     a    c 

      case 1.2 : t1 * t2  <> (t1 * t2) + (t1 * t3) 
           use   a    b       a     b     a    c 


   case 1 :  s3 < s2 

      LHS : (s1, a) * ( (s2, b) + (s3, c))      = (s1, a) * (s3, c) = (s1 * s2, a * c) 
      RHS : (s1 * s2, a * b) + (s1 * s3, a * c) = (s1 * s2, (a * b) + (a * c)) 

      Need a * c <> (a * b) + (a * c) 
      
      case 1.1 : t1 * t2  = (t1 * t2) + (t1 * t3) 
           so    t1 * t3 <> (t1 * t2) + (t1 * t3) 
           use   a    c      a     b     a    c 

      case 1.2 : t1 * t2  <> (t1 * t2) + (t1 * t3) ={commT}=  (t1 * t3) + (t1 * t2)
           use    a    c                                       a     b     a    c 

Definition cef_llex_product_not_left_distributive
      (S T : Type)
      (rS : brel S)
      (rT : brel T)
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
      (addS : binary_op S) 
      (addT : binary_op T)
      (mulT : binary_op T) 
:= if (rS (addS s2 s3) s2) 
   then if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
   else if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t2), (s3, t3)))
        else ((s1, t1), ((s2, t3), (s3, t2))). 
*) 

Lemma bop_llex_product_not_left_distributive_v3 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T),
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_selective S rS addS → 
      bop_commutative S rS addS → 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_commutative T rT addT → (* NB *) 
      bop_not_left_cancellative S rS mulS → 
      bop_not_left_constant T rT mulT → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS selS commS symT transT commT  
          [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
exists(cef_llex_product_not_left_distributive S T rS rT s1 s2 s3 t1 t2 t3 addS addT mulT). 
unfold cef_llex_product_not_left_distributive. 
destruct(selS s2 s3) as [H | H]. 
   case_eq(rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))); intro J; simpl. 

      rewrite H. simpl. 
      apply andb_is_false_right. right.    
      rewrite N. compute. 
      apply symS in H. rewrite N, E, H.  
      assert (fact1 := commT (mulT t1 t2) (mulT t1 t3)). 
      assert (fact2 := transT _ _ _ J fact1). 
      assert (fact3 := brel_transititivity_implies_dual _ _ transT _ _ _ fact2 F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite H; compute.           
      apply andb_is_false_right. right.    
      apply symS in H. rewrite N, E, H. 
      assumption. 

   assert (A : rS (addS s2 s3) s2 = false).  
       apply (brel_symmetric_implies_dual _ _ symS) in N.
       apply symS in H. 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ H N). 

   case_eq(rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))); intro J; rewrite A; compute. 
      apply andb_is_false_right. right.  rewrite N.
      apply (brel_symmetric_implies_dual _ _ symS) in A.  rewrite A. 
      rewrite E. 
      assert (fact5 := brel_transititivity_implies_dual _ _ transT _ _ _ J F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 


      rewrite N. rewrite E. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      case_eq(rS (mulS s1 (addS s2 s3)) (addS (mulS s1 s2) (mulS s1 s3))); intro K; auto.    
      assert (fact1 := commT (mulT t1 t2) (mulT t1 t3)). 
      apply (brel_symmetric_implies_dual _ _ symT) in J.
      assert (fact2 := brel_transititivity_implies_dual _ _ transT _ _ _ fact1 J). 
      apply (brel_symmetric_implies_dual _ _ symT).             
      assumption. 
Defined.  



Lemma bop_llex_product_right_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS -> 
      brel_symmetric S rS -> 
      brel_transitive S rS -> 
      bop_congruence S rS mulS -> 
      brel_reflexive T rT -> 
      brel_transitive T rT -> 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
      ((bop_right_cancellative S rS mulS) + (bop_right_constant T rT mulT)) → 
         bop_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refS symS transS b_congS refT transT ldS ldT D 
           [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       case_eq(rS s2 s3); intro H1; 
       case_eq(rS s2 (addS s2 s3)); intro H2; 
       case_eq(rS (mulS s2 s1) (mulS s3 s1)); intro H3; 
       case_eq(rS (mulS s2 s1) (addS (mulS s2 s1) (mulS s3 s1))); intro H4; simpl. 
          apply ldT. 
          apply ldT. 
          assert(fact := b_congS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          assert(fact := b_congS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          apply ldT. 
          apply ldT. 
          assert(fact := b_congS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          assert(fact := b_congS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (addT t2 t3)). 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (addT t2 t3)). 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          apply refT. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). 
             assert (fact2 := b_congS _ _ _ _ H2 (refS s1)).
             assert (fact3 := transS _ _ _ fact2 fact1). 
             rewrite fact3 in H4. discriminate. 
             apply K. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (addT t2 t3)). 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (addT t2 t3)). 
             assert (fact3 := transT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). apply symS in fact1. 
             assert (fact2 := transS _ _ _ H4 fact1). 
             apply C in fact2. 
             rewrite fact2 in H2. discriminate. 
             apply K. 
          apply refT. 
Defined. 

Lemma bop_llex_product_not_right_distributive_v1 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t Pt] [ [s1 [s2 s3 ] ] nld ].
       exists ((s1, t), ((s2, t), (s3, t))); simpl. 
       rewrite nld. simpl. reflexivity. 
Defined. 


Lemma bop_llex_product_not_right_distributive_v2 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      brel_reflexive S rS → 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s Ps] refS [ [t1 [t2 t3 ] ] nld ].
       exists ((s, t1), ((s, t2), (s, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS s). rewrite (refS (mulS s s)). 
       assumption. 
Defined. 


Lemma bop_llex_product_not_right_distributive_v3: 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_selective S rS addS → 
      bop_commutative S rS addS → 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_commutative T rT addT → 
      bop_not_right_cancellative S rS mulS → 
      bop_not_right_constant T rT mulT → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. 
intros S T rS rT addS mulS addT mulT symS transS selS commS symT transT commT 
          [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
exists(cef_llex_product_not_right_distributive S T rS rT s1 s2 s3 t1 t2 t3 addS addT mulT). 
unfold cef_llex_product_not_right_distributive. 
destruct(selS s2 s3) as [H | H]. 
   case_eq(rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))); intro J; simpl. 

      rewrite H. simpl. 
      apply andb_is_false_right. right.    
      apply symS in H. 
      rewrite N; compute. rewrite H, E.  rewrite N. 
      assert (fact1 := commT (mulT t2 t1) (mulT t3 t1)). 
      assert (fact2 := transT _ _ _ J fact1). 
      assert (fact3 := brel_transititivity_implies_dual _ _ transT _ _ _ fact2 F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite H; compute.           
      apply andb_is_false_right. right.    
      apply symS in H. rewrite N, E, H. 
      assumption. 

   assert (A : rS (addS s2 s3) s2 = false).
       apply (brel_symmetric_implies_dual _ _ symS) in N.
       apply symS in H. 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ H N). 
   case_eq(rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))); intro J; simpl; rewrite A; compute. 

      apply andb_is_false_right. right.    
      rewrite N. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      rewrite E. 
      assert (fact5 := brel_transititivity_implies_dual _ _ transT _ _ _ J F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite N. rewrite E. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      case_eq(rS (mulS (addS s2 s3) s1) (addS (mulS s2 s1) (mulS s3 s1))); intro K; auto.    
      assert (fact1 := commT (mulT t2 t1) (mulT t3 t1)). 
      apply (brel_symmetric_implies_dual _ _ symT) in J.
      assert (fact2 := brel_transititivity_implies_dual _ _ transT _ _ _ fact1 J). 
      apply (brel_symmetric_implies_dual _ _ symT).             
      assumption. 
Defined. 







Lemma bops_llex_product_id_equals_ann : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      brel_reflexive T rT → 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_commutative S rS addS → 
      bops_id_equals_ann S rS addS mulS → 
      bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refS symS transS refT symT transT commS 
             [eIS [eAS pS]] [eIT [eAT pT]]. 
       assert (addIST := bop_llex_exists_id S T rS rT addS addT symS transS refT eIS eIT commS). 
       assert (mulAST := bop_product_exists_ann S T rS rT mulS mulT eAS eAT). 
       unfold bops_id_equals_ann. 
       exists addIST; exists mulAST. 
       destruct eIS as [iS piS]. 
       destruct eAS as [aS paS]. 
       destruct eIT as [iT piT]. 
       destruct eAT as [aT paT].       
       destruct addIST as [[iS2 iT2] piST].  
       destruct mulAST as [[aS2 aT2] paST].  
       simpl. simpl in pS, pT. 
       assert (fact_aS2 := bop_product_is_ann_left S T rS rT mulS mulT aS2 aT2 paST). 
       assert (fact_aT2 := bop_product_is_ann_right S T rS rT mulS mulT aS2 aT2 paST).
       assert (fact_iS2 := bop_llex_is_id_left S T rS rT addS addT iS2 iT2 piST). 
       assert (fact_iT2 := bop_llex_is_id_right S T rS rT addS addT refS iS2 iT2 piST). 
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



Lemma bops_product_llex_id_equals_ann : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      brel_reflexive T rT → 
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bop_commutative S rS addS → 
      bops_id_equals_ann S rS mulS addS  → 
      bops_id_equals_ann T rT mulT addT  → 
         bops_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ mulS mulT)
             (bop_llex _ _ rS addS addT). 
Proof. intros S T rS rT addS mulS addT mulT refS symS transS refT symT transT commS 
             [eIS [eAS pS]] [eIT [eAT pT]]. 
       unfold bops_id_equals_ann. 
       assert (mulIST := bop_product_exists_id S T rS rT mulS mulT eIS eIT). 
       exists mulIST. 
       assert (addAST := bop_llex_exists_ann S T rS rT addS addT symS transS refT eAS eAT commS ). 
       exists addAST. 
       destruct eIS as [iS piS]. 
       destruct eAS as [aS paS]. 
       destruct eIT as [iT piT]. 
       destruct eAT as [aT paT].       
       destruct addAST as [[aS2 aT2] paST].  
       destruct mulIST as [[iS2 iT2] piST].  
       simpl. simpl in pS, pT. 
       assert (fact_iS2 := bop_product_is_id_left S T rS rT mulS mulT iS2 iT2 piST). 
       assert (fact_iT2 := bop_product_is_id_right S T rS rT mulS mulT iS2 iT2 piST).
       assert (fact_aS2 := bop_llex_is_ann_left S T rS rT addS addT aS2 aT2 paST). 
       assert (fact_aT2 := bop_llex_is_ann_right S T rS rT addS addT refS aS2 aT2 paST). 

       assert (fact1 :=  bop_is_id_equal S rS symS transS mulS iS iS2 piS fact_iS2). 
       assert (fact2 :=  bop_is_id_equal T rT symT transT mulT iT iT2 piT fact_iT2). 
       assert (fact3 :=  bop_is_ann_equal S rS symS transS addS aS aS2 paS fact_aS2). 
       assert (fact4 :=  bop_is_ann_equal T rT symT transT addT aT aT2 paT fact_aT2). 

       apply symS in fact1.        
       assert (fact5 := transS _ _ _ fact1 pS).  
       assert (fact6 := transS _ _ _ fact5 fact3).  
       apply symT in fact2.        
       assert (fact7 := transT _ _ _ fact2 pT).  
       assert (fact9 := transT _ _ _ fact7 fact4).  
       rewrite fact6, fact9. 
       simpl. reflexivity. 
Defined. 

Lemma bops_llex_product_not_left_distributive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [t tP] [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, t), ((s2, t), (s3, t))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bops_llex_product_not_left_distributive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      brel_reflexive S rS → 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT [s sP] refS [ [t1 [t2 t3 ] ] nd ].
       exists ((s, t1), ((s, t2), (s, t3))). simpl. 
       rewrite (refS s). rewrite (refS (mulS s s)). 
       rewrite nd.  apply andb_comm. 
Defined. 


Lemma bops_llex_product_not_right_distributive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness T rT → 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT  [t tP] [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, t), ((s2, t), (s3, t))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bops_llex_product_not_right_distributive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_witness S rS → 
      brel_reflexive S rS → 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT  [s sP] refS [ [t1 [t2 t3] ] nd ].
       exists ((s, t1), ((s, t2), (s, t3))). simpl. 
       rewrite (refS s). rewrite (refS (mulS s s)). 
       rewrite nd.  apply andb_comm. 
Defined. 

Lemma bops_llex_product_not_id_equals_ann_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_llex_is_id_left S T rS rT addS addT iS iT qi).
       assert (fact2 := bop_product_is_ann_left S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. reflexivity. 
Defined. 

Lemma bops_llex_product_not_id_equals_ann_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS  → 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT refS H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_llex_is_id_right S T rS rT addS addT refS iS iT qi).
       assert (fact2 := bop_product_is_ann_right S T rS rT mulS mulT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. apply andb_comm. 
Defined. 


Lemma bops_product_llex_not_id_equals_ann_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      bops_not_id_equals_ann S rS mulS addS → 
         bops_not_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ mulS mulT)
             (bop_llex _ _ rS addS addT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_id_left S T rS rT mulS mulT iS iT qi).
       assert (fact2 := bop_llex_is_ann_left S T rS rT addS addT aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. reflexivity. 
Defined. 

Lemma bops_product_llex_not_id_equals_ann_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS  → 
      bops_not_id_equals_ann T rT mulT addT → 
         bops_not_id_equals_ann (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ mulS mulT) 
             (bop_llex _ _ rS addS addT). 
Proof. unfold bops_not_id_equals_ann. 
       intros S T rS rT addS mulS addT mulT refS H [iS iT] [aS aT] qi qa. simpl. 
       assert (fact1 := bop_product_is_id_right S T rS rT mulS mulT iS iT qi).
       assert (fact2 := bop_llex_is_ann_right S T rS rT addS addT refS aS aT qa).
       assert (fact3 := H _ _ fact1 fact2). 
       rewrite fact3. apply andb_comm. 
Defined. 


       
(* absorption *) 

(* left left *) 


Lemma bops_llex_product_left_left_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive T rT → 
      bops_left_left_absorptive S rS addS mulS → 
      ((bops_left_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
         bops_left_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refT ldS [ldT| F] [s1 t1] [s2 t2].
       simpl. 
       unfold bops_left_left_absorptive in ldS. 
       unfold bops_left_left_absorptive in ldT. 
       rewrite ldS. simpl. 
       case_eq(rS s1 (mulS s1 s2)); intro H. 
          apply ldT.
          compute.  rewrite ldS. rewrite H. 
          apply refT. 
       compute. 
       rewrite ldS. rewrite F. rewrite F. 
       apply refT. 
Defined. 

Lemma bops_llex_product_not_left_left_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 


Lemma bops_llex_product_not_left_left_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS  → 
      brel_transitive S rS  → 
      bops_left_left_absorptive S rS addS mulS → 
      bops_not_left_left_absorptive T rT addT mulT → 
      bop_not_anti_left S rS mulS  →
         bops_not_left_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS laS [ [t1 t2] P ] [ [s1 s2]  Q].
       exists ((s1, t1), (s2, t2)). 
       compute. 
       rewrite laS. rewrite Q. 
       assumption. 
Defined. 


(* left right *) 
Lemma bops_llex_product_left_right_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive T rT → 
      bops_left_right_absorptive S rS addS mulS → 
      ((bops_left_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
         bops_left_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refT ldS [ldT| F] [s1 t1] [s2 t2].
       simpl. 
       unfold bops_left_right_absorptive in ldS. 
       unfold bops_left_right_absorptive in ldT.
       compute.  
       rewrite ldS. 
       case_eq(rS s1 (mulS s2 s1)); intro H. 
          apply ldT.
          apply refT. 
       compute. 
       rewrite ldS. rewrite F. rewrite F. 
       apply refT. 
Defined. 

Lemma bops_llex_product_not_left_right_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 


Lemma bops_llex_product_not_left_right_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS  → 
      brel_transitive S rS  → 
      bops_left_right_absorptive S rS addS mulS → 
      bops_not_left_right_absorptive T rT addT mulT → 
      bop_not_anti_right S rS mulS  → 
         bops_not_left_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS laS [ [t1 t2] P ] [ [s1 s2]  Q] .
       exists ((s1, t1), (s2, t2)). 
       compute. 
       rewrite laS. rewrite Q. 
       assumption. 
Defined. 



(* right left *) 
Lemma bops_llex_product_right_left_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive T rT → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bops_right_left_absorptive S rS addS mulS → 
      ((bops_right_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
         bops_right_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT refT symS transS ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       unfold bops_right_left_absorptive in ldS. 
       unfold bops_right_left_absorptive in ldT. 
       rewrite ldS. 
       case_eq(rS (mulS s1 s2) s1); intro H. 
          apply ldT. 
          case_eq(rS (mulS s1 s2) (addS (mulS s1 s2) s1)) ; intro K. 
             assert (fact1 := ldS s1 s2). apply symS in fact1. 
             assert (fact2 := transS _ _ _ K fact1).            
             rewrite fact2 in H. discriminate. 
             apply refT. 
       unfold bops_right_left_absorptive in ldS. 
       unfold bop_anti_left in F.
       assert (F' : ∀ s t : S, rS (mulS s t) s = false). 
          intros s t. apply (brel_symmetric_implies_dual _ _ symS). apply F. 
       rewrite ldS, F'. 
       assert (L : rS (mulS s1 s2) (addS (mulS s1 s2) s1) = false). 
          assert (fact1 := ldS s1 s2).
          assert (fact2 := F s1 s2). 
          assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 fact2). 
          apply (brel_symmetric_implies_dual _ _ symS).  assumption. 
       rewrite L. apply refT. 
Defined. 


Lemma bops_llex_product_not_right_left_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 


Lemma bops_llex_product_not_right_left_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS  → 
      brel_transitive S rS  → 
      bops_right_left_absorptive S rS addS mulS → 
      bops_not_right_left_absorptive T rT addT mulT → 
      bop_not_anti_left S rS mulS  → 
         bops_not_right_left_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS laS [ [t1 t2] P ] [ [s1 s2]  Q] .
       exists ((s1, t1), (s2, t2)). 
       compute. 
       rewrite laS. apply symS in Q. rewrite Q. 
       assumption. 
Defined. 


(* right_right *) 
Lemma bops_llex_product_right_right_absorptive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      brel_reflexive T rT → 
      bops_right_right_absorptive S rS addS mulS → 
      ((bops_right_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
         bops_right_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS refT laS [laT| F] [s1 t1] [s2 t2]; simpl. 
       unfold bops_right_right_absorptive in laS. 
       unfold bops_right_right_absorptive in laT. 
       rewrite laS. simpl. 
       case_eq(rS (mulS s2 s1) s1); intro H1. 
          apply laT.
          compute.  
          case_eq(rS (mulS s2 s1) (addS (mulS s2 s1) s1)); intro H2. 
             rewrite H1.  
             assert (fact1 := laS s1 s2). apply symS in fact1. 
             assert (fact2 := transS _ _ _ H2 fact1). 
             rewrite fact2 in H1. discriminate. 
             apply refT. 
          unfold bops_right_right_absorptive in laS. 
          unfold bop_anti_right in F. 
          compute. 
          rewrite laS. simpl. 
          assert (fact1 := F s1 s2). apply (brel_symmetric_implies_dual _ _ symS) in fact1. 
          rewrite fact1. 
          case_eq (rS (mulS s2 s1) (addS (mulS s2 s1) s1)); intro H. 
             assert (fact2 := laS s1 s2). apply symS in fact2. 
             assert (fact3 := transS _ _ _ H fact2). rewrite fact3 in fact1. discriminate. 
             apply refT. 
Defined. 

Lemma bops_llex_product_not_right_right_absorptive_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T) (t :T), 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT t [ [s1 s2] P ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P. simpl. reflexivity. 
Defined. 


Lemma bops_llex_product_not_right_right_absorptive_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) 
     (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_symmetric S rS  → 
      brel_transitive S rS  → 
      bops_right_right_absorptive S rS addS mulS → 
      bops_not_right_right_absorptive T rT addT mulT → 
      bop_not_anti_right S rS mulS  → 
         bops_not_right_right_absorptive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT). 
Proof. intros S T rS rT addS mulS addT mulT symS transS laS [ [t1 t2] P ] [ [s1 s2]  Q] .
       exists ((s1, t1), (s2, t2)). 
       compute. 
       rewrite laS. apply symS in Q. rewrite Q. 
       assumption. 
Defined. 


