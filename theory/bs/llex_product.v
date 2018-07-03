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

Section LlexProduct. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.

Variable wS : S. 
Variable wT : T.

Variable addS  mulS : binary_op S. 
Variable addT mulT : binary_op T.


Variable conS : brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.


Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.  
Variable tranT : brel_transitive T rT.

Variable a_conS : bop_congruence S rS addS.
Variable m_conS : bop_congruence S rS mulS.
Variable a_conT : bop_congruence T rT addT.
Variable m_conT : bop_congruence T rT mulT.

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [+] b" := (bop_llex rS a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).

Lemma bop_llex_product_left_distributive : 
      bop_left_distributive S rS addS mulS → bop_left_distributive T rT addT mulT → 
         ((bop_left_cancellative S rS mulS) + (bop_left_constant T rT mulT)) → 
             bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT D [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       case_eq(rS s2 s3); intro H1; 
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 *S s2) (s1 *S s3)); intro H3; 
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H4; simpl. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          apply refT. 

          assert (fact1 := ldS s1 s2 s3). 
          assert (fact2 := m_conS _ _ _ _ (refS s1) H2).
          assert (fact3 := tranS _ _ _ fact2 fact1). 
          rewrite fact3 in H4. discriminate. 

          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). apply symS in fact1. 
             assert (fact2 := tranS _ _ _ H4 fact1). 
             apply C in fact2. 
             rewrite fact2 in H2. discriminate. 
             apply K. (* "direct" use of K *) 
          apply refT. 
Defined. 

Definition bop_is_left_ann (S : Type) (eq : brel S) (b : binary_op S) (a : S)
    :=  ∀ s : S, (eq (b a s) a = true).

Definition bop_not_is_left_ann (S : Type) (r : brel S) (b : binary_op S) (a : S)
    := {s : S & (r (b a s) a = false)}.

Definition bop_left_cancellative_weak (S : Type) (eq : brel S) (b : binary_op S)
    := ∀ s t u : S, eq (b s t) (b s u) = true -> (eq t u = true) + (bop_is_left_ann S eq b s).

Definition bop_not_left_cancellative_weak (S : Type) (eq : brel S) (b : binary_op S)
   := { z : S * (S * S) & match z with (s, (t, u)) => (eq (b s t) (b s u) = true) * (eq t u = false) * (bop_not_is_left_ann S eq b s) end }. 


Lemma bop_llex_product_left_distributive_weak : 
      bop_left_distributive S rS addS mulS → bop_left_distributive T rT addT mulT → 
         ((bop_left_cancellative_weak S rS mulS) + (bop_left_constant T rT mulT)) → 
             bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT D [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       case_eq(rS s2 s3); intro H1; 
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 *S s2) (s1 *S s3)); intro H3; 
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H4; simpl. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          assert(fact := m_conS _ _ _ _ (refS s1) H1). rewrite fact in H3. discriminate. 
          destruct D as [C | K].
              apply C in H3.
              destruct H3 as [H3 | H3]. 
                 rewrite H3 in H1. discriminate.
                 admit. (* HERE 
                                 s1 (s2 + s3) = s1 s2 + s1 s3 
                                              = s1 s2 
                         *) 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3.
             destruct H3 as [H3 | H3]. 
                rewrite H3 in H1. discriminate. 
                admit. (* OK HERE *) 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          apply refT. 

          assert (fact1 := ldS s1 s2 s3). 
          assert (fact2 := m_conS _ _ _ _ (refS s1) H2).
          assert (fact3 := tranS _ _ _ fact2 fact1). 
          rewrite fact3 in H4. discriminate. 

          destruct D as [C | K]. 
             apply C in H3.
             destruct H3 as [H3 | H3]. 
                rewrite H3 in H1. discriminate. 
                admit. (* HERE *) 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3.
             destruct H3 as [H3 | H3]. 
                rewrite H3 in H1. discriminate. 
                admit. (* OK HERE *) 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). apply symS in fact1. 
             assert (fact2 := tranS _ _ _ H4 fact1). 
             apply C in fact2.
             destruct fact2 as [fact2 | fact2].
                rewrite fact2 in H2. discriminate. 
                admit. (* OK HERE *) 
             apply K. (* "direct" use of K *) 
          apply refT. 
Admitted. 




Lemma bop_llex_product_not_left_distributive_v1 : 
      bop_not_left_distributive S rS addS mulS → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 


Lemma bop_llex_product_not_left_distributive_v2 : 
      bop_not_left_distributive T rT addT mulT → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS wS). rewrite (refS (mulS wS wS)). 
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
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → (* NB *) 
      bop_not_left_cancellative S rS mulS → bop_not_left_constant T rT mulT → 
            bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros selS commS commT  [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
exists(cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3 addS addT mulT). 
unfold cef_llex_product_not_left_distributive. 
destruct(selS s2 s3) as [H | H]. 
   case_eq(rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))); intro J; simpl. 

      rewrite H. simpl. 
      apply andb_is_false_right. right.    
      rewrite N. compute. 
      apply symS in H. rewrite N, E, H.  
      assert (fact1 := commT (t1 *T t2) (t1 *T t3)). 
      assert (fact2 := tranT _ _ _ J fact1). 
      assert (fact3 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact2 F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite H; compute.           
      apply andb_is_false_right. right.    
      apply symS in H. rewrite N, E, H. 
      assumption. 

   assert (A : rS (s2 +S s3) s2 = false).  
       apply (brel_symmetric_implies_dual _ _ symS) in N.
       apply symS in H. 
       apply (brel_transititivity_implies_dual _ _ tranS _ _ _ H N). 

   case_eq(rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))); intro J; rewrite A; compute. 
      apply andb_is_false_right. right.  rewrite N.
      apply (brel_symmetric_implies_dual _ _ symS) in A.  rewrite A. 
      rewrite E. 
      assert (fact5 := brel_transititivity_implies_dual _ _ tranT _ _ _ J F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 


      rewrite N. rewrite E. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      case_eq(rS (s1 *S (s2 +S s3)) ((s1 *S s2) +S (s1 *S s3))); intro K; auto.    
      assert (fact1 := commT (t1 *T t2) (t1 *T t3)). 
      apply (brel_symmetric_implies_dual _ _ symT) in J.
      assert (fact2 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact1 J). 
      apply (brel_symmetric_implies_dual _ _ symT).             
      assumption. 
Defined.  



Lemma bop_llex_product_not_left_distributive_v3_weak : 
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → (* NB *) 
      bop_not_left_cancellative_weak S rS mulS → bop_not_left_constant T rT mulT → 
            bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros selS commS commT  [ [s1 [s2 s3 ] ] [[E N] _] ] [ [t1 [ t2 t3 ]] F].
exists(cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3 addS addT mulT). 
unfold cef_llex_product_not_left_distributive. 
destruct(selS s2 s3) as [H | H]. 
   case_eq(rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))); intro J; simpl. 

      rewrite H. simpl. 
      apply andb_is_false_right. right.    
      rewrite N. compute. 
      apply symS in H. rewrite N, E, H.  
      assert (fact1 := commT (t1 *T t2) (t1 *T t3)). 
      assert (fact2 := tranT _ _ _ J fact1). 
      assert (fact3 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact2 F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite H; compute.           
      apply andb_is_false_right. right.    
      apply symS in H. rewrite N, E, H. 
      assumption. 

   assert (A : rS (s2 +S s3) s2 = false).  
       apply (brel_symmetric_implies_dual _ _ symS) in N.
       apply symS in H. 
       apply (brel_transititivity_implies_dual _ _ tranS _ _ _ H N). 

   case_eq(rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))); intro J; rewrite A; compute. 
      apply andb_is_false_right. right.  rewrite N.
      apply (brel_symmetric_implies_dual _ _ symS) in A.  rewrite A. 
      rewrite E. 
      assert (fact5 := brel_transititivity_implies_dual _ _ tranT _ _ _ J F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 


      rewrite N. rewrite E. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      case_eq(rS (s1 *S (s2 +S s3)) ((s1 *S s2) +S (s1 *S s3))); intro K; auto.    
      assert (fact1 := commT (t1 *T t2) (t1 *T t3)). 
      apply (brel_symmetric_implies_dual _ _ symT) in J.
      assert (fact2 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact1 J). 
      apply (brel_symmetric_implies_dual _ _ symT).             
      assumption. 
Defined.  



Lemma bop_llex_product_right_distributive : 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
      ((bop_right_cancellative S rS mulS) + (bop_right_constant T rT mulT)) → 
         bop_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT D [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       case_eq(rS s2 s3); intro H1; 
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s2 *S s1) (s3 *S s1)); intro H3; 
       case_eq(rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))); intro H4; simpl. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          assert(fact := m_conS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          assert(fact := m_conS _ _ _ _ H1 (refS s1)). rewrite fact in H3. discriminate. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          apply refT. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). 
             assert (fact2 := m_conS _ _ _ _ H2 (refS s1)).
             assert (fact3 := tranS _ _ _ fact2 fact1). 
             rewrite fact3 in H4. discriminate. 
             apply K. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). apply symS in fact1. 
             assert (fact2 := tranS _ _ _ H4 fact1). 
             apply C in fact2. 
             rewrite fact2 in H2. discriminate. 
             apply K. 
          apply refT. 
Defined. 

Lemma bop_llex_product_not_right_distributive_v1 : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 


Lemma bop_llex_product_not_right_distributive_v2 : 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS wS). rewrite (refS (mulS wS wS)). 
       assumption. 
Defined. 


Lemma bop_llex_product_not_right_distributive_v3: 
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → bop_not_right_cancellative S rS mulS → 
      bop_not_right_constant T rT mulT → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros selS commS commT [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
exists(cef_llex_product_not_right_distributive rS rT s1 s2 s3 t1 t2 t3 addS addT mulT). 
unfold cef_llex_product_not_right_distributive. 
destruct(selS s2 s3) as [H | H]. 
   case_eq(rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))); intro J; simpl. 

      rewrite H. simpl. 
      apply andb_is_false_right. right.    
      apply symS in H. 
      rewrite N; compute. rewrite H, E.  rewrite N. 
      assert (fact1 := commT (t2 *T t1) (t3 *T t1)). 
      assert (fact2 := tranT _ _ _ J fact1). 
      assert (fact3 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact2 F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite H; compute.           
      apply andb_is_false_right. right.    
      apply symS in H. rewrite N, E, H. 
      assumption. 

   assert (A : rS (s2 +S s3) s2 = false).
       apply (brel_symmetric_implies_dual _ _ symS) in N.
       apply symS in H. 
       apply (brel_transititivity_implies_dual _ _ tranS _ _ _ H N). 
   case_eq(rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))); intro J; simpl; rewrite A; compute. 

      apply andb_is_false_right. right.    
      rewrite N. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      rewrite E. 
      assert (fact5 := brel_transititivity_implies_dual _ _ tranT _ _ _ J F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite N. rewrite E. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      case_eq(rS ((s2 +S s3) *S s1) ((s2 *S s1) +S (s3 *S s1))); intro K; auto.    
      assert (fact1 := commT (t2 *T t1) (t3 *T t1)). 
      apply (brel_symmetric_implies_dual _ _ symT) in J.
      assert (fact2 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact1 J). 
      apply (brel_symmetric_implies_dual _ _ symT).             
      assumption. 
Defined.

Lemma bops_llex_product_not_left_distributive_left : 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. rewrite nd.  simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_left_distributive_right : 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl.
       rewrite (refS wS). rewrite (refS (mulS wS wS)). rewrite nd.  apply andb_comm. 
Defined. 


Lemma bops_llex_product_not_right_distributive_left : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. rewrite nd.  simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_right_distributive_right :   
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) . 
Proof. intros [ [t1 [t2 t3] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite (refS wS). rewrite (refS (wS *S wS)). 
       rewrite nd.  apply andb_comm. 
Defined. 


Lemma bops_llex_product_id_equals_ann : 
      bop_commutative S rS addS → bops_id_equals_ann S rS addS mulS → bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros commS [iS [piS paS]] [iT [piT paT]]. 
       exists (iS, iT). split.
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto.        
Defined. 



Lemma bops_product_llex_id_equals_ann : 
      bop_commutative S rS addS → bops_id_equals_ann S rS mulS addS  → 
      bops_id_equals_ann T rT mulT addT  → 
      bops_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. intros commS [iS [piS paS]] [iT [piT paT]]. 
       exists (iS, iT). split.
       apply bop_product_is_id; auto.               
       apply bop_llex_is_ann; auto.
Defined. 

Lemma bops_llex_product_not_id_equals_ann_left : 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H s) as [ [s' [L | R]] | [s' [L | R]] ].
       left. exists (s', t). compute. rewrite L. left. reflexivity.
       left. exists (s', t). compute. rewrite R. right. reflexivity.   
       right. exists (s', t). compute. rewrite L. left. reflexivity.
       right. exists (s', t). compute. rewrite R. right. reflexivity.   
Defined. 

Lemma bops_llex_product_not_id_equals_ann_right : 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H t) as [ [t' [L | R]] | [t' [L | R]] ].
       left. exists (s, t'). compute. case_eq(rS (s +S s) s); intro J. rewrite refS. rewrite L. left; auto. left; auto. 
       left. exists (s, t'). compute. case_eq(rS (s +S s) s); intro J. rewrite refS. rewrite R. right; auto. left; auto. 
       right. exists (s, t'). compute. case_eq(rS (s *S s) s); intro J. rewrite L. left; auto. left; auto. 
       right. exists (s, t'). compute. case_eq(rS (s *S s) s); intro J. rewrite R. right; auto. left; auto. 
Defined. 


Lemma bops_product_llex_not_id_equals_ann_left : 
      bops_not_id_equals_ann S rS mulS addS → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT). 
Proof. unfold bops_not_id_equals_ann. intros H [s t]. 
       destruct (H s) as [ [s' [L| R] ] | [s' [L | R]] ].
       left. exists (s', t). compute. rewrite L. left. reflexivity.
       left. exists (s', t). compute. rewrite R. right. reflexivity.
       right. exists (s', t). compute. rewrite L. left. reflexivity.
       right. exists (s', t). compute. rewrite R. right. reflexivity.              
Defined. 

Lemma bops_product_llex_not_id_equals_ann_right :
      bop_idempotent S rS addS → (* NB *) 
      bops_not_id_equals_ann T rT mulT addT → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT). 
Proof. unfold bops_not_id_equals_ann. intros idemS H [s t]. 
       destruct (H t) as [ [t' [L| R] ] | [t' [L | R]] ].
       left. exists (s, t'). compute. rewrite L. case(rS (s *S s) s); left; reflexivity.
       left. exists (s, t'). compute. rewrite R. case(rS (s *S s) s); right; reflexivity.
       right. exists (s, t'). compute. rewrite (idemS s). rewrite refS. rewrite L. left. reflexivity.
       right. exists (s, t'). compute. rewrite (idemS s). rewrite refS. rewrite R. right. reflexivity.
Defined. 

       
(* absorption *) 

(* left left *) 

Lemma bops_llex_product_left_left_absorptive : 
      bops_left_left_absorptive S rS addS mulS → 
      ((bops_left_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
         bops_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2].
       simpl. 
       unfold bops_left_left_absorptive in ldS. 
       unfold bops_left_left_absorptive in ldT. 
       rewrite ldS. simpl. 
       case_eq(rS s1 (s1 *S s2)); intro H. 
          apply ldT.
          compute.  rewrite ldS. rewrite H. 
          apply refT. 
       compute. 
       rewrite ldS. rewrite F. rewrite F. 
       apply refT. 
Defined. 

Lemma bops_llex_product_not_left_left_absorptive_left : 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_left_left_absorptive_right : 
      bops_left_left_absorptive S rS addS mulS → bops_not_left_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  →
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]. exists ((s1, t1), (s2, t2)). compute. rewrite laS. rewrite Q. assumption. Defined. 

(* left right *) 
Lemma bops_llex_product_left_right_absorptive :
      bops_left_right_absorptive S rS addS mulS → 
      ((bops_left_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
         bops_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2].
       simpl. 
       unfold bops_left_right_absorptive in ldS. 
       unfold bops_left_right_absorptive in ldT.
       compute.  
       rewrite ldS. 
       case_eq(rS s1 (s2 *S s1)); intro H. 
          apply ldT.
          apply refT. 
       compute. 
       rewrite ldS. rewrite F. rewrite F. 
       apply refT. 
Defined. 

Lemma bops_llex_product_not_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_left_right_absorptive_right : 
      bops_left_right_absorptive S rS addS mulS → bops_not_left_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q] . exists ((s1, t1), (s2, t2)). compute. rewrite laS. rewrite Q. assumption. Defined. 

(* right left *) 
Lemma bops_llex_product_right_left_absorptive : 
      bops_right_left_absorptive S rS addS mulS → 
      ((bops_right_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
         bops_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       unfold bops_right_left_absorptive in ldS. 
       unfold bops_right_left_absorptive in ldT. 
       rewrite ldS. 
       case_eq(rS (s1 *S s2) s1); intro H. 
          apply ldT. 
          case_eq(rS (s1 *S s2) ((s1 *S s2) +S s1)) ; intro K. 
             assert (fact1 := ldS s1 s2). apply symS in fact1. 
             assert (fact2 := tranS _ _ _ K fact1).            
             rewrite fact2 in H. discriminate. 
             apply refT. 
       unfold bops_right_left_absorptive in ldS. 
       unfold bop_anti_left in F.
       assert (F' : ∀ s t : S, rS (s *S t) s = false). 
          intros s t. apply (brel_symmetric_implies_dual _ _ symS). apply F. 
       rewrite ldS, F'. 
       assert (L : rS (s1 *S s2) ((s1 *S s2) +S s1) = false). 
          assert (fact1 := ldS s1 s2).
          assert (fact2 := F s1 s2). 
          assert (fact3 := brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 fact2). 
          apply (brel_symmetric_implies_dual _ _ symS).  assumption. 
       rewrite L. apply refT. 
Defined. 


Lemma bops_llex_product_not_right_left_absorptive_left : 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_right_left_absorptive_right : 
      bops_right_left_absorptive S rS addS mulS → bops_not_right_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]. exists ((s1, t1), (s2, t2)). compute. rewrite laS. apply symS in Q. rewrite Q. 
       assumption. 
Defined. 


(* right_right *) 
Lemma bops_llex_product_right_right_absorptive : 
      bops_right_right_absorptive S rS addS mulS → 
      ((bops_right_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
         bops_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros laS [laT| F] [s1 t1] [s2 t2]; simpl. 
       unfold bops_right_right_absorptive in laS. 
       unfold bops_right_right_absorptive in laT. 
       rewrite laS. simpl. 
       case_eq(rS (s2 *S s1) s1); intro H1. 
          apply laT.
          compute.  
          case_eq(rS (s2 *S s1) ((s2 *S s1) +S s1)); intro H2. 
             rewrite H1.  
             assert (fact1 := laS s1 s2). apply symS in fact1. 
             assert (fact2 := tranS _ _ _ H2 fact1). 
             rewrite fact2 in H1. discriminate. 
             apply refT. 
          unfold bops_right_right_absorptive in laS. 
          unfold bop_anti_right in F. 
          compute. 
          rewrite laS. simpl. 
          assert (fact1 := F s1 s2). apply (brel_symmetric_implies_dual _ _ symS) in fact1. 
          rewrite fact1. 
          case_eq (rS (s2 *S s1) ((s2 *S s1) +S s1)); intro H. 
             assert (fact2 := laS s1 s2). apply symS in fact2. 
             assert (fact3 := tranS _ _ _ H fact2). rewrite fact3 in fact1. discriminate. 
             apply refT. 
Defined. 

Lemma bops_llex_product_not_right_right_absorptive_left : 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_right_right_absorptive_right : 
      bops_right_right_absorptive S rS addS mulS → bops_not_right_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q] . exists ((s1, t1), (s2, t2)). 
       compute. rewrite laS. apply symS in Q. rewrite Q. assumption. 
Defined. 



(* Decide *) 

Definition bops_llex_product_left_distributive_decide : 
      bop_selective S rS addS  →      (* NB *) 
      bop_commutative S rS addS  →    (* NB *) 
      bop_commutative T rT addT  →    (* NB *) 
      bop_left_cancellative_decidable S rS mulS  → 
      bop_left_constant_decidable T rT mulT → 
      bop_left_distributive_decidable S rS addS mulS → 
      bop_left_distributive_decidable T rT addT mulT → 
         bop_left_distributive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT)
:= λ selS commS commT lcS_d lkT_d ldS_d ldT_d, 
match ldS_d with 
|inl ldS =>
   match ldT_d with 
   |inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (bop_llex_product_left_distributive ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_llex_product_left_distributive ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_llex_product_not_left_distributive_v3 selS commS commT not_lcS not_lkT)
                                     
            end 
       end 
   |inr not_ldT => inr _ (bop_llex_product_not_left_distributive_v2 not_ldT)
   end 
|inr not_ldS => inr _ (bop_llex_product_not_left_distributive_v1 not_ldS ) 
end. 

Definition bops_llex_product_right_distributive_decide : 
      bop_selective S rS addS  →      (* NB *) 
      bop_commutative S rS addS  →    (* NB *) 
      bop_commutative T rT addT  →    (* NB *) 
      bop_right_cancellative_decidable S rS mulS  → 
      bop_right_constant_decidable T rT mulT → 
      bop_right_distributive_decidable S rS addS mulS → 
      bop_right_distributive_decidable T rT addT mulT → 
         bop_right_distributive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT)
:= λ selS commS commT lcS_d lkT_d ldS_d ldT_d, 
match ldS_d with 
|inl ldS =>
   match ldT_d with 
   |inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (bop_llex_product_right_distributive ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_llex_product_right_distributive ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_llex_product_not_right_distributive_v3 selS commS commT not_lcS not_lkT)
            end 
       end 
   |inr not_ldT => inr _ (bop_llex_product_not_right_distributive_v2 not_ldT)
   end 
|inr not_ldS => inr _ (bop_llex_product_not_right_distributive_v1 not_ldS)
end. 


(*
 LA(S) -> 
          LA(T) -> (LA(T) | nQ) -> LA(lex, product) 
          nLA(T) -> 
             nQ  -> (LA(T) | nQ) -> LA(lex, product) 
              Q -> (nLA(T) & Q) -> nLA(lex, product) 
nLA(S) -> nLA(lex, product) 

*)
Definition bops_llex_product_left_left_absorptive_decide : 
      bops_left_left_absorptive_decidable S rS addS mulS → 
      bops_left_left_absorptive_decidable T rT addT mulT → 
      bop_anti_left_decidable S rS mulS → 
         bops_left_left_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_left_left_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_left_left_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_left_left_absorptive_right laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_left_left_absorptive_left not_laS) 
end. 

Definition bops_llex_product_left_right_absorptive_decide : 
      bops_left_right_absorptive_decidable S rS addS mulS → 
      bops_left_right_absorptive_decidable T rT addT mulT → 
      bop_anti_right_decidable S rS mulS → 
         bops_left_right_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_left_right_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_left_right_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_left_right_absorptive_right laS not_laT not_antilS )
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_left_right_absorptive_left not_laS ) 
end. 

Definition bops_llex_product_right_left_absorptive_decide : 
      bops_right_left_absorptive_decidable S rS addS mulS → 
      bops_right_left_absorptive_decidable T rT addT mulT → 
      bop_anti_left_decidable S rS mulS → 
         bops_right_left_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_right_left_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_right_left_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_right_left_absorptive_right laS not_laT not_antilS )
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_right_left_absorptive_left not_laS ) 
end. 

Definition bops_llex_product_right_right_absorptive_decide : 
      bops_right_right_absorptive_decidable S rS addS mulS → 
      bops_right_right_absorptive_decidable T rT addT mulT → 
      bop_anti_right_decidable S rS mulS → 
         bops_right_right_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_right_right_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_right_right_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_right_right_absorptive_right laS not_laT not_antilS )
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_right_right_absorptive_left not_laS ) 
end.


Definition bops_llex_product_id_equals_ann_decide : 
      bop_commutative S rS addS  →
      bops_id_equals_ann_decidable S rS addS mulS → 
      bops_id_equals_ann_decidable T rT addT mulT →  
        bops_id_equals_ann_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT)
 := λ commS dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bops_llex_product_id_equals_ann commS ieaS ieaT)
     | inr nieaT => inr _ (bops_llex_product_not_id_equals_ann_right nieaT)
     end 
   | inr nieaS   => inr _ (bops_llex_product_not_id_equals_ann_left nieaS)
   end. 


Definition bops_product_llex_id_equals_ann_decide : 
  bop_commutative S rS addS  →
  bop_idempotent S rS addS  →
  bops_id_equals_ann_decidable S rS mulS addS  → 
  bops_id_equals_ann_decidable T rT mulT addT  →  
        bops_id_equals_ann_decidable (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT) 
:= λ commS idemS dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bops_product_llex_id_equals_ann commS ieaS ieaT)
     | inr nieaT => inr _ (bops_product_llex_not_id_equals_ann_right idemS nieaT)
     end 
   | inr nieaS   => inr _ (bops_product_llex_not_id_equals_ann_left nieaS)
   end. 

End LlexProduct. 