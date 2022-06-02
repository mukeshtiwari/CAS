Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.theory.

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures. 
Require Import CAS.coq.tr.left.product. 

Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.
Require Import CAS.coq.st.cast_up. 
From Coq Require Import String List.
Local Open Scope string_scope.
Import ListNotations.




(* why? *) 
Definition ltr_weak_congruence (L S : Type) (rS : brel S) (lt : ltr_type L S) := 
   ∀ (l : L) (s1 s2 : S), rS s1 s2 = true -> rS (lt l s1) (lt l s2) = true.


Section Theory.

Variable LS : Type.     
Variable S  : Type.
Variable LT : Type. 
Variable T  : Type.

Variable eqLS : brel LS. 
Variable eqLT : brel LT.

Variable eqS : brel S. 
Variable eqT : brel T.

Variable argT : T.  (* for llex product *) 
Variable wS : S. 
Variable wT : T.

Variable wLS : LS. 
Variable wLT : LT.

Variable addS : binary_op S. 
Variable addT : binary_op T.

Variable ltrS : ltr_type LS S.
Variable ltrT : ltr_type LT T. 

Variable conS : brel_congruence S eqS eqS. 
Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.  
Variable trnS : brel_transitive S eqS.

Variable conT : brel_congruence T eqT eqT. 
Variable refT : brel_reflexive T eqT.
Variable symT : brel_symmetric T eqT.  
Variable trnT : brel_transitive T eqT.

Variable refLS : brel_reflexive LS eqLS.
Variable refLT : brel_reflexive LT eqLT.


Variable a_conS : bop_congruence S eqS addS.
Variable a_conT : bop_congruence T eqT addT.

(*
Variable m_conS : ltr_weak_congruence LS S rS mulS.
Variable m_conT : ltr_weak_congruence LT T rT mulT. 
 *)

Variable m_conS : ltr_congruence LS S eqLS eqS ltrS.
Variable m_conT : ltr_congruence LT T eqLT eqT ltrT.

Variable a_commS : bop_commutative S eqS addS.
Variable a_idemS : bop_idempotent S eqS addS.


Notation "a =S b"  := (eqS a b = true) (at level 15).
Notation "a =T b"  := (eqT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a |S> b"  := (ltrS a b) (at level 15).
Notation "a |T> b"  := (ltrT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [+] b" := (bop_llex argT eqS a b) (at level 15).
Notation "a [*] b" := (ltr_product a b) (at level 15).

(* Note : this is a minor modification of the proof from bs/llex_product.v .... *) 
Lemma slt_llex_product_distributive
      (selS_or_annT : bop_selective S eqS addS + ltr_is_ann LT T eqT ltrT argT)      
      (ldS : slt_distributive eqS addS ltrS)
      (ldT : slt_distributive eqT addT ltrT) 
      (D : ((ltr_left_cancellative LS S eqS ltrS) + (ltr_left_constant LT T eqT ltrT))): 
             slt_distributive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold ltr_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS.
       unfold llex_p2.
       case_eq(eqS s2 (s2 +S s3)); intro H2; 
       case_eq(eqS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))); intro H4; simpl. 
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + apply ldT. 
         + assert (F1 := trnS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 |S> s3)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 |S> s3)))). 
           assert (F5 := trnS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := trnS _ _ _ F1 H3). 
             apply LC in F2. 
             assert (F3 := trnS _ _ _ H2 F2).
             assert (F4 := conS _ _ _ _ (refS (s2 +S s3)) F3). 
             rewrite <- F4 in H1. apply symS in H2.
             rewrite H2 in H1. discriminate H1.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t2 (t2 +T t3)). 
             exact (trnT _ _ _ F2 F1). 
         + apply refT. 
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3.
         + assert (F1 := trnS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 |S> s2)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 |S> s2)) F3). apply symS in F2.
           assert (F5 := trnS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           rewrite (trnS _ _ _ F1 F2) in H3. discriminate H3.            
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := trnS _ _ _ F1 H3). 
             apply LC in F2. 
             rewrite F2 in H1. discriminate H1.
           * exact(LK t1 t2 t3). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H2).
           assert (F3 := trnS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := trnS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t3 (t2 +T t3)). 
             exact (trnT _ _ _ F2 F1). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           assert (F3 := trnS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := trnS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 argT (t2 +T t3)). 
             exact (trnT _ _ _ F2 F1).              
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := trnS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * exact (LK t1 argT t2). 
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3.
         + apply refT. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F2. 
           assert (F3 := trnS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := trnS _ _ _ F1 H3). 
             apply LC in F2.
             rewrite F2 in H1. discriminate H1.
           * exact (LK t1 argT t3). 
         + destruct selS_or_annT as [selS | argT_is_annT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * exact (argT_is_annT t1). 
Qed. 


Lemma slt_llex_product_not_distributive_v1 : 
      slt_not_distributive eqS addS ltrS → slt_not_distributive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wLT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 

Lemma slt_llex_product_not_distributive_v2 (dS : slt_distributive eqS addS ltrS): 
  slt_not_distributive eqT addT ltrT → slt_not_distributive  (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wLS, t1), ((wS, t2), (wS, t3))); simpl.        
       unfold brel_product, llex_p2.
       apply bop_and_false_intro. right. 
       assert (F1 := a_idemS wS). rewrite F1. apply symS in F1. rewrite F1. 
       assert (A : eqS (wLS |S> wS) ((wLS |S> wS) +S (wLS |S> wS)) = true). 
          assert (B := dS wLS wS wS). 
          assert (C := m_conS _ _ _ _ (refLS wLS) F1).
          exact (trnS _ _ _ C B).
       rewrite A. apply symS in A. rewrite A. 
       exact nld. 
Defined.


(* see cases 1-4 in the proof below *) 

Definition A_witness_slt_llex_product_not_left_distributive
      (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
      (s1 : LS) (s2 s3 : S)
      (t1 : LT) (t2 t3 : T)
:= if (eqS (s2 +S s3) s2) 
   then if eqS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if eqS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))
              then (* case 1 *) 
                   if eqT (t1 |T> t2) ((t1 |T> t2) +T (t1 |T> t3))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if eqS (s2 +S s3) s3
        then (* case 3 *) 
             if eqT (t1 |T> t3) ((t1 |T> t2) +T (t1 |T> t3))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => if eqT argT (t1 |T> t2)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             end.   

(* for use in CAS 
Definition witness_slt_llex_product_not_left_distributive_new
      (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T))
      (s1 : LS) (s2 s3 : S)
      (t1 : LT) (t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))
              then (* case 1 *) 
                   if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => if rT argT (t1 *T t2)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             end.   

*) 
Lemma slt_llex_product_not_distributive_v3
      (a_commT : bop_commutative T eqT addT) (*NB*)
      (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
      (ldS : slt_distributive eqS addS ltrS)
      (ldT : slt_distributive eqT addT ltrT) : 
      ltr_not_left_cancellative LS S eqS ltrS →
      ltr_not_left_constant LT T eqT ltrT → 
         slt_not_distributive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(A_witness_slt_llex_product_not_left_distributive selS_or_id_annT s1 s2 s3 t1 t2 t3). 
       unfold A_witness_slt_llex_product_not_left_distributive. 
       unfold ltr_product, brel_product, bop_llex.        
       case_eq(eqS s2 (s2 +S s3)); intro H2; 
       case_eq(eqS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))); intro H4; simpl. 
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + rewrite (trnS _ _ _ H2 H1) in N. discriminate N. 
         + assert (F1 := trnS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 |S> s3)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 |S> s3)))). 
           assert (F5 := trnS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + (* ============= case 1 ======================
              E : (s1 |S> s2) =S (s1 |S> s3)
              N : rS s2 s3 = false
              F : rT (t1 |T> t2) (t1 |T> t3) = false

             H2 : s2 =S (s2 +S s3)
             H4 : (s1 |S> s2) =S ((s1 |S> s2) +S (s1 |S> s3))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s1 |S> s2) +S (s1 |S> s3)) =S (s1 |S> s3)
             ===========need=================
             rT (a *T b) ((a *T b) +T (a *T c)) = false

             if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
             then (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     b     a     c       a     b    (use a_commT  !!!) 

             else (t1 *T t2) ((t1 *T t2) +T (t1 *T t3)) = false
                   a      b     a     b      a     c 
           *) 
           unfold llex_p2. rewrite (symS _ _ H2).
           case_eq(eqT (t1 |T> t2) ((t1 |T> t2) +T (t1 |T> t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(eqT (t1 |T> t3) ((t1 |T> t3) +T (t1 |T> t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 |T> t3) (t1 |T> t2)). 
                assert (F4 := trnT _ _ _ F2 F3). apply symT in F4. 
                rewrite (trnT _ _ _ F1 F4) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + apply symS in E.
           assert (F1 := trnS _ _ _ E H4). apply symS in F1. 
           rewrite F1 in H3. discriminate H3. 
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + assert (F1 := trnS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 |S> s2)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 |S> s2)) F3). apply symS in F2.
           assert (F5 := trnS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           rewrite (trnS _ _ _ F1 F2) in H3. discriminate H3.            
         + (* ===============case 2==============================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

             H2 : s2 =S (s2 +S s3)
             H4 : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
             ==========need==================
             rT (a *T b) (a *T c) = false
             so use F: 
             rT (t1 *T t2) (t1 *T t3) = false
                 a     b    c     d 
           *)
           unfold llex_p2. rewrite (symS _ _ H2). rewrite H2. 
           apply bop_and_false_intro. right. rewrite H1, H4, H3. 
           exact F. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H2).
           assert (F3 := trnS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + (* ==================case 3=========================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

              H2 : rS s2 (s2 +S s3) = false
              H4 : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
              H1 : (s2 +S s3) =S s3
              H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
              ===========need=================
              rT (a *T c) ((a *T b) +T (a *T c)) = false

             if rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))
             then (t1 *T t2) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     c     a     c       a     b    (use a_commT !!!) 

             else (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     c      a     b       a     c 

           *) 
           assert (G : eqS (s2 +S s3) s2 = false).
              case_eq(eqS (s2 +S s3) s2); intro H; auto.
                apply symS in H. rewrite H in H2. discriminate H2.            
           unfold llex_p2. rewrite G. 
           case_eq(eqT (t1 |T> t3) ((t1 |T> t2) +T (t1 |T> t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(eqT (t1 |T> t2) ((t1 |T> t3) +T (t1 |T> t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 |T> t3) (t1 |T> t2)). 
                assert (F4 := trnT _ _ _ F2 F3). apply symT in F1. 
                rewrite (trnT _ _ _ F4 F1) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           assert (F3 := trnS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + (* =============case 4=================================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

              H2 : rS s2 (s2 +S s3) = false
              H4 : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
              H1 : rS (s2 +S s3) s3 = false
              H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
             =============need===============
              rT (a *T argT) ((a *T b) +T (a *T c)) = false
  
             case split: 
             selective(+S) : contradiction with H1 H2. 
             
             argT is id for +T and is ann for *T: 
             =============need===============
             rT argT ((a *T b) +T (a *T c)) = false
             
             let b = argT. so  ((a *T b) +T (a *T c)) =T (a *T c). 

             =============need===============
             rT argT (a *T c) = false

             if argT = (t1 *T t2)
             then let (a *T c) = (t1 *T t3)
             else let (a *T c) = (t1 *T t2)
           *)
           destruct selS_or_id_annT as [selS | [idT annT]].
           * destruct (selS s2 s3) as [F1 | F1]. 
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1.
           * assert (G : eqS (s2 +S s3) s2 = false).
             case_eq(eqS (s2 +S s3) s2); intro H; auto.
             apply symS in H. rewrite H in H2. discriminate H2.
             unfold llex_p2. rewrite G.
             case_eq(eqT argT (t1 |T> t2)); intro F6.
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4. 
                assert (F2 := annT t1).
                destruct (idT (t1 |T> t3)) as [F3 F4].                          
                assert (F5 : ((t1 |T> argT) +T (t1 |T> t3)) =T (t1 |T> t3)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 |T> t3))). 
                   exact (trnT _ _ _ F5 F3). 
                case_eq(eqT (t1 |T> argT) ((t1 |T> argT) +T (t1 |T> t3))); intro F7; auto.
                ++ assert (F8 := trnT _ _ _ F7 F5).
                   assert (F9 := trnT _ _ _ F2 F6). apply symT in F9. 
                   rewrite (trnT _ _ _ F9 F8) in F. discriminate F. 
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                assert (F2 := annT t1).
                destruct (idT (t1 |T> t2)) as [F3 F4].                                          
                assert (F5 : ((t1 |T> argT) +T (t1 |T> t2)) =T (t1 |T> t2)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 |T> t2))). 
                   exact (trnT _ _ _ F5 F3). 
                case_eq(eqT (t1 |T> argT) ((t1 |T> argT) +T (t1 |T> t2))); intro F7; auto.
                ++ assert (F8 := trnT _ _ _ F7 F5). apply symT in F2. 
                   rewrite (trnT _ _ _ F2 F8) in F6. discriminate F6. 
         + apply symS in E. assert (F1 := trnS _ _ _ E H4). 
           apply symS in F1. rewrite F1 in H3. discriminate H3. 
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + apply symS in E. assert (F1 := trnS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F2. 
           assert (F3 := trnS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + apply symS in E. assert (F1 := trnS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := a_idemS (s1 |S> s3)). 
           assert (F2 := a_conS _ _ _ _ E (refS (s1 |S> s3))). 
           assert (F3 := trnS _ _ _ F2 F1).
           rewrite F3 in H3. discriminate H3. 
Defined.



(* Absorption *)

(* compare to bs/llex_product.v 

   Here we have 
   absortive(S llex T) 
   <-> (strictly_absorptive S) + (absorptive(S) * absorptive(T))

   In bs we have 
   absortive(S llex T) 
   <-> (absorptive(S) * (absorptive(T) + anti_left(mulS)) 
   <-> (absorptive(S) * anti_left(mulS)) + (absorptive(S) * absorptive(T))
   where anti_left(mulS) = ∀ s t : S, eqS s (mulS s t) = false

 slt_strictly_absorptive: 
  ∀ (l : L) (s : S),
    (eqS s (add s (ltr l s)) = true) * (eqS (ltr l s) (add s (ltr l s)) = false)

  absorptive(S) * anti_left(mulS): 
  (∀ (l : L) (s : S), 
      eqS s (add s (ltr l s)) = true) * (∀ s t : S, eqS s (mulS s t) = false)
 *)

Lemma slt_llex_product_absorptive : 
      (slt_strictly_absorptive eqS addS ltrS) +  
      ((slt_absorptive eqS addS ltrS) * (slt_absorptive eqT addT ltrT)) → 
         slt_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [sabsS | [absS absT]].
       + intros [lS lT] [s t].
         destruct (sabsS lS s) as [A B]. compute. 
         rewrite A.
         case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro C.
         ++ apply symS in C. rewrite C in B. discriminate B. 
         ++ apply refT. 
       + intros [lS lT] [s t].
         assert (A := absS lS s).
         assert (B := absT lT t). compute.          
         rewrite A.
         case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro D.
         ++ exact B. 
         ++ apply refT. 
Qed. 

Lemma slt_llex_product_not_absorptive_left : 
      slt_not_absorptive eqS addS ltrS → 
         slt_not_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wLT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma slt_llex_product_not_absorptive_right : 
      (slt_not_strictly_absorptive eqS addS ltrS) *  
      ((slt_absorptive eqS addS ltrS) * (slt_not_absorptive eqT addT ltrT)) → 
         slt_not_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [[[lS s] A] [absS [[lT t] B]]]; compute.
       assert (C := absS lS s).
       exists ((lS, lT), (s, t)). rewrite C.
       destruct A as [A | A]. 
       + rewrite A in C. discriminate C. 
       + assert (D : eqS (s +S (lS |S> s)) (lS |S> s) = true).
            apply symS in C.
            assert (H := trnS _ _ _ A C). 
            assert (E := a_idemS (lS |S> s)).
            apply symS in H. 
            exact (trnS _ _ _ C H). 
        rewrite D.
         exact B. 
Defined.



Lemma slt_llex_product_strictly_absorptive : 
      (slt_strictly_absorptive eqS addS ltrS) +  
      ((slt_absorptive eqS addS ltrS) * (slt_strictly_absorptive eqT addT ltrT)) → 
         slt_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [sabsS | [absS sabsT]].
       + intros [lS lT] [s t].
         destruct (sabsS lS s) as [A B]. split; compute. 
         ++ rewrite A.
            case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro C.
            +++ apply symS in C. rewrite C in B. discriminate B. 
            +++ apply refT. 
         ++ rewrite A. rewrite B. reflexivity.
       + intros [lS lT] [s t].
         assert (A := absS lS s).
         destruct (sabsT lT t) as [B C]. split; compute.          
         ++ rewrite A.
            case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro D.
            +++ exact B. 
            +++ apply refT. 
         ++ rewrite A.
            case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro D.
            +++ apply symS in D. rewrite D. exact C.
            +++ case_eq(eqS (lS |S> s) (s +S (lS |S> s))); intro E. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
                ++++ reflexivity. 
Qed.


Lemma slt_llex_product_not_strictly_absorptive_left : 
      slt_not_absorptive eqS addS ltrS → 
         slt_not_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wLT), (s2, wT)). simpl. rewrite P. simpl. left. reflexivity. Defined. 


Lemma slt_llex_product_not_strictly_absorptive_right : 
      (slt_not_strictly_absorptive eqS addS ltrS) *  
      ((slt_absorptive eqS addS ltrS) * (slt_not_strictly_absorptive eqT addT ltrT)) → 
         slt_not_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [[[lS s] A] [absS [[lT t] B]]]; compute.
       assert (C := absS lS s).
       exists ((lS, lT), (s, t)). rewrite C.
       destruct A as [A | A]. 
       + rewrite A in C. discriminate C.          
       + rewrite A. 
        destruct B as [B | B].
         ++ left. apply symS in A. rewrite A. exact B. 
         ++ rewrite (symS _ _ A). right. exact B.
Qed.             

End Theory. 

Section ACAS.


Section Decide.

Variables (LS S LT T : Type)  
          (eqLS : brel LS)
          (eqLT : brel LT)
          (eqS : brel S)
          (eqT : brel T)
          (argT : T)
          (wLS : LS)
          (wLT : LT)                     
          (wS : S)
          (wT : T)           
          (eqvLS : eqv_proofs LS eqLS)
          (eqvLT : eqv_proofs LT eqLT)                     
          (eqvS : eqv_proofs S eqS)
          (eqvT : eqv_proofs T eqT)           
          (addS : binary_op S) 
          (addT : binary_op T)
          (idemS : bop_idempotent S eqS addS)
          (commS : bop_commutative S eqS addS)
          (commT : bop_commutative T eqT addT)                     
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T)
          (a_congS : bop_congruence S eqS addS)
          (a_congT : bop_congruence T eqT addT)
          (ltr_congS : ltr_congruence LS S eqLS eqS ltrS).                     

Definition slt_llex_product_distributive_decide
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (LDS_d : slt_distributive_decidable eqS addS ltrS)
           (LDT_d : slt_distributive_decidable eqT addT ltrT)
           (LCS_d : ltr_left_cancellative_decidable LS S eqS ltrS)
           (LKT_d : ltr_left_constant_decidable LT T eqT ltrT): 
  slt_distributive_decidable
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let congS := A_eqv_congruence _ _ eqvS in   
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
let symT := A_eqv_symmetric _ _ eqvT in
let trnT := A_eqv_transitive _ _ eqvT in
let refLS := A_eqv_reflexive _ _ eqvLS in
let selS_or_annT :=
    match selS_or_id_annT with
    | inl sel         => inl sel
    | inr (_, is_ann) => inr is_ann 
    end
in       
match LDS_d with
| inl LDS  =>
  match LDT_d with
  | inl LDT  =>
    match LCS_d with
    | inl LCS  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inl LCS))
    | inr nLCS =>
      match LKT_d with
      | inl LKT  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inr LKT))
      | inr nLKT => inr (slt_llex_product_not_distributive_v3 LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT refS symS trnS refT symT trnT refLS a_congS a_congT ltr_congS idemS commT selS_or_id_annT LDS LDT nLCS nLKT) 
      end 
    end 
  | inr nLDT => inr (slt_llex_product_not_distributive_v2 LS S LT T eqLS eqS eqT argT wS wLS addS addT ltrS ltrT symS trnS refLS ltr_congS idemS LDS nLDT)    
  end 
| inr nLDS => inr (slt_llex_product_not_distributive_v1 LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nLDS) 
end.     


Definition slt_llex_product_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable eqS addS ltrS)
           (absS_d : slt_absorptive_decidable eqS addS ltrS)
           (absT_d : slt_absorptive_decidable eqT addT ltrT) :
  slt_absorptive_decidable
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS trnS idemS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.     

Definition slt_llex_product_strictly_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable eqS addS ltrS)
           (absS_d : slt_absorptive_decidable eqS addS ltrS)
           (absT_d : slt_strictly_absorptive_decidable eqT addT ltrT) :
  slt_strictly_absorptive_decidable
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=    
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in  
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_strictly_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_strictly_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.

Definition slt_llex_product_proofs
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (QS : left_transform_proofs LS S eqS eqLS ltrS)
           (QT : left_transform_proofs LT T eqT eqLT ltrT)           
           (PS : slt_proofs eqS addS ltrS)
           (PT : slt_proofs eqT addT ltrT) : 
  slt_proofs 
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let DS_d := A_slt_distributive_d _ _ _ PS in
let DT_d := A_slt_distributive_d _ _ _ PT in
let CS_d := A_left_transform_left_cancellative_d _ _ _ _ _ QS in
let KT_d := A_left_transform_left_constant_d _ _ _ _ _ QT in
let asbS_d := A_slt_absorptive_d _ _ _ PS in
let asbT_d := A_slt_absorptive_d _ _ _ PT in
let sasbS_d := A_slt_strictly_absorptive_d _ _ _ PS in
let sasbT_d := A_slt_strictly_absorptive_d _ _ _ PT in
{|
  A_slt_distributive_d          := slt_llex_product_distributive_decide commT selS_or_id_annT DS_d DT_d CS_d KT_d 
; A_slt_absorptive_d            := slt_llex_product_absorptive_decide sasbS_d asbS_d asbT_d
; A_slt_strictly_absorptive_d   := slt_llex_product_strictly_absorptive_decide sasbS_d asbS_d sasbT_d
|}.


Definition bops_llex_product_exists_id_ann_decide :
    forall (L₁ S₁ L₂ S₂ : Type)
      (l₁ : L₁)
      (l₂ : L₂)
      (s₁ : S₁)
      (s₂ : S₂)
      (brelL₁ : brel L₁)
      (brelL₂ : brel L₂) 
      (brelS₁ : brel S₁)
      (brelS₂ : brel S₂)
      (eqv_proofL₁ : eqv_proofs L₁ brelL₁)
      (eqv_proofL₂ : eqv_proofs L₂ brelL₂)
      (eqv_proofS₁ : eqv_proofs S₁ brelS₁)
      (eqv_proofS₂ : eqv_proofs S₂ brelS₂)
      (bopS₁ : binary_op S₁)
      (bopS₂ : binary_op S₂)
      (ltr₁ : ltr_type L₁ S₁)
      (ltr₂ : ltr_type L₂ S₂),
    slt_exists_id_ann_decidable brelS₁ bopS₁ ltr₁ ->
    slt_exists_id_ann_decidable brelS₂ bopS₂ ltr₂ ->
    slt_exists_id_ann_decidable
      (brel_product brelS₁ brelS₂)
      (bop_llex s₂ brelS₁ bopS₁ bopS₂) 
      (ltr_product ltr₁ ltr₂).
  Proof.
    intros * ? ? ? ? ? ? ? ? 
      Ha Hb Hc Hd ? ? ? ? H.
    refine 
    (match H with
      | SLT_Id_Ann_Proof_None _ _ _ (pa, pb) => fun Hlt => _ 
      | SLT_Id_Ann_Proof_Id_None _ _ _ (pa, pb) => fun Hlt => 
          match Hlt with 
          | SLT_Id_Ann_Proof_None _ _ _ (qa, qb)  => _ 
          | SLT_Id_Ann_Proof_Id_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_None_Ann _ _ _ (qa, qb) => _
          | SLT_Id_Ann_Proof_Equal _ _ _ q  => _ 
          | SLT_Id_Ann_Proof_Not_Equal _ _ _ q => _
          end
      | SLT_Id_Ann_Proof_None_Ann _ _ _ (pa, pb) => fun Hlt => 
          match Hlt with 
          | SLT_Id_Ann_Proof_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_Id_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_None_Ann _ _ _ (qa, qb) => _
          | SLT_Id_Ann_Proof_Equal _ _ _ q => _ 
          | SLT_Id_Ann_Proof_Not_Equal _ _ _ q => _
          end
      | SLT_Id_Ann_Proof_Equal _ _ _ p => fun Hlt => 
          match Hlt with 
          | SLT_Id_Ann_Proof_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_Id_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_None_Ann _ _ _ (qa, qb) => _
          | SLT_Id_Ann_Proof_Equal _ _ _ q => _ 
          | SLT_Id_Ann_Proof_Not_Equal _ _ _ q => _
          end
      | SLT_Id_Ann_Proof_Not_Equal _ _ _ p => fun Hlt => 
          match Hlt with 
          | SLT_Id_Ann_Proof_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_Id_None _ _ _ (qa, qb) => _ 
          | SLT_Id_Ann_Proof_None_Ann _ _ _ (qa, qb) => _
          | SLT_Id_Ann_Proof_Equal _ _ _ q  => _ 
          | SLT_Id_Ann_Proof_Not_Equal _ _ _ q => _
          end
      end).
      + clear p. 
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_left.
        exact pa.
        eapply ltr_product_not_exists_ann_left.
        exact l₂.
        exact pb.
      + clear p; clear p0.
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_right.
        destruct Hc; try assumption.
        exact qa.
        eapply ltr_product_not_exists_ann_left.
        exact l₂.
        exact pb.
      + clear p; clear p0.
        eapply SLT_Id_Ann_Proof_Id_None; split.
        eapply bop_llex_exists_id; 
        destruct Hc, Hd; try assumption.
        eapply ltr_product_not_exists_ann_left.
        exact l₂.
        exact pb.
      + clear p; clear p0.
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_right;
        destruct Hc; try assumption.
        eapply ltr_product_not_exists_ann_left.
        exact l₂.
        exact pb.
      + clear p.
        eapply SLT_Id_Ann_Proof_Id_None; split.
        destruct q as (x & p₁ & p₂).
        eapply bop_llex_exists_id;
        destruct Hc, Hd; try assumption.
        exists x; exact p₁.
        eapply ltr_product_not_exists_ann_left.
        exact l₂.
        exact pb.
      + clear p.
        eapply SLT_Id_Ann_Proof_Id_None; split.
        destruct q as ((x, y) & (p₁, p₂) & p₃).
        eapply bop_llex_exists_id;
        destruct Hc, Hd; try assumption.
        exists x; exact p₁.
        eapply ltr_product_not_exists_ann_left.
        exact l₂.
        exact pb.
      + clear p; clear p0.
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_right;
        destruct Hc; try assumption.
        eapply ltr_product_not_exists_ann_right.
        exact l₁.
        exact qb.
      + clear p; clear p0.
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_left;
        destruct Hc; try assumption.
        eapply ltr_product_not_exists_ann_right.
        exact l₁.
        exact qb. 
      + clear p; clear p0.
        eapply SLT_Id_Ann_Proof_None_Ann; split.
        eapply bop_llex_not_exists_id_left;
        destruct Hc; try assumption.
        eapply ltr_product_exists_ann;
        try assumption.
      + clear p.
        eapply SLT_Id_Ann_Proof_None_Ann; split.
        eapply bop_llex_not_exists_id_left;
        destruct Hc; try assumption.
        eapply ltr_product_exists_ann;
        try assumption.
        destruct q as (x & p₁ & p₂).
        exists x; exact p₂.
      + clear p.
        eapply SLT_Id_Ann_Proof_None_Ann; split.
        eapply bop_llex_not_exists_id_left;
        destruct Hc; try assumption.
        eapply ltr_product_exists_ann;
        try assumption.
        destruct q as ((x, y) & (p₁, p₂) & p₃).
        exists y; exact p₂.
      + clear p0.
        destruct p as (x & p₁ & p₂).
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_right;
        destruct Hc; try assumption.
        eapply ltr_product_not_exists_ann_right.
        exact l₁.
        exact qb.
      + clear p0.
        destruct p as (x & p₁ & p₂).
        eapply SLT_Id_Ann_Proof_Id_None; split.
        eapply bop_llex_exists_id;
        destruct Hc, Hd; try assumption.
        exists x; exact p₁.
        eapply ltr_product_not_exists_ann_right.
        exact l₁.
        exact qb.
      + clear p0.
        destruct p as (x & p₁ & p₂).
        eapply SLT_Id_Ann_Proof_None_Ann; split.
        eapply bop_llex_not_exists_id_right;
        destruct Hc; try assumption.
        eapply ltr_product_exists_ann;
        try assumption.
        exists x; exact p₂.
      + eapply SLT_Id_Ann_Proof_Equal. 
        destruct p as (x & p₁ & p₂).
        destruct q as (y & q₁ & q₂).
        exists (x, y); split.
        eapply bop_llex_is_id; 
        destruct Hc, Hd; 
        try assumption.
        eapply ltr_product_is_ann;
        try assumption.
      + eapply SLT_Id_Ann_Proof_Not_Equal.
        unfold slt_exists_id_ann_not_equal.
        destruct p as (px & p₁ & p₂).
        destruct q as ((qx, qy) & (q₁, q₂) & q₃).
        exists ((px, qx), (px, qy)).
        split.
        split.
        eapply bop_llex_is_id;
        destruct Hc, Hd; 
        try assumption.
        eapply ltr_product_is_ann;
        try assumption.
        simpl; rewrite q₃; 
        apply andb_false_r.
      + clear p0. 
        eapply SLT_Id_Ann_Proof_None; split.
        eapply bop_llex_not_exists_id_right;
        destruct Hc; try assumption.
        eapply ltr_product_not_exists_ann_right.
        exact l₁.
        exact qb.
      + clear p0.
        eapply SLT_Id_Ann_Proof_Id_None; split.
        destruct p as ((x, y) & (p₁, p₂) & p₃).
        eapply bop_llex_exists_id;
        destruct Hc, Hd; try assumption.
        exists x; exact p₁.
        eapply ltr_product_not_exists_ann_right.
        exact l₁.
        exact qb.
      + clear p0.
        eapply SLT_Id_Ann_Proof_None_Ann; split.
        eapply bop_llex_not_exists_id_right;
        destruct Hc; try assumption.
        eapply ltr_product_exists_ann;
        try assumption.
        unfold ltr_exists_ann.
        destruct p as ((x, y) & (p₁, p₂) & p₃).
        exists y; exact p₂.
      + destruct p as ((px, py) & (p₁, p₂) & p₃).
        destruct q as (qx & q₁ & q₂).  
        eapply SLT_Id_Ann_Proof_Not_Equal.
        unfold slt_exists_id_ann_not_equal.
        exists ((px, qx), (py, qx)).
        split.
        split.
        eapply bop_llex_is_id;
        destruct Hc, Hd; 
        try assumption.
        eapply ltr_product_is_ann;
        try assumption.
        simpl; rewrite p₃; 
        reflexivity.
      + eapply SLT_Id_Ann_Proof_Not_Equal. 
        destruct p as ((px, py) & (p₁, p₂) & p₃).
        destruct q as ((qx, qy) & (q₁, q₂) & q₃).
        unfold slt_exists_id_ann_not_equal.
        exists ((px, qx), (py, qy)).
        split. 
        split.
        eapply bop_llex_is_id;
        destruct Hc, Hd; 
        try assumption.
        eapply ltr_product_is_ann;
        try assumption.
        simpl; rewrite p₃; 
        reflexivity.
  Defined.


End Decide.     

Section Combinators.


    Definition A_llex_product_from_A_slt_CS_A_slt_C {L₁ S₁ L₂ S₂: Type} 
      (A : @A_slt_CS L₁ S₁) (B : @A_slt_C L₂ S₂) : @A_slt (L₁ * L₂) (S₁ * S₂).
      refine 
      {|
          A_slt_carrier := A_eqv_product _ _ (A_slt_CS_carrier A) (A_slt_C_carrier B)
        ; A_slt_label := A_eqv_product _ _ (A_slt_CS_label A) (A_slt_C_label B)
        ; A_slt_plus := bop_llex 
            (A_eqv_witness _ (A_slt_C_carrier B))
            (A_eqv_eq _ (A_slt_CS_carrier A)) 
            (A_slt_CS_plus A) 
            (A_slt_C_plus B)
        ; A_slt_trans := ltr_product (A_slt_CS_trans A) (A_slt_C_trans B) 
        ; A_slt_plus_proofs := sg_llex_proofs S₁ S₂ 
            (A_eqv_witness _ (A_slt_CS_carrier A))
            (A_eqv_witness _ (A_slt_C_carrier B))
            _ 
            (A_eqv_eq _ (A_slt_CS_carrier A)) 
            (A_eqv_eq _ (A_slt_C_carrier B)) 
            (A_eqv_new _ (A_slt_CS_carrier A)) 
            (A_eqv_not_trivial _ (A_slt_CS_carrier A))
            (A_eqv_new _ (A_slt_C_carrier B)) 
            (A_eqv_not_trivial _ (A_slt_C_carrier B))  
            (A_slt_CS_plus A)
            (A_slt_C_plus B) 
            (A_eqv_proofs _ (A_slt_CS_carrier A)) 
            (A_eqv_proofs _ (A_slt_C_carrier B)) 
            (A_sg_CS_proofs_to_sg_proofs 
              (A_eqv_eq _ (A_slt_CS_carrier A))
              (A_slt_CS_plus A)
              (A_eqv_witness _ (A_slt_CS_carrier A)) 
              (A_eqv_new _ (A_slt_CS_carrier A)) 
              (A_eqv_not_trivial _ (A_slt_CS_carrier A))
              (A_eqv_proofs _ (A_slt_CS_carrier A))
              (A_slt_CS_plus_proofs A))
            (A_sg_C_proofs_to_sg_proofs 
              (A_eqv_eq _ (A_slt_C_carrier B))
              (A_slt_C_plus B)
              (A_eqv_witness _ (A_slt_C_carrier B)) 
              (A_eqv_new _ (A_slt_C_carrier B)) 
              (A_eqv_not_trivial _ (A_slt_C_carrier B))
              (A_eqv_proofs _ (A_slt_C_carrier B))
              (A_slt_C_plus_proofs B))    
            (bop_selective_implies_idempotent _ _ _ 
              (A_sg_CS_selective _ _ _ (A_slt_CS_plus_proofs A))) 
            (A_sg_CS_commutative _ _ _ (A_slt_CS_plus_proofs A))
            (inl
            (A_sg_CS_selective S₁ (A_eqv_eq S₁ (A_slt_CS_carrier A))
               (A_slt_CS_plus A) (A_slt_CS_plus_proofs A)))                    
        ; A_slt_trans_proofs := ltr_product_proofs L₁ S₁ L₂ S₂ 
            (A_eqv_eq _ (A_slt_CS_carrier A)) 
            (A_eqv_eq _ (A_slt_CS_label A))  
            (A_eqv_witness _ (A_slt_CS_carrier A))  
            (A_eqv_witness _ (A_slt_CS_label A))
            (A_slt_CS_trans A) 
            (A_eqv_reflexive _ _ (A_eqv_proofs _ (A_slt_CS_carrier A)))
            (A_eqv_eq _ (A_slt_C_carrier B)) 
            (A_eqv_eq _ (A_slt_C_label B))  
            (A_eqv_witness _ (A_slt_C_carrier B))  
            (A_eqv_witness _ (A_slt_C_label B))
            (A_slt_C_trans B) 
            (A_eqv_reflexive _ _ (A_eqv_proofs _ (A_slt_C_carrier B)))
            (A_slt_CS_trans_proofs A) (A_slt_C_trans_proofs B)
        ; A_slt_exists_plus_ann_d := bop_llex_exists_ann_decide S₁ S₂ 
            (A_eqv_witness S₂ (A_slt_C_carrier B))
            (A_eqv_eq S₁ (A_slt_CS_carrier A)) 
            (A_eqv_eq S₂ (A_slt_C_carrier B))
            (A_slt_CS_plus A) (A_slt_C_plus B) 
            (A_eqv_proofs _ (A_slt_CS_carrier A)) 
            (A_eqv_proofs _ (A_slt_C_carrier B)) 
            (A_slt_CS_exists_plus_ann_d A) 
            (A_slt_C_exists_plus_ann_d B) 
        ; A_slt_id_ann_proofs_d  := bops_llex_product_exists_id_ann_decide
            L₁ S₁ L₂ S₂ 
            (A_eqv_witness _ (A_slt_CS_label A))  
            (A_eqv_witness _ (A_slt_C_label B))
            (A_eqv_witness _ (A_slt_CS_carrier A))  
            (A_eqv_witness _ (A_slt_C_carrier B))  
            _ _ _ _ 
            (A_eqv_proofs _ (A_slt_CS_label A)) 
            (A_eqv_proofs _ (A_slt_C_label B)) 
            (A_eqv_proofs _ (A_slt_CS_carrier A))
            (A_eqv_proofs _ (A_slt_C_carrier B))  
            _ _ _ _ 
            (A_slt_CS_id_ann_proofs_d A)
            (A_slt_C_id_ann_proofs_d B) 
        ; A_slt_proofs :=   slt_llex_product_proofs L₁ S₁ L₂ S₂ 
            (A_eqv_eq _ (A_slt_CS_label A)) 
            (A_eqv_eq _ (A_slt_C_label B))
            (A_eqv_eq S₁ (A_slt_CS_carrier A)) 
            (A_eqv_eq S₂ (A_slt_C_carrier B))
            (A_eqv_witness S₂ (A_slt_C_carrier B)) 
            (A_eqv_witness _ (A_slt_CS_label A))  
            (A_eqv_witness _ (A_slt_C_label B))
            (A_eqv_witness _ (A_slt_CS_carrier A))  
            (A_eqv_witness _ (A_slt_C_carrier B)) 
            (A_eqv_proofs _ (A_slt_CS_label A)) 
            (A_eqv_proofs _ (A_slt_CS_carrier A)) 
            (A_eqv_proofs _ (A_slt_C_carrier B)) 
            (A_slt_CS_plus A) 
            (A_slt_C_plus B) 
            (bop_selective_implies_idempotent _ _ _ 
              (A_sg_CS_selective _ _ _ (A_slt_CS_plus_proofs A))) 
            (A_sg_C_commutative _ _ _ (A_slt_C_plus_proofs B))
            (A_slt_CS_trans A) 
            (A_slt_C_trans B) 
            (A_sg_CS_congruence _ _ _ (A_slt_CS_plus_proofs A))
            (A_sg_C_congruence _ _ _ (A_slt_C_plus_proofs B)) 
            (A_left_transform_congruence _ _ _ _ _ (A_slt_CS_trans_proofs A))
            (A_sg_C_commutative _ _ _ (A_slt_C_plus_proofs B)) 
            (inl (A_sg_CS_selective _ _ _ (A_slt_CS_plus_proofs A)))
            (A_slt_CS_trans_proofs A) 
            (A_slt_C_trans_proofs B)
            (A_slt_CS_proofs A)
            (A_slt_C_proofs B)
        ; A_slt_ast := ast.Cas_ast "A_llex_product_from_A_slt_CS_A_slt_C" 
            [A_slt_CS_ast A; A_slt_C_ast B]
      |}.
    Defined.

   

    Definition A_llex_product_from_A_slt_CI_A_slt_C_zero_is_ltr_ann 
      {L₁ S₁ L₂ S₂: Type} (A : @A_slt_CI L₁ S₁) 
      (B : @A_slt_C_zero_is_ltr_ann L₂ S₂) :  @A_slt (L₁ * L₂) (S₁ * S₂).
    refine 
    {|
          A_slt_carrier := A_eqv_product _ _ 
            (A_slt_CI_carrier A) (A_slt_C_zero_is_ltr_ann_carrier B)
        ; A_slt_label := A_eqv_product _ _ 
            (A_slt_CI_label A) 
            (A_slt_C_zero_is_ltr_ann_label B)
        ; A_slt_plus := bop_llex 
            (projT1 (A_slt_C_zero_is_ltr_ann_id_ann_proofs B))
            (A_eqv_eq _ (A_slt_CI_carrier A)) 
            (A_slt_CI_plus A) 
            (A_slt_C_zero_is_ltr_ann_plus B)                                          
        ; A_slt_trans  := ltr_product 
            (A_slt_CI_trans A) 
            (A_slt_C_zero_is_ltr_ann_trans B)
        ; A_slt_plus_proofs   := @sg_llex_proofs S₁ S₂ 
            (A_eqv_witness _ (A_slt_CI_carrier A))
            (A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier B))
            (projT1 (A_slt_C_zero_is_ltr_ann_id_ann_proofs B))
            (A_eqv_eq _ (A_slt_CI_carrier A)) 
            (A_eqv_eq _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
            (A_eqv_new _ (A_slt_CI_carrier A)) 
            (A_eqv_not_trivial _ (A_slt_CI_carrier A))
            (A_eqv_new _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
            (A_eqv_not_trivial _ (A_slt_C_zero_is_ltr_ann_carrier B))  
            (A_slt_CI_plus A)
            (A_slt_C_zero_is_ltr_ann_plus B) 
            (A_eqv_proofs _ (A_slt_CI_carrier A)) 
            (A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
            (A_sg_CI_proofs_to_sg_proofs 
              (A_eqv_eq _ (A_slt_CI_carrier A))
              (A_slt_CI_plus A)
              (A_eqv_witness _ (A_slt_CI_carrier A)) 
              (A_eqv_new _ (A_slt_CI_carrier A)) 
              (A_eqv_not_trivial _ (A_slt_CI_carrier A))
              (A_eqv_proofs _ (A_slt_CI_carrier A))
              (A_slt_CI_plus_proofs A))
            (A_sg_C_proofs_to_sg_proofs 
              (A_eqv_eq _ (A_slt_C_zero_is_ltr_ann_carrier B))
              (A_slt_C_zero_is_ltr_ann_plus B)
              (A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
              (A_eqv_new _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
              (A_eqv_not_trivial _ (A_slt_C_zero_is_ltr_ann_carrier B))
              (A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier B))
              (A_slt_C_zero_is_ltr_ann_plus_proofs B))    
            (A_sg_CI_idempotent _ _ _ (A_slt_CI_plus_proofs A)) 
            (A_sg_CI_commutative _ _ _ (A_slt_CI_plus_proofs A)) 
            _ 
                                          
        ; A_slt_trans_proofs  := ltr_product_proofs L₁ S₁ L₂ S₂ 
            (A_eqv_eq _ (A_slt_CI_carrier A)) 
            (A_eqv_eq _ (A_slt_CI_label A))  
            (A_eqv_witness _ (A_slt_CI_carrier A))  
            (A_eqv_witness _ (A_slt_CI_label A))
            (A_slt_CI_trans A) 
            (A_eqv_reflexive _ _ (A_eqv_proofs _ (A_slt_CI_carrier A)))
            (A_eqv_eq _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
            (A_eqv_eq _ (A_slt_C_zero_is_ltr_ann_label B))  
            (A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier B))  
            (A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_label B))
            (A_slt_C_zero_is_ltr_ann_trans B) 
            (A_eqv_reflexive _ _ (A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier B)))
            (A_slt_CI_trans_proofs A) 
            (A_slt_C_zero_is_ltr_ann_trans_proofs B) 
        ; A_slt_exists_plus_ann_d := bop_llex_exists_ann_decide S₁ S₂ 
            (projT1 (A_slt_C_zero_is_ltr_ann_id_ann_proofs B))
            (A_eqv_eq S₁ (A_slt_CI_carrier A)) 
            (A_eqv_eq S₂ (A_slt_C_zero_is_ltr_ann_carrier B))
            (A_slt_CI_plus A) (A_slt_C_zero_is_ltr_ann_plus B) 
            (A_eqv_proofs _ (A_slt_CI_carrier A)) 
            (A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier B)) 
            (A_slt_CI_exists_plus_ann_d A) 
            (A_slt_C_zero_is_ltr_ann_exists_plus_ann_d B)                         
        ; A_slt_id_ann_proofs_d :=  bops_llex_product_exists_id_ann_decide L₁ S₁ L₂ S₂
            (A_eqv_witness L₁ (A_slt_CI_label A))
            (A_eqv_witness L₂ (A_slt_C_zero_is_ltr_ann_label B))
            (A_eqv_witness S₁ (A_slt_CI_carrier A))
            (projT1 (A_slt_C_zero_is_ltr_ann_id_ann_proofs B))
            (A_eqv_eq L₁ (A_slt_CI_label A))
            (A_eqv_eq L₂ (A_slt_C_zero_is_ltr_ann_label B))
            (A_eqv_eq S₁ (A_slt_CI_carrier A))
            (A_eqv_eq S₂ (A_slt_C_zero_is_ltr_ann_carrier B))
            (A_eqv_proofs L₁ (A_slt_CI_label A))
            (A_eqv_proofs L₂ (A_slt_C_zero_is_ltr_ann_label B))
            (A_eqv_proofs S₁ (A_slt_CI_carrier A))
            (A_eqv_proofs S₂ (A_slt_C_zero_is_ltr_ann_carrier B))
            (A_slt_CI_plus A) (A_slt_C_zero_is_ltr_ann_plus B)
            (A_slt_CI_trans A) (A_slt_C_zero_is_ltr_ann_trans B)
            (A_slt_CI_id_ann_proofs_d A)
            (SLT_Id_Ann_Proof_Equal
              (A_eqv_eq S₂ (A_slt_C_zero_is_ltr_ann_carrier B))
              (A_slt_C_zero_is_ltr_ann_plus B)
              (A_slt_C_zero_is_ltr_ann_trans B)
              (A_slt_C_zero_is_ltr_ann_id_ann_proofs B))
        ; A_slt_proofs := _                       
        ; A_slt_ast := ast.Cas_ast "A_llex_product_from_A_slt_CS_A_slt_C" 
            [A_slt_CI_ast A; A_slt_C_zero_is_ltr_ann_ast B]
    
    |}.
    

    (* I need to go right *)
    right.
    destruct B, A_slt_C_zero_is_ltr_ann_plus_proofs,
    A_slt_C_zero_is_ltr_ann_carrier, A_slt_C_zero_is_ltr_ann_id_ann_proofs; 
    simpl in *.
    destruct p as (pa & pb).
    exact pa.
    eapply  slt_llex_product_proofs.
    exact (A_eqv_witness _ (A_slt_CI_label A)).
    exact (A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_label B)).
    exact (A_eqv_witness _ (A_slt_CI_carrier A)).
    exact (A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier B)).
    exact (A_eqv_proofs _ (A_slt_CI_label A)).
    exact (A_eqv_proofs _ (A_slt_CI_carrier A)).
    exact (A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier B)).
    exact (A_sg_CI_idempotent _ _ _ (A_slt_CI_plus_proofs A)).
    exact (A_sg_C_commutative _ _ _ 
      (A_slt_C_zero_is_ltr_ann_plus_proofs B)).
    exact (A_sg_CI_congruence _ _ _ (A_slt_CI_plus_proofs A)).
    exact (A_sg_C_congruence _ _ _ 
      (A_slt_C_zero_is_ltr_ann_plus_proofs B)).
    exact (A_left_transform_congruence _ _ _ _ _ 
      (A_slt_CI_trans_proofs A)).
    exact (A_sg_C_commutative _ _ _ (A_slt_C_zero_is_ltr_ann_plus_proofs B)).
    right.
    destruct B, A_slt_C_zero_is_ltr_ann_plus_proofs,
    A_slt_C_zero_is_ltr_ann_carrier, A_slt_C_zero_is_ltr_ann_id_ann_proofs; 
    simpl in *.
    exact p. 
    exact (A_slt_CI_trans_proofs A).
    exact (A_slt_C_zero_is_ltr_ann_trans_proofs B).
    exact (A_slt_CI_proofs A).
    exact (A_slt_C_zero_is_ltr_ann_proofs B).
  Defined.
  
    
End Combinators.   
  
End ACAS.

From Coq Require Import String.
Open Scope string_scope.
Section AMCAS.


  Definition cast_first_to_A_slt_CS_and_second_to_A_slt_C {L₁ S₁ L₂ S₂: Type}
    (A : @A_slt_mcas L₁ S₁) (B : @A_slt_mcas L₂ S₂) 
    : @A_slt_mcas (L₁ * L₂) (S₁ * S₂) :=
    match cast_A_slt_mcas_to_A_slt_CS A with
    | A_SLT_CS slt₁ => 
        match cast_A_slt_mcas_to_A_slt_C B with 
        | A_SLT_C slt₂ => 
            A_slt_classify_slt (A_llex_product_from_A_slt_CS_A_slt_C slt₁ slt₂)
        | _ => 
            A_SLT_Error ["Cannot cast the second componento of A_slt_C"] 
        end
    | _  => 
        match cast_A_slt_mcas_to_A_slt_CI A with  
        | A_SLT_CI slt₃ => 
          match cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann B with 
          | A_SLT_C_Zero_Is_Ltr_ann slt₄ => 
              A_slt_classify_slt 
                (A_llex_product_from_A_slt_CI_A_slt_C_zero_is_ltr_ann slt₃ slt₄)
          | _ => 
             A_SLT_Error ["Cannot cast the second componento of A_slt_C_zero_is_ltr_ann"]
          end
        | _ => A_SLT_Error ["Cannot cast up the first component of A_SLT_CS and A_SLT_CI"]
        end
    end.
    
    

End AMCAS.

Section CAS.

Section Decide.

(*  
Variables (LS S LT T : Type)  
          (eqLS : brel LS)
          (eqLT : brel LT)
          (eqS : brel S)
          (eqT : brel T)
          (argT : T)
          (wLS : LS)
          (wLT : LT)                     
          (wS : S)
          (wT : T)           
          (addS : binary_op S) 
          (addT : binary_op T)
          (idemS : bop_idempotent S eqS addS)
          (commS : bop_commutative S eqS addS)
          (commT : bop_commutative T eqT addT)                     
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T).

Definition slt_llex_product_distributive_certify
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (LDS_d : slt_distributive_decidable LS S eqS addS ltrS)
           (LDT_d : slt_distributive_decidable LT T eqT addT ltrT)
           (LCS_d : ltr_left_cancellative_decidable LS S eqS ltrS)
           (LKT_d : ltr_left_constant_decidable LT T eqT ltrT): 
  @slt_distributive_decidable (LS * LT) (S * T) := 
let selS_or_annT :=
    match selS_or_id_annT with
    | inl sel         => inl sel
    | inr (_, is_ann) => inr is_ann 
    end
in       
match LDS_d with
| inl LDS  =>
  match LDT_d with
  | inl LDT  =>
    match LCS_d with
    | inl LCS  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inl LCS))
    | inr nLCS =>
      match LKT_d with
      | inl LKT  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inr LKT))
      | inr nLKT => inr (slt_llex_product_not_distributive_v3 LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT refS symS trnS refT symT trnT refLS a_congS a_congT ltr_congS idemS commT selS_or_id_annT LDS LDT nLCS nLKT) 
      end 
    end 
  | inr nLDT => inr (slt_llex_product_not_distributive_v2 LS S LT T eqLS eqS eqT argT wS wLS addS addT ltrS ltrT symS trnS refLS ltr_congS idemS LDS nLDT)    
  end 
| inr nLDS => inr (slt_llex_product_not_distributive_v1 LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nLDS) 
end.     


Definition slt_llex_product_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable LS S eqS addS ltrS)
           (absS_d : slt_absorptive_decidable LS S eqS addS ltrS)
           (absT_d : slt_absorptive_decidable LT T eqT addT ltrT) :
  slt_absorptive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS trnS idemS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.     

Definition slt_llex_product_strictly_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable LS S eqS addS ltrS)
           (absS_d : slt_absorptive_decidable LS S eqS addS ltrS)
           (absT_d : slt_strictly_absorptive_decidable LT T eqT addT ltrT) :
  slt_strictly_absorptive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=    
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in  
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_strictly_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_strictly_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.

Definition slt_llex_product_proofs
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (QS : left_transform_proofs LS S eqS eqLS ltrS)
           (QT : left_transform_proofs LT T eqT eqLT ltrT)           
           (PS : slt_proofs LS S eqS addS ltrS)
           (PT : slt_proofs LT T eqT addT ltrT) : 
  slt_proofs (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let DS_d := A_slt_distributive_d _ _ _ _ _ PS in
let DT_d := A_slt_distributive_d _ _ _ _ _ PT in
let CS_d := A_left_transform_left_cancellative_d _ _ _ _ _ QS in
let KT_d := A_left_transform_left_constant_d _ _ _ _ _ QT in
let asbS_d := A_slt_absorptive_d _ _ _ _ _ PS in
let asbT_d := A_slt_absorptive_d _ _ _ _ _ PT in
let sasbS_d := A_slt_strictly_absorptive_d _ _ _ _ _ PS in
let sasbT_d := A_slt_strictly_absorptive_d _ _ _ _ _ PT in
{|
  A_slt_distributive_d          := slt_llex_product_distributive_decide commT selS_or_id_annT DS_d DT_d CS_d KT_d 
; A_slt_absorptive_d            := slt_llex_product_absorptive_decide sasbS_d asbS_d asbT_d
; A_slt_strictly_absorptive_d   := slt_llex_product_strictly_absorptive_decide sasbS_d asbS_d sasbT_d
|}.


 *)



  



End Decide.       
Section Combinators.

  Definition llex_product_from_slt_CS_slt_C {L₁ S₁ L₂ S₂: Type} 
    (A : @slt_CS L₁ S₁) (B : @slt_C L₂ S₂) : @slt (L₁ * L₂) (S₁ * S₂).
  refine
    {|
        slt_carrier := eqv_product (slt_CS_carrier A) (slt_C_carrier B) 
      ; slt_label := eqv_product (slt_CS_label A) (slt_C_label B)
      ; slt_plus  :=   bop_llex 
          (eqv_witness (slt_C_carrier B))
          (eqv_eq (slt_CS_carrier A)) 
          (slt_CS_plus A) 
          (slt_C_plus B)                                          
      ; slt_trans := ltr_product 
          (slt_CS_trans A) 
          (slt_C_trans B) 
      ; slt_plus_certs := sg_llex_certificates 
          (eqv_eq (slt_CS_carrier A)) 
          (eqv_witness (slt_CS_carrier A)) 
          (eqv_new (slt_CS_carrier A)) 
          (eqv_witness (slt_C_carrier B)) 
          (eqv_witness (slt_C_carrier B))
          (eqv_new (slt_C_carrier B)) 
          (slt_CS_plus A)
          (sg_CS_certs_to_sg_certs  
            (eqv_eq (slt_CS_carrier A))
            (slt_CS_plus A)
            (eqv_witness (slt_CS_carrier A))
            (eqv_new (slt_CS_carrier A))
            (slt_CS_plus_certs A))
          (sg_C_certs_to_sg_certs  
            (eqv_eq (slt_C_carrier B))
            (slt_C_plus B)
            (eqv_witness (slt_C_carrier B))
            (eqv_new (slt_C_carrier B))
            (slt_C_plus_certs B))
          _
          (sg_CS_commutative (slt_CS_plus_certs A)) 

      ; slt_trans_certs := ltr_product_certs 
          (eqv_witness (slt_CS_carrier A))
          (eqv_witness (slt_CS_label A))
          (slt_CS_trans_certs A)
          (eqv_witness (slt_C_carrier B))
          (eqv_witness (slt_C_label B))
          (slt_C_trans_certs B) 


      ; slt_exists_plus_ann_d := check_exists_ann_llex
          (slt_CS_exists_plus_ann_d A)
          (slt_C_exists_plus_ann_d B)


      ; slt_id_ann_certs_d := _                 
      ; slt_certs := _                               
      ; slt_ast := ast.Cas_ast "A_llex_product_from_A_slt_CS_A_slt_C" 
        [slt_CS_ast A; slt_C_ast B]
    |}.
  Admitted.

   Definition llex_product_from_slt_CI_slt_C_zero_is_ltr_ann 
    {L₁ S₁ L₂ S₂: Type} (A : @slt_CI L₁ S₁) 
    (B : @slt_C_zero_is_ltr_ann L₂ S₂) :  @slt (L₁ * L₂) (S₁ * S₂).
    refine
    {|
        slt_carrier := eqv_product
          (slt_CI_carrier A) (slt_C_zero_is_ltr_ann_carrier B)
      ; slt_label := eqv_product 
          (slt_CI_label A) 
          (slt_C_zero_is_ltr_ann_label B)
      ; slt_plus  := bop_llex 
          (match slt_C_zero_is_ltr_ann_id_ann_certs B with
            | Assert_Slt_Exists_Id_Ann_Equal s => s
          end) 
          (eqv_eq (slt_CI_carrier A)) 
          (slt_CI_plus A) 
          (slt_C_zero_is_ltr_ann_plus B)                                             
      ; slt_trans := ltr_product 
          (slt_CI_trans A) 
          (slt_C_zero_is_ltr_ann_trans B) 
      ; slt_plus_certs := _                             
      ; slt_trans_certs  := ltr_product_certs 
          (eqv_witness (slt_CI_carrier A))
          (eqv_witness (slt_CI_label A))
          (slt_CI_trans_certs A)
          (eqv_witness (slt_C_zero_is_ltr_ann_carrier B))
          (eqv_witness (slt_C_zero_is_ltr_ann_label B))
          (slt_C_zero_is_ltr_ann_trans_certs B) 
      ; slt_exists_plus_ann_d := check_exists_ann_llex
          (slt_CI_exists_plus_ann_d A)
          (slt_C_zero_is_ltr_ann_exists_plus_ann_d B)                        
      ; slt_id_ann_certs_d := _                 
      ; slt_certs := _ 
      ; slt_ast := ast.Cas_ast "A_llex_product_from_A_slt_CS_A_slt_C" 
            [slt_CI_ast A; slt_C_zero_is_ltr_ann_ast B]
    |}.
  Admitted.  

   
  


End Combinators.   
  
End CAS.

Section MCAS.

  (* name should change *)
  Definition cast_first_to_slt_CS_and_second_to_slt_C {L₁ S₁ L₂ S₂: Type}
    (A : @slt_mcas L₁ S₁) (B : @slt_mcas L₂ S₂) 
    : @slt_mcas (L₁ * L₂) (S₁ * S₂) :=
    match cast_slt_mcas_to_slt_CS A with
    | SLT_CS slt₁ => 
        match cast_slt_mcas_to_slt_C B with 
        | SLT_C slt₂ => 
            slt_classify_slt (llex_product_from_slt_CS_slt_C slt₁ slt₂)
        | _ => 
            SLT_Error ["Cannot cast the second componento of A_slt_C"] 
        end
    | _  => 
        match cast_slt_mcas_to_slt_CI A with  
        | SLT_CI slt₃ => 
          match cast_slt_mcas_to_slt_C_zero_is_ltr_ann B with 
          | SLT_C_Zero_Is_Ltr_ann slt₄ => 
              slt_classify_slt 
                (llex_product_from_slt_CI_slt_C_zero_is_ltr_ann slt₃ slt₄)
          | _ => 
             SLT_Error ["Cannot cast the second componento of A_slt_C_zero_is_ltr_ann"]
          end
        | _ => SLT_Error ["Cannot cast up the first component of A_SLT_CS and A_SLT_CI"]
        end
    end.
    
    

End MCAS.


Section Verify.

End Verify.   
  
