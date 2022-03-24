Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.llex.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 


Section Theory.

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.

Variable wS : S. 
Variable wT : T.
Variable argT : T.

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

Variable a_commS : bop_commutative S rS addS.
Variable a_idemS : bop_idempotent S rS addS.

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [+] b" := (bop_llex argT rS a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).
Notation "[| p1 | a | c | b | d |]" := (llex_p2 argT rS addT p1 a c b d) (at level 15).


Lemma bop_llex_product_left_distributive 
      (selS_or_annT : bop_selective S rS addS + bop_is_ann T rT mulT argT)
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT)
      (D : (bop_left_cancellative S rS mulS) + (bop_left_constant T rT mulT)) : 
         bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product.
       apply bop_and_intro. 
       apply ldS. 
       unfold llex_p2.
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + apply ldT. 
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 *S s3)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 *S s3)))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply LC in F2. 
             assert (F3 := tranS _ _ _ H2 F2).
             assert (F4 := conS _ _ _ _ (refS (s2 +S s3)) F3). 
             rewrite <- F4 in H1. apply symS in H2.
             rewrite H2 in H1. discriminate H1.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t2 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + apply refT. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 *S s2)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 *S s2)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply LC in F2. 
             rewrite F2 in H1. discriminate H1.
           * exact(LK t1 t2 t3). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H2).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t3 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 argT (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1).              (* NB : idT_is_annT -> not NK *)
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * exact (LK t1 argT t2). 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + apply refT. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply LC in F2.
             rewrite F2 in H1. discriminate H1.
           * exact (LK t1 argT t3). 
         + destruct selS_or_annT as [selS | argT_is_annT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * destruct (argT_is_annT t1) as [F1 F2].  exact F2. 
Qed. 




Lemma bop_llex_product_not_left_distributive_v1 : 
  bop_not_left_distributive S rS addS mulS → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [s1 [s2 s3 ] ] nld ].
       exists ((s1, wT), ((s2, wT), (s3, wT))).
       compute. rewrite nld. reflexivity.
Defined. 


Lemma bop_llex_product_not_left_distributive_v2 : 
  bop_not_left_distributive T rT addT mulT → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wS, t1), ((wS, t2), (wS, t3))).
       unfold brel_product. unfold bop_product, bop_llex. 
       apply bop_and_false_intro. right. unfold llex_p2.
       assert (F1 := a_idemS wS). rewrite F1. apply symS in F1. rewrite F1. 
       assert (F2 := a_idemS (wS *S wS)). rewrite F2. apply symS in F2. rewrite F2. 
       exact nld. 
Defined. 


(* see cases 1-4 in the proof below *) 

Definition A_witness_llex_product_not_left_distributive
(*      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT)) *) 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
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
        else (* case 4 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => *) if rT argT (t1 *T t2)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             (*end *).   

(* for use in CAS *) 
Definition witness_llex_product_not_left_distributive_new
(*      (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T)) *) 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
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
        else (* case 4 
             match selS_or_id_annT with 
             | inl Assert_Bop_Selective =>
                       (* can't reach this branch 
                          Note: If we write "inl _" here, we get "magic" in extracted OCaml! 
                       *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr (Assert_Exists_Id _, Assert_Exists_Ann _) =>
              *) 
                        if rT argT (t1 *T t2)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             (*end*).   


(* for use in CAS 
Definition witness_llex_product_not_left_distributive_without_selectivity
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
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
             if rT argT (t1 *T t2)
             then ((s1, t1), ((s2, argT), (s3, t3)))
             else ((s1, t1), ((s2, argT), (s3, t2))). 
*) 
(* for use in CAS 
Definition witness_llex_product_not_left_distributive_with_selectivity
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
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
             (* can't reach this branch *)           
             ((s1, t1), ((s2, t2), (s3, t3))). 

*) 


Lemma bop_llex_product_not_left_distributive_v3
      (a_commT : bop_commutative T rT addT) (*NB*)
      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT) : 
      bop_not_left_cancellative S rS mulS → bop_not_left_constant T rT mulT → 
      bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(A_witness_llex_product_not_left_distributive (* selS_or_id_annT *) s1 s2 s3 t1 t2 t3). 
       unfold A_witness_llex_product_not_left_distributive. 
       unfold bop_product, brel_product, bop_llex.        
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + rewrite (tranS _ _ _ H2 H1) in N. discriminate N. 
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 *S s3)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 *S s3)))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + (* ============= case 1 ======================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

             H2 : s2 =S (s2 +S s3)
             H4 : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
             ===========need=================
             rT (a *T b) ((a *T b) +T (a *T c)) = false

             if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
             then (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     b     a     c       a     b    (use a_commT  !!!) 

             else (t1 *T t2) ((t1 *T t2) +T (t1 *T t3)) = false
                   a      b     a     b      a     c 
           *) 
           unfold llex_p2. rewrite (symS _ _ H2).
           case_eq(rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(rT (t1 *T t3) ((t1 *T t3) +T (t1 *T t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 *T t3) (t1 *T t2)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F4. 
                rewrite (tranT _ _ _ F1 F4) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + apply symS in E.
           assert (F1 := tranS _ _ _ E H4). apply symS in F1. 
           rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 *S s2)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 *S s2)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
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
           assert (F2 := m_conS _ _ _ _ (refS s1) H2).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
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
           assert (G : rS (s2 +S s3) s2 = false).
              case_eq(rS (s2 +S s3) s2); intro H; auto.
                apply symS in H. rewrite H in H2. discriminate H2.            
           unfold llex_p2. rewrite G. 
           case_eq(rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(rT (t1 *T t2) ((t1 *T t3) +T (t1 *T t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 *T t3) (t1 *T t2)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F1. 
                rewrite (tranT _ _ _ F4 F1) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
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
           * assert (G : rS (s2 +S s3) s2 = false).
             case_eq(rS (s2 +S s3) s2); intro H; auto.
             apply symS in H. rewrite H in H2. discriminate H2.
             unfold llex_p2. rewrite G.
             case_eq(rT argT (t1 *T t2)); intro F6.
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t1 *T t3)) as [F3 F4].                          
                assert (F5 : ((t1 *T argT) +T (t1 *T t3)) =T (t1 *T t3)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 *T t3))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (t1 *T argT) ((t1 *T argT) +T (t1 *T t3))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5).
                   assert (F9 := tranT _ _ _ F2 F6). apply symT in F9. 
                   rewrite (tranT _ _ _ F9 F8) in F. discriminate F. 
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t1 *T t2)) as [F3 F4].                                          
                assert (F5 : ((t1 *T argT) +T (t1 *T t2)) =T (t1 *T t2)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 *T t2))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (t1 *T argT) ((t1 *T argT) +T (t1 *T t2))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5). apply symT in F2. 
                   rewrite (tranT _ _ _ F2 F8) in F6. discriminate F6. 
         + apply symS in E. assert (F1 := tranS _ _ _ E H4). 
           apply symS in F1. rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := a_idemS (s1 *S s3)). 
           assert (F2 := a_conS _ _ _ _ E (refS (s1 *S s3))). 
           assert (F3 := tranS _ _ _ F2 F1).
           rewrite F3 in H3. discriminate H3. 
Defined. 



(*
Non-selective 
s1 +S s2 <> s1
s1 +S s2 <> s2

We know that argT is an id for +T
and +T is 

exists t : artT *T t <> argT or t *T argT <> argT 

want 

case 1: artT *T t <> argT. 

case 2:  t *T argT <> argT. 

LHS = 
(a, t) * ((s1, y) lex (s2, z)) 
= (a, t) * (s1 + s2, argT) 
= (a * (s1 + s2), t * argT) 
<>
= (a * (s1 + s2), T(a*s1, a*s2, t * y, x * z)) 
= (a * s1, t * y) lex (a * s2, x * z)
= (a, t) * (s1, y)) lex ((a, x) * (s2, z))


T(a*s1, a*s2, t * y, x * z))
= case a *s1 = a*s1 + a*s2 = a*s2 => (t * y) +T (x * z)
       a *s1 = a*s1 + a*s2 <> a*s2 => (t * y) 
       a *s1 <> a*s1 + a*s2 = a*s2 => (x * z)
       a *s1 <> a*s1 + a*s2 <> a*s2 => argT 

Note: if +S has an id we could use a = id to make this work. 
LHS = 
(id, t) * ((s1, y) lex (s2, z)) 
= (id, t) * (s1 + s2, argT) 
= (id * (s1 + s2), t * argT) 
= (s1 + s2, t * argT) 
<>
= (s1 + s2, argT)
= (s1, t * y) lex (s2, x * z)
= (id * s1, t * y) lex (id * s2, x * z)
= (id, t) * (s1, y)) lex ((id, x) * (s2, z))

with no id? 

G :  ∀ i exists s, i s <> s or s i <> s  

------------
If *S is cancellative? 
  
    a *s1 = a*s1 + a*s2  => a*(s1 + s2) = a*s1 
                         => (s1 + s2) = s1  **** etc
   so must have 
       a *s1 <> a*s1 + a*s2 <> a*s2 => argT <> argT. 

If *T is left_constant? 

 *)
Lemma bop_llex_product_not_left_distributive_testing_1_2_3 (a : S) (y z : T) 
      (nselS : bop_not_selective S rS addS)
      (nannT : bop_not_is_ann T rT mulT argT)
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT)
      (D : (bop_left_cancellative S rS mulS) + (bop_left_constant T rT mulT)) :       
  bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. destruct nselS as [[s1 s2] [A B]]; destruct nannT as [t F].
       assert (A' : rS s1 (s1 +S s2) = false). admit.
       assert (B' : rS s2 (s1 +S s2) = false). admit.        
       destruct F as [F | F]; destruct D as [D | D]. 
       + (* F : rT (argT *T t) argT = false   D : bop_left_cancellative S rS mulS *)
         admit. 
       + (* F : rT (argT *T t) argT = false   D : bop_left_constant T rT mulT     *)
         admit. 
       + (* F : rT (t *T argT) argT = false   D : bop_left_cancellative S rS mulS *)
         exists ((a, t), ((s1, wT), (s2, wT))). compute. 
         rewrite ldS. rewrite B. rewrite A'.
         case_eq(rS (a *S s1) ((a *S s1) +S (a *S s2))); intro E;
         case_eq(rS ((a *S s1) +S (a *S s2)) (a *S s2)); intro G.
         ++ admit.  (* contradicts D *) 
         ++ admit. (* contradicts D *) 
         ++ admit. (* contradicts D *) 
         ++ exact F. 
       + (* F : rT (t *T argT) argT = false   D : bop_left_constant T rT mulT     *) 
         admit. 
Admitted. 





Lemma bop_llex_product_right_distributive 
      (selS_or_annT : bop_selective S rS addS + bop_is_ann T rT mulT argT)
      (rdS : bop_right_distributive S rS addS mulS)
      (rdT : bop_right_distributive T rT addT mulT)
      (D : (bop_right_cancellative S rS mulS) + (bop_right_constant T rT mulT)) : 
         bop_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product.
       apply bop_and_intro. 
       apply rdS. 
       unfold llex_p2.
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + apply rdT.
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s3 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ F3 (refS (s3 *S s1))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply RC in F2. 
             assert (F3 := tranS _ _ _ H2 F2).
             assert (F4 := conS _ _ _ _ (refS (s2 +S s3)) F3). 
             rewrite <- F4 in H1. apply symS in H2.
             rewrite H2 in H1. discriminate H1.
           * assert (F1 := rdT t1 t2 t3).
             assert (F2 := RK t1 t2 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + apply refT.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s2 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ (refS (s2 *S s1)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply RC in F2. 
             rewrite F2 in H1. discriminate H1.
           * exact(RK t1 t2 t3). 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H2 (refS s1)).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply RC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := rdT t1 t2 t3).
             assert (F2 := RK t1 t3 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply RC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := rdT t1 t2 t3).
             assert (F2 := RK t1 argT (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1).              (* NB : idT_is_annT -> not RK *)
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply RC in F2.
             rewrite F2 in H2. discriminate H2.
           * exact (RK t1 argT t2). 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + apply refT. 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply RC in F2.
             rewrite F2 in H1. discriminate H1.
           * exact (RK t1 argT t3). 
         + destruct selS_or_annT as [selS | argT_is_annT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * destruct (argT_is_annT t1) as [F1 F2].  exact F1. 
Qed. 

Lemma bop_llex_product_not_right_distributive_v1 : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 


Lemma bop_llex_product_not_right_distributive_v2 : 
      bop_not_right_distributive T rT addT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [t1 [t2 t3 ] ] nrd ].
       exists ((wS, t1), ((wS, t2), (wS, t3))).
      unfold brel_product. unfold bop_product, bop_llex. 
       apply bop_and_false_intro. right. unfold llex_p2.
       assert (F1 := a_idemS wS). rewrite F1. apply symS in F1. rewrite F1. 
       assert (F2 := a_idemS (wS *S wS)). rewrite F2. apply symS in F2. rewrite F2. 
       exact nrd. 
Defined. 


(* see cases 1-4 in the proof below *) 

Definition A_witness_llex_product_not_right_distributive
(*      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT)) *) 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => *) if rT argT (t2 *T t1)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             (* end *).   

(* for use in CAS *) 
Definition witness_llex_product_not_right_distributive_new
(*      (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T)) *) 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 
             match selS_or_id_annT with 
             | inl Assert_Bop_Selective
                 => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr (Assert_Exists_Id _, Assert_Exists_Ann _)
                     =>
             *)         if rT argT (t2 *T t1)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             (*end*).   



(* for use in CAS 
Definition witness_llex_product_not_right_distributive_without_selectivity 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             if rT argT (t2 *T t1)
             then ((s1, t1), ((s2, argT), (s3, t3)))
             else ((s1, t1), ((s2, argT), (s3, t2))). 
*) 
(* for use in CAS 
Definition witness_llex_product_not_right_distributive_with_selectivity 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *)
             (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3))). 

*) 
Lemma bop_llex_product_not_right_distributive_v3 
      (a_commT : bop_commutative T rT addT) (*NB*)
      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))
      (rdS : bop_right_distributive S rS addS mulS)
      (rdT : bop_right_distributive T rT addT mulT) : 
      bop_not_right_cancellative S rS mulS → bop_not_right_constant T rT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(A_witness_llex_product_not_right_distributive (* selS_or_id_annT *) s1 s2 s3 t1 t2 t3). 
       unfold A_witness_llex_product_not_right_distributive. 
       unfold bop_product, brel_product, bop_llex.
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + rewrite (tranS _ _ _ H2 H1) in N. discriminate N. 
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s3 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ F3 (refS (s3 *S s1))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + (* ============= case 1 ======================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false
  
             H2 : s2 =S (s2 +S s3)
             H4 : (s2 *S s1) =S ((s2 *S s1) +S (s3 *S s1))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
             ===========need=================
             rT (b *T a) ((b *T a) +T (c *T a)) = false

             if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then (t3 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false
                   b     a     c     a        b    a    (use a_commT) 

             else rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false 
                      b      a    b     a       c     a 
            *)
           unfold llex_p2. rewrite (symS _ _ H2).
           case_eq(rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))); intro F1.
           * rewrite H1, H2, H3, H4.
             apply bop_and_false_intro. right.
             case_eq(rT (t3 *T t1) ((t3 *T t1) +T (t2 *T t1))); intro F2; auto.              
             -- assert (F3 := a_commT (t3 *T t1) (t2 *T t1)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F4. 
                rewrite (tranT _ _ _ F1 F4) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H1, H2, H3, H4.
             exact F1.            
         + apply symS in E.
           assert (F1 := tranS _ _ _ E H4). apply symS in F1. 
           rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s2 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ (refS (s2 *S s1)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + (* ===============case 2==============================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false

             H2 : s2 =S (s2 +S s3)
             H4 : rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1)) = false
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
             ==========need==================
               rT (b *T a) (c *T a) = false

             so use F: 
             rT (t2 *T t1) (t3 *T t1) = false
                 b     a    c     a 
           *)
           unfold llex_p2. rewrite (symS _ _ H2). 
           apply bop_and_false_intro. right. rewrite H1, H2, H4, H3. 
           exact F.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H2 (refS s1)).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + (* ==================case 3=========================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false

             H2 : rS s2 (s2 +S s3) = false
             H4 : (s2 *S s1) =S ((s2 *S s1) +S (s3 *S s1))
             H1 : (s2 +S s3) =S s3
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
            =========need===================
             rT (c *T a) ((b *T a) +T (c *T a)) = false

             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then (t2 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false
                   c     a     c     a       b     a    (use a_commT) 

             else (t3 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false
                   c     a      b     a       c     a 
           *)   
           assert (G : rS (s2 +S s3) s2 = false).
              case_eq(rS (s2 +S s3) s2); intro H; auto.
                apply symS in H. rewrite H in H2. discriminate H2.            
           unfold llex_p2. rewrite G. 
           case_eq(rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H1, H2, H3, H4. 
               case_eq(rT (t2 *T t1) ((t3 *T t1) +T (t2 *T t1))); intro F2; auto.              
             -- assert (F3 := a_commT (t3 *T t1) (t2 *T t1)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F1. 
                rewrite (tranT _ _ _ F4 F1) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H1, H2, H3, H4. 
             exact F1.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + (* =============case 4=================================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false

             H2 : rS s2 (s2 +S s3) = false
             H4 : (s2 *S s1) =S ((s2 *S s1) +S (s3 *S s1))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
             =============need===============
               rT (argT *T a) ((b *T a) +T (c *T a)) = false
  
             case split: 
             selective(+S) : contradiction with H1 H2. 
             
             argT is id for +T and is ann for *T: 
             =============need===============
             rT argT ((b *T a) +T (c *T a)) = false
             
             let b = argT. so  ((b *T a) +T (c *T a)) = (c *T a)

             =============need===============
             rT argT (c *T a) = false

             if argT = (t2 *T t1)
             then let (c *T a) = (t3 *T t1)
             else let (c *T a) = (t2 *T t1)
           *)
           destruct selS_or_id_annT as [selS | [idT annT]].
           * destruct (selS s2 s3) as [F1 | F1]. 
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1.
           * assert (G : rS (s2 +S s3) s2 = false).
             case_eq(rS (s2 +S s3) s2); intro H; auto.
             apply symS in H. rewrite H in H2. discriminate H2.
             unfold llex_p2. rewrite G.
             case_eq(rT argT (t2 *T t1)); intro F6.
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t3 *T t1)) as [F3 F4].                          
                assert (F5 : ((argT *T t1) +T (t3 *T t1)) =T (t3 *T t1)).
                   assert (F5 := a_conT _ _ _ _ F1 (refT (t3 *T t1))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (argT *T t1) ((argT *T t1) +T (t3 *T t1))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5). apply symT in F6. apply symT in F1. 
                   assert (F9 := tranT _ _ _ F6 F1). 
                   rewrite (tranT _ _ _ F9 F8) in F. discriminate F. 
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t2 *T t1)) as [F3 F4].                                          
                assert (F5 : (argT *T t1) +T (t2 *T t1) =T (t2 *T t1)). 
                   assert (F5 := a_conT _ _ _ _ F1 (refT (t2 *T t1))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (argT *T t1) ((argT *T t1) +T (t2 *T t1))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5). apply symT in F1. 
                   rewrite (tranT _ _ _ F1 F8) in F6. discriminate F6. 
         + apply symS in E. assert (F1 := tranS _ _ _ E H4). 
           apply symS in F1. rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := a_idemS (s3 *S s1)). 
           assert (F2 := a_conS _ _ _ _ E (refS (s3 *S s1))). 
           assert (F3 := tranS _ _ _ F2 F1).
           rewrite F3 in H3. discriminate H3. 
Defined.




(* absorption *) 

(* left left *) 

Lemma bops_llex_product_left_left_absorptive : 
      bops_left_left_absorptive S rS addS mulS → 
      ((bops_left_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
         bops_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       - rewrite ldS. 
         case_eq(rS (s1 +S (s1 *S s2)) (s1 *S s2)); intro H. 
          + apply ldT.
          + apply refT. 
       - rewrite ldS.
         case_eq(rS (s1 +S (s1 *S s2)) (s1 *S s2)); intro H. 
         + assert (K := F s1 s2).
           assert (J := ldS s1 s2).
           rewrite (tranS _ _ _ J H) in K. discriminate K. 
          + apply refT.
Qed.

Lemma bops_llex_product_not_left_left_absorptive_left : 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_left_left_absorptive_right : 
      bops_left_left_absorptive S rS addS mulS → bops_not_left_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  →
      bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]; compute.
       exists ((s1, t1), (s2, t2)).
       rewrite laS.
       assert (F1 : (s1 +S (s1 *S s2)) =S (s1 *S s2)).
          assert (F2 := a_idemS (s1 *S s2)).
          assert (F3 := a_conS _ _ _ _ Q (refS (s1 *S s2))).        
          exact (tranS _ _ _ F3 F2). 
       rewrite F1. exact P.        
Defined.



(* left right *) 
Lemma bops_llex_product_left_right_absorptive :
      bops_left_right_absorptive S rS addS mulS → 
      ((bops_left_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
      bops_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       - rewrite ldS. 
         case_eq(rS (s1 +S (s2 *S s1)) (s2 *S s1)); intro H. 
          + apply ldT.
          + apply refT. 
       - rewrite ldS.
         case_eq(rS (s1 +S (s2 *S s1)) (s2 *S s1)); intro H. 
         + assert (K := F s1 s2).
           assert (J := ldS s1 s2).
           rewrite (tranS _ _ _ J H) in K. discriminate K. 
          + apply refT.
Defined. 

Lemma bops_llex_product_not_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_left_right_absorptive_right : 
      bops_left_right_absorptive S rS addS mulS → bops_not_left_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  → 
      bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]. compute. 
       exists ((s1, t1), (s2, t2)).
       rewrite laS. 
       assert (F1 : (s1 +S (s2 *S s1)) =S (s2 *S s1)).
          assert (F2 := a_idemS (s2 *S s1)).
          assert (F3 := a_conS _ _ _ _ Q (refS (s2 *S s1))).        
          exact (tranS _ _ _ F3 F2). 
       rewrite F1. exact P.        
Defined.



(* right left *) 
Lemma bops_llex_product_right_left_absorptive : 
      bops_right_left_absorptive S rS addS mulS → 
      ((bops_right_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
      bops_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       - assert (J := ldS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s1 *S s2) ((s1 *S s2) +S s1)) ; intro K. 
         + apply ldT. 
         + apply refT. 
       - assert (J := ldS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s1 *S s2) ((s1 *S s2) +S s1)) ; intro K.
         + apply symS in J. apply symS in K.
           assert (F1 := tranS _ _ _ J K). 
           assert (F2 := F s1 s2). 
           rewrite F1 in F2. discriminate F2. 
         + apply refT. 
Defined. 

Lemma bops_llex_product_not_right_left_absorptive_left : 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). compute. rewrite P. reflexivity. Defined. 

Lemma bops_llex_product_not_right_left_absorptive_right : 
      bops_right_left_absorptive S rS addS mulS → bops_not_right_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  → 
      bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]; compute. 
       exists ((s1, t1), (s2, t2)).
       assert (K := laS s1 s2). rewrite K. apply symS in K. rewrite K. 
       assert (J : (s1 *S s2) =S ((s1 *S s2) +S s1)).
          assert (L := a_idemS (s1 *S s2)). 
          assert (M := a_conS _ _ _ _ (refS (s1 *S s2)) Q). apply symS in L. apply symS in M. 
          exact (tranS _ _ _ L M). 
       rewrite J. exact P. 
Defined.



(* right_right *) 
Lemma bops_llex_product_right_right_absorptive : 
      bops_right_right_absorptive S rS addS mulS → 
      ((bops_right_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
      bops_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [laT| F] [s1 t1] [s2 t2]; compute. 
       - assert (J := laS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s2 *S s1) ((s2 *S s1) +S s1)) ; intro K. 
         + apply laT. 
         + apply refT. 
       - assert (J := laS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s2 *S s1) ((s2 *S s1) +S s1)) ; intro K.
         + apply symS in J. apply symS in K.
           assert (F1 := tranS _ _ _ J K). 
           assert (F2 := F s1 s2). 
           rewrite F1 in F2. discriminate F2. 
         + apply refT. 
Defined.

Lemma bops_llex_product_not_right_right_absorptive_left : 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). compute. rewrite P. reflexivity. Defined. 


Lemma bops_llex_product_not_right_right_absorptive_right : 
  bops_right_right_absorptive S rS addS mulS → bops_not_right_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  →
  bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]; compute.
       exists ((s1, t1), (s2, t2)). 
       assert (K := laS s1 s2). rewrite K. apply symS in K. rewrite K. 
       assert (J : (s2 *S s1) =S ((s2 *S s1) +S s1)).
          assert (L := a_idemS (s2 *S s1)). 
          assert (M := a_conS _ _ _ _ (refS (s2 *S s1)) Q). apply symS in L. apply symS in M. 
          exact (tranS _ _ _ L M). 
       rewrite J. exact P. 
Defined. 



End Theory.

Section ACAS.

Section Decide.

Lemma bops_llex_product_exists_id_ann_equal_left 
(S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
(eqvS : eqv_proofs S eqS)
(eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T): 
      bops_exists_id_ann_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT).
       destruct eqvS, eqvT. split.
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
Defined. 

Lemma bops_llex_product_exists_id_ann_not_equal_left_v1
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T):         
      bops_exists_id_ann_not_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)).
       destruct eqvS, eqvT. split. split. 
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_llex_product_exists_id_ann_not_equal_left_v2
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_not_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)). 
       destruct eqvS, eqvT. split. split.        
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iT_not_aT.
       case_eq(eqS iS iS); intro A; reflexivity. 
Defined. 

Lemma bops_llex_product_exists_id_ann_not_equal_left_v3
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T): 
      bops_exists_id_ann_not_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_not_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)).
       destruct eqvS, eqvT. split. split.               
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_llex_product_exists_id_ann_equal_right
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T): 
      bops_exists_id_ann_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_product bS2 bT2)
                               (bop_llex argT eqS bS1 bT1). 
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT).
       destruct eqvS, eqvT. split.
       apply bop_product_is_id; auto.        
       apply bop_llex_is_ann; auto.
Defined. 


Lemma bops_llex_product_exists_id_ann_not_equal_right_v1
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_not_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_not_equal (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)
                                   (bop_llex argT eqS bS1 bT1). 
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)).
       destruct eqvS, eqvT. split. split.                      
       apply bop_product_is_id; auto. 
       apply bop_llex_is_ann; auto.
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_llex_product_exists_id_ann_not_equal_right_v2
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_not_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_not_equal (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)                                   
                                   (bop_llex argT eqS bS1 bT1). 
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)).
       destruct eqvS, eqvT. split. split. 
       apply bop_product_is_id; auto.        
       apply bop_llex_is_ann; auto.
       compute. rewrite iT_not_aT.
       case_eq(eqS iS iS); intro A; reflexivity. 
Defined. 

Lemma bops_llex_product_exists_id_ann_not_equal_right_v3
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_not_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_not_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_not_equal (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)
                                   (bop_llex argT eqS bS1 bT1).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)).
       destruct eqvS, eqvT. split. split.        
       apply bop_product_is_id; auto.        
       apply bop_llex_is_ann; auto.
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Definition bops_llex_product_exists_id_ann_decide_left 
           (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
           (eqvS : eqv_proofs S eqS)
           (eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T)           
           (PS : exists_id_ann_decidable S eqS bS1 bS2)
           (PT : exists_id_ann_decidable T eqT bT1 bT2) :
           exists_id_ann_decidable (S * T)
                                   (brel_product eqS eqT)
                                   (bop_llex argT eqS bS1 bT1)
                                   (bop_product bS2 bT2) :=
let symS := A_eqv_symmetric _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in     
let F0 := bop_llex_exists_id S T eqS eqT bS1 bT1 symS argT refT    in
let F1 := bop_llex_not_exists_id S T eqS eqT bS1 bT1 symS argT in  

let F3 := bop_product_exists_ann S T eqS eqT bS2 bT2     in 
let F2 := bop_product_not_exists_ann S T eqS eqT bS2 bT2 in

let F4 := bops_llex_product_exists_id_ann_equal_left S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2 in 
let F5 := bops_llex_product_exists_id_ann_not_equal_left_v2 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2 in 
let F6 := bops_llex_product_exists_id_ann_not_equal_left_v1 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2 in
let F7 := bops_llex_product_exists_id_ann_not_equal_left_v3 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 

let E5 := extract_exist_id_from_exists_id_ann_equal S eqS bS1 bS2 in
let E1 := extract_exist_id_from_exists_id_ann_equal T eqT bT1 bT2 in 

let E6 := extract_exist_ann_from_exists_id_ann_equal S eqS bS1 bS2 in
let E3 := extract_exist_ann_from_exists_id_ann_equal T eqT bT1 bT2 in

let E7 := extract_exist_id_from_exists_id_ann_not_equal S eqS bS1 bS2 in
let E2 := extract_exist_id_from_exists_id_ann_not_equal T eqT bT1 bT2 in 

let E8 := extract_exist_ann_from_exists_id_ann_not_equal S eqS bS1 bS2 in 
let E4 := extract_exist_ann_from_exists_id_ann_not_equal T eqT bT1 bT2 in

match PS with 
| Id_Ann_Proof_None _ _ _ _ (nidS, nannS)               =>
     Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS), F2 (inl nannS))
| Id_Ann_Proof_Id_None _ _ _ _ (idS, nannS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inl nannS))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS idT, F2 (inl nannS))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inl nannS))                     
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS (E1 idT_annT_equal), F2 (inl nannS))              
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS (E2 idT_annT_not_equal), F2 (inl nannS))              
  end   
| Id_Ann_Proof_None_Ann _ _ _ _ (nidS, annS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS),F2 (inr nannT))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS), F2 (inr nannT))                         
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS annT)                      
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS (E3 idT_annT_equal))  
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS (E4 idT_annT_not_equal))   
  end   
| Id_Ann_Proof_Equal _ _ _ _ (idS_annS_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inr nannT))                      
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 (E5 idS_annS_equal) idT, F2 (inr nannT))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inr nidT), F3 (E6 idS_annS_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Equal _ _ _ _ (F4 idS_annS_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F5 idS_annS_equal idT_annT_not_equal)
  end   
| Id_Ann_Proof_Not_Equal _ _ _ _ (idS_annS_not_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inr nannT))             
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
    Id_Ann_Proof_Id_None _ _ _ _ (F0 (E7 idS_annS_not_equal) idT, F2 (inr nannT))                    
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inr nidT), F3 (E8 idS_annS_not_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F6 idS_annS_not_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F7 idS_annS_not_equal idT_annT_not_equal)
  end   
end. 


Definition bops_llex_product_exists_id_ann_decide_right
           (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
           (eqvS : eqv_proofs S eqS)
           (eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T)           
           (PS : exists_id_ann_decidable S eqS bS2 bS1)
           (PT : exists_id_ann_decidable T eqT bT2 bT1) :
           exists_id_ann_decidable (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)
                                   (bop_llex argT eqS bS1 bT1) :=
let symS := A_eqv_symmetric _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in     
let F0 := bop_llex_exists_ann S T eqS eqT bS1 bT1 symS argT refT    in
let F1 := bop_llex_not_exists_ann S T eqS eqT bS1 bT1 symS argT in  

let F3 := bop_product_exists_id S T eqS eqT bS2 bT2     in 
let F2 := bop_product_not_exists_id S T eqS eqT bS2 bT2 in

let F4 := bops_llex_product_exists_id_ann_equal_right S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 
let F5 := bops_llex_product_exists_id_ann_not_equal_right_v2 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 
let F6 := bops_llex_product_exists_id_ann_not_equal_right_v1 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in
let F7 := bops_llex_product_exists_id_ann_not_equal_right_v3 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 

let E5 := extract_exist_id_from_exists_id_ann_equal S eqS bS2 bS1 in
let E1 := extract_exist_id_from_exists_id_ann_equal T eqT bT2 bT1 in 

let E6 := extract_exist_ann_from_exists_id_ann_equal S eqS bS2 bS1 in
let E3 := extract_exist_ann_from_exists_id_ann_equal T eqT bT2 bT1 in

let E7 := extract_exist_id_from_exists_id_ann_not_equal S eqS bS2 bS1 in
let E2 := extract_exist_id_from_exists_id_ann_not_equal T eqT bT2 bT1 in 

let E8 := extract_exist_ann_from_exists_id_ann_not_equal S eqS bS2 bS1 in 
let E4 := extract_exist_ann_from_exists_id_ann_not_equal T eqT bT2 bT1 in

match PS with 
| Id_Ann_Proof_None _ _ _ _ (nidS, nannS)               =>
     Id_Ann_Proof_None _ _ _ _ (F2 (inl nidS), F1 (inl nannS))
| Id_Ann_Proof_Id_None _ _ _ _ (idS, nannS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inl nannS))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 idS idT, F1 (inl nannS))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inl nannS))                     
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 idS (E1 idT_annT_equal), F1 (inl nannS))              
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 idS (E2 idT_annT_not_equal), F1 (inl nannS))              
  end   
| Id_Ann_Proof_None_Ann _ _ _ _ (nidS, annS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inl nidS), F1 (inr nannT))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inl nidS), F1 (inr nannT))                         
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inl nidS), F0 annS annT)                      
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inl nidS), F0 annS (E3 idT_annT_equal))  
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inl nidS), F0 annS (E4 idT_annT_not_equal))   
  end   
| Id_Ann_Proof_Equal _ _ _ _ (idS_annS_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inr nannT))                      
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 (E5 idS_annS_equal) idT, F1 (inr nannT))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inr nidT), F0 (E6 idS_annS_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Equal _ _ _ _ (F4 idS_annS_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F5 idS_annS_equal idT_annT_not_equal)
  end   
| Id_Ann_Proof_Not_Equal _ _ _ _ (idS_annS_not_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inr nannT))             
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
    Id_Ann_Proof_Id_None _ _ _ _ (F3 (E7 idS_annS_not_equal) idT, F1 (inr nannT))                    
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inr nidT), F0 (E8 idS_annS_not_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F6 idS_annS_not_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F7 idS_annS_not_equal idT_annT_not_equal)
  end   
end. 



    

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.
Variable eqvS : eqv_proofs S rS.
Variable eqvT : eqv_proofs T rT.   

Variable idem_addS : bop_idempotent S rS addS.  (* needed for associativity of llex *)
Variable comm_addS : bop_commutative S rS addS. (* needed for associativity of llex *)
Variable cng_addS  : bop_congruence S rS addS.
Variable cng_mulS  : bop_congruence S rS mulS. 
Variable cng_addT  : bop_congruence T rT addT.
Variable cng_mulT  : bop_congruence T rT mulT. 


Definition bops_llex_product_left_distributive_decide
           (comm_addT : bop_commutative T rT addT) 
           (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))           
           (ldS_d : bop_left_distributive_decidable S rS addS mulS)
           (ldT_d : bop_left_distributive_decidable T rT addT mulT)            
           (lcS_d : bop_left_cancellative_decidable S rS mulS)
           (lkT_d : bop_left_constant_decidable T rT mulT) : 
              bop_left_distributive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let selS_or_annT :=
    match selS_or_id_annT with
    | inl selS => inl selS
    | inr (_, annT) => inr annT 
    end
in
let cngS := A_eqv_congruence S rS eqvS in 
let refS := A_eqv_reflexive S rS eqvS in 
let symS := A_eqv_symmetric S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let symT := A_eqv_symmetric T rT eqvT in 
let trnT := A_eqv_transitive T rT eqvT in 
let F0 := bop_llex_product_left_distributive S T rS rT argT addS mulS addT mulT cngS refS symS
                                             trnS refT trnT cng_addS cng_mulS idem_addS selS_or_annT in 
let F1 := bop_llex_product_not_left_distributive_v1 S T rS rT wT argT addS mulS addT mulT in 
let F2 := bop_llex_product_not_left_distributive_v2 S T rS rT wS argT addS mulS addT mulT symS idem_addS  in
let F3 := bop_llex_product_not_left_distributive_v3 S T rS rT argT addS mulS addT mulT refS symS
                                                    trnS refT symT trnT cng_addS cng_mulS cng_addT idem_addS comm_addT selS_or_id_annT in 
match ldS_d with 
| inl ldS =>
   match ldT_d with 
   | inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (F0 ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (F0 ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (F3 ldS ldT not_lcS not_lkT)
                                     
            end 
       end 
   |inr not_ldT => inr _ (F2 not_ldT)
   end 
|inr not_ldS => inr _ (F1 not_ldS ) 
end. 


  
Definition bops_llex_product_right_distributive_decide
           (comm_addT : bop_commutative T rT addT) (*NB*)
           (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))           
           (rdS_d : bop_right_distributive_decidable S rS addS mulS)
           (rdT_d : bop_right_distributive_decidable T rT addT mulT)            
           (rcS_d : bop_right_cancellative_decidable S rS mulS)
           (rkT_d : bop_right_constant_decidable T rT mulT) : 
              bop_right_distributive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let selS_or_annT :=
    match selS_or_id_annT with
    | inl selS => inl selS
    | inr (_, annT) => inr annT 
    end
in
let cngS := A_eqv_congruence S rS eqvS in 
let refS := A_eqv_reflexive S rS eqvS in 
let symS := A_eqv_symmetric S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let symT := A_eqv_symmetric T rT eqvT in 
let trnT := A_eqv_transitive T rT eqvT in 
let F0 := bop_llex_product_right_distributive S T rS rT argT addS mulS addT mulT cngS refS symS
                                             trnS refT trnT cng_addS cng_mulS idem_addS selS_or_annT in 
let F1 := bop_llex_product_not_right_distributive_v1 S T rS rT wT argT addS mulS addT mulT in 
let F2 := bop_llex_product_not_right_distributive_v2 S T rS rT wS argT addS mulS addT mulT symS idem_addS  in
let F3 := bop_llex_product_not_right_distributive_v3 S T rS rT argT addS mulS addT mulT refS symS
                                                    trnS refT symT trnT cng_addS cng_mulS cng_addT idem_addS comm_addT selS_or_id_annT in
match rdS_d with 
| inl rdS =>
   match rdT_d with 
   | inl rdT =>
       match rcS_d with 
       | inl rcS => inl _ (F0 rdS rdT (inl _ rcS))
       | inr not_rcS => 
            match rkT_d with 
            | inl rkT => inl _ (F0 rdS rdT (inr _ rkT))
            | inr not_rkT => inr _ (F3 rdS rdT not_rcS not_rkT)
            end 
       end 
   |inr not_rdT => inr _ (F2 not_rdT)
   end 
|inr not_rdS => inr _ (F1 not_rdS ) 
end. 


Definition bops_llex_product_left_left_absorptive_decide 
      (laS_d : bops_left_left_absorptive_decidable S rS addS mulS)
      (laT_d : bops_left_left_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_left_decidable S rS mulS) : 
         bops_left_left_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_left_left_absorptive S T rS rT argT addS mulS addT mulT trnS refT in 
let F1 := bops_llex_product_not_left_left_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_left_left_absorptive_right S T rS rT argT addS mulS addT mulT refS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 


Definition bops_llex_product_left_right_absorptive_decide 
      (laS_d : bops_left_right_absorptive_decidable S rS addS mulS)
      (laT_d : bops_left_right_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_right_decidable S rS mulS) : 
         bops_left_right_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_left_right_absorptive S T rS rT argT addS mulS addT mulT trnS refT in 
let F1 := bops_llex_product_not_left_right_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_left_right_absorptive_right S T rS rT argT addS mulS addT mulT refS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 

Definition bops_llex_product_right_left_absorptive_decide 
      (laS_d : bops_right_left_absorptive_decidable S rS addS mulS)
      (laT_d : bops_right_left_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_left_decidable S rS mulS) : 
         bops_right_left_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in   
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_right_left_absorptive S T rS rT argT addS mulS addT mulT symS trnS refT in 
let F1 := bops_llex_product_not_right_left_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_right_left_absorptive_right S T rS rT argT addS mulS addT mulT refS symS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 

Definition bops_llex_product_right_right_absorptive_decide 
      (laS_d : bops_right_right_absorptive_decidable S rS addS mulS)
      (laT_d : bops_right_right_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_right_decidable S rS mulS) : 
         bops_right_right_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in   
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_right_right_absorptive S T rS rT argT addS mulS addT mulT symS trnS refT in 
let F1 := bops_llex_product_not_right_right_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_right_right_absorptive_right S T rS rT argT addS mulS addT mulT refS symS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 


End Decide. 

Section Proofs.     
(*
  id_ann_proofs

A_id_ann_plus_times_d
     : ∀ (S : Type) (eq : brel S) (plus times : binary_op S),
         id_ann_proofs S eq plus times
         → exists_id_ann_decidable S eq plus times

A_id_ann_times_plus_d
     : ∀ (S : Type) (eq : brel S) (plus times : binary_op S),
         id_ann_proofs S eq plus times
         → exists_id_ann_decidable S eq times plus


bops_llex_product_exists_id_ann_decide_left 
     : ∀ (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T),
         brel_symmetric S eqS
         → brel_transitive S eqS
           → brel_reflexive T eqT
             → ∀ (bS1 bS2 : binary_op S) (bT1 bT2 : binary_op T),
                 bop_commutative S eqS bS1
                 → exists_id_ann_decidable S eqS bS1 bS2
                   → exists_id_ann_decidable T eqT bT1 bT2
                     → exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) (bop_llex argT eqS bS1 bT1)
                         (bop_product bS2 bT2)

So, have 

A_id_ann_plus_times_d : exists_id_ann_decidable S eqS plusS timesS
A_id_ann_times_plus_d : exists_id_ann_decidable S eq timesS plusS
and 
A_id_ann_plus_times_d : exists_id_ann_decidable T eqT plusT timesT
A_id_ann_times_plus_d : exists_id_ann_decidable T eqT timesT plusT

want 

A_id_ann_plus_times_d : exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) (bop_llex argT eqS plusS plusT)
                         (bop_product timesS timesT)

from bops_llex_product_exists_id_ann_decide_left. 

I need 

A_id_ann_times_plus_d : exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) (bop_product timesS timesT)
                         (bop_llex argT eqS plusS plusT)


bops_llex_product_exists_id_ann_decide_right: 
     : ∀ (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T),
         brel_symmetric S eqS
         → brel_transitive S eqS
           → brel_reflexive T eqT
             → ∀ (bS1 bS2 : binary_op S) (bT1 bT2 : binary_op T),
                 bop_commutative S eqS bS1
                 → exists_id_ann_decidable S eqS bS2 bS1
                   → exists_id_ann_decidable T eqT bT2 bT1
                     → exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) 
                         (bop_product bS2 bT2)
                         (bop_llex argT eqS bS1 bT1)

 *)

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.
Variable eqvS : eqv_proofs S rS.
Variable eqvT : eqv_proofs T rT.   

(*
Variable idem_addS : bop_idempotent S rS addS.  (* needed for associativity of llex *)
Variable comm_addS : bop_commutative S rS addS. (* needed for associativity of llex *)
Variable cng_addS  : bop_congruence S rS addS.
Variable cng_mulS  : bop_congruence S rS mulS. 
Variable cng_addT  : bop_congruence T rT addT.
Variable cng_mulT  : bop_congruence T rT mulT. 
*) 

  
Definition id_ann_proofs_llex_product
 (pS : id_ann_proofs S rS addS mulS)
 (pT : id_ann_proofs T rT addT mulT) : 
        id_ann_proofs (S * T) 
           (brel_product rS rT) 
           (bop_llex argT rS addS addT)
           (bop_product mulS mulT) := 
let pS_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ _ pS in 
let pS_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ pS in 
let pT_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ _ pT in 
let pT_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ pT in 
{|
  A_id_ann_plus_times_d := bops_llex_product_exists_id_ann_decide_left S T rS rT argT eqvS eqvT
                              addS mulS addT mulT pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; A_id_ann_times_plus_d := bops_llex_product_exists_id_ann_decide_right S T rS rT argT eqvS eqvT
                              addS mulS addT mulT pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.

(*   bs_proofs   *) 


Definition bs_proofs_llex_product_idempotent_case
           (id_is_annT : (bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT))
           (addPS : sg_CI_proofs S rS addS)
           (addPT : sg_CI_proofs T rT addT)
           (mulPS : sg_proofs S rS mulS)
           (mulPT : sg_proofs T rT mulT)
           (pS : bs_proofs  S rS addS mulS)
           (pT : bs_proofs  T rT addT mulT) : 
                bs_proofs (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) := 
let idem_addS := A_sg_CI_idempotent _ _ _ addPS in 
let comm_addT := A_sg_CI_commutative _ _ _ addPT in
let cng_addS := A_sg_CI_congruence _ _ _ addPS in
let cng_mulS := A_sg_congruence _ _ _ mulPS in 
let cng_addT := A_sg_CI_congruence _ _ _ addPT in 
let LC := A_sg_left_cancel_d _ _ _ mulPS  in 
let RC := A_sg_right_cancel_d _ _ _ mulPS in
let LK := A_sg_left_constant_d _ _ _ mulPT in 
let RK := A_sg_right_constant_d _ _ _ mulPT in                
let ALS := A_sg_anti_left_d _ _ _ mulPS in 
let ARS := A_sg_anti_right_d _ _ _ mulPS in 
let LDS := A_bs_left_distributive_d _ _ _ _ pS in 
let LDT := A_bs_left_distributive_d _ _ _ _  pT in 
let RDS := A_bs_right_distributive_d _ _ _ _ pS in 
let RDT := A_bs_right_distributive_d _ _ _ _ pT in
let LLAS := A_bs_left_left_absorptive_d _ _ _ _ pS in
let LLAT := A_bs_left_left_absorptive_d _ _ _ _ pT in
let LRAS := A_bs_left_right_absorptive_d _ _ _ _ pS in
let LRAT := A_bs_left_right_absorptive_d _ _ _ _ pT in
let RLAS := A_bs_right_left_absorptive_d _ _ _ _ pS in
let RLAT := A_bs_right_left_absorptive_d _ _ _ _ pT in
let RRAS := A_bs_right_right_absorptive_d _ _ _ _ pS in
let RRAT := A_bs_right_right_absorptive_d _ _ _ _ pT in
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                               cng_addS cng_mulS cng_addT comm_addT (inr id_is_annT) LDS LDT LC LK 
; A_bs_right_distributive_d   := 
    bops_llex_product_right_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS cng_mulS cng_addT comm_addT (inr id_is_annT) RDS RDT RC RK 
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LLAS LLAT ALS 
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LRAS LRAT ARS 
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RLAS RLAT ALS 
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RRAS RRAT ARS 
|}.

Definition bs_proofs_llex_product_selective_case
           (addPS : sg_CS_proofs S rS addS)
           (addPT : sg_CI_proofs T rT addT)
           (mulPS : sg_proofs S rS mulS)
           (mulPT : sg_proofs T rT mulT)
           (pS : bs_proofs  S rS addS mulS)
           (pT : bs_proofs  T rT addT mulT) : 
                bs_proofs (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) := 
let selS     := A_sg_CS_selective _ _ _ addPS in
let idem_addS := bop_selective_implies_idempotent S rS addS selS in 
let comm_addT := A_sg_CI_commutative _ _ _ addPT in
let cng_addS := A_sg_CS_congruence _ _ _ addPS in
let cng_mulS := A_sg_congruence _ _ _ mulPS in 
let cng_addT := A_sg_CI_congruence _ _ _ addPT in 
let LC := A_sg_left_cancel_d _ _ _ mulPS  in 
let RC := A_sg_right_cancel_d _ _ _ mulPS in
let LK := A_sg_left_constant_d _ _ _ mulPT in 
let RK := A_sg_right_constant_d _ _ _ mulPT in                
let ALS := A_sg_anti_left_d _ _ _ mulPS in 
let ARS := A_sg_anti_right_d _ _ _ mulPS in 
let LDS := A_bs_left_distributive_d _ _ _ _ pS in 
let LDT := A_bs_left_distributive_d _ _ _ _  pT in 
let RDS := A_bs_right_distributive_d _ _ _ _ pS in 
let RDT := A_bs_right_distributive_d _ _ _ _ pT in
let LLAS := A_bs_left_left_absorptive_d _ _ _ _ pS in
let LLAT := A_bs_left_left_absorptive_d _ _ _ _ pT in
let LRAS := A_bs_left_right_absorptive_d _ _ _ _ pS in
let LRAT := A_bs_left_right_absorptive_d _ _ _ _ pT in
let RLAS := A_bs_right_left_absorptive_d _ _ _ _ pS in
let RLAT := A_bs_right_left_absorptive_d _ _ _ _ pT in
let RRAS := A_bs_right_right_absorptive_d _ _ _ _ pS in
let RRAT := A_bs_right_right_absorptive_d _ _ _ _ pT in
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                               cng_addS cng_mulS cng_addT comm_addT (inl selS) LDS LDT LC LK 
; A_bs_right_distributive_d   := 
    bops_llex_product_right_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS cng_mulS cng_addT comm_addT (inl selS) RDS RDT RC RK 
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LLAS LLAT ALS 
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LRAS LRAT ARS 
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RLAS RLAT ALS 
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RRAS RRAT ARS 
|}.



Definition bs_proofs_llex_product_v3 
           (addPS : sg_CS_proofs S rS addS)
           (addPT : sg_CS_proofs T rT addT)
           (mulPS : sg_proofs S rS mulS)
           (mulPT : sg_proofs T rT mulT)
           (pS : bs_proofs  S rS addS mulS)
           (pT : bs_proofs  T rT addT mulT) : 
                bs_proofs (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) := 
let selS     := A_sg_CS_selective _ _ _ addPS in
let idem_addS := bop_selective_implies_idempotent S rS addS selS in 
let comm_addT := A_sg_CS_commutative _ _ _ addPT in
let cng_addS := A_sg_CS_congruence _ _ _ addPS in
let cng_mulS := A_sg_congruence _ _ _ mulPS in 
let cng_addT := A_sg_CS_congruence _ _ _ addPT in 
let LC := A_sg_left_cancel_d _ _ _ mulPS  in 
let RC := A_sg_right_cancel_d _ _ _ mulPS in
let LK := A_sg_left_constant_d _ _ _ mulPT in 
let RK := A_sg_right_constant_d _ _ _ mulPT in                
let ALS := A_sg_anti_left_d _ _ _ mulPS in 
let ARS := A_sg_anti_right_d _ _ _ mulPS in 
let LDS := A_bs_left_distributive_d _ _ _ _ pS in 
let LDT := A_bs_left_distributive_d _ _ _ _  pT in 
let RDS := A_bs_right_distributive_d _ _ _ _ pS in 
let RDT := A_bs_right_distributive_d _ _ _ _ pT in
let LLAS := A_bs_left_left_absorptive_d _ _ _ _ pS in
let LLAT := A_bs_left_left_absorptive_d _ _ _ _ pT in
let LRAS := A_bs_left_right_absorptive_d _ _ _ _ pS in
let LRAT := A_bs_left_right_absorptive_d _ _ _ _ pT in
let RLAS := A_bs_right_left_absorptive_d _ _ _ _ pS in
let RLAT := A_bs_right_left_absorptive_d _ _ _ _ pT in
let RRAS := A_bs_right_right_absorptive_d _ _ _ _ pS in
let RRAT := A_bs_right_right_absorptive_d _ _ _ _ pT in
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                               cng_addS cng_mulS cng_addT comm_addT (inl selS) LDS LDT LC LK 
; A_bs_right_distributive_d   := 
    bops_llex_product_right_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS cng_mulS cng_addT comm_addT (inl selS) RDS RDT RC RK 
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LLAS LLAT ALS 
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LRAS LRAT ARS 
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RLAS RLAT ALS 
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RRAS RRAT ARS 
|}.


Definition bs_proofs_llex_product_INTERNAL
           (addPS : sg_proofs S rS addS)
           (addPT : sg_proofs T rT addT)
           (mulPS : sg_proofs S rS mulS)
           (mulPT : sg_proofs T rT mulT)
           (pS : bs_proofs  S rS addS mulS)
           (pT : bs_proofs  T rT addT mulT)
           (idem_addS : bop_idempotent S rS addS)
           (comm_addT : bop_commutative T rT addT) 
           (P : (bop_selective S rS addS) +
                             ((bop_is_id T rT addT argT) *
                             (bop_is_ann T rT mulT argT))) : 
                bs_proofs (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) := 
let cng_addS := A_sg_congruence _ _ _ addPS in
let cng_mulS := A_sg_congruence _ _ _ mulPS in 
let cng_addT := A_sg_congruence _ _ _ addPT in 
let LC := A_sg_left_cancel_d _ _ _ mulPS  in 
let RC := A_sg_right_cancel_d _ _ _ mulPS in
let LK := A_sg_left_constant_d _ _ _ mulPT in 
let RK := A_sg_right_constant_d _ _ _ mulPT in                
let ALS := A_sg_anti_left_d _ _ _ mulPS in 
let ARS := A_sg_anti_right_d _ _ _ mulPS in 
let LDS := A_bs_left_distributive_d _ _ _ _ pS in 
let LDT := A_bs_left_distributive_d _ _ _ _  pT in 
let RDS := A_bs_right_distributive_d _ _ _ _ pS in 
let RDT := A_bs_right_distributive_d _ _ _ _ pT in
let LLAS := A_bs_left_left_absorptive_d _ _ _ _ pS in
let LLAT := A_bs_left_left_absorptive_d _ _ _ _ pT in
let LRAS := A_bs_left_right_absorptive_d _ _ _ _ pS in
let LRAT := A_bs_left_right_absorptive_d _ _ _ _ pT in
let RLAS := A_bs_right_left_absorptive_d _ _ _ _ pS in
let RLAT := A_bs_right_left_absorptive_d _ _ _ _ pT in
let RRAS := A_bs_right_right_absorptive_d _ _ _ _ pS in
let RRAT := A_bs_right_right_absorptive_d _ _ _ _ pT in
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                               cng_addS cng_mulS cng_addT comm_addT P LDS LDT LC LK 
; A_bs_right_distributive_d   := 
    bops_llex_product_right_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS cng_mulS cng_addT comm_addT P RDS RDT RC RK 
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LLAS LLAT ALS 
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LRAS LRAT ARS 
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RLAS RLAT ALS 
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RRAS RRAT ARS 
|}.




(* *) 

End Proofs.

Section Combinators.



Definition A_llex_product_INTERNAL
           (S T : Type)
           (argT : T) 
           (A : A_bs S)
           (B : A_bs T)
           (idemS : bop_idempotent S (A_eqv_eq _ (A_bs_eqv _ A)) (A_bs_plus _ A))
           (commS : bop_commutative S (A_eqv_eq _ (A_bs_eqv _ A)) (A_bs_plus _ A))
           (commT : bop_commutative T (A_eqv_eq _ (A_bs_eqv _ B)) (A_bs_plus _ B))           
           (P : (bop_selective S (A_eqv_eq _ (A_bs_eqv _ A)) (A_bs_plus _ A)) +
                ((bop_is_id T (A_eqv_eq _ (A_bs_eqv _ B)) (A_bs_plus _ B) argT)
                 *
                 (bop_is_ann T (A_eqv_eq _ (A_bs_eqv _ B)) (A_bs_times _ B) argT)
                )
           ) : A_bs (S * T) :=
let eqvS   := A_bs_eqv _ A in
let eqvT   := A_bs_eqv _ B in
let eqS    := A_eqv_eq _ eqvS in
let eqT    := A_eqv_eq _ eqvT in
let eqvPS  := A_eqv_proofs _ eqvS in
let eqvPT  := A_eqv_proofs _ eqvT in
let plusS  := A_bs_plus _ A in
let plusT  := A_bs_plus _ B in
let timesS  := A_bs_times _ A in
let timesT  := A_bs_times _ B in
let id_annS  := A_bs_id_ann_proofs _ A in
let id_annT  := A_bs_id_ann_proofs _ B in
let plusPS  := A_bs_plus_proofs _ A in
let plusPT  := A_bs_plus_proofs _ B in
let timesPS  := A_bs_times_proofs _ A in
let timesPT  := A_bs_times_proofs _ B in
let pS       := A_bs_proofs _ A in
let pT       := A_bs_proofs _ B in 
(* these should move to the A_eqv_proof structures *)
let wS     := A_eqv_witness _ eqvS in
let f      := A_eqv_new _ eqvS in
let ntS    := A_eqv_not_trivial _ eqvS in 
let wT     := A_eqv_witness _ eqvT in
let g      := A_eqv_new _ eqvT in
let ntT    := A_eqv_not_trivial _ eqvT in
match P with
| inl sel         =>
{|
  A_bs_eqv           := A_eqv_product S T eqvS eqvT 
; A_bs_plus          := bop_llex wT eqS plusS plusT 
; A_bs_times         := bop_product timesS timesT
; A_bs_plus_proofs   := sg_llex_proofs S T wS wT wT eqS eqT f ntS g ntT plusS plusT eqvPS eqvPT plusPS plusPT idemS commS (inl sel)
; A_bs_times_proofs  := sg_proofs_product S T eqS eqT timesS timesT wS f wT g ntS ntT eqvPS eqvPT timesPS timesPT 
; A_bs_id_ann_proofs := id_ann_proofs_llex_product S T wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT id_annS id_annT 
; A_bs_proofs        := bs_proofs_llex_product_INTERNAL S T wS wT wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT plusPS plusPT timesPS timesPT pS pT idemS commT (inl sel) 
; A_bs_ast           := Ast_bs_llex_product (A_bs_ast S A, A_bs_ast T B)
|}
| inr (idP, annP) =>
{|
  A_bs_eqv           := A_eqv_product S T eqvS eqvT 
; A_bs_plus          := bop_llex argT eqS plusS plusT 
; A_bs_times         := bop_product timesS timesT
; A_bs_plus_proofs   := sg_llex_proofs S T wS wT argT eqS eqT f ntS g ntT plusS plusT eqvPS eqvPT plusPS plusPT idemS commS (inr idP)
; A_bs_times_proofs  := sg_proofs_product S T eqS eqT timesS timesT wS f wT g ntS ntT eqvPS eqvPT timesPS timesPT 
; A_bs_id_ann_proofs := id_ann_proofs_llex_product S T argT eqS eqT plusS timesS plusT timesT eqvPS eqvPT id_annS id_annT 
; A_bs_proofs        := bs_proofs_llex_product_INTERNAL S T wS wT argT eqS eqT plusS timesS plusT timesT eqvPS eqvPT plusPS plusPT timesPS timesPT pS pT idemS commT (inr(idP, annP))
; A_bs_ast           := Ast_bs_llex_product (A_bs_ast S A, A_bs_ast T B)
|}
end.    

  

Definition A_llex_product_from_CS_CI (S T : Type) (A : A_bs_CS S) (B : A_bs_CI T) : A_bs_CI (S * T) :=
let eqvS   := A_bs_CS_eqv _ A in
let eqvT   := A_bs_CI_eqv _ B in
let eqS    := A_eqv_eq _ eqvS in
let eqT    := A_eqv_eq _ eqvT in
let eqvPS  := A_eqv_proofs _ eqvS in
let eqvPT  := A_eqv_proofs _ eqvT in
let plusS  := A_bs_CS_plus _ A in
let plusT  := A_bs_CI_plus _ B in
let timesS  := A_bs_CS_times _ A in
let timesT  := A_bs_CI_times _ B in
let id_annS  := A_bs_CS_id_ann_proofs _ A in
let id_annT  := A_bs_CI_id_ann_proofs _ B in
let plusPS  := A_bs_CS_plus_proofs _ A in
let plusPT  := A_bs_CI_plus_proofs _ B in
let timesPS  := A_bs_CS_times_proofs _ A in
let timesPT  := A_bs_CI_times_proofs _ B in
let pS       := A_bs_CS_proofs _ A in
let pT       := A_bs_CI_proofs _ B in 
(* these should move to the A_eqv_proof structures *)
let wS     := A_eqv_witness _ eqvS in
let f      := A_eqv_new _ eqvS in
let ntS    := A_eqv_not_trivial _ eqvS in 
let wT     := A_eqv_witness _ eqvT in
let g      := A_eqv_new _ eqvT in
let ntT    := A_eqv_not_trivial _ eqvT in 
{|
  A_bs_CI_eqv           := A_eqv_product S T eqvS eqvT 
; A_bs_CI_plus          := bop_llex wT eqS plusS plusT 
; A_bs_CI_times         := bop_product timesS timesT
; A_bs_CI_plus_proofs   := sg_CI_llex_proofs_v2 S T wS wT eqS eqT plusS plusT eqvPS eqvPT plusPS plusPT 
; A_bs_CI_times_proofs  := sg_proofs_product S T eqS eqT timesS timesT wS f wT g ntS ntT eqvPS eqvPT timesPS timesPT 
; A_bs_CI_id_ann_proofs := id_ann_proofs_llex_product S T wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT id_annS id_annT 
; A_bs_CI_proofs        := bs_proofs_llex_product_selective_case S T wS wT wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT plusPS plusPT timesPS timesPT pS pT 
; A_bs_CI_ast           := Ast_bs_llex_product (A_bs_CS_ast S A, A_bs_CI_ast T B)
|}.


Definition A_llex_product_from_CS_CS (S T : Type) (A : A_bs_CS S) (B : A_bs_CS T) : A_bs_CS (S * T) :=
let eqvS   := A_bs_CS_eqv _ A in
let eqvT   := A_bs_CS_eqv _ B in
let eqS    := A_eqv_eq _ eqvS in
let eqT    := A_eqv_eq _ eqvT in
let eqvPS  := A_eqv_proofs _ eqvS in
let eqvPT  := A_eqv_proofs _ eqvT in
let plusS  := A_bs_CS_plus _ A in
let plusT  := A_bs_CS_plus _ B in
let timesS  := A_bs_CS_times _ A in
let timesT  := A_bs_CS_times _ B in
let id_annS  := A_bs_CS_id_ann_proofs _ A in
let id_annT  := A_bs_CS_id_ann_proofs _ B in
let plusPS  := A_bs_CS_plus_proofs _ A in
let plusPT  := A_bs_CS_plus_proofs _ B in
let timesPS  := A_bs_CS_times_proofs _ A in
let timesPT  := A_bs_CS_times_proofs _ B in
let pS       := A_bs_CS_proofs _ A in
let pT       := A_bs_CS_proofs _ B in 
(* these should move to the A_eqv_proof structures *)
let wS     := A_eqv_witness _ eqvS in
let f      := A_eqv_new _ eqvS in
let ntS    := A_eqv_not_trivial _ eqvS in 
let wT     := A_eqv_witness _ eqvT in
let g      := A_eqv_new _ eqvT in
let ntT    := A_eqv_not_trivial _ eqvT in 
{|
  A_bs_CS_eqv           := A_eqv_product S T eqvS eqvT 
; A_bs_CS_plus          := bop_llex wT eqS plusS plusT 
; A_bs_CS_times         := bop_product timesS timesT
; A_bs_CS_plus_proofs   := sg_CS_llex_proofs S T wT eqS eqT plusS plusT eqvPS eqvPT plusPS plusPT 
; A_bs_CS_times_proofs  := sg_proofs_product S T eqS eqT timesS timesT wS f wT g ntS ntT eqvPS eqvPT timesPS timesPT 
; A_bs_CS_id_ann_proofs := id_ann_proofs_llex_product S T wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT id_annS id_annT 
; A_bs_CS_proofs        := bs_proofs_llex_product_v3 S T wS wT wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT plusPS plusPT timesPS timesPT pS pT 
; A_bs_CS_ast           := Ast_bs_llex_product (A_bs_CS_ast S A, A_bs_CS_ast T B)
|}.



End Combinators. 
End ACAS.


Section AMCAS.

Open Scope list_scope.
Open Scope string_scope.

Definition A_mcas_bs_llex_product (S T : Type) (A : A_bs_mcas S)  (B : A_bs_mcas T)  : A_bs_mcas (S * T) :=
match A_bs_mcas_cast_up _ A, A_bs_mcas_cast_up _ B with
| A_BS_bs _ A', A_BS_bs _ B'               =>
  let sgPS := A_bs_plus_proofs _ A' in
  let sgPT := A_bs_plus_proofs _ B' in   
  match A_sg_commutative_d _ _ _ sgPS, A_sg_commutative_d _ _ _ sgPT with
  | inl commS, inl commT =>
    match A_sg_idempotent_d _ _ _ sgPS with
    | inl idemS => 
      match A_sg_selective_d _ _ _ sgPS with
      | inl selS => A_bs_classify _ (A_BS_bs _ (A_llex_product_INTERNAL S T (A_eqv_witness _ (A_bs_eqv _ B')) A' B' idemS commS commT (inl selS)))
      | inr nsel =>
        match A_id_ann_plus_times_d _ _ _ _ (A_bs_id_ann_proofs _ B') with 
        | Id_Ann_Proof_Equal _ _ _ _ (existT _ id (idP, annP)) =>
             A_bs_classify _ (A_BS_bs _ (A_llex_product_INTERNAL S T id A' B' idemS commS commT (inr (idP, annP))))
        | _  => A_BS_Error _ ("mcas_llex_product : second algebra must have an additive identity that is a multiplicative annihilator" :: nil)     
        end
      end
    | _ => A_BS_Error _ ("mcas_llex_product : first algebra must have an addition that is idempotent" :: nil)        
    end
  | inl _, inr _       => A_BS_Error _ ("mcas_llex_product : the second algebra must have an commutative addition" :: nil)
  | inr _, inl _       => A_BS_Error _ ("mcas_llex_product : the first algebra must have a commutative addition" :: nil)        
  | inr _, inr _       => A_BS_Error _ ("mcas_llex_product : both algebras must have commutative additions" :: nil)        
  end
| A_BS_Error _ sl1, A_BS_Error _ sl2 => A_BS_Error _ (sl1 ++ sl2)
| A_BS_Error _ sl1, _                => A_BS_Error _ sl1
| _,  A_BS_Error _ sl2               => A_BS_Error _ sl2
| _, _                               => A_BS_Error _ ("Internal Error : mcas_lex_product" :: nil)
end.

End AMCAS.


Section CAS.


Section Certify.

Definition bops_llex_product_exists_id_ann_certify
           {S T : Type} 
           (PS : @exists_id_ann_certificate S)
           (PT : @exists_id_ann_certificate T) :
                 @exists_id_ann_certificate (S * T) := 
match PS with 
| Id_Ann_Cert_None           => Id_Ann_Cert_None  
| Id_Ann_Cert_Id_None idS    =>
  match PT with 
  | Id_Ann_Cert_None           => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT    => Id_Ann_Cert_Id_None (idS, idT)
  | Id_Ann_Cert_None_Ann annT  => Id_Ann_Cert_None
  | Id_Ann_Cert_Equal idT_annT => Id_Ann_Cert_Id_None  (idS, idT_annT) 
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Id_None  (idS, idT) 
  end   
| Id_Ann_Cert_None_Ann annS   =>
  match PT with 
  | Id_Ann_Cert_None              => Id_Ann_Cert_None  
  | Id_Ann_Cert_Id_None idT       => Id_Ann_Cert_None  
  | Id_Ann_Cert_None_Ann  annT    => Id_Ann_Cert_None_Ann (annS, annT)                      
  | Id_Ann_Cert_Equal  (idT_annT) => Id_Ann_Cert_None_Ann  (annS, idT_annT)  
  | Id_Ann_Cert_Not_Equal  (idT, annT) => Id_Ann_Cert_None_Ann  (annS, annT)  
  end   
| Id_Ann_Cert_Equal  (idS_annS)  =>
  match PT with 
  | Id_Ann_Cert_None             => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT      => Id_Ann_Cert_Id_None (idS_annS, idT)
  | Id_Ann_Cert_None_Ann annT    => Id_Ann_Cert_None_Ann (idS_annS, annT)
  | Id_Ann_Cert_Equal (idT_annT) => Id_Ann_Cert_Equal (idS_annS, idT_annT)
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Not_Equal ((idS_annS, idT), (idS_annS, annT))
  end   
| Id_Ann_Cert_Not_Equal  (idS, annS)  =>
  match PT with 
  | Id_Ann_Cert_None             => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT      => Id_Ann_Cert_Id_None (idS, idT) 
  | Id_Ann_Cert_None_Ann annT    => Id_Ann_Cert_None_Ann (annS, annT)
  | Id_Ann_Cert_Equal (idT_annT) => Id_Ann_Cert_Not_Equal ((idS, idT_annT), (annS, idT_annT))
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Not_Equal ((idS, idT), (annS, annT))
  end   
end.



Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.


Definition bops_llex_product_left_distributive_certify_new
(*     (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T)) *) 
     (lcS_d : @check_left_cancellative S) 
     (lkT_d : @check_left_constant T) 
     (ldS_d : @check_left_distributive S) 
     (ldT_d : @check_left_distributive T) : 
     @check_left_distributive (S * T) := 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive  
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive  
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive  
                    (witness_llex_product_not_left_distributive_new S T rS rT argT addS mulS addT mulT (* selS_or_id_annT *) s1 s2 s3 t1 t2 t3 )
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.


(*
Definition bops_llex_product_left_distributive_certify
     (lcS_d : @check_left_cancellative S) 
     (lkT_d : @check_left_constant T) 
     (ldS_d : @check_left_distributive S) 
     (ldT_d : @check_left_distributive T) : 
     @check_left_distributive (S * T) := 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive  
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive  
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive  
                    (witness_llex_product_not_left_distributive_with_selectivity S T rS rT addS mulS addT mulT s1 s2 s3 t1 t2 t3)
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.


Definition bops_llex_product_left_distributive_certify_without_selectivity 
     (lcS_d : @check_left_cancellative S) 
     (lkT_d : @check_left_constant T) 
     (ldS_d : @check_left_distributive S) 
     (ldT_d : @check_left_distributive T) : 
     @check_left_distributive (S * T) := 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive  
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive  
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive  
                    (witness_llex_product_not_left_distributive_without_selectivity S T rS rT argT addS mulS addT mulT s1 s2 s3 t1 t2 t3)
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.
*) 



Definition bops_llex_product_right_distributive_certify_new
(*     (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T))  *) 
     (lcS_d : check_right_cancellative (S := S)) 
     (lkT_d : check_right_constant (S := T)) 
     (ldS_d : check_right_distributive (S := S)) 
     (ldT_d : check_right_distributive (S := T)) : 
     check_right_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive  
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive  
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive  
                     (witness_llex_product_not_right_distributive_new S T rS rT argT addS mulS addT mulT (* selS_or_id_annT *) s1 s2 s3 t1 t2 t3) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.


(*  
Definition bops_llex_product_right_distributive_certify
     (lcS_d : check_right_cancellative (S := S)) 
     (lkT_d : check_right_constant (S := T)) 
     (ldS_d : check_right_distributive (S := S)) 
     (ldT_d : check_right_distributive (S := T)) : 
     check_right_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive  
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive  
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive  
                     (witness_llex_product_not_right_distributive_with_selectivity S T rS rT addS mulS addT mulT s1 s2 s3 t1 t2 t3) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.

Definition bops_llex_product_right_distributive_certify_without_selectivity 
     (lcS_d : check_right_cancellative (S := S)) 
     (lkT_d : check_right_constant (S := T)) 
     (ldS_d : check_right_distributive (S := S)) 
     (ldT_d : check_right_distributive (S := T)) : 
     check_right_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive  
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive  
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive  
                     (witness_llex_product_not_left_distributive_without_selectivity S T rS rT argT addS mulS addT mulT s1 s2 s3 t1 t2 t3) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.
 *)


Definition bops_llex_product_left_left_absorptive_certify 
     (dS : @check_left_left_absorptive S) 
     (dT : @check_left_left_absorptive T)
     (alS : @check_anti_left S) : 
        @check_left_left_absorptive (S * T) := 
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive  
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Left_Left_Absorptive  
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Left_Left_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive  ((s1, argT), (s2, argT))
end. 


Definition bops_llex_product_left_right_absorptive_certify 
     (dS : @check_left_right_absorptive S)
     (dT : @check_left_right_absorptive T) 
     (alS : @check_anti_right S) : 
       @check_left_right_absorptive (S * T) := 
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive  
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Left_Right_Absorptive  
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Left_Right_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive  ((s1, wT), (s2, wT))
end. 



Definition bops_llex_product_right_left_absorptive_certify 
     (dS : @check_right_left_absorptive S) 
     (dT : @check_right_left_absorptive T)
     (alS : @check_anti_left S) : 
       @check_right_left_absorptive (S * T) := 
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive  
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Right_Left_Absorptive  
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Right_Left_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive  ((s1, wT), (s2, wT))
end. 


Definition bops_llex_product_right_right_absorptive_certify 
     (dS : @check_right_right_absorptive S) 
     (dT : @check_right_right_absorptive T) 
     (alS : @check_anti_right S) : 
       @check_right_right_absorptive (S * T) := 
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive  
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Right_Right_Absorptive  
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Right_Right_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive  ((s1, wT), (s2, wT))
end. 

End Certify. 

Section Certificates.

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.


Definition id_ann_certs_llex_product
 (pS : @id_ann_certificates S)
 (pT : @id_ann_certificates T) : @id_ann_certificates (S * T) := 
let pS_id_ann_plus_times_d := id_ann_plus_times_d pS in 
let pS_id_ann_times_plus_d := id_ann_times_plus_d pS in 
let pT_id_ann_plus_times_d := id_ann_plus_times_d pT in 
let pT_id_ann_times_plus_d := id_ann_times_plus_d pT in 
{|
  id_ann_plus_times_d := bops_llex_product_exists_id_ann_certify pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; id_ann_times_plus_d := bops_llex_product_exists_id_ann_certify pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.

(*
Definition bs_certs_llex_product_without_selectivity
           (mulPS : @sg_certificates S)
           (mulPT : @sg_certificates T)
           (pS : @bs_certificates  S)
           (pT : @bs_certificates  T) : @bs_certificates (S * T) :=
let LC := sg_left_cancel_d mulPS  in 
let RC := sg_right_cancel_d mulPS in
let LK := sg_left_constant_d mulPT in 
let RK := sg_right_constant_d mulPT in                
let ALS := sg_anti_left_d mulPS in 
let ARS := sg_anti_right_d mulPS in 
let LDS := bs_left_distributive_d pS in 
let LDT := bs_left_distributive_d  pT in 
let RDS := bs_right_distributive_d pS in 
let RDT := bs_right_distributive_d pT in
let LLAS := bs_left_left_absorptive_d pS in
let LLAT := bs_left_left_absorptive_d pT in
let LRAS := bs_left_right_absorptive_d pS in
let LRAT := bs_left_right_absorptive_d pT in
let RLAS := bs_right_left_absorptive_d pS in
let RLAT := bs_right_left_absorptive_d pT in
let RRAS := bs_right_right_absorptive_d pS in
let RRAT := bs_right_right_absorptive_d pT in
{|
  bs_left_distributive_d    := 
    bops_llex_product_left_distributive_certify_without_selectivity S T wS wT argT rS rT addS mulS addT mulT LC LK LDS LDT
; bs_right_distributive_d   := 
    bops_llex_product_right_distributive_certify_without_selectivity S T wS wT argT rS rT addS mulS addT mulT RC RK RDS RDT 
; bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_certify S T argT LLAS LLAT ALS 
; bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_certify S T argT LRAS LRAT ARS 
; bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_certify S T argT RLAS RLAT ALS 
; bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_certify S T argT RRAS RRAT ARS 
|}.


Definition bs_certs_llex_product
           (mulPS : @sg_certificates S)
           (mulPT : @sg_certificates T)
           (pS : @bs_certificates  S)
           (pT : @bs_certificates  T) : @bs_certificates (S * T) :=
let LC := sg_left_cancel_d mulPS  in 
let RC := sg_right_cancel_d mulPS in
let LK := sg_left_constant_d mulPT in 
let RK := sg_right_constant_d mulPT in                
let ALS := sg_anti_left_d mulPS in 
let ARS := sg_anti_right_d mulPS in 
let LDS := bs_left_distributive_d pS in 
let LDT := bs_left_distributive_d  pT in 
let RDS := bs_right_distributive_d pS in 
let RDT := bs_right_distributive_d pT in
let LLAS := bs_left_left_absorptive_d pS in
let LLAT := bs_left_left_absorptive_d pT in
let LRAS := bs_left_right_absorptive_d pS in
let LRAT := bs_left_right_absorptive_d pT in
let RLAS := bs_right_left_absorptive_d pS in
let RLAT := bs_right_left_absorptive_d pT in
let RRAS := bs_right_right_absorptive_d pS in
let RRAT := bs_right_right_absorptive_d pT in
{|
  bs_left_distributive_d    :=
    bops_llex_product_left_distributive_certify S T wS wT rS rT addS mulS addT mulT LC LK LDS LDT 
; bs_right_distributive_d   := 
    bops_llex_product_right_distributive_certify S T wS wT rS rT addS mulS addT mulT RC RK RDS RDT 
; bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_certify S T argT LLAS LLAT ALS 
; bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_certify S T argT LRAS LRAT ARS 
; bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_certify S T argT RLAS RLAT ALS 
; bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_certify S T argT RRAS RRAT ARS 
|}.

*) 

Definition bs_certs_llex_product_INTERNAL
           (addPS : @sg_certificates S)
           (addPT : @sg_certificates T)
           (mulPS : @sg_certificates S)
           (mulPT : @sg_certificates T)
           (pS :    @bs_certificates  S)
           (pT :    @bs_certificates  T)
           (idem_addS : @assert_idempotent S)
           (comm_addT : @assert_commutative T) 
          (* (P : (@assert_selective S) +
                             ((@assert_exists_id T) *
                              (@assert_exists_ann T))) *) : 
                @bs_certificates (S * T) := 

let LC := sg_left_cancel_d mulPS  in 
let RC := sg_right_cancel_d mulPS in
let LK := sg_left_constant_d mulPT in 
let RK := sg_right_constant_d mulPT in                
let ALS := sg_anti_left_d mulPS in 
let ARS := sg_anti_right_d mulPS in 
let LDS := bs_left_distributive_d pS in 
let LDT := bs_left_distributive_d  pT in 
let RDS := bs_right_distributive_d pS in 
let RDT := bs_right_distributive_d pT in
let LLAS := bs_left_left_absorptive_d pS in
let LLAT := bs_left_left_absorptive_d pT in
let LRAS := bs_left_right_absorptive_d pS in
let LRAT := bs_left_right_absorptive_d pT in
let RLAS := bs_right_left_absorptive_d pS in
let RLAT := bs_right_left_absorptive_d pT in
let RRAS := bs_right_right_absorptive_d pS in
let RRAT := bs_right_right_absorptive_d pT in
{|
  bs_left_distributive_d    := bops_llex_product_left_distributive_certify_new S T wS wT argT rS rT addS mulS addT mulT (* P *) LC LK LDS LDT 
; bs_right_distributive_d   := bops_llex_product_right_distributive_certify_new S T wS wT argT rS rT addS mulS addT mulT (* P *)  RC RK RDS RDT 
; bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_certify S T wT LLAS LLAT ALS 
; bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_certify S T wT LRAS LRAT ARS 
; bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_certify S T wT RLAS RLAT ALS 
; bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_certify S T wT RRAS RRAT ARS 
|}. 

  
End Certificates.

Section Combinators.


(*  
Definition llex_product_from_CS_CI {S T : Type} (A : @bs_CS S) (B : @bs_CI T) : @bs_CI (S * T) :=
let eqvS   := bs_CS_eqv A in
let eqvT   := bs_CI_eqv B in
let eqS    := eqv_eq eqvS in
let eqT    := eqv_eq eqvT in
let eqvPS  := eqv_certs eqvS in
let eqvPT  := eqv_certs eqvT in
let plusS  := bs_CS_plus A in
let plusT  := bs_CI_plus B in
let timesS  := bs_CS_times A in
let timesT  := bs_CI_times B in
let id_annS  := bs_CS_id_ann_certs A in
let id_annT  := bs_CI_id_ann_certs B in
let plusPS  := bs_CS_plus_certs A in
let plusPT  := bs_CI_plus_certs B in
let timesPS  := bs_CS_times_certs A in
let timesPT  := bs_CI_times_certs B in
let pS       := bs_CS_certs A in
let pT       := bs_CI_certs B in 
(* these should move to the eqv_cert structures *)
let wS     := eqv_witness eqvS in
let wT     := eqv_witness eqvT in
{|
  bs_CI_eqv           := eqv_product eqvS eqvT 
; bs_CI_plus          := bop_llex wT eqS plusS plusT 
; bs_CI_times         := bop_product timesS timesT
; bs_CI_plus_certs    := sg_CI_llex_certs_v2 wS plusPS plusPT 
; bs_CI_times_certs   := sg_certs_product wS wT timesPS timesPT 
; bs_CI_id_ann_certs  := id_ann_certs_llex_product S T id_annS id_annT 
; bs_CI_certs         := bs_certs_llex_product S T wS wT wT eqS eqT plusS timesS plusT timesT timesPS timesPT pS pT 
; bs_CI_ast           := Ast_bs_llex (bs_CS_ast A, bs_CI_ast B)
|}.



Definition llex_product_from_CS_CS {S T : Type} (A : @bs_CS S) (B : @bs_CS T) : @bs_CS (S * T) :=
let eqvS   := bs_CS_eqv A in
let eqvT   := bs_CS_eqv B in
let eqS    := eqv_eq eqvS in
let eqT    := eqv_eq eqvT in
let eqvPS  := eqv_certs eqvS in
let eqvPT  := eqv_certs eqvT in
let plusS  := bs_CS_plus A in
let plusT  := bs_CS_plus B in
let timesS  := bs_CS_times A in
let timesT  := bs_CS_times B in
let id_annS  := bs_CS_id_ann_certs A in
let id_annT  := bs_CS_id_ann_certs B in
let plusPS  := bs_CS_plus_certs A in
let plusPT  := bs_CS_plus_certs B in
let timesPS  := bs_CS_times_certs A in
let timesPT  := bs_CS_times_certs B in
let pS       := bs_CS_certs A in
let pT       := bs_CS_certs B in 
(* these should move to the eqv_cert structures *)
let wS     := eqv_witness eqvS in
let wT     := eqv_witness eqvT in
{|
  bs_CS_eqv           := eqv_product eqvS eqvT 
; bs_CS_plus          := bop_llex wT eqS plusS plusT 
; bs_CS_times         := bop_product timesS timesT
; bs_CS_plus_certs    := sg_CS_llex_certs plusPS plusPT 
; bs_CS_times_certs   := sg_certs_product wS wT timesPS timesPT 
; bs_CS_id_ann_certs  := id_ann_certs_llex_product S T id_annS id_annT 
; bs_CS_certs         := bs_certs_llex_product S T wS wT wT eqS eqT plusS timesS plusT timesT timesPS timesPT pS pT 
; bs_CS_ast           := Ast_bs_llex (bs_CS_ast A, bs_CS_ast B)
|}.
*) 

Definition llex_product_INTERNAL
           {S T : Type}
           (argT : T) 
           (A : @bs S)
           (B : @bs T)
           (idemS : @assert_idempotent S)
           (commS : @assert_commutative S) 
           (commT : @assert_commutative T)
           (* (P : (@assert_selective S) +
                ((@assert_exists_id T) * (@assert_exists_ann T ))) *) : @bs (S * T) :=
let eqvS     := bs_eqv A in
let eqvT     := bs_eqv B in
let eqS      := eqv_eq eqvS in
let eqT      := eqv_eq eqvT in
let eqvPS    := eqv_certs eqvS in
let eqvPT    := eqv_certs eqvT in
let plusS    := bs_plus A in
let plusT    := bs_plus B in
let timesS   := bs_times A in
let timesT   := bs_times B in
let id_annS  := bs_id_ann_certs A in
let id_annT  := bs_id_ann_certs B in
let plusPS   := bs_plus_certs A in
let plusPT   := bs_plus_certs B in
let timesPS  := bs_times_certs A in
let timesPT  := bs_times_certs B in
let pS       := bs_certs A in
let pT       := bs_certs B in 

let wS     := eqv_witness eqvS in
let f      := eqv_new eqvS in
let wT     := eqv_witness eqvT in
let g      := eqv_new eqvT in
(*match P with
| inl Assert_Selective => 
{|
  bs_eqv          := eqv_product eqvS eqvT 
; bs_plus         := bop_llex wT eqS plusS plusT 
; bs_times        := bop_product timesS timesT
; bs_plus_certs   := sg_llex_certificates eqS wS f wT wT g plusS plusPS plusPT idemS commS (* (inl Assert_Selective) *) 
; bs_times_certs  := sg_certs_product wS wT timesPS timesPT 
; bs_id_ann_certs := id_ann_certs_llex_product S T id_annS id_annT 
; bs_certs        := bs_certs_llex_product_INTERNAL S T wS wT wT eqS eqT plusS timesS plusT timesT plusPS plusPT timesPS timesPT pS pT idemS commT (* (inl Assert_Selective) *) 
; bs_ast           := Ast_bs_llex_product (bs_ast A, bs_ast B)
|}.
  
| inr (idP, annP) =>
*)
{|
  bs_eqv          := eqv_product eqvS eqvT 
; bs_plus         := bop_llex argT eqS plusS plusT 
; bs_times        := bop_product timesS timesT
; bs_plus_certs   := sg_llex_certificates eqS wS f wT argT g plusS plusPS plusPT idemS commS (* (inr idP) *) 
; bs_times_certs  := sg_certs_product wS wT timesPS timesPT 
; bs_id_ann_certs := id_ann_certs_llex_product S T id_annS id_annT 
; bs_certs        := bs_certs_llex_product_INTERNAL S T wS wT argT eqS eqT plusS timesS plusT timesT plusPS plusPT timesPS timesPT pS pT idemS commT (* (inr (idP, annP)) *) 
; bs_ast           := Ast_bs_llex_product (bs_ast A, bs_ast B)
|} . 
(*end*) 



Definition llex_product_INTERNAL_selective
           {S T : Type}
           (argT : T) 
           (A : @bs S)
           (B : @bs T)
           (idemS : @assert_idempotent S)
           (commS : @assert_commutative S) 
           (commT : @assert_commutative T)
           (* (P : (@assert_selective S) +
                ((@assert_exists_id T) * (@assert_exists_ann T ))) *) : @bs (S * T) :=
let eqvS     := bs_eqv A in
let eqvT     := bs_eqv B in
let eqS      := eqv_eq eqvS in
let eqT      := eqv_eq eqvT in
let eqvPS    := eqv_certs eqvS in
let eqvPT    := eqv_certs eqvT in
let plusS    := bs_plus A in
let plusT    := bs_plus B in
let timesS   := bs_times A in
let timesT   := bs_times B in
let id_annS  := bs_id_ann_certs A in
let id_annT  := bs_id_ann_certs B in
let plusPS   := bs_plus_certs A in
let plusPT   := bs_plus_certs B in
let timesPS  := bs_times_certs A in
let timesPT  := bs_times_certs B in
let pS       := bs_certs A in
let pT       := bs_certs B in 

let wS     := eqv_witness eqvS in
let f      := eqv_new eqvS in
let wT     := eqv_witness eqvT in
let g      := eqv_new eqvT in
{|
  bs_eqv          := eqv_product eqvS eqvT 
; bs_plus         := bop_llex wT eqS plusS plusT 
; bs_times        := bop_product timesS timesT
; bs_plus_certs   := sg_llex_certificates eqS wS f wT wT g plusS plusPS plusPT idemS commS (* (inl Assert_Selective) *) 
; bs_times_certs  := sg_certs_product wS wT timesPS timesPT 
; bs_id_ann_certs := id_ann_certs_llex_product S T id_annS id_annT 
; bs_certs        := bs_certs_llex_product_INTERNAL S T wS wT wT eqS eqT plusS timesS plusT timesT plusPS plusPT timesPS timesPT pS pT idemS commT (* (inl Assert_Selective) *) 
; bs_ast           := Ast_bs_llex_product (bs_ast A, bs_ast B)
|}.

End Combinators.

End CAS.


Section MCAS.

Open Scope list_scope.
Open Scope string_scope.

Definition mcas_bs_llex_product {S T : Type} (A : @bs_mcas S)  (B : @bs_mcas T)  : @bs_mcas (S * T) :=
match bs_mcas_cast_up A, bs_mcas_cast_up B with
| BS_bs A', BS_bs B'               =>
  let sgPS := bs_plus_certs A' in
  let sgPT := bs_plus_certs B' in   
  match sg_commutative_d sgPS, sg_commutative_d sgPT with
  | Certify_Commutative, Certify_Commutative =>
    match sg_idempotent_d sgPS with
    | Certify_Idempotent => 
      match sg_selective_d sgPS with
      | Certify_Selective => bs_classify (BS_bs (llex_product_INTERNAL_selective
                                                   (eqv_witness (bs_eqv B'))
                                                   A' B'
                                                   Assert_Idempotent
                                                   Assert_Commutative
                                                   Assert_Commutative
                                                   (* (inl Assert_Selective) *) ))
      | _ =>
        match id_ann_plus_times_d (bs_id_ann_certs B') with 
        | Id_Ann_Cert_Equal id =>
          bs_classify (BS_bs (llex_product_INTERNAL
                                id A' B'
                                Assert_Idempotent
                                Assert_Commutative
                                Assert_Commutative
                                (* (inr (Assert_Exists_Id id, Assert_Exists_Ann id)) *) ))
        | _  => BS_Error ("mcas_llex_product : second algebra must have an additive identity that is a multiplicative annihilator" :: nil)     
        end
      end
    | _ => BS_Error ("mcas_llex_product : first algebra must have an addition that is idempotent" :: nil)        
    end
  | Certify_Commutative, _       => BS_Error ("mcas_llex_product : the second algebra must have an commutative addition" :: nil)
  | _, Certify_Commutative       => BS_Error ("mcas_llex_product : the first algebra must have a commutative addition" :: nil)        
  | _,  _                        => BS_Error ("mcas_llex_product : both algebras must have commutative additions" :: nil)        
  end
| BS_Error sl1, BS_Error sl2   => BS_Error (sl1 ++ sl2)
| BS_Error sl1, _              => BS_Error sl1
| _,  BS_Error sl2             => BS_Error sl2
| _, _                         => BS_Error ("Internal Error : mcas_lex_product" :: nil)
end.

End MCAS.


Section Verify.

Section Certify.

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.
Variable eqvS : eqv_proofs S rS.
Variable eqvT : eqv_proofs T rT.   


Lemma correct_bops_llex_product_exists_id_ann_certify_left
  (pS : exists_id_ann_decidable S rS addS mulS)                                                   
  (pT : exists_id_ann_decidable T rT addT mulT) :                                                   
  p2c_exists_id_ann (S * T) 
                    (brel_product rS rT)
                    (bop_llex wT rS addS addT)
                    (bop_product mulS mulT)
                    (bops_llex_product_exists_id_ann_decide_left S T 
                        rS rT wT eqvS eqvT addS mulS addT mulT pS pT)
  =
  bops_llex_product_exists_id_ann_certify (p2c_exists_id_ann S rS addS mulS pS)
                                          (p2c_exists_id_ann T rT addT mulT pT). 
Proof. unfold p2c_exists_id_ann, bops_llex_product_exists_id_ann_decide_left,
       bops_llex_product_exists_id_ann_certify; simpl.
       destruct pS; simpl.
       + destruct pT; simpl. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]; destruct p0 as [[idT C] D]; simpl. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct b as [idT_annT D]; simpl. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct b as [[idT annT] D]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct p0 as [C [annT D]]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct b as [idT_annT C]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct b as [[idT annT] C]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct b as [idS_annS A]; destruct p as [C D]. reflexivity. 
         ++ destruct b as [idS_annS A]; destruct p as [[idT C] D]; simpl. reflexivity. 
         ++ destruct b as [idS_annS A]; destruct p as [C [annT D]]; simpl. reflexivity. 
         ++ destruct b as [idS_annS [A B]]; destruct b0 as [idT_annT [C D]]; simpl. reflexivity. 
         ++ destruct b as [idS_annS [A B]]; destruct b0 as [[idT annT] [[C D] E]]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [D E]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [[idT D] E]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [D [annT E]]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct b0 as [idT_annT [D E]]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct b0 as [[idT annT] [[D E] F]]; simpl. reflexivity. 
Qed. 
  
Lemma correct_bops_llex_product_exists_id_ann_certify_right 
  (pS : exists_id_ann_decidable S rS mulS addS)
  (pT : exists_id_ann_decidable T rT mulT addT) : 
  p2c_exists_id_ann (S * T) 
                    (brel_product rS rT)
                    (bop_product mulS mulT)                    
                    (bop_llex wT rS addS addT)
                    (bops_llex_product_exists_id_ann_decide_right S T
                        rS rT wT eqvS eqvT addS mulS addT mulT pS pT)
  =                    
  bops_llex_product_exists_id_ann_certify (p2c_exists_id_ann S rS mulS addS pS)
                                          (p2c_exists_id_ann T rT mulT addT pT). 
Proof. unfold p2c_exists_id_ann, bops_llex_product_exists_id_ann_decide_right,
       bops_llex_product_exists_id_ann_certify; simpl.
       destruct pS; simpl.
       + destruct pT; simpl. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]; destruct p0 as [[idT C] D]; simpl. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct b as [idT_annT D]; simpl. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct b as [[idT annT] D]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct p0 as [C [annT D]]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct b as [idT_annT C]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct b as [[idT annT] C]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct b as [idS_annS A]; destruct p as [C D]. reflexivity. 
         ++ destruct b as [idS_annS A]; destruct p as [[idT C] D]; simpl. reflexivity. 
         ++ destruct b as [idS_annS A]; destruct p as [C [annT D]]; simpl. reflexivity. 
         ++ destruct b as [idS_annS [A B]]; destruct b0 as [idT_annT [C D]]; simpl. reflexivity. 
         ++ destruct b as [idS_annS [A B]]; destruct b0 as [[idT annT] [[C D] E]]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [D E]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [[idT D] E]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [D [annT E]]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct b0 as [idT_annT [D E]]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct b0 as [[idT annT] [[D E] F]]; simpl. reflexivity. 
Qed. 

Lemma correct_bops_llex_product_left_left_absorptive_certify
  (t : T) 
  (idemS : bop_idempotent S rS addS)
  (cng_addS : bop_congruence S rS addS)            
  (ALS  : bop_anti_left_decidable S rS mulS)
  (LLS  : bops_left_left_absorptive_decidable S rS addS mulS)
  (LLT  : bops_left_left_absorptive_decidable T rT addT mulT) : 
  p2c_left_left_absorptive (S * T)
                           (brel_product rS rT)
                           (bop_llex t rS addS addT)
                           (bop_product mulS mulT)
                           (bops_llex_product_left_left_absorptive_decide
                                    S T wT t rS rT addS mulS addT mulT eqvS eqvT 
                                    idemS cng_addS LLS LLT ALS) 
  = 
  bops_llex_product_left_left_absorptive_certify S T wT
                                 (p2c_left_left_absorptive S rS addS mulS LLS)
                                 (p2c_left_left_absorptive T rT addT mulT LLT) 
                                 (p2c_anti_left_check S rS mulS ALS). 
Proof. destruct ALS as [lcS | [[x1 x2] A]];
       destruct LLS as [ldS | [[s1 s2] nldS]];
       destruct LLT as [ldT | [[t1 t2] nldT]]; 
       unfold p2c_left_left_absorptive, p2c_anti_left_check; 
       unfold bops_llex_product_left_left_absorptive_decide,
       bops_llex_product_left_left_absorptive_certify; simpl; 
       try reflexivity. 
Qed.



Lemma correct_bops_llex_product_left_right_absorptive_certify
  (t : T)       
  (idemS : bop_idempotent S rS addS)      
  (cng_addS : bop_congruence S rS addS)            
  (ALS  : bop_anti_right_decidable S rS mulS)
  (LLS  : bops_left_right_absorptive_decidable S rS addS mulS)
  (LLT  : bops_left_right_absorptive_decidable T rT addT mulT) : 
  p2c_left_right_absorptive (S * T)
                           (brel_product rS rT)
                           (bop_llex t rS addS addT)
                           (bop_product mulS mulT)
                           (bops_llex_product_left_right_absorptive_decide
                                    S T wT t rS rT addS mulS addT mulT eqvS eqvT 
                                    idemS cng_addS LLS LLT ALS) 
  = 
  bops_llex_product_left_right_absorptive_certify S T wT
                                 (p2c_left_right_absorptive S rS addS mulS LLS)
                                 (p2c_left_right_absorptive T rT addT mulT LLT) 
                                 (p2c_anti_right_check S rS mulS ALS). 
Proof. destruct ALS as [lcS | [[x1 x2] A]];
       destruct LLS as [ldS | [[s1 s2] nldS]];
       destruct LLT as [ldT | [[t1 t2] nldT]]; 
       unfold p2c_left_right_absorptive, p2c_anti_right_check; 
       unfold bops_llex_product_left_right_absorptive_decide,
       bops_llex_product_left_right_absorptive_certify; simpl; 
       reflexivity. 
Qed.


Lemma correct_bops_llex_product_right_left_absorptive_certify
  (t : T)       
  (idemS : bop_idempotent S rS addS)      
  (cng_addS : bop_congruence S rS addS)            
  (ALS  : bop_anti_left_decidable S rS mulS)
  (LLS  : bops_right_left_absorptive_decidable S rS addS mulS)
  (LLT  : bops_right_left_absorptive_decidable T rT addT mulT) : 
  p2c_right_left_absorptive (S * T)
                           (brel_product rS rT)
                           (bop_llex t rS addS addT)
                           (bop_product mulS mulT)
                           (bops_llex_product_right_left_absorptive_decide
                                    S T wT t rS rT addS mulS addT mulT eqvS eqvT 
                                    idemS cng_addS LLS LLT ALS) 
  = 
  bops_llex_product_right_left_absorptive_certify S T wT
                                 (p2c_right_left_absorptive S rS addS mulS LLS)
                                 (p2c_right_left_absorptive T rT addT mulT LLT) 
                                 (p2c_anti_left_check S rS mulS ALS). 
Proof. destruct ALS as [lcS | [[x1 x2] A]];
       destruct LLS as [ldS | [[s1 s2] nldS]];
       destruct LLT as [ldT | [[t1 t2] nldT]]; 
       unfold p2c_right_left_absorptive, p2c_anti_left_check; 
       unfold bops_llex_product_right_left_absorptive_decide,
       bops_llex_product_right_left_absorptive_certify; simpl; 
       reflexivity. 
Qed.



Lemma correct_bops_llex_product_right_right_absorptive_certify
  (t : T)       
  (idemS : bop_idempotent S rS addS)      
  (cng_addS : bop_congruence S rS addS)            
  (ALS  : bop_anti_right_decidable S rS mulS)
  (LLS  : bops_right_right_absorptive_decidable S rS addS mulS)
  (LLT  : bops_right_right_absorptive_decidable T rT addT mulT) : 
  p2c_right_right_absorptive (S * T)
                           (brel_product rS rT)
                           (bop_llex t rS addS addT)
                           (bop_product mulS mulT)
                           (bops_llex_product_right_right_absorptive_decide
                                    S T wT t rS rT addS mulS addT mulT eqvS eqvT 
                                    idemS cng_addS LLS LLT ALS) 
  = 
  bops_llex_product_right_right_absorptive_certify S T wT
                                 (p2c_right_right_absorptive S rS addS mulS LLS)
                                 (p2c_right_right_absorptive T rT addT mulT LLT) 
                                 (p2c_anti_right_check S rS mulS ALS).
Proof. destruct ALS as [lcS | [[x1 x2] A]];
       destruct LLS as [ldS | [[s1 s2] nldS]];
       destruct LLT as [ldT | [[t1 t2] nldT]]; 
       unfold p2c_right_right_absorptive, p2c_anti_right_check; 
       unfold bops_llex_product_right_right_absorptive_decide,
       bops_llex_product_right_right_absorptive_certify; simpl; 
       reflexivity. 
Qed.


Lemma correct_bops_llex_product_left_distributive_certify
  (P : (bop_selective S rS addS) + ((bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT)))
  (idemS : bop_idempotent S rS addS)      
  (com_addT : bop_commutative T rT addT)      
  (cng_addS : bop_congruence S rS addS)
  (cng_mulS : bop_congruence S rS mulS)
  (cng_addT : bop_congruence T rT addT)
  (LDS : bop_left_distributive_decidable S rS addS mulS)
  (LDT : bop_left_distributive_decidable T rT addT mulT)
  (LCS : bop_left_cancellative_decidable S rS mulS)
  (LKT : bop_left_constant_decidable T rT mulT) : 
  p2c_left_distributive (S * T)
                      (brel_product rS rT)
                      (bop_llex argT rS addS addT)
                      (bop_product mulS mulT)
                      (bops_llex_product_left_distributive_decide S T
                                 wS wT argT rS rT addS mulS addT mulT eqvS eqvT
                                 idemS cng_addS cng_mulS cng_addT com_addT 
                                  P LDS LDT LCS LKT)                                  
   = 
   bops_llex_product_left_distributive_certify_new
                              S T wS wT argT rS rT addS mulS addT mulT
(*                              (match P with
                               | inl _ => inl Assert_Selective
                               | inr (P1, P2) => inr (Assert_Exists_Id argT, Assert_Exists_Ann argT)
                               end ) *) 
                              (p2c_left_cancel_check S rS mulS LCS) 
                              (p2c_left_constant_check T rT mulT LKT)
                              (p2c_left_distributive S rS addS mulS LDS) 
                              (p2c_left_distributive T rT addT mulT LDT).
Proof. destruct LCS as [lcS | [[x1 [x2 x3]] [A B]]];
       destruct LKT as [lkT | [[y1 [y2 y3]] C]];
       destruct LDS as [ldS | [[s1 [s2 s3]] nldS]];
       destruct LDT as [ldT | [[t1 [t2 t3]] nldT]]; 
       unfold p2c_left_distributive, p2c_left_cancel_check, p2c_left_constant_check,
       p2c_left_distributive; 
       unfold bops_llex_product_left_distributive_certify_new,
              bops_llex_product_left_distributive_decide; 
       destruct P as [selS | [P1 P2]]; compute; try reflexivity.
Qed.

Lemma correct_bops_llex_product_right_distributive_certify
  (P : (bop_selective S rS addS) + ((bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT)))      
  (idemS : bop_idempotent S rS addS)      
  (cng_addS : bop_congruence S rS addS)      
  (com_addT : bop_commutative T rT addT)      
  (cng_addT : bop_congruence T rT addT)
  (cng_mulS : bop_congruence S rS mulS)  
  (RDS : bop_right_distributive_decidable S rS addS mulS)
  (RDT : bop_right_distributive_decidable T rT addT mulT)
  (RCS : bop_right_cancellative_decidable S rS mulS)
  (RKT : bop_right_constant_decidable T rT mulT) : 
  p2c_right_distributive (S * T)
                      (brel_product rS rT)
                      (bop_llex argT rS addS addT)
                      (bop_product mulS mulT)
                      (bops_llex_product_right_distributive_decide S T
                                 wS wT argT rS rT addS mulS addT mulT eqvS eqvT
                                 idemS cng_addS cng_mulS cng_addT com_addT 
                                 P RDS RDT RCS RKT)                                  
   = 
   bops_llex_product_right_distributive_certify_new
                              S T wS wT argT rS rT addS mulS addT mulT
(*                              (match P with
                               | inl _ => inl Assert_Selective
                               | inr (P1, P2) => inr (Assert_Exists_Id argT, Assert_Exists_Ann argT)
                               end )     *)
                              (p2c_right_cancel_check S rS mulS RCS) 
                              (p2c_right_constant_check T rT mulT RKT)
                              (p2c_right_distributive S rS addS mulS RDS) 
                              (p2c_right_distributive T rT addT mulT RDT).
Proof. destruct RCS as [lcS | [[x1 [x2 x3]] [A B]]];
       destruct RKT as [lkT | [[y1 [y2 y3]] C]];
       destruct RDS as [ldS | [[s1 [s2 s3]] nldS]];
       destruct RDT as [ldT | [[t1 [t2 t3]] nldT]]; 
       unfold p2c_right_distributive, p2c_right_cancel_check, p2c_right_constant_check,
       p2c_right_distributive; 
       unfold bops_llex_product_right_distributive_certify_new,
              bops_llex_product_right_distributive_decide; 
       destruct P as [selS | [P1 P2]]; compute; try reflexivity.
Qed.


(*
Lemma correct_bops_llex_product_left_distributive_certify_selective_case
  (idemS : bop_idempotent S rS addS)
  (selS : bop_selective S rS addS)      
  (com_addT : bop_commutative T rT addT)      
  (cng_addS : bop_congruence S rS addS)
  (cng_mulS : bop_congruence S rS mulS)
  (cng_addT : bop_congruence T rT addT)
  (LDS : bop_left_distributive_decidable S rS addS mulS)
  (LDT : bop_left_distributive_decidable T rT addT mulT)
  (LCS : bop_left_cancellative_decidable S rS mulS)
  (LKT : bop_left_constant_decidable T rT mulT) : 
  p2c_left_distributive (S * T)
                      (brel_product rS rT)
                      (bop_llex wT rS addS addT)
                      (bop_product mulS mulT)
                      (bops_llex_product_left_distributive_decide S T
                                 wS wT wT rS rT addS mulS addT mulT eqvS eqvT
                                 idemS cng_addS cng_mulS cng_addT com_addT 
                                 (inl selS) LDS LDT LCS LKT)                                  
   = 
   bops_llex_product_left_distributive_certify
                              S T wS wT rS rT addS mulS addT mulT
                              (p2c_left_cancel_check S rS mulS LCS) 
                              (p2c_left_constant_check T rT mulT LKT)
                              (p2c_left_distributive S rS addS mulS LDS) 
                              (p2c_left_distributive T rT addT mulT LDT).
Proof. destruct LCS as [lcS | [[x1 [x2 x3]] [A B]]];
       destruct LKT as [lkT | [[y1 [y2 y3]] C]];
       destruct LDS as [ldS | [[s1 [s2 s3]] nldS]];
       destruct LDT as [ldT | [[t1 [t2 t3]] nldT]]; 
       unfold p2c_left_distributive, p2c_left_cancel_check, p2c_left_constant_check,
       p2c_left_distributive; 
       unfold bops_llex_product_left_distributive_certify,
       bops_llex_product_left_distributive_decide; 
       unfold a_witness_llex_product_not_left_distributive,
       witness_llex_product_not_left_distributive_with_selectivity; simpl; 
       try reflexivity.
Qed.



Lemma correct_bops_llex_product_left_distributive_certify_idempotent_case
  (idemS : bop_idempotent S rS addS)
  (P : (bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT))    
  (com_addT : bop_commutative T rT addT)      
  (cng_addS : bop_congruence S rS addS)
  (cng_mulS : bop_congruence S rS mulS)
  (cng_addT : bop_congruence T rT addT)
  (LDS : bop_left_distributive_decidable S rS addS mulS)
  (LDT : bop_left_distributive_decidable T rT addT mulT)
  (LCS : bop_left_cancellative_decidable S rS mulS)
  (LKT : bop_left_constant_decidable T rT mulT) : 
  p2c_left_distributive (S * T)
                      (brel_product rS rT)
                      (bop_llex argT rS addS addT)
                      (bop_product mulS mulT)
                      (bops_llex_product_left_distributive_decide S T
                                 wS wT argT rS rT addS mulS addT mulT eqvS eqvT
                                 idemS cng_addS cng_mulS cng_addT com_addT 
                                 (inr P) LDS LDT LCS LKT)                                  
   = 
   bops_llex_product_left_distributive_certify
                              S T wS wT rS rT addS mulS addT mulT
                              (p2c_left_cancel_check S rS mulS LCS) 
                              (p2c_left_constant_check T rT mulT LKT)
                              (p2c_left_distributive S rS addS mulS LDS) 
                              (p2c_left_distributive T rT addT mulT LDT).
Proof. destruct LCS as [lcS | [[x1 [x2 x3]] [A B]]];
       destruct LKT as [lkT | [[y1 [y2 y3]] C]];
       destruct LDS as [ldS | [[s1 [s2 s3]] nldS]];
       destruct LDT as [ldT | [[t1 [t2 t3]] nldT]]; 
       unfold p2c_left_distributive, p2c_left_cancel_check, p2c_left_constant_check,
       p2c_left_distributive; 
       unfold bops_llex_product_left_distributive_certify,
       bops_llex_product_left_distributive_decide; 
       unfold a_witness_llex_product_not_left_distributive,
       witness_llex_product_not_left_distributive_with_selectivity; simpl; 
         try reflexivity.
       destruct P as [P1 P2]. unfold a_witness_llex_product_not_left_distributive.
       reflexivity.        
Qed.

Lemma correct_bops_llex_product_right_distributive_certify_with_selectivity
  (idemS : bop_idempotent S rS addS)      
  (selS : bop_selective S rS addS)
  (cng_addS : bop_congruence S rS addS)      
  (com_addT : bop_commutative T rT addT)      
  (cng_addT : bop_congruence T rT addT)
  (cng_mulS : bop_congruence S rS mulS)  
  (RDS : bop_right_distributive_decidable S rS addS mulS)
  (RDT : bop_right_distributive_decidable T rT addT mulT)
  (RCS : bop_right_cancellative_decidable S rS mulS)
  (RKT : bop_right_constant_decidable T rT mulT) : 
  p2c_right_distributive (S * T)
                      (brel_product rS rT)
                      (bop_llex wT rS addS addT)
                      (bop_product mulS mulT)
                      (bops_llex_product_right_distributive_decide S T
                                 wS wT wT rS rT addS mulS addT mulT eqvS eqvT
                                 idemS cng_addS cng_mulS cng_addT com_addT 
                                 (inl selS) RDS RDT RCS RKT)                                  
   = 
   bops_llex_product_right_distributive_certify
                              S T wS wT rS rT addS mulS addT mulT
                              (p2c_right_cancel_check S rS mulS RCS) 
                              (p2c_right_constant_check T rT mulT RKT)
                              (p2c_right_distributive S rS addS mulS RDS) 
                              (p2c_right_distributive T rT addT mulT RDT).
Proof. destruct RCS as [lcS | [[x1 [x2 x3]] [A B]]];
       destruct RKT as [lkT | [[y1 [y2 y3]] C]];
       destruct RDS as [ldS | [[s1 [s2 s3]] nldS]];
       destruct RDT as [ldT | [[t1 [t2 t3]] nldT]]; 
       unfold p2c_right_distributive, p2c_right_cancel_check, p2c_right_constant_check,
       p2c_right_distributive; 
       unfold bops_llex_product_right_distributive_certify,
       bops_llex_product_right_distributive_decide; 
       unfold a_witness_llex_product_not_right_distributive,
       witness_llex_product_not_right_distributive_with_selectivity; simpl;
       reflexivity. 
Qed.

*) 


End Certify.     
 
Section Certificates.

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.
Variable eqvS : eqv_proofs S rS.
Variable eqvT : eqv_proofs T rT.   
    


Lemma correct_id_ann_certs_llex_product
  (pS : id_ann_proofs S rS addS mulS)
  (pT : id_ann_proofs T rT addT mulT) :
  P2C_id_ann (S * T)
             (brel_product rS rT)
             (bop_llex wT rS addS addT)
             (bop_product mulS mulT)
             (id_ann_proofs_llex_product S T wT rS rT addS mulS addT mulT eqvS eqvT pS pT)
  = 
  id_ann_certs_llex_product S T (P2C_id_ann S rS addS mulS pS) (P2C_id_ann T rT addT mulT pT). 
Proof. destruct pS, pT; unfold P2C_id_ann, id_ann_proofs_llex_product, id_ann_certs_llex_product; simpl. 
       rewrite correct_bops_llex_product_exists_id_ann_certify_left.        
       rewrite correct_bops_llex_product_exists_id_ann_certify_right.        
       reflexivity. 
Qed. 


Lemma correct_bs_certs_llex_product_INTERNAL_selective 
     (addPS : sg_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT)
     (idemS : bop_idempotent S rS addS)
     (commS : bop_commutative S rS addS)
     (commT : bop_commutative T rT addT)
     (sel : bop_selective S rS addS) : 
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex wT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_INTERNAL S T wS wT wT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT idemS commT (inl sel))
  = 
  bs_certs_llex_product_INTERNAL S T wS wT wT rS rT addS mulS addT mulT 
                   (P2C_sg S rS addS addPS)
                   (P2C_sg T rT addT addPT)
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT)
                   Assert_Idempotent
                   Assert_Commutative
                   (*(inl Assert_Selective) *). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_INTERNAL, bs_certs_llex_product_INTERNAL.
       unfold P2C_bs, P2C_sg; simpl.
       rewrite correct_bops_llex_product_left_distributive_certify.
       rewrite correct_bops_llex_product_right_distributive_certify. 
       rewrite correct_bops_llex_product_left_left_absorptive_certify. 
       rewrite correct_bops_llex_product_left_right_absorptive_certify. 
       rewrite correct_bops_llex_product_right_left_absorptive_certify.
       rewrite correct_bops_llex_product_right_right_absorptive_certify. 
       reflexivity.
Qed.
                                 

Lemma correct_bs_certs_llex_product_INTERNAL_idempotent
     (addPS : sg_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT)
     (idemS : bop_idempotent S rS addS)
     (commS : bop_commutative S rS addS)
     (commT : bop_commutative T rT addT)
     (P : (bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT)) : 
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex argT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_INTERNAL S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT idemS commT (inr P))
  = 
  bs_certs_llex_product_INTERNAL S T wS wT argT rS rT addS mulS addT mulT 
                   (P2C_sg S rS addS addPS)
                   (P2C_sg T rT addT addPT)
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT)
                   Assert_Idempotent
                   Assert_Commutative
                   (*(inr (Assert_Exists_Id argT, Assert_Exists_Ann argT)) *). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_INTERNAL, bs_certs_llex_product_INTERNAL.
       unfold P2C_bs, P2C_sg; simpl.
       destruct P as [P1 P2]. 
       rewrite correct_bops_llex_product_left_distributive_certify.
       rewrite correct_bops_llex_product_right_distributive_certify. 
       rewrite correct_bops_llex_product_left_left_absorptive_certify. 
       rewrite correct_bops_llex_product_left_right_absorptive_certify. 
       rewrite correct_bops_llex_product_right_left_absorptive_certify. 
       rewrite correct_bops_llex_product_right_right_absorptive_certify. 
       reflexivity.
Qed.

(*
Lemma correct_bs_certs_llex_product_INTERNAL
     (addPS : sg_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT)
     (idemS : bop_idempotent S rS addS)
     (commS : bop_commutative S rS addS)
     (commT : bop_commutative T rT addT)
     (P : (bop_selective S rS addS) + ((bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT)))      :      
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex argT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_INTERNAL S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT idemS commT P)
  = 
  bs_certs_llex_product_INTERNAL S T wS wT argT rS rT addS mulS addT mulT 
                   (P2C_sg S rS addS addPS)
                   (P2C_sg T rT addT addPT)
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT)
                   Assert_Idempotent
                   Assert_Commutative
                   (match P with
                               | inl _ => inl Assert_Selective
                               | inr (P1, P2) => inr (Assert_Exists_Id argT, Assert_Exists_Ann argT)
                    end). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_INTERNAL, bs_certs_llex_product_INTERNAL.
       unfold P2C_bs, P2C_sg; simpl.
       destruct P as [sel | [A B]]; 
       rewrite correct_bops_llex_product_left_distributive_certify; 
       rewrite correct_bops_llex_product_right_distributive_certify; 
       rewrite correct_bops_llex_product_left_left_absorptive_certify; 
       rewrite correct_bops_llex_product_left_right_absorptive_certify; 
       rewrite correct_bops_llex_product_right_left_absorptive_certify; 
       rewrite correct_bops_llex_product_right_right_absorptive_certify; 
       try reflexivity.
Qed.
*)                                  

(*

Lemma correct_bs_certs_llex_product_INTERNAL_selective_case 
     (addPS : sg_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT)
     (idemS : bop_idempotent S rS addS)
     (commS : bop_commutative S rS addS)
     (commT : bop_commutative T rT addT)     
     (selS  : bop_selective S rS addS) : 
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex wT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_INTERNAL S T wS wT wT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT idemS commT (inl selS))
  = 
  bs_certs_llex_product_INTERNAL S T wS wT wT rS rT addS mulS addT mulT 
                   (P2C_sg S rS addS addPS)
                   (P2C_sg T rT addT addPT)
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT)
                   Assert_Idempotent
                   Assert_Commutative
                   (inl Assert_Selective). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_INTERNAL, bs_certs_llex_product_INTERNAL.
       unfold P2C_bs, P2C_sg; simpl.
       rewrite correct_bops_llex_product_left_left_absorptive_certify. 
       rewrite correct_bops_llex_product_left_right_absorptive_certify. 
       rewrite correct_bops_llex_product_right_left_absorptive_certify. 
       rewrite correct_bops_llex_product_right_right_absorptive_certify.       
       rewrite correct_bops_llex_product_left_distributive_certify_with_selectivity.   
       rewrite correct_bops_llex_product_right_distributive_certify_with_selectivity.   

       reflexivity.
Qed.        



Lemma correct_bs_certs_llex_product_INTERNAL_idempotent_case 
     (addPS : sg_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT)
     (idemS : bop_idempotent S rS addS)
     (commS : bop_commutative S rS addS)
     (commT : bop_commutative T rT addT)     
     (P : ((bop_is_id T rT addT argT) *
           (bop_is_ann T rT mulT argT))) : 
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex argT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_INTERNAL S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT idemS commT (inr P))
  = 
  bs_certs_llex_product_INTERNAL S T wS wT argT rS rT addS mulS addT mulT 
                   (P2C_sg S rS addS addPS)
                   (P2C_sg T rT addT addPT)
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT)
                   Assert_Idempotent
                   Assert_Commutative
                   (inr (Assert_Exists_Id argT, Assert_Exists_Ann argT)). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_INTERNAL, bs_certs_llex_product_INTERNAL.
       unfold P2C_bs, P2C_sg; simpl.
       rewrite correct_bops_llex_product_left_left_absorptive_certify. 
       rewrite correct_bops_llex_product_left_right_absorptive_certify. 
       rewrite correct_bops_llex_product_right_left_absorptive_certify. 
       rewrite correct_bops_llex_product_right_right_absorptive_certify.       
       rewrite correct_bops_llex_product_left_distributive_certify_with_selectivity.   
       rewrite correct_bops_llex_product_right_distributive_certify_with_selectivity.   

       reflexivity.
Qed.        


Lemma correct_bs_certs_llex_product_v2 
     (addPS : sg_CS_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_CI_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT) : 
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex wT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_v2 S T wS wT wT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT)
  = 
  bs_certs_llex_product  S T wS wT wT rS rT addS mulS addT mulT 
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_v2, bs_certs_llex_product.
       unfold P2C_bs, P2C_sg_CS, P2C_sg_CI, P2C_sg; simpl.
       rewrite correct_bops_llex_product_left_distributive_certify_with_selectivity.   
       rewrite correct_bops_llex_product_right_distributive_certify_with_selectivity.   
       rewrite correct_bops_llex_product_left_left_absorptive_certify. 
       rewrite correct_bops_llex_product_left_right_absorptive_certify. 
       rewrite correct_bops_llex_product_right_left_absorptive_certify. 
       rewrite correct_bops_llex_product_right_right_absorptive_certify.
       reflexivity.
Qed.        


Lemma correct_bs_certs_llex_product_v3
     (addPS : sg_CS_proofs S rS addS) 
     (mulPS : sg_proofs S rS mulS)
     (addPT : sg_CS_proofs T rT addT) 
     (mulPT : sg_proofs T rT mulT)     
     (pS : bs_proofs S rS addS mulS) 
     (pT : bs_proofs T rT addT mulT) : 
  P2C_bs (S * T)
         (brel_product rS rT) 
         (bop_llex wT rS addS addT) 
         (bop_product mulS mulT)
         (bs_proofs_llex_product_v3 S T wS wT wT rS rT addS mulS addT mulT eqvS eqvT 
                      addPS addPT mulPS mulPT pS pT)
  = 
  bs_certs_llex_product S T wS wT wT rS rT addS mulS addT mulT 
                   (P2C_sg S rS mulS mulPS)
                   (P2C_sg T rT mulT mulPT)
                   (P2C_bs S rS addS mulS pS)
                   (P2C_bs T rT addT mulT pT). 
Proof. destruct addPS, mulPS, addPT, mulPT, pS, pT.
       unfold bs_proofs_llex_product_v3, bs_certs_llex_product.
       unfold P2C_bs, P2C_sg_CS, P2C_sg_CS, P2C_sg; simpl.
       rewrite correct_bops_llex_product_left_distributive_certify_with_selectivity.   
       rewrite correct_bops_llex_product_right_distributive_certify_with_selectivity.   
       rewrite correct_bops_llex_product_left_left_absorptive_certify. 
       rewrite correct_bops_llex_product_left_right_absorptive_certify. 
       rewrite correct_bops_llex_product_right_left_absorptive_certify. 
       rewrite correct_bops_llex_product_right_right_absorptive_certify.
       reflexivity.
Qed.        
*) 
End Certificates.     

Section Combinators.

  (*
Theorem correct_llex_product_from_CS_CI (S T : Type) (A : A_bs_CS S) (B : A_bs_CI T) :
  A2C_bs_CI (S * T) (A_llex_product_from_CS_CI S T A B)
  =
  llex_product_from_CS_CI (A2C_bs_CS S A) (A2C_bs_CI T B). 
Proof. destruct A, B; unfold A2C_bs_CI, A2C_bs_CS, A_llex_product_from_CS_CI, llex_product_from_CS_CI; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_sg_certs_product.
       rewrite correct_id_ann_certs_llex_product.       
       rewrite correct_sg_CI_llex_certs_v2.        (* naming convention? *) 
       rewrite correct_bs_certs_llex_product_v2. 
       reflexivity. 
Qed.

Theorem correct_llex_product_from_CS_CS (S T : Type) (A : A_bs_CS S) (B : A_bs_CS T) :
  A2C_bs_CS (S * T) (A_llex_product_from_CS_CS S T A B)
  =
  llex_product_from_CS_CS (A2C_bs_CS S A) (A2C_bs_CS T B). 
Proof. destruct A, B; unfold A2C_bs_CS, A_llex_product_from_CS_CS, llex_product_from_CS_CS; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_sg_certs_product.
       rewrite correct_id_ann_certs_llex_product.
       rewrite correct_bs_certs_llex_product_v3.                      
       rewrite correct_sg_CS_certs_llex. 
       reflexivity. 
Qed.

*)

Theorem correct_llex_product_INTERNAL_selective 
        (S T : Type)
        (wT : T)         
        (A : A_bs S)
        (B : A_bs T)
        (idemS : bop_idempotent S (A_eqv_eq S (A_bs_eqv S A)) (A_bs_plus S A))
        (commS : bop_commutative S (A_eqv_eq S (A_bs_eqv S A)) (A_bs_plus S A))
        (commT : bop_commutative T (A_eqv_eq T (A_bs_eqv T B)) (A_bs_plus T B))
        (selS  : bop_selective S (A_eqv_eq S (A_bs_eqv S A)) (A_bs_plus S A)) : 
  A2C_bs (S * T) (A_llex_product_INTERNAL S T wT A B idemS commS commT (inl selS))
  =
  llex_product_INTERNAL_selective wT (A2C_bs S A) (A2C_bs T B) Assert_Idempotent Assert_Commutative Assert_Commutative (*(inl Assert_Selective)*) .
Proof. destruct A, B; unfold A2C_bs, A2C_bs, A_llex_product_INTERNAL, llex_product_INTERNAL_selective; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_sg_certs_product.
       rewrite correct_id_ann_certs_llex_product.       
       rewrite <- correct_sg_llex_certificates_CS_version. 
       rewrite correct_bs_certs_llex_product_INTERNAL_selective. 
       reflexivity.
       simpl in commS. exact commS. 
Qed. 

Theorem correct_llex_product_INTERNAL_idempotent
        (S T : Type)
        (argT : T) 
        (A : A_bs S)
        (B : A_bs T)
        (idemS : bop_idempotent S (A_eqv_eq S (A_bs_eqv S A)) (A_bs_plus S A))
        (commS : bop_commutative S (A_eqv_eq S (A_bs_eqv S A)) (A_bs_plus S A))
        (commT : bop_commutative T (A_eqv_eq T (A_bs_eqv T B)) (A_bs_plus T B))
        (C : bop_is_id T (A_eqv_eq T (A_bs_eqv T B)) (A_bs_plus T B) argT)
        (D : bop_is_ann T (A_eqv_eq T (A_bs_eqv T B)) (A_bs_times T B) argT) : 
  A2C_bs (S * T) (A_llex_product_INTERNAL S T argT A B idemS commS commT (inr (C, D)))
  =
  llex_product_INTERNAL argT (A2C_bs S A) (A2C_bs T B)
                        Assert_Idempotent
                        Assert_Commutative
                        Assert_Commutative
                        (*(inr (Assert_Exists_Id argT, Assert_Exists_Ann argT)) *). 
Proof. destruct A, B; unfold A2C_bs, A2C_bs, A_llex_product_INTERNAL, llex_product_INTERNAL; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_sg_certs_product.
       rewrite correct_id_ann_certs_llex_product.
       rewrite <- correct_sg_llex_certificates_CI_version. 
       rewrite correct_bs_certs_llex_product_INTERNAL_idempotent.        
       reflexivity.
       simpl in commS. exact commS. 
Qed. 


(* this type of corrctness proof needs to be in properties and structures. 
   Perhaps they can be generated automatically .... 
*) 
Lemma FF_commutative (U : Type) (A : A_bs U) :
sg_commutative_d (bs_plus_certs (A2C_bs U A))
= 
p2c_commutative_check _ _ _ (A_sg_commutative_d U (A_eqv_eq U (A_bs_eqv U A))  (A_bs_plus U A) (A_bs_plus_proofs U A)).
Proof. destruct A. destruct A_bs_proofs. simpl. reflexivity. Qed. 
       

Lemma FF_selective (U : Type) (A : A_bs U) :
sg_selective_d (bs_plus_certs (A2C_bs U A))
= 
p2c_selective_check _ _ _ (A_sg_selective_d U (A_eqv_eq U (A_bs_eqv U A))  (A_bs_plus U A) (A_bs_plus_proofs U A)).
Proof. destruct A. destruct A_bs_proofs. simpl. reflexivity. Qed. 

Lemma FF_idempotent (U : Type) (A : A_bs U) :
sg_idempotent_d (bs_plus_certs (A2C_bs U A))
= 
p2c_idempotent_check _ _ _ (A_sg_idempotent_d U (A_eqv_eq U (A_bs_eqv U A))  (A_bs_plus U A) (A_bs_plus_proofs U A)).
Proof. destruct A. destruct A_bs_proofs. simpl. reflexivity. Qed. 

Lemma FF_id_ann_plus_times (U : Type) (A : A_bs U) :
  id_ann_plus_times_d (bs_id_ann_certs (A2C_bs U A))
  =                       
  p2c_exists_id_ann _ _ _ _ (A_id_ann_plus_times_d U (A_eqv_eq U (A_bs_eqv U A)) (A_bs_plus U A) (A_bs_times U A) (A_bs_id_ann_proofs U A)). 
Proof. destruct A. destruct A_bs_proofs. simpl. reflexivity. Qed. 


(* this proof is a mess.  clean it up someday ... *) 
Theorem correct_mcas_bs_llex_product (S T : Type) (bsS : A_bs_mcas S) (bsT : A_bs_mcas T): 
         mcas_bs_llex_product (A2C_mcas_bs S bsS) (A2C_mcas_bs T bsT) 
         = 
         A2C_mcas_bs (S * T) (A_mcas_bs_llex_product S T bsS bsT).
Proof. unfold mcas_bs_llex_product, A_mcas_bs_llex_product. 
       rewrite correct_bs_mcas_cast_up.
       rewrite correct_bs_mcas_cast_up.       
       destruct (A_bs_cas_up_is_error_or_bs S bsS) as [[l1 A] | [s1 A]];
       destruct (A_bs_cas_up_is_error_or_bs T bsT) as [[l2 B] | [s2 B]].
       + rewrite A, B. simpl. reflexivity. 
       + rewrite A, B. simpl. reflexivity.
       + rewrite A, B. simpl. reflexivity.
       + rewrite A, B.
         unfold A2C_mcas_bs.
         rewrite FF_commutative. 
         rewrite FF_commutative.
         rewrite FF_idempotent.
         rewrite FF_selective. 
         destruct (A_sg_commutative_d S (A_eqv_eq S (A_bs_eqv S s1))  (A_bs_plus S s1) (A_bs_plus_proofs S s1))
           as [commS | [[a b] ncommS ]]; unfold p2c_commutative_check.
         ++ destruct (A_sg_commutative_d T (A_eqv_eq T (A_bs_eqv T s2)) (A_bs_plus T s2) (A_bs_plus_proofs T s2))
             as [commT | [[d e] ncommT ]]; unfold p2c_commutative_check.
            +++ destruct (A_sg_idempotent_d S (A_eqv_eq S (A_bs_eqv S s1)) (A_bs_plus S s1) (A_bs_plus_proofs S s1))
                as [idemS | [c nidemS ]]; unfold p2c_idempotent_check.
                ++++ destruct (A_sg_selective_d S (A_eqv_eq S (A_bs_eqv S s1)) (A_bs_plus S s1) (A_bs_plus_proofs S s1))
                    as [selS | [[h i] nselS ]]; unfold p2c_selective_check.                     
                     +++++ rewrite <- (correct_llex_product_INTERNAL_selective S T (eqv_witness (bs_eqv (A2C_bs T s2))) s1 s2 idemS commS commT selS).
                           unfold bs_classify, A_bs_classify.
                           assert (D := correct_bs_classify_bs _ (A_llex_product_INTERNAL S T (A_eqv_witness T (A_bs_eqv T s2)) s1 s2 idemS commS commT (inl selS))).
                           unfold A2C_mcas_bs in D. exact D. 
                     +++++ rewrite FF_id_ann_plus_times.
                           case_eq (A_id_ann_plus_times_d T (A_eqv_eq T (A_bs_eqv T s2)) (A_bs_plus T s2) (A_bs_times T s2) (A_bs_id_ann_proofs T s2)).
                             intros [X1 X2] Y. unfold p2c_exists_id_ann. reflexivity. 
                             intros [X1 X2] Y. unfold p2c_exists_id_ann. reflexivity. 
                             intros [X1 X2] Y. unfold p2c_exists_id_ann. reflexivity.
                             intros [X1 [X3 X4]] Y. unfold p2c_exists_id_ann. unfold projT1.
                             rewrite <- (correct_llex_product_INTERNAL_idempotent S T X1 s1 s2 idemS commS commT X3 X4).
                             unfold bs_classify, A_bs_classify.
                             assert (D := correct_bs_classify_bs _ (A_llex_product_INTERNAL S T X1 s1 s2 idemS commS commT (inr (X3, X4)))).
                             unfold A2C_mcas_bs in D. exact D. 
                             intros [X1 X2] Y. unfold p2c_exists_id_ann. reflexivity.                             
                ++++ reflexivity. 
            +++ reflexivity. 
         ++ destruct (A_sg_commutative_d T (A_eqv_eq T (A_bs_eqv T s2)) (A_bs_plus T s2) (A_bs_plus_proofs T s2))
             as [commT | [[d e] ncommT ]]; unfold p2c_commutative_check; reflexivity. 
Qed.


End Combinators.   

End Verify.  


