Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.lex. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.and. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.



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
Notation "a [+] b" := (bop_lex_left argT rS a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).
Notation "[| p1 | a | c | b | d |]" := (llex_p2 argT rS addT p1 a c b d) (at level 15).

(*
Lemma bop_llex_product_left_monotone : 
  bop_left_monotone S rS addS mulS → bop_left_monotone T rT addT mulT →
  bop_left_cancellative S rS mulS →
             bop_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT lcS [s1 t1] [s2 t2] [s3 t3]. 
       unfold bop_product, bop_llex, brel_product. intro A. apply andb_is_true_left in A. destruct A as [A B]. 
       apply andb_true_intro. split.  
       apply ldS.
       case_eq(rS s2 s3); intro H1;        
       case_eq(rS s2 (s2 +S s3)); intro H2; auto.
          rewrite H2 in A. discriminate A. 
          rewrite H2 in A. discriminate A. 

       case_eq(rS s2 s3); intro H1;        
       case_eq(rS (s1 *S s2) (s1 *S s3)); intro H2; auto.
          rewrite H1 in B. apply ldT; auto. 
          rewrite H1 in B. compute. rewrite H2.
             case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H3; auto.             
                assert (C := m_conS _ _ _ _ (refS s1) H1). rewrite C in H2. discriminate H2. 
          rewrite H1 in B. apply lcS in H2. rewrite H2 in H1. discriminate H1. 
          rewrite H1 in B. compute. rewrite H2. 
             case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H3; auto.
                rewrite (ldS s1 s2 s3 A) in H3. discriminate H3. 
Qed. 

Lemma bop_llex_product_not_left_monotone_v1 (selS : bop_selective S rS addS ) : 
  bop_not_left_monotone S rS addS mulS → 
         bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3]] [A B] ].
       exists ((s1, wT), ((s2, wT), (s3, wT))); compute. rewrite A, B.
       split; auto. case_eq(rS s2 s3); intro C; auto.
          assert (D := bop_selective_implies_idempotent _ _ _ selS (s1 *S s2)). 
          apply symS in D. 
          assert (E : ((s1 *S s2) +S (s1 *S s2)) =S ((s1 *S s2) +S (s1 *S s3))).
             assert (F : (s1 *S s2) =S (s1 *S s3)). exact (m_conS _ _ _ _ (refS s1) C).
             exact (a_conS _ _ _ _ (refS (s1 *S s2)) F). 
          rewrite (tranS _ _ _ D E) in B. discriminate B. 
Defined.        


Lemma bop_llex_product_not_left_monotone_v2 (selS : bop_selective S rS addS ) : 
  bop_not_left_monotone T rT addT mulT → 
         bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3]] [A B] ].
       exists ((wS, t1), ((wS, t2), (wS, t3))); compute. 
       split; auto. rewrite (refS wS).
       assert (C : wS =S (wS +S wS)).
          destruct (selS wS wS) as [D | D]; apply symS; auto. 
       rewrite C; auto. 
       rewrite (refS ((wS *S wS))).
       assert (C : (wS *S wS) =S ((wS *S wS) +S (wS *S wS))).
          destruct (selS (wS *S wS) (wS *S wS)) as [D | D]; apply symS; auto.        
       rewrite C; auto. 
Defined.


Lemma bop_llex_product_not_left_monotone_v3 (selS : bop_selective S rS addS ) :
  bop_not_left_cancellative S rS mulS →
  bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [[s1 [s2 s3]] [A B]].
       exists ((s1, wT), ((s2, wT), (s3, wT))); compute. rewrite A, B. 
       case_eq(rS s2 (s2 +S s3)); intro C. 
          rewrite refT. split; auto.
          case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro D; auto. 
             admit. 
          destruct (selS s2 s3) as [D | D].
             apply symS in D. rewrite D in C. discriminate C.
             admit. 
Admitted.

Lemma bop_llex_product_not_left_monotone_v4 (selS : bop_selective S rS addS ) :
  bop_not_left_constant T rT mulT →  
  bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [[t1 [t2 t3]] A].
       exists ((wS, t1), ((wS, t2), (wS, t3))); compute. 
       assert (B : rS wS (wS +S wS) = true). admit. 
       rewrite B. rewrite refS. rewrite refS. 
       assert (C : rS (wS *S wS) ((wS *S wS) +S (wS *S wS)) = true). admit. 
       rewrite C. 
Admitted. 


Lemma bop_llex_product_not_left_monotone_v5 (selS : bop_selective S rS addS ) :
  bop_not_left_cancellative S rS mulS →
  bop_not_left_constant T rT mulT →    
  bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [[s1 [s2 s3]] [A B]] [[t1 [t2 t3]] C].
(*

  A : (s1 *S s2) =S (s1 *S s3)
  B : rS s2 s3 = false
  t1, t2, t3 : T
  C : rT (t1 *T t2) (t1 *T t3) = false
  
need (a, b) (c, d) (e, f) 

(c, d) = (c, d) + (e, f) 
AND 
(a, b)(c, d) <> (a, b)(c, d) + (a, b)(e, f) 
That is 
(ac, bd) <> (ac, bd) + (ae, bf)

try a = s1, c = s2, e = s3

(s2, d) = (s2, d) + (s3, f) 
AND 
(s1 s2, bd) <> (s1 s2 , bd) + (s1 s3, bf)
            =  (s1 s2  + s1 s3 , ???) 
            =  (s1 s2 , bd + bf) 
*) 
Admitted.              

*) 

Lemma bop_llex_product_left_distributive 
      (selS_or_idT : bop_selective S rS addS + bop_is_id T rT addT argT)
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT)
      (D : (bop_left_cancellative S rS mulS) + (bop_left_constant T rT mulT)) : 
         bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_lex_left, brel_product.
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
           * admit.
           * admit.              
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H2).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + destruct D as [LC | LK].
           * admit.
           * admit.              
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * admit.
           * admit.              
         + destruct D as [LC | LK].
           * admit.
           * admit.              
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + apply refT. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * admit.
           * admit.              
         + destruct selS_or_idT as [selS | idT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * destruct D as [LC | LK].
             -- assert (F1 := ldS s1 s2 s3).
(*

  (s1, t1) * [(s2, t2) + (s3, t3)] = [(s1, t1) * (s2, t2)] + [(s1, t1) * (s3, t3)] 
 
  (s1, t1) * (s2 + s2, idT)  = (s1 * s2,  t1 * t2) + (s1 * s3, t1 * t3)

  (s1 * (s2 + s2), t1) = (s1 * s2,  t1 * t2) + (s1 * s3, t1 * t3)

  (s1 * (s2 + s2), t1) = ((s1 * s2) + (s1 * s3),  idT ) 

  H2 : rS s2 (s2 +S s3) = false
  H4 : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  H1 : rS (s2 +S s3) s3 = false
  H3 : rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3) = false
  F1 : (s1 *S (s2 +S s3)) =S ((s1 *S s2) +S (s1 *S s3))

s2 # s3 

(s1 *S s2) # (s1 *S s3)

*) 
                
                admit. 
             -- admit. (* need LK * idT -> false *)
Admitted. 

(*       
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
*) 

(*
Lemma bop_lex_left_product_left_distributive_dual : 
      bop_left_distributive S rS mulS addS → bop_left_distributive T rT mulT addT  → 
             bop_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT). 
Proof. intros ldS ldT [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_lex_left, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       unfold bop_left_distributive in ldS, ldT. 
       case_eq(rS s1 (s2 *S s3)); intro H1; 
       case_eq(rS s1 s2); intro H2; 
       case_eq(rS s1 s3); intro H3. 
          apply ldT.
          case_eq(rS s1 (s1 +S s3)); intro H4; simpl. 
             admit.              
             admit.              
          case_eq(rS s1 (s1 +S s2)); intro H4; simpl. 
             admit.              
             admit. (* contra if *S selective *)              
          case_eq(rS s1 (s1 +S s2)); intro H4;
          case_eq(rS s1 (s1 +S s3)); intro H5; simpl.                
             admit. (* contra if *S selective only need H1,2,3 *)                           
             admit. (* contra if *S selective *)                                        
             admit. (* contra if *S selective *)             
             admit. (* contra if *S selective *)             
          case_eq(rS s1 (s1 +S (s2 *S s3))); intro H4; simpl. 
             admit. (* contra if *S selective only need H1,2,3 *)              
             admit. (* contra if *S selective *)             
          admit.   (* contra if *S selective *) 
          admit.   (* contra if *S selective *) 
          admit.   (* contra if *S selective *) 
Admitted. 
*) 

Definition bop_is_left_ann (S : Type) (eq : brel S) (b : binary_op S) (a : S)
    :=  ∀ s : S, (eq (b a s) a = true).

Definition bop_not_is_left_ann (S : Type) (r : brel S) (b : binary_op S) (a : S)
    := {s : S & (r (b a s) a = false)}.

Definition bop_left_cancellative_weak (S : Type) (eq : brel S) (b : binary_op S)
    := ∀ s t u : S, eq (b s t) (b s u) = true -> (eq t u = true) + (bop_is_left_ann S eq b s).

Definition bop_not_left_cancellative_weak (S : Type) (eq : brel S) (b : binary_op S)
   := { z : S * (S * S) & match z with (s, (t, u)) => (eq (b s t) (b s u) = true) * (eq t u = false) * (bop_not_is_left_ann S eq b s) end }. 


(*  COUNTER EXAMPLE: 

H1 : rS s2 s3 = false
H2 : s2 =S (s2 +S s3)
H3 : bop_is_left_ann S rS mulS s1  from   H3 : (s1 *S s2) =S (s1 *S s3)   and (bop_left_cancellative_weak S rS mulS) 
LHS
                                 (s1, t1) * ((s2, t2) + (s3, t3))
                               = (s1, t1) * (s2, t2) 
                               = (s1 * s2, t1 * t2) 
                               = (s1, t1 * t2) 
RHS
                                 ((s1, t1) * (s2, t2)) + ((s1, t1) * (s3, t3))
                               = (s1 * s2, t1 * t2) + (s1 * s3, t1 * t3)
                               = (s1, t1 * t2) + (s1, t1 * t3)
                               = (s1, (t1 * t2) + (t1 * t3))


Lemma bop_lex_left_product_left_distributive_weak : 
      bop_left_distributive S rS addS mulS → bop_left_distributive T rT addT mulT → 
         ((bop_left_cancellative_weak S rS mulS) + (bop_left_constant T rT mulT)) → 
             bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT D [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_lex_left, brel_product. 
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
                 compute in H3. admit.  <----------------COUNTER EXAMPLE 
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
                admit. <----------------COUNTER EXAMPLE 
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
Admitted. *) 




Lemma bop_lex_left_product_not_left_distributive_v1 : 
  bop_not_left_distributive S rS addS mulS → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 
*) 

Lemma bop_lex_left_product_not_left_distributive_v2 : 
  bop_not_left_distributive T rT addT mulT → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS wS). rewrite (refS (mulS wS wS)). 
       assumption. 
Defined. 
*) 





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


Definition cef_llex_product_not_left_distributive  
      {S T : Type}
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


Definition cef_llex_product_not_right_distributive
      {S T : Type}
      (rS : brel S)
      (rT : brel T)
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
      (addS : binary_op S) 
      (addT : binary_op T)
      (mulT : binary_op T) 
:= if (rS (addS s2 s3) s2) 
   then if rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
   else if rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))
        then ((s1, t1), ((s2, t2), (s3, t3)))
        else ((s1, t1), ((s2, t3), (s3, t2))). 



Lemma bop_lex_left_product_not_left_distributive_v3 : 
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → (* NB *) 
      bop_not_left_cancellative S rS mulS → bop_not_left_constant T rT mulT → 
      bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
*) 


Lemma bop_lex_left_product_not_left_distributive_v3_weak : 
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → (* NB *) 
      bop_not_left_cancellative_weak S rS mulS → bop_not_left_constant T rT mulT → 
      bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
*) 


Lemma bop_lex_left_product_right_distributive : 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
      ((bop_right_cancellative S rS mulS) + (bop_right_constant T rT mulT)) → 
      bop_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros ldS ldT D [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_lex_left, brel_product. 
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
*) 
Lemma bop_lex_left_product_not_right_distributive_v1 : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 


Lemma bop_lex_left_product_not_right_distributive_v2 : 
      bop_not_right_distributive T rT addT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS wS). rewrite (refS (mulS wS wS)). 
       assumption. 
Defined. 
*) 

Lemma bop_lex_left_product_not_right_distributive_v3: 
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → bop_not_right_cancellative S rS mulS → 
      bop_not_right_constant T rT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
 *)

Lemma bops_llex_product_not_left_distributive_left : 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. rewrite nd.  simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_left_distributive_right : 
      bop_not_left_distributive T rT addT mulT → 
      bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros [ [t1 [t2 t3 ] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl.
       rewrite (refS wS). rewrite (refS (mulS wS wS)). rewrite nd.  apply andb_comm. 
Defined. 
*) 

Lemma bops_llex_product_not_right_distributive_left : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. rewrite nd.  simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_right_distributive_right :   
      bop_not_right_distributive T rT addT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) .
Admitted.
(*
Proof. intros [ [t1 [t2 t3] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite (refS wS). rewrite (refS (wS *S wS)). 
       rewrite nd.  apply andb_comm. 
Defined. 
*) 

Lemma bops_llex_product_id_equals_ann : 
      bop_commutative S rS addS → bops_id_equals_ann S rS addS mulS → bops_id_equals_ann T rT addT mulT → 
      bops_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros commS [iS [piS paS]] [iT [piT paT]]. 
       exists (iS, iT). split.
       apply bop_lex_left_is_id; auto.
       apply bop_product_is_ann; auto.        
Defined. 
*) 


Lemma bops_product_llex_id_equals_ann : 
      bop_commutative S rS addS → bops_id_equals_ann S rS mulS addS  → 
      bops_id_equals_ann T rT mulT addT  → 
      bops_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. intros commS [iS [piS paS]] [iT [piT paT]]. 
       exists (iS, iT). split.
       apply bop_product_is_id; auto.               
       apply bop_lex_left_is_ann; auto.
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
Admitted.
(*
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H t) as [ [t' [L | R]] | [t' [L | R]] ].
       left. exists (s, t'). compute. case_eq(rS (s +S s) s); intro J. rewrite refS. rewrite L. left; auto. left; auto. 
       left. exists (s, t'). compute. case_eq(rS (s +S s) s); intro J. rewrite refS. rewrite R. right; auto. left; auto. 
       right. exists (s, t'). compute. case_eq(rS (s *S s) s); intro J. rewrite L. left; auto. left; auto. 
       right. exists (s, t'). compute. case_eq(rS (s *S s) s); intro J. rewrite R. right; auto. left; auto. 
Defined. 
*) 

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
Admitted.
(*
Proof. unfold bops_not_id_equals_ann. intros idemS H [s t]. 
       destruct (H t) as [ [t' [L| R] ] | [t' [L | R]] ].
       left. exists (s, t'). compute. rewrite L. case(rS (s *S s) s); left; reflexivity.
       left. exists (s, t'). compute. rewrite R. case(rS (s *S s) s); right; reflexivity.
       right. exists (s, t'). compute. rewrite (idemS s). rewrite refS. rewrite L. left. reflexivity.
       right. exists (s, t'). compute. rewrite (idemS s). rewrite refS. rewrite R. right. reflexivity.
Defined. 
*) 
       
(* absorption *) 

(* left left *) 

Lemma bops_llex_product_left_left_absorptive : 
      bops_left_left_absorptive S rS addS mulS → 
      ((bops_left_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
      bops_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
 *)

Lemma bops_llex_product_left_left_absorptive_dual :
      bop_selective S rS addS → bop_idempotent T rT mulT →   
      bops_left_left_absorptive S rS mulS addS → bops_left_left_absorptive T rT mulT addT → 
      bops_left_left_absorptive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Admitted.
(*
Proof. intros selS itemT ldS ldT [s1 t1] [s2 t2]; simpl.
       unfold bops_left_left_absorptive in ldS, ldT.
       unfold brel_llt. unfold brel_conjunction. unfold brel_llte. unfold brel_complement. 
       rewrite ldS; simpl. 
       case_eq(rS s1 s2); intro H1;
       case_eq(rS s1 (s1 +S s2)); intro H2; simpl.
          apply ldT.
          apply ldT.            
          rewrite symT; auto. 
          destruct (selS s1 s2) as [H3 | H3]. 
             apply symS in H3. rewrite H3 in H2. discriminate H2. 
             admit. (* BUSTED! *) 
Admitted. 
*) 


Lemma bops_llex_product_not_left_left_absorptive_left : 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_left_left_absorptive_right : 
      bops_left_left_absorptive S rS addS mulS → bops_not_left_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  →
      bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]. exists ((s1, t1), (s2, t2)). compute. rewrite laS. rewrite Q. assumption. Defined. 
 *)

(* left right *) 
Lemma bops_llex_product_left_right_absorptive :
      bops_left_right_absorptive S rS addS mulS → 
      ((bops_left_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
      bops_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
 *)


Lemma bops_llex_product_not_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_left_right_absorptive_right : 
      bops_left_right_absorptive S rS addS mulS → bops_not_left_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  → 
      bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q] . exists ((s1, t1), (s2, t2)). compute. rewrite laS. rewrite Q. assumption. Defined. 
 *)


(* right left *) 
Lemma bops_llex_product_right_left_absorptive : 
      bops_right_left_absorptive S rS addS mulS → 
      ((bops_right_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
      bops_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
*) 

Lemma bops_llex_product_not_right_left_absorptive_left : 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_right_left_absorptive_right : 
      bops_right_left_absorptive S rS addS mulS → bops_not_right_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  → 
      bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]. exists ((s1, t1), (s2, t2)). compute. rewrite laS. apply symS in Q. rewrite Q. 
       assumption. 
Defined. 
*) 

(* right_right *) 
Lemma bops_llex_product_right_right_absorptive : 
      bops_right_right_absorptive S rS addS mulS → 
      ((bops_right_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
      bops_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
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
 *)

Lemma bops_llex_product_not_right_right_absorptive_left : 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_right_right_absorptive_right : 
  bops_right_right_absorptive S rS addS mulS → bops_not_right_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  →
  bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Admitted.
(*
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q] . exists ((s1, t1), (s2, t2)). 
       compute. rewrite laS. apply symS in Q. rewrite Q. assumption. 
Defined. 
*) 


(* Decide 

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
       | inl lcS => inl _ (bop_lex_left_product_left_distributive ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_lex_left_product_left_distributive ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_lex_left_product_not_left_distributive_v3 selS commS commT not_lcS not_lkT)
                                     
            end 
       end 
   |inr not_ldT => inr _ (bop_lex_left_product_not_left_distributive_v2 not_ldT)
   end 
|inr not_ldS => inr _ (bop_lex_left_product_not_left_distributive_v1 not_ldS ) 
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
       | inl lcS => inl _ (bop_lex_left_product_right_distributive ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_lex_left_product_right_distributive ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_lex_left_product_not_right_distributive_v3 selS commS commT not_lcS not_lkT)
            end 
       end 
   |inr not_ldT => inr _ (bop_lex_left_product_not_right_distributive_v2 not_ldT)
   end 
|inr not_ldS => inr _ (bop_lex_left_product_not_right_distributive_v1 not_ldS)
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

*) 
End Theory.



(*
Section ACAS.

Section Proofs.

Variable S T : Type.
Variable eqvS : A_eqv S.
Variable eqvT : A_eqv T.
Variable plusS timesS : binary_op S.
Variable plusT timesT : binary_op T.
Variable comS : bop_commutative S (A_eqv_eq S eqvS) plusS.
Variable selS : bop_selective S (A_eqv_eq S eqvS) plusS.
Variable comT : bop_commutative T (A_eqv_eq T eqvT) plusT.
Variable c_timesS : bop_congruence S (A_eqv_eq S eqvS) timesS.

Variable left_cancel_timesS    : bop_left_cancellative_decidable S (A_eqv_eq S eqvS) timesS.     (* A_msg_left_cancel_d S rS timesS sg_S *)
Variable right_cancel_timesS   : bop_right_cancellative_decidable S (A_eqv_eq S eqvS) timesS.    (* A_msg_right_cancel_d S rS timesS sg_S *)
Variable anti_left_timesS      : bop_anti_left_decidable S (A_eqv_eq S eqvS) timesS.             (* A_msg_anti_left_d S rS timesS sg_S *)
Variable anti_right_timesS     : bop_anti_right_decidable S (A_eqv_eq S eqvS) timesS.            (* A_msg_anti_right_d S rS timesS sg_S *)
Variable left_constant_timesT  : bop_left_constant_decidable T (A_eqv_eq T eqvT) timesT.         (* A_msg_left_constant_d T rT timesT sg_T *)    
Variable right_constant_timesT : bop_right_constant_decidable T (A_eqv_eq T eqvT) timesT.        (* A_msg_right_constant_d T rT timesT sg_T *)


Definition bs_proofs_llex_product : 
     bs_proofs  S (A_eqv_eq S eqvS) plusS timesS -> 
     bs_proofs  T (A_eqv_eq T eqvT) plusT timesT -> 
        bs_proofs (S * T) 
           (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT)) 
           (bop_lex_left     (A_eqv_eq S eqvS) plusS plusT)
           (bop_product timesS timesT)
:= λ pS pT,
let rS     := A_eqv_eq S eqvS in
let s      := A_eqv_witness S eqvS in     
let eqvPS  := A_eqv_proofs S eqvS in   
let refS   := A_eqv_reflexive S rS eqvPS in 
let symS   := A_eqv_symmetric S rS eqvPS in 
let transS := A_eqv_transitive S rS eqvPS in
let rT     := A_eqv_eq T eqvT in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let ntT    := A_eqv_not_trivial T eqvT in  
let eqvPT  := A_eqv_proofs T  eqvT in   
let refT   := A_eqv_reflexive T rT eqvPT in 
let symT   := A_eqv_symmetric T rT eqvPT in 
let transT := A_eqv_transitive T rT eqvPT in
let congT  := A_eqv_congruence T rT eqvPT in 
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T rS rT s t plusS timesS plusT timesT refS symS transS refT symT transT c_timesS selS comS comT
     left_cancel_timesS
     left_constant_timesT                                           
     (A_bs_left_distributive_d S rS plusS timesS pS)
     (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d   := 
   bops_llex_product_right_distributive_decide S T rS rT s t plusS timesS plusT timesT refS symS transS refT symT transT c_timesS selS comS comT
     right_cancel_timesS
     right_constant_timesT                                           
     (A_bs_right_distributive_d S rS plusS timesS pS)
     (A_bs_right_distributive_d T rT plusT timesT pT)
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T rS rT t plusS timesS plusT timesT refT
    (A_bs_left_left_absorptive_d S rS plusS timesS pS)
    (A_bs_left_left_absorptive_d T rT plusT timesT pT)
    anti_left_timesS
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T rS rT t plusS timesS plusT timesT refT 
    (A_bs_left_right_absorptive_d S rS plusS timesS pS)
    (A_bs_left_right_absorptive_d T rT plusT timesT pT)
    anti_right_timesS    
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T rS rT t plusS timesS plusT timesT symS transS refT 
       (A_bs_right_left_absorptive_d S rS plusS timesS pS)
       (A_bs_right_left_absorptive_d T rT plusT timesT pT)
       anti_left_timesS
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T rS rT t plusS timesS plusT timesT symS transS refT
       (A_bs_right_right_absorptive_d S rS plusS timesS pS)
       (A_bs_right_right_absorptive_d T rT plusT timesT pT)
       anti_right_timesS           
|}.


Definition semiring_proofs_llex:
     semiring_proofs  S (A_eqv_eq S eqvS) plusS timesS -> 
     semiring_proofs  T (A_eqv_eq T eqvT) plusT timesT ->
     (bop_left_cancellative S (A_eqv_eq S eqvS) timesS + bop_left_constant T (A_eqv_eq T eqvT) timesT) ->
     (bop_right_cancellative S (A_eqv_eq S eqvS) timesS + bop_right_constant T (A_eqv_eq T eqvT) timesT) ->      
        semiring_proofs (S * T) 
           (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT)) 
           (bop_lex_left     (A_eqv_eq S eqvS) plusS plusT)
           (bop_product timesS timesT)
:= λ pS pT dL dR,
let rS     := A_eqv_eq S eqvS in
let eqvPS  := A_eqv_proofs S eqvS in   
let refS   := A_eqv_reflexive S rS eqvPS in 
let symS   := A_eqv_symmetric S rS eqvPS in 
let trnS   := A_eqv_transitive S rS eqvPS in
let rT     := A_eqv_eq T eqvT in
let t      := A_eqv_witness T eqvT in
let eqvPT  := A_eqv_proofs T  eqvT in   
let refT   := A_eqv_reflexive T rT eqvPT in 
let trnT   := A_eqv_transitive T rT eqvPT in
let ldS := A_semiring_left_distributive _ _ _ _ pS in
let rdS := A_semiring_right_distributive _ _ _ _ pS in         
let ldT := A_semiring_left_distributive _ _ _ _ pT in
let rdT := A_semiring_right_distributive _ _ _ _ pT in         
{| A_semiring_left_distributive       :=
     bop_lex_left_product_left_distributive S T rS rT plusS timesS plusT timesT refS symS trnS refT trnT c_timesS ldS ldT dL
 ; A_semiring_right_distributive      :=
        bop_lex_left_product_right_distributive S T rS rT plusS timesS plusT timesT refS symS trnS refT trnT c_timesS rdS rdT dR       
 ; A_semiring_left_left_absorptive_d  :=
    bops_llex_product_left_left_absorptive_decide S T rS rT t plusS timesS plusT timesT refT
    (A_semiring_left_left_absorptive_d S rS plusS timesS pS)
    (A_semiring_left_left_absorptive_d T rT plusT timesT pT)
    anti_left_timesS
 ; A_semiring_left_right_absorptive_d :=
    bops_llex_product_left_right_absorptive_decide S T rS rT t plusS timesS plusT timesT refT 
    (A_semiring_left_right_absorptive_d S rS plusS timesS pS)
    (A_semiring_left_right_absorptive_d T rT plusT timesT pT)
    anti_right_timesS    
|}.

Definition id_ann_proofs_llex
(dS : id_ann_proofs S (A_eqv_eq S eqvS) plusS timesS)
(dT : id_ann_proofs T (A_eqv_eq T eqvT) plusT timesT) :
  id_ann_proofs (S * T)
                (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                (bop_lex_left (A_eqv_eq S eqvS) plusS plusT)
                (bop_product timesS timesT) := 
let rS     := A_eqv_eq S eqvS in
let eqvPS  := A_eqv_proofs S eqvS in   
let refS   := A_eqv_reflexive S rS eqvPS in 
let symS   := A_eqv_symmetric S rS eqvPS in 
let trnS   := A_eqv_transitive S rS eqvPS in
let rT     := A_eqv_eq T eqvT in
let eqvPT  := A_eqv_proofs T  eqvT in   
let refT   := A_eqv_reflexive T rT eqvPT in 
{|     
  A_id_ann_exists_plus_id_d       :=
    bop_lex_left_exists_id_decide S T rS rT plusS plusT refS symS trnS refT comS
                              (A_id_ann_exists_plus_id_d _ _ _ _ dS)
                              (A_id_ann_exists_plus_id_d _ _ _ _ dT) 
; A_id_ann_exists_plus_ann_d      :=
    bop_lex_left_exists_ann_decide S T rS rT plusS plusT refS symS trnS refT comS
                               (A_id_ann_exists_plus_ann_d _ _ _ _ dS)
                               (A_id_ann_exists_plus_ann_d _ _ _ _ dT) 
; A_id_ann_exists_times_id_d      :=
    bop_product_exists_id_decide S T rS rT timesS timesT
                                 (A_id_ann_exists_times_id_d _ _ _ _ dS)
                                 (A_id_ann_exists_times_id_d _ _ _ _ dT)
; A_id_ann_exists_times_ann_d     :=
    bop_product_exists_ann_decide S T rS rT timesS timesT
                                  (A_id_ann_exists_times_ann_d _ _ _ _ dS)
                                  (A_id_ann_exists_times_ann_d _ _ _ _ dT)
; A_id_ann_plus_id_is_times_ann_d :=  
    bops_llex_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS trnS refT comS 
     (A_id_ann_plus_id_is_times_ann_d S rS plusS timesS dS)
     (A_id_ann_plus_id_is_times_ann_d T rT plusT timesT dT)
; A_id_ann_times_id_is_plus_ann_d :=  
   bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS trnS refT comS 
   (bop_selective_implies_idempotent S rS plusS selS)  (* NB : selectivity used here *) 
   (A_id_ann_times_id_is_plus_ann_d S rS plusS timesS dS)
   (A_id_ann_times_id_is_plus_ann_d T rT plusT timesT dT)
|}.


Definition zero_one_proofs_llex 
(dS : zero_one_proofs S (A_eqv_eq S eqvS) plusS timesS)
(dT : zero_one_proofs T (A_eqv_eq T eqvT) plusT timesT) :
  zero_one_proofs (S * T)
                (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                (bop_lex_left (A_eqv_eq S eqvS) plusS plusT)
                (bop_product timesS timesT) :=
let rS     := A_eqv_eq S eqvS in
let eqvPS  := A_eqv_proofs S eqvS in   
let refS   := A_eqv_reflexive S rS eqvPS in 
let symS   := A_eqv_symmetric S rS eqvPS in 
let trnS   := A_eqv_transitive S rS eqvPS in
let rT     := A_eqv_eq T eqvT in
let eqvPT  := A_eqv_proofs T  eqvT in   
let refT   := A_eqv_reflexive T rT eqvPT in 
{|
   A_zero_one_exists_plus_ann_d      :=
     bop_lex_left_exists_ann_decide S T rS rT plusS plusT refS symS trnS refT comS
       (A_zero_one_exists_plus_ann_d S rS plusS timesS dS )
       (A_zero_one_exists_plus_ann_d T rT plusT timesT dT)
 ; A_zero_one_exists_times_id        :=
     bop_product_exists_id S T rS rT timesS timesT
      (A_zero_one_exists_times_id S rS plusS timesS dS)
      (A_zero_one_exists_times_id T rT plusT timesT dT) 
 ; A_zero_one_plus_id_is_times_ann   :=
    bops_llex_product_id_equals_ann S T rS rT plusS timesS plusT timesT symS trnS refT comS 
     (A_zero_one_plus_id_is_times_ann S rS plusS timesS dS)
     (A_zero_one_plus_id_is_times_ann T rT plusT timesT dT)
 ; A_zero_one_times_id_is_plus_ann_d :=
   bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS trnS refT comS 
   (bop_selective_implies_idempotent S rS plusS selS)  (* NB : selectivity used here *) 
   (A_zero_one_times_id_is_plus_ann_d S rS plusS timesS dS)
   (A_zero_one_times_id_is_plus_ann_d T rT plusT timesT dT)
     
|}.


Definition bounded_proofs_llex 
(dS : bounded_proofs S (A_eqv_eq S eqvS) plusS timesS)
(dT : bounded_proofs T (A_eqv_eq T eqvT) plusT timesT) :
  bounded_proofs (S * T)
                 (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                 (bop_lex_left (A_eqv_eq S eqvS) plusS plusT)
                 (bop_product timesS timesT) :=
let rS     := A_eqv_eq S eqvS in
let eqvPS  := A_eqv_proofs S eqvS in   
let symS   := A_eqv_symmetric S rS eqvPS in 
let trnS   := A_eqv_transitive S rS eqvPS in
let rT     := A_eqv_eq T eqvT in
let eqvPT  := A_eqv_proofs T  eqvT in   
let refT   := A_eqv_reflexive T rT eqvPT in 
{|
  A_bounded_plus_id_is_times_ann :=
    bops_llex_product_id_equals_ann S T rS rT plusS timesS plusT timesT symS trnS refT comS 
     (A_bounded_plus_id_is_times_ann S rS plusS timesS dS)
     (A_bounded_plus_id_is_times_ann T rT plusT timesT dT)
 ; A_bounded_times_id_is_plus_ann :=
   bops_product_llex_id_equals_ann S T rS rT plusS timesS plusT timesT symS trnS refT comS 
   (A_bounded_times_id_is_plus_ann S rS plusS timesS dS)
   (A_bounded_times_id_is_plus_ann T rT plusT timesT dT)
      
|}.

  
End Proofs. 

Definition A_bs_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs T -> A_bs (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_bs_CS_eqv S bsS   in
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
let plusS  := A_bs_CS_plus S bsS  in 
let plusT  := A_bs_plus T bsT  in
let timesS := A_bs_CS_times S bsS in 
let timesT := A_bs_times T bsT in
let comS   := A_sg_CS_commutative _ _ _ (A_bs_CS_plus_proofs S bsS) in
let selS   := A_sg_CS_selective _ _ _ (A_bs_CS_plus_proofs S bsS) in
let comT   := A_asg_commutative _ _ _ (A_bs_plus_proofs T bsT) in
let c_timesS := A_msg_congruence S rS timesS (A_bs_CS_times_proofs S bsS) in 
let left_cancel_timesS    := A_msg_left_cancel_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let right_cancel_timesS   := A_msg_right_cancel_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let anti_left_timesS      := A_msg_anti_left_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let anti_right_timesS     := A_msg_anti_right_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let left_constant_timesT  := A_msg_left_constant_d T rT timesT (A_bs_times_proofs T bsT) in 
let right_constant_timesT := A_msg_right_constant_d T rT timesT (A_bs_times_proofs T bsT) in 
{| 
     A_bs_eqv         := A_eqv_product S T eqvS eqvT 
   ; A_bs_plus        := bop_lex_left rS plusS plusT 
   ; A_bs_times       := bop_product timesS timesT 
   ; A_bs_plus_proofs := asg_proofs_llex S T rS rT plusS plusT s peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := msg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_times_proofs T bsT)
   ; A_bs_id_ann_proofs := id_ann_proofs_llex S T eqvS eqvT plusS timesS plusT timesT comS selS 
                           (A_bs_CS_id_ann_proofs S bsS)
                           (A_bs_id_ann_proofs T bsT)
   ; A_bs_proofs    := bs_proofs_llex_product S T eqvS eqvT plusS timesS plusT timesT comS selS comT c_timesS
                                      left_cancel_timesS    
                                      right_cancel_timesS   
                                      anti_left_timesS      
                                      anti_right_timesS     
                                      left_constant_timesT  
                                      right_constant_timesT 
                                      (A_bs_CS_proofs S bsS) 
                                      (A_bs_proofs T bsT)
   ; A_bs_ast        := Ast_bs_llex (A_bs_CS_ast S bsS, A_bs_ast T bsT)
|}. 



Definition A_bs_CS_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_CS T -> A_bs_CS (S * T)
:= λ S T bsS bsT,
let eqvS   := A_bs_CS_eqv S bsS   in
let eqvT   := A_bs_CS_eqv T bsT   in
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
let plusS  := A_bs_CS_plus S bsS  in 
let plusT  := A_bs_CS_plus T bsT  in
let timesS := A_bs_CS_times S bsS in 
let timesT := A_bs_CS_times T bsT in
let comS   := A_sg_CS_commutative _ _ _ (A_bs_CS_plus_proofs S bsS) in
let selS   := A_sg_CS_selective _ _ _ (A_bs_CS_plus_proofs S bsS) in
let comT   := A_sg_CS_commutative _ _ _ (A_bs_CS_plus_proofs T bsT) in
let c_timesS := A_msg_congruence S rS timesS (A_bs_CS_times_proofs S bsS) in 
let left_cancel_timesS    := A_msg_left_cancel_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let right_cancel_timesS   := A_msg_right_cancel_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let anti_left_timesS      := A_msg_anti_left_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let anti_right_timesS     := A_msg_anti_right_d S rS timesS (A_bs_CS_times_proofs S bsS) in 
let left_constant_timesT  := A_msg_left_constant_d T rT timesT (A_bs_CS_times_proofs T bsT) in 
let right_constant_timesT := A_msg_right_constant_d T rT timesT (A_bs_CS_times_proofs T bsT) in 
{| 
     A_bs_CS_eqv         := A_eqv_product S T eqvS eqvT 
   ; A_bs_CS_plus        := bop_lex_left rS plusS plusT 
   ; A_bs_CS_times       := bop_product timesS timesT 
   ; A_bs_CS_plus_proofs := sg_CS_proofs_llex S T rS rT plusS plusT peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_plus_proofs T bsT) 
   ; A_bs_CS_times_proofs := msg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_CS_times_proofs T bsT)
   ; A_bs_CS_id_ann_proofs := id_ann_proofs_llex S T eqvS eqvT plusS timesS plusT timesT comS selS 
                           (A_bs_CS_id_ann_proofs S bsS)
                           (A_bs_CS_id_ann_proofs T bsT)
   ; A_bs_CS_proofs    := bs_proofs_llex_product S T eqvS eqvT plusS timesS plusT timesT comS selS comT c_timesS
                                      left_cancel_timesS    
                                      right_cancel_timesS   
                                      anti_left_timesS      
                                      anti_right_timesS     
                                      left_constant_timesT  
                                      right_constant_timesT 
                                      (A_bs_CS_proofs S bsS) 
                                      (A_bs_CS_proofs T bsT)
   ; A_bs_CS_ast        := Ast_bs_llex (A_bs_CS_ast S bsS, A_bs_CS_ast T bsT)
|}. 

End ACAS.

Section CAS.

Definition bops_llex_product_left_distributive_check 
     {S T : Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (s : S) 
     (t : T) 
     (lcS_d : check_left_cancellative (S := S)) 
     (lkT_d : check_left_constant (S := T)) 
     (ldS_d : check_left_distributive (S := S)) 
     (ldT_d : check_left_distributive (S := T)) : 
     check_left_distributive (S := (S * T)) 
:= 
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
                     (cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, t), ((s2, t), (s3, t))) 
end.

Definition bops_llex_product_right_distributive_check 
     {S T : Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (s : S) 
     (t : T) 
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
                     (cef_llex_product_not_right_distributive rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, t), ((s2, t), (s3, t))) 
end.


(* these are the same as for product *) 
Definition bops_llex_product_plus_id_is_times_ann_check : 
   ∀ {S T : Type},  
     check_plus_id_equals_times_ann (S := S) -> 
     check_plus_id_equals_times_ann (S := T) -> 
     check_plus_id_equals_times_ann (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann s => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann t => Certify_Plus_Id_Equals_Times_Ann (s, t) 
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann  
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 

Definition bops_llex_product_times_id_equals_plus_ann_check : 
   ∀ {S T : Type},  
     check_times_id_equals_plus_ann (S := S) -> 
     check_times_id_equals_plus_ann (S := T) -> 
     check_times_id_equals_plus_ann (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann s => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann t => Certify_Times_Id_Equals_Plus_Ann (s, t) 
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann  
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann 
   end. 



Definition bops_llex_product_left_left_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := T) -> 
     check_anti_left (S := S) -> 
     check_left_left_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Left_Left_Absorptive  ((s1, t), (s2, t))
end. 


Definition bops_llex_product_left_right_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := T) -> 
     check_anti_right (S := S) -> 
     check_left_right_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Left_Right_Absorptive  ((s1, t), (s2, t))
end. 



Definition bops_llex_product_right_left_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := T) -> 
     check_anti_left (S := S) -> 
     check_right_left_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Right_Left_Absorptive  ((s1, t), (s2, t))
end. 


Definition bops_llex_product_right_right_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := T) -> 
     check_anti_right (S := S) -> 
     check_right_right_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Right_Right_Absorptive  ((s1, t), (s2, t))
end. 



Section Certs.

Variable S T : Type.
Variable rS : brel S. 
Variable rT : brel T.
Variable s : S.
Variable t : T. 
Variable plusS timesS : binary_op S.
Variable plusT timesT : binary_op T.

Variable left_cancel_timesS    : @check_left_cancellative S.   
Variable right_cancel_timesS   : @check_right_cancellative S.  
Variable anti_left_timesS      : @check_anti_left S.           
Variable anti_right_timesS     : @check_anti_right S.          
Variable left_constant_timesT  : @check_left_constant T.       
Variable right_constant_timesT : @check_right_constant T.

Definition bs_certs_llex_product : @bs_certificates  S -> @bs_certificates  T -> @bs_certificates (S * T) 
:= λ pS pT,
{|
  bs_left_distributive_d    := 
    bops_llex_product_left_distributive_check rS rT plusS plusT timesT s t 
     left_cancel_timesS
     left_constant_timesT                                           
     (bs_left_distributive_d pS)
     (bs_left_distributive_d pT)
; bs_right_distributive_d   := 
   bops_llex_product_right_distributive_check rS rT plusS plusT timesT s t 
     right_cancel_timesS
     right_constant_timesT                                           
     (bs_right_distributive_d pS)
     (bs_right_distributive_d pT)
; bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_check t 
    (bs_left_left_absorptive_d pS)
    (bs_left_left_absorptive_d pT)
    anti_left_timesS
; bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_check t
    (bs_left_right_absorptive_d pS)
    (bs_left_right_absorptive_d pT)
    anti_right_timesS    
; bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_check t 
       (bs_right_left_absorptive_d pS)
       (bs_right_left_absorptive_d pT)
       anti_left_timesS
; bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_check t 
       (bs_right_right_absorptive_d pS)
       (bs_right_right_absorptive_d pT)
       anti_right_timesS           
|}.


Definition id_ann_certs_llex_product
(dS : @id_ann_certificates S)  (dT : @id_ann_certificates T ) : @id_ann_certificates (S * T) := 
{|     
  id_ann_exists_plus_id_d       :=
    check_exists_id_llex (id_ann_exists_plus_id_d dS) (id_ann_exists_plus_id_d dT) 
; id_ann_exists_plus_ann_d      :=
    check_exists_ann_llex (id_ann_exists_plus_ann_d dS) (id_ann_exists_plus_ann_d dT) 
; id_ann_exists_times_id_d      :=
    check_exists_id_product (id_ann_exists_times_id_d dS) (id_ann_exists_times_id_d dT)
; id_ann_exists_times_ann_d     :=
    check_exists_ann_product (id_ann_exists_times_ann_d dS) (id_ann_exists_times_ann_d dT)
; id_ann_plus_id_is_times_ann_d :=  
    bops_llex_product_plus_id_is_times_ann_check (id_ann_plus_id_is_times_ann_d dS) (id_ann_plus_id_is_times_ann_d dT)
; id_ann_times_id_is_plus_ann_d :=
   bops_llex_product_times_id_equals_plus_ann_check (id_ann_times_id_is_plus_ann_d dS) (id_ann_times_id_is_plus_ann_d dT)
|}.


End Certs. 


Definition bs_llex_product : ∀ {S T : Type},  @bs_CS S -> @bs T -> @bs (S * T)
:= λ {S T} bsS bsT, 
{| 
     bs_eqv        := eqv_product  
                           (bs_CS_eqv bsS) 
                           (bs_eqv bsT) 
   ; bs_plus       := bop_lex_left 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_plus bsT) 
   ; bs_times       := bop_product 
                           (bs_CS_times bsS) 
                           (bs_times bsT) 
   ; bs_plus_certs := asg_certs_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS)
                           (eqv_witness (bs_CS_eqv bsS))                            
                           (bs_CS_plus_certs bsS) 
                           (bs_plus_certs bsT) 
   ; bs_times_certs := msg_certs_product 
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_eqv bsT)) 
                           (bs_CS_times_certs bsS)
                           (bs_times_certs bsT)
   ; bs_id_ann_certs := id_ann_certs_llex_product S T (bs_CS_id_ann_certs bsS) (bs_id_ann_certs bsT)
   ; bs_certs    := bs_certs_llex_product S T
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (eqv_eq (bs_eqv bsT))
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_eqv bsT))
                           (bs_CS_plus bsS)
                           (bs_plus bsT) 
                           (bs_times bsT)
                           (msg_left_cancel_d (bs_CS_times_certs bsS))
                           (msg_right_cancel_d (bs_CS_times_certs bsS))
                           (msg_anti_left_d (bs_CS_times_certs bsS))
                           (msg_anti_right_d (bs_CS_times_certs bsS))
                           (msg_left_constant_d (bs_times_certs bsT))
                           (msg_right_constant_d (bs_times_certs bsT))
                           (bs_CS_certs bsS) 
                           (bs_certs bsT)
   ; bs_ast        := Ast_bs_llex (bs_CS_ast bsS, bs_ast bsT)
|}.


Definition bs_CS_llex_product : ∀ {S T : Type},  bs_CS (S := S) -> bs_CS (S := T) -> bs_CS (S := (S * T)) 
:= λ {S T} bsS bsT, 
{| 
     bs_CS_eqv        := eqv_product  
                           (bs_CS_eqv bsS) 
                           (bs_CS_eqv bsT) 
   ; bs_CS_plus       := bop_lex_left 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_CS_plus bsT) 
   ; bs_CS_times       := bop_product 
                           (bs_CS_times bsS) 
                           (bs_CS_times bsT) 
   ; bs_CS_plus_certs := sg_CS_certs_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_CS_plus_certs bsS) 
                           (bs_CS_plus_certs bsT) 
   ; bs_CS_times_certs := msg_certs_product 
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_CS_eqv bsT)) 
                           (bs_CS_times_certs bsS)
                           (bs_CS_times_certs bsT)                           
   ; bs_CS_id_ann_certs := id_ann_certs_llex_product S T (bs_CS_id_ann_certs bsS) (bs_CS_id_ann_certs bsT)
   ; bs_CS_certs    := bs_certs_llex_product S T
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (eqv_eq (bs_CS_eqv bsT))
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_CS_eqv bsT))
                           (bs_CS_plus bsS)
                           (bs_CS_plus bsT) 
                           (bs_CS_times bsT)
                           (msg_left_cancel_d (bs_CS_times_certs bsS))
                           (msg_right_cancel_d (bs_CS_times_certs bsS))
                           (msg_anti_left_d (bs_CS_times_certs bsS))
                           (msg_anti_right_d (bs_CS_times_certs bsS))
                           (msg_left_constant_d (bs_CS_times_certs bsT))
                           (msg_right_constant_d (bs_CS_times_certs bsT))
                           (bs_CS_certs bsS) 
                           (bs_CS_certs bsT)
   ; bs_CS_ast        := Ast_bs_llex (bs_CS_ast bsS, bs_CS_ast bsT)
|}. 

End CAS.

Section Verify.


Section ChecksCorrect.
  Variable S : Type.
  Variable T : Type.
  Variable eqvS : A_eqv S.
  Variable eqvT : A_eqv T.
(*  
  Variable rS : brel S.
  Variable rT : brel T.
*)
  Let rS : brel S := A_eqv_eq S eqvS. 
  Let rT : brel T := A_eqv_eq T eqvT. 
  Variable plusS timesS : binary_op S.
  Variable plusT timesT : binary_op T.
(*  
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.
*)
  Let wS : S := A_eqv_witness S eqvS. 
  Let f : S -> S := A_eqv_new S eqvS.     
  Let Pf : brel_not_trivial S rS f := A_eqv_not_trivial S eqvS.     
  Let wT : T := A_eqv_witness T eqvT. 
  Let g : T -> T := A_eqv_new T eqvT.           
  Let Pg : brel_not_trivial T rT g := A_eqv_not_trivial T eqvT.     
(*  
  Variable refS : brel_reflexive S rS.   
  Variable symS : brel_symmetric S rS.
  Variable trnS : brel_transitive S rS.
  Variable refT : brel_reflexive T rT.
  Variable symT : brel_symmetric T rT.  
  Variable trnT : brel_transitive T rT. 
 *)
  Let refS : brel_reflexive S rS  := A_eqv_reflexive S rS (A_eqv_proofs S eqvS) . 
  Let symS : brel_symmetric S rS  := A_eqv_symmetric S rS (A_eqv_proofs S eqvS) . 
  Let trnS : brel_transitive S rS := A_eqv_transitive S rS (A_eqv_proofs S eqvS) . 
  Let refT : brel_reflexive T rT  := A_eqv_reflexive T rT (A_eqv_proofs T eqvT) . 
  Let symT : brel_symmetric T rT  := A_eqv_symmetric T rT (A_eqv_proofs T eqvT) . 
  Let trnT : brel_transitive T rT := A_eqv_transitive T rT (A_eqv_proofs T eqvT) .
  
  Variable cong_timesS : bop_congruence S rS timesS.
  Variable sel_plusS   : bop_selective S rS plusS.
  Variable comsg_plusS : bop_commutative S rS plusS.
  Variable comsg_plusT : bop_commutative T rT plusT.

Lemma bop_lex_left_product_left_distributive_check_correct : 
  ∀ (qS_d : bop_left_cancellative_decidable S rS timesS) 
     (qT_d : bop_left_constant_decidable T rT timesT)
     (pS_d : bop_left_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_left_distributive_decidable T rT plusT timesT), 
    bops_llex_product_left_distributive_check rS rT plusS plusT timesT wS wT
       (p2c_left_cancel_check S rS timesS qS_d)
       (p2c_left_constant_check T rT timesT qT_d)                                                                                            
       (p2c_left_distributive S rS plusS timesS pS_d)
       (p2c_left_distributive T rT plusT timesT pT_d)
     = 
     @p2c_left_distributive (S * T) 
        (brel_product rS rT)
        (bop_lex_left rS plusS plusT)
        (bop_product timesS timesT)
        (bops_llex_product_left_distributive_decide S T rS rT wS wT plusS timesS plusT timesT refS symS trnS refT symT trnT
                                                    cong_timesS sel_plusS comsg_plusS comsg_plusT qS_d qT_d pS_d pT_d).
Proof. intros [lcS | [[u1 [u2 u3]] [L R]] ]
              [lkS | [[v1 [v2 v3]] P] ]
              [ ldS | [ [s1 [s2 s3]] nldS] ]
              [ ldT | [ [t1 [t2 t3]] nldT] ];
         compute; reflexivity. Qed. 

Lemma bop_lex_left_product_right_distributive_check_correct : 
  ∀ (qS_d : bop_right_cancellative_decidable S rS timesS) 
     (qT_d : bop_right_constant_decidable T rT timesT)
     (pS_d : bop_right_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_right_distributive_decidable T rT plusT timesT), 
    bops_llex_product_right_distributive_check rS rT plusS plusT timesT wS wT
       (p2c_right_cancel_check S rS timesS qS_d)
       (p2c_right_constant_check T rT timesT qT_d)                                                                                            
       (p2c_right_distributive S rS plusS timesS pS_d)
       (p2c_right_distributive T rT plusT timesT pT_d)
     = 
     @p2c_right_distributive (S * T) 
        (brel_product rS rT)
        (bop_lex_left rS plusS plusT)
        (bop_product timesS timesT)
        (bops_llex_product_right_distributive_decide S T rS rT wS wT plusS timesS plusT timesT refS symS trnS refT symT trnT
                                                     cong_timesS sel_plusS comsg_plusS comsg_plusT qS_d qT_d pS_d pT_d).
Proof. intros [lcS | [[u1 [u2 u3]] [L R]] ]
              [lkS | [[v1 [v2 v3]] P] ]
              [ ldS | [ [s1 [s2 s3]] nldS] ]
              [ ldT | [ [t1 [t2 t3]] nldT] ];
         compute; reflexivity. Qed. 


     

Lemma bop_lex_left_product_plus_id_is_times_ann_check_correct : 
  ∀ (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
     (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product rS rT)
      (bop_lex_left rS plusS plusT)
      (bop_product timesS timesT)
      (bops_llex_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS trnS refT comsg_plusS pS_d pT_d)
   = 
   bops_llex_product_plus_id_is_times_ann_check 
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros [ [a [LS RS]] | neqS] [ [b [LT RT]] | neqT]; compute; reflexivity. Qed.



     
     

Lemma bop_lex_left_product_times_id_equals_plus_ann_check_correct : 
  ∀ (idem_plusS : bop_idempotent S rS plusS)
     (pS_d : bops_id_equals_ann_decidable S rS timesS plusS)
     (pT_d : bops_id_equals_ann_decidable T rT timesT plusT), 
   p2c_times_id_equals_plus_ann (S * T) 
      (brel_product rS rT)
      (bop_lex_left rS plusS plusT)
      (bop_product timesS timesT)
      (bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT
                                              timesT refS symS trnS refT comsg_plusS idem_plusS pS_d pT_d)
   = 
   bops_llex_product_times_id_equals_plus_ann_check 
      (p2c_times_id_equals_plus_ann S rS plusS timesS pS_d) 
      (p2c_times_id_equals_plus_ann T rT plusT timesT pT_d).
Proof. intros idem_plusS [ [a [LS RS]] | neqS] [ [b [LT RT]] | neqT]; compute; reflexivity. Qed.


Lemma bop_lex_left_product_left_left_absorbtive_check_correct : 
  ∀ (alS : bop_anti_left_decidable S rS timesS)
     (pS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_left_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_left_left_absorptive_check wT 
       (p2c_left_left_absorptive S rS plusS timesS pS_d)
       (p2c_left_left_absorptive T rT plusT timesT pT_d)
       (p2c_anti_left_check S rS timesS alS) 
     = 
   p2c_left_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_lex_left rS plusS plusT)
        (bop_product timesS timesT)
        (bops_llex_product_left_left_absorptive_decide S T rS rT wT plusS timesS plusT timesT refT pS_d pT_d alS).
Proof. intros [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; simpl; auto. Qed. 


Lemma bop_lex_left_product_right_left_absorbtive_check_correct : 
  ∀ (alS : bop_anti_left_decidable S rS timesS)
     (pS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_left_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_right_left_absorptive_check wT 
       (p2c_right_left_absorptive S rS plusS timesS pS_d)
       (p2c_right_left_absorptive T rT plusT timesT pT_d)
       (p2c_anti_left_check S rS timesS alS) 
     = 
   p2c_right_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_lex_left rS plusS plusT)
        (bop_product timesS timesT)
        (bops_llex_product_right_left_absorptive_decide S T rS rT wT plusS timesS plusT timesT symS trnS refT pS_d pT_d alS).
Proof. intros [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; simpl; auto. Qed. 


Lemma bop_lex_left_product_left_right_absorbtive_check_correct : 
  ∀ (alS : bop_anti_right_decidable S rS timesS)
     (pS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_right_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_left_right_absorptive_check wT 
       (p2c_left_right_absorptive S rS plusS timesS pS_d)
       (p2c_left_right_absorptive T rT plusT timesT pT_d)
       (p2c_anti_right_check S rS timesS alS)        
     = 
     p2c_left_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_lex_left rS plusS plusT)
        (bop_product timesS timesT)
        (bops_llex_product_left_right_absorptive_decide S T rS rT wT plusS timesS plusT timesT refT pS_d pT_d alS).
Proof. intros [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed.


Lemma bop_lex_left_product_right_right_absorbtive_check_correct : 
  ∀ (alS : bop_anti_right_decidable S rS timesS)
     (pS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_right_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_right_right_absorptive_check wT 
       (p2c_right_right_absorptive S rS plusS timesS pS_d)
       (p2c_right_right_absorptive T rT plusT timesT pT_d)
       (p2c_anti_right_check S rS timesS alS)        
     = 
     p2c_right_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_lex_left rS plusS plusT)
        (bop_product timesS timesT)
        (bops_llex_product_right_right_absorptive_decide S T rS rT wT plusS timesS plusT timesT symS trnS refT pS_d pT_d alS).
Proof. intros [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed.

End ChecksCorrect.

Section CertsCorrect.

Variable S T : Type.
Variable eqvS : A_eqv S.
Variable eqvT : A_eqv T.
Let rS := A_eqv_eq S eqvS.
Let rT := A_eqv_eq T eqvT.
Let wS := A_eqv_witness S eqvS.
Let wT := A_eqv_witness T eqvT.
Variable plusS timesS : binary_op S.
Variable plusT timesT : binary_op T.
Variable comS : bop_commutative S rS plusS.
Variable selS : bop_selective S rS plusS.
Variable comT : bop_commutative T rT plusT.
Variable c_timesS : bop_congruence S rS timesS.

Variable left_cancel_timesS    : bop_left_cancellative_decidable S rS timesS.     
Variable right_cancel_timesS   : bop_right_cancellative_decidable S rS timesS.    
Variable anti_left_timesS      : bop_anti_left_decidable S rS timesS.             
Variable anti_right_timesS     : bop_anti_right_decidable S rS timesS.            
Variable left_constant_timesT  : bop_left_constant_decidable T rT timesT.         
Variable right_constant_timesT : bop_right_constant_decidable T rT timesT.        


Lemma  correct_bs_certs_llex_product : 
  ∀ (bsS : bs_proofs S rS plusS timesS)
     (bsT : bs_proofs T rT plusT timesT),
    bs_certs_llex_product S T rS rT wS wT plusS plusT timesT
                          (p2c_left_cancel_check _ _ _ left_cancel_timesS)
                          (p2c_right_cancel_check _ _ _ right_cancel_timesS)
                          (p2c_anti_left_check _ _ _ anti_left_timesS)
                          (p2c_anti_right_check _ _ _ anti_right_timesS)
                          (p2c_left_constant_check _ _ _ left_constant_timesT)
                          (p2c_right_constant_check _ _ _ right_constant_timesT)
                          (P2C_bs S rS plusS timesS bsS)
                          (P2C_bs T rT plusT timesT bsT)
  =
 P2C_bs (S * T) (brel_product rS rT)
                 (bop_lex_left rS plusS plusT)
                 (bop_product timesS timesT)
                 (bs_proofs_llex_product S T eqvS eqvT plusS timesS plusT timesT comS selS comT c_timesS
                                         left_cancel_timesS right_cancel_timesS anti_left_timesS
                                         anti_right_timesS left_constant_timesT right_constant_timesT bsS bsT). 
Proof. intros.
       unfold bs_certs_llex_product, bs_proofs_llex_product, P2C_bs; simpl.
(*       
       rewrite bop_lex_left_product_plus_id_is_times_ann_check_correct.        
       rewrite bop_lex_left_product_times_id_equals_plus_ann_check_correct.                     
       destruct timesPS. destruct timesPT. simpl.  
       destruct A_msg_exists_id as [idS idPS]; destruct A_msg_exists_id0 as [idT idPT]; simpl.
 *)
       unfold rS, rT, wS, wT.  (* ugly! *) 
       rewrite <- bop_lex_left_product_left_distributive_check_correct. 
       rewrite <- bop_lex_left_product_right_distributive_check_correct. 
       rewrite <- bop_lex_left_product_left_left_absorbtive_check_correct. 
       rewrite <- bop_lex_left_product_left_right_absorbtive_check_correct. 
       rewrite <- bop_lex_left_product_right_left_absorbtive_check_correct. 
       rewrite <- bop_lex_left_product_right_right_absorbtive_check_correct.
       reflexivity. 
Qed.   


Lemma  correct_id_ann_certs_llex_product : 
  ∀ (bsS : id_ann_proofs S rS plusS timesS)
     (bsT : id_ann_proofs T rT plusT timesT),
  id_ann_certs_llex_product S T (P2C_id_ann S rS plusS timesS bsS) (P2C_id_ann T rT plusT timesT bsT)
  = 
  P2C_id_ann (S * T) (brel_product rS rT)
                     (bop_lex_left rS plusS plusT) 
                     (bop_product timesS timesT) 
                     (id_ann_proofs_llex S T eqvS eqvT plusS timesS plusT timesT comS selS bsS bsT). 
Proof. intros.
       unfold id_ann_certs_llex_product, id_ann_proofs_llex, P2C_id_ann; simpl.
       unfold rS, rT, wS, wT.  (* ugly! *) 
       rewrite bop_lex_left_product_plus_id_is_times_ann_check_correct.        
       rewrite bop_lex_left_product_times_id_equals_plus_ann_check_correct.
       rewrite <- correct_check_exists_id_product.
       rewrite <- correct_check_exists_ann_product.       
       rewrite correct_check_exists_id_llex.
       rewrite correct_check_exists_ann_llex.       
       reflexivity. 
Qed.   
End CertsCorrect. 


Theorem correct_bs_llex_product : ∀ (S T : Type) (bsS: A_bs_CS S) (bsT : A_bs T), 
   bs_llex_product (A2C_bs_CS S bsS) (A2C_bs T bsT)
   =
   A2C_bs (S * T) (A_bs_llex_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_llex_product, A_bs_llex_product, A2C_bs, A2C_bs_CS; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_asg_certs_llex.
       rewrite <- correct_msg_certs_product.        
       rewrite <- correct_bs_certs_llex_product.
       rewrite <- correct_id_ann_certs_llex_product. 
       reflexivity. 
Qed. 



Theorem correct_bs_CS_llex_product : ∀ (S T : Type) (bsS: A_bs_CS S) (bsT : A_bs_CS T), 
   bs_CS_llex_product (A2C_bs_CS S bsS) (A2C_bs_CS T bsT)
   =
   A2C_bs_CS (S * T) (A_bs_CS_llex_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_CS_llex_product, A_bs_CS_llex_product, A2C_bs_CS; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_sg_CS_certs_llex.        
       rewrite <- correct_msg_certs_product.
       rewrite <- correct_id_ann_certs_llex_product.               
       rewrite <- correct_bs_certs_llex_product.
       reflexivity.
Qed. 

End Verify.   

*)
