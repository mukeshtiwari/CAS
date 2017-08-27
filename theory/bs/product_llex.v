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

Section ProductLlex. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T. 

Variable addS  mulS : binary_op S. 
Variable addT mulT : binary_op T.

Variable ntS  : brel_nontrivial S rS. 
Variable conS : brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable ntT  : brel_nontrivial T rT. 
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

Lemma bop_product_llex_left_distributive : 
             bop_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. compute.
       assert (F1 : rS (s1 +S (s2 *S s3)) ((s1 +S s2) *S (s1 +S s3)) = true). admit.
       rewrite F1.
       case_eq (rS s1 (s2 *S s3)); intro H1.
          case_eq(rS s1 s2); intro H2.
             case_eq(rS s1 s3); intro H3.
                admit.
                case_eq(rS s1 (s1 +S s3)); intro H4.
                   admit.
                   admit.
             case_eq(rS s1 (s1 +S s2)); intro H3.             
                case_eq(rS s1 s3); intro H4.
                   admit.
                   case_eq(rS s1 (s1 +S s3)); intro H5.                    
                      admit.                 
                      admit. 
                case_eq(rS s1 s3); intro H4.
                   admit. 
                   case_eq(rS s1 (s1 +S s3)); intro H5.
                      admit.                 
                      admit. 
          case_eq(rS s1 s2); intro H2.
             case_eq(rS s1 s3); intro H3.
                case_eq(rS s1 (s1 +S (s2 *S s3))); intro H4.
                   admit.
                   admit.
                case_eq(rS s1 (s1 +S (s2 *S s3))); intro H4. 
                   case_eq(rS s1 (s1 +S s3)); intro H5. 
                       admit. 
                       admit. 
                   case_eq(rS s1 (s1 +S s3)); intro H5. 
                       admit. 
                       admit. 
             case_eq(rS s1 (s1 +S (s2 *S s3))); intro H3.             
                case_eq(rS s1 s3); intro H4.
                   case_eq(rS s1 (s1 +S s2)); intro H5. 
                      admit. 
                      admit.                 
                   case_eq(rS s1 (s1 +S s2)); intro H5. 
                      case_eq(rS s1 (s1 +S s3) ); intro H6. 
                         admit.                 
                         admit.                 
                      case_eq(rS s1 (s1 +S s3) ); intro H6. 
                         admit.                 
                         admit.                 
                case_eq(rS s1 s3); intro H4.
                   case_eq(rS s1 (s1 +S s2)); intro H5. 
                      admit. 
                      admit. 
                   case_eq(rS s1 (s1 +S s2)); intro H5. 
                      case_eq(rS s1 (s1 +S s3) ); intro H6. 
                         admit.                 
                         admit.                 
                      case_eq(rS s1 (s1 +S s3) ); intro H6. 
                         admit.                 
                         admit.                 
Admitted. 


Lemma bops_product_lex_left_left_absorptive : 
         bops_left_left_absorptive (S * T) (rS <*> rT)  (mulS [*] mulT) (addS [+] addT). 
Proof. intros [s1 t1] [s2 t2]. compute.
       assert (F : rS s1 (s1 *S (s1 +S s2)) = true). admit.
       rewrite F.
       case_eq(rS s1 s2 ); intro H1.
          admit. 
          case_eq(rS s1 (s1 +S s2)); intro H2. 
             admit. 
             admit. 
Admitted.

End ProductLlex. 