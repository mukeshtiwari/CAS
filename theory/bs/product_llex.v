Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.cef. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.llte_llt. 
Require Import CAS.theory.bop.llex.
Require Import CAS.theory.bop.product. 


(*
  (min, plus)  : D  
  (max, min)   : D 

  (llex min max, product plus min) : D 

  (llex max min, product min plus) : NOT D 

------

  (product plus min, llex min max) : NOT D 


  (product min plus, llex max min) : NOT D 

becase (plus, min) : NOT D. 


*) 



Lemma bop_product_llex_left_distributive : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS  mulS : binary_op S) (addT mulT : binary_op T), 
      brel_reflexive S rS -> 
      brel_symmetric S rS -> 
      brel_transitive S rS -> 
      bop_congruence S rS mulS -> 
      brel_reflexive T rT -> 
      brel_transitive T rT -> 
      bop_left_distributive S rS mulS addS → 
      bop_left_distributive T rT mulT addT → 
         bop_left_distributive (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product _ _ mulS mulT)
             (bop_llex  _ _ rS addS addT). 
Proof. intros S T rS rT addS mulS addT mulT refS symS transS b_congS refT transT ldS ldT 
           [s1 t1] [s2 t2] [s3 t3].
(*

   (s1, t1) llex (s2 s3, t2 t3) =?= ((s1, t1) llex (s2 t2)) * ((s1, t1) llex (s3, t3))

*) 
       simpl. rewrite ldS. simpl. 
       case_eq (rS s1 (mulS s2 s3)); intro H1. 
          case_eq(rS s1 s2); intro H2. 
             case_eq(rS s1 s3); intro H3. 
                apply ldT. 
                unfold brel_llt. unfold brel_conjunction. unfold brel_llte, brel_dual. 
                rewrite H3. 
                case_eq(rS s1 (addS s1 s3)); intro H4; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s3) = true


  H1 : rS s1 (mulS s1 s3) = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s3) = true

  Get contradiction if 
      rS s1 (addS s1 s3) = true -> rS s3 (mulS s1 s3) = true

  ============================
   rT (addT t1 (mulT t2 t3)) (mulT (addT t1 t2) t1) = true
                   *) 
                   admit. 
                   (*
MODULARITY 
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s3) = false
  ============================
   rT (addT t1 (mulT t2 t3)) (mulT (addT t1 t2) t3) = true
                   *) 
                   admit. 
             case_eq(rS s1 s3); intro H3. 
                unfold brel_llt. unfold brel_conjunction. unfold brel_llte, brel_dual. 
                rewrite H2. 
                case_eq(rS s1 (addS s1 s2)); intro H4; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (addS s1 s2) = true


  H1 : rS s1 (mulS s2 s1) = true
  H2 : rS s1 s2 = false
  H4 : rS s1 (addS s1 s2) = true


  Get contradiction if 
      rS s1 (addS s1 s2) = true -> rS s2 (mulS s2 s1) = true

  ============================
   rT (addT t1 (mulT t2 t3)) (mulT t1 (addT t1 t3)) = true
                   *) 
                   admit. 
                   (*

comm(mulT) + Modularity 
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (addS s1 s2) = false
  ============================
   rT (addT t1 (mulT t2 t3)) (mulT t2 (addT t1 t3)) = true
                   *) 
                   admit. 
                unfold brel_llt. unfold brel_conjunction. unfold brel_llte, brel_dual. 
                rewrite H2, H3. 
                case_eq(rS s1 (addS s1 s2) ); intro H4; 
                case_eq(rS s1 (addS s1 s3)); intro H5; simpl. 
                   (*
???
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s2) = true
  H5 : rS s1 (addS s1 s3) = true
  ============================
   rT (addT t1 (mulT t2 t3)) (mulT t1 t1) = true
                   *) 
                   admit. 
                   (*
??? 
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s2) = true
  H5 : rS s1 (addS s1 s3) = false
  ============================
   rT (addT t1 (mulT t2 t3)) (mulT t1 t3) = true
                   *) 
                   admit. 
                   (*
??? 
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s2) = false
  H5 : rS s1 (addS s1 s3) = true
  ============================
   rT (addT t1 (mulT t2 t3)) (mulT t2 t1) = true
                   *) 
                   admit. 
                   (*
??
  H1 : rS s1 (mulS s2 s3) = true
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = false
  H4 : rS s1 (addS s1 s2) = false
  H5 : rS s1 (addS s1 s3) = false
  ============================
   rT (addT t1 (mulT t2 t3)) (mulT t2 t3) = true
                   *) 
                   admit. 
          case_eq(rS s1 s2); intro H2; case_eq(rS s1 s3); intro H3; 
             unfold brel_llt; unfold brel_conjunction; unfold brel_llte, brel_dual; simpl; 
             case_eq(rS s1 (mulS s2 s3)); intro H4; simpl; 
             case_eq(rS s1 (addS s1 (mulS s2 s3))); intro H5; simpl. 
                (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) (addT t1 t3)) = true
                *) 
                rewrite H4 in H1. discriminate. 
                (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) (addT t1 t3)) = true
                *) 
                rewrite H4 in H1. discriminate. 
                (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true


  H1 : rS s1 (mulS s1 s1) = false
  H5 : rS s1 (addS s1 (mulS s1 s1)) = true

  contradiction with Idem(mulS) 

  ============================
   rT t1 (mulT (addT t1 t2) (addT t1 t3)) = true
      t1 = (t1 + t2) * (t1 + t3) = t1 + (t2 * t3). 
                *) 
                admit. 
                (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false

  contradiction with Idem(mulS) 


  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) (addT t1 t3)) = true
                *) 
                admit. 

                rewrite H3. case_eq(rS s1 (addS s1 s3)); intro H6; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s3) = true
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) t1) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s3) = false
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) t3) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                rewrite H3. case_eq(rS s1 (addS s1 s3)); intro H6; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s3) = true
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) t1) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s3) = false
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) t3) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                rewrite H3. case_eq(rS s1 (addS s1 s3)); intro H6; simpl. 
                   (*


  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s3) = true


  H1 : rS s1 (mulS s1 s3) = false
  H3 : rS s1 s3 = false
  H5 : rS s1 (addS s1 (mulS s1 s3)) = true
  H6 : rS s1 (addS s1 s3) = true

ABSORPTION 
or contradiction with rS s1 (addS s1 s3) = true -> rS s3 = (mulS s1 s3) = true 

  ============================
   rT t1 (mulT (addT t1 t2) t1) = true
                   *) 
                   admit. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s3) = false


  H1 : rS s1 (mulS s1 s3) = false
  H3 : rS s1 s3 = false
  H5 : rS s1 (addS s1 (mulS s1 s3)) = true
  H6 : rS s1 (addS s1 s3) = false

   s3 < s1 

   s1 < (s1 * s3) 

  ============================
   rT t1 (mulT (addT t1 t2) t3) = true
                   *) 
                   admit. 
                rewrite H3. case_eq(rS s1 (addS s1 s3)); intro H6; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s3) = true
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) t1) = true
                   *) 
                   admit. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = true
  H3 : rS s1 s3 = false
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s3) = false
  ============================
   rT (mulT t2 t3) (mulT (addT t1 t2) t3) = true
                   *) 
                   admit. 

                rewrite H2. case_eq(rS s1 (addS s1 s2)); intro H6; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s2) = true
  ============================
   rT (mulT t2 t3) (mulT t1 (addT t1 t3)) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s2) = false
  ============================
   rT (mulT t2 t3) (mulT t2 (addT t1 t3)) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                rewrite H2. case_eq(rS s1 (addS s1 s2)); intro H6; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s2) = true
  ============================
   rT (mulT t2 t3) (mulT t1 (addT t1 t3)) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = true
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s2) = false
  ============================
   rT (mulT t2 t3) (mulT t2 (addT t1 t3)) = true
                   *) 
                   rewrite H4 in H1. discriminate. 
                rewrite H2. case_eq(rS s1 (addS s1 s2)); intro H6; simpl. 
                   (*

ABSORB 

  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s2) = true
  ============================
   rT t1 (mulT t1 (addT t1 t3)) = true
                   *) 
                   admit. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = true
  H6 : rS s1 (addS s1 s2) = false
  ============================
   rT t1 (mulT t2 (addT t1 t3)) = true
                   *) 
                   admit. 
                rewrite H2. case_eq(rS s1 (addS s1 s2)); intro H6; simpl. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s2) = true
  ============================
   rT (mulT t2 t3) (mulT t1 (addT t1 t3)) = true
                   *) 
                   admit. 
                   (*
  H1 : rS s1 (mulS s2 s3) = false
  H2 : rS s1 s2 = false
  H3 : rS s1 s3 = true
  H4 : rS s1 (mulS s2 s3) = false
  H5 : rS s1 (addS s1 (mulS s2 s3)) = false
  H6 : rS s1 (addS s1 s2) = false
  ============================
   rT (mulT t2 t3) (mulT t2 (addT t1 t3)) = true
                   *) 
                   admit. 

                rewrite H2, H3. case_eq(rS s1 (addS s1 s2)); intro H6; 
                                case_eq(rS s1 (addS s1 s3)); intro H7; simpl. 
                   (*
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
                   *) 
                   apply refT. (* or rewrite H4 in H1. discriminate. *) 
                rewrite H2, H3. case_eq(rS s1 (addS s1 s2)); intro H6; 
                                case_eq(rS s1 (addS s1 s3)); intro H7; simpl. 
                   (*
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
                   *) 
                   rewrite H4 in H1. discriminate. 
                   (*
                   *) 
                   apply refT. 
                rewrite H2, H3. case_eq(rS s1 (addS s1 s2)); intro H6; 
                                case_eq(rS s1 (addS s1 s3)); intro H7; simpl. 
                   (*
                   *) 
                   admit. 
                   (*
                   *) 
                   admit. 
                   (*
                   *) 
                   admit. 
                   (*
                   *) 
                   admit. 
                rewrite H2, H3. case_eq(rS s1 (addS s1 s2)); intro H6; 
                                case_eq(rS s1 (addS s1 s3)); intro H7; simpl. 
                   (*
                   *) 
                   admit. 
                   (*
                   *) 
                   admit. 
                   (*
                   *) 
                   admit. 
                   (*
                   *) 
                   apply refT. 
Defined. 










