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

Variable f : S -> S.
Variable ntS : brel_not_trivial S rS f. 
Variable g : T -> T.
Variable ntT : brel_not_trivial T rT g. 

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



Lemma bop_product_llex_not_left_distributive_v1
      (nldS : bop_not_left_distributive S rS mulS addS) : 
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct nldS as [[s1 [s2 s3]] H].
       exists ((s1, wT), ((s2, wT), (s3, wT))).
       compute. rewrite H. reflexivity. 
Defined.

Lemma bop_product_llex_not_left_distributive_v2 
      (*  ldS : bop_left_distributive S rS mulS addS  *) 
      (m_idemS : bop_idempotent S rS mulS)
      
      (nldT : bop_not_left_distributive T rT mulT addT) : 
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct nldT as [[t1 [t2 t3]] H].
       exists ((wS, t1), ((wS, t2), (wS, t3))). 
       compute. 
       case_eq(rS (wS +S (wS *S wS)) ((wS +S wS) *S (wS +S wS))); intro K; auto. 
       + assert (A := a_idemS wS). rewrite A.
         apply symS in A. rewrite A.
         assert (C := m_conS _ _ _ _ A A).
         assert (D := tranS _ _ _ K (symS _ _ C)). rewrite D.
         case_eq (rS wS (wS +S (wS *S wS))); intro E.
         ++ exact H.
         ++ assert (F := m_idemS wS).
            assert (G := a_conS _ _ _ _ (refS wS) F).
            assert (I := tranS _ _ _ A (symS _ _ G)).
            rewrite I in E. discriminate E. 
Defined.

(* for case ldT : bop_left_distributive T rT mulT addT) *) 
Lemma bop_product_llex_not_left_distributive_v3
      (ldS : bop_left_distributive S rS mulS addS)
      (m_idemS : bop_idempotent S rS mulS)

      (a_selS : bop_selective S rS addS)                  
      (m_nidemT : bop_not_idempotent T rT mulT)
           (a_nrS : bop_not_is_right S rS addS): (* follows from a_commS + a_idemS *) 
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct m_nidemT as [t1 H2].
       destruct a_nrS as [[s1 s2] H3].
       exists ((s1, t1), ((s2, t1), (s2, t1))). 
       compute.
       assert (C := ldS s1 s2 s2). rewrite C. 
       assert (D := m_idemS (s1 +S s2)).
       assert (G := tranS _ _ _ C D).
       assert (I := m_idemS s2). 
       case_eq (rS (s1 +S (s2 *S s2)) (s2 *S s2)); intro B. 
       + assert (J := tranS _ _ _ B I).
         assert (K := tranS _ _ _ (symS _ _ G) J). 
         rewrite K in H3. discriminate H3. 
       + rewrite H3.
         destruct (a_selS s1 s2) as [M | M].
         ++ apply symS in M. rewrite M.
            rewrite (tranS _ _ _ M (symS _ _ G)).
            case_eq(rT t1 (t1 *T t1)); intro F; auto.
            +++ apply symT in F. rewrite F in H2.
                discriminate H2. 
         ++ rewrite M in H3. discriminate H3. 
Defined.


Lemma bop_product_llex_not_left_distributive_v4
      (ldS : bop_left_distributive S rS mulS addS)
      (m_nidemS : bop_not_idempotent S rS mulS)
      (llaS : bops_left_left_absorptive S rS addS mulS)
      (nldT : bop_not_left_distributive T rT mulT addT) : 
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct nldT as [[t1 [t2 t3]] H].
       destruct m_nidemS as [s H']. 
       exists ((s, t1), ((s, t2), (s, t3))). 
       compute. 
       rewrite ldS.
       assert (A := a_idemS s). rewrite A. 
       apply symS in A. rewrite A. 
       assert (B := ldS s s s).
       assert (C := m_conS _ _ _ _ A A).
       assert (D := tranS _ _ _ B (symS _ _ C)). rewrite D.
       assert (E := llaS s s). rewrite E. 
       exact H.
Defined.  

Lemma bop_product_llex_not_left_distributive_v4_2
      (ldS : bop_left_distributive S rS mulS addS)
      (m_nidemS : bop_not_idempotent S rS mulS)
      (nllaS : bops_not_left_left_absorptive S rS addS mulS)
      (nldT : bop_not_left_distributive T rT mulT addT) : 
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct nldT as [[t1 [t2 t3]] H1].
       destruct m_nidemS as [s1 H2].
       destruct nllaS as [[s2 s3] H3]. 
       exists ((s2, t1), ((s2, t2), (s1, t3))). 
       compute.
       assert (H4 := ldS s2 s2 s1). 
       rewrite H4.
       assert (A := a_idemS s2). rewrite A. 
       apply symS in A. rewrite A. 
       case_eq(rS (s2 +S (s2 *S s3)) (s2 *S s3)); intro B.
       + admit. 
       + admit. 
Admitted. 

(*
           bs_trivial : exists a, forall b c, a = b + c and a = b * c
           bs_not_trivial : forall a, exists b c, a <> b + c or a <> b * c
                            exists f, forall a, f a = (b, c) and (a <> b + c or a <> b * c)
          
 *)


Lemma bop_product_llex_not_left_distributive_v5 (t1 t2 t3 : T) 
      (ldS : bop_left_distributive S rS mulS addS)
      (ldT : bop_left_distributive T rT mulT addT)
      (a_selS : bop_selective S rS addS)
      (m_idemS : bop_idempotent S rS mulS)
      (m_idemT : bop_idempotent T rT mulT) : 
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct (ntS wS) as [H1 H2].
       destruct (a_selS (f wS) wS) as [H3 | H3]. 
       + exists ((wS, t1), ((f wS, t2), (f wS, t3))). compute.
         assert (H := ldS wS (f wS) (f wS)). rewrite H.
         assert (H4 := m_idemS (wS +S f wS)).
         assert (H5 := tranS _ _ _ H H4). 
         assert (H6 : rS wS (wS +S f wS) = false). admit. rewrite H6.
         assert (H7 : rS (wS +S f wS) (f wS) = true). admit. rewrite H7.
         assert (H8 : rS (wS +S (f wS *S f wS)) (f wS *S f wS) = true). admit. rewrite H8.
         case_eq(rS wS (wS +S (f wS *S f wS))); intro H9.
         ++ admit. 
         ++ admit. (** OOOOPS **)
Admitted. 

Lemma bop_product_llex_not_left_distributive_v6 (t1 t2 t3 : T) 
      (ldS : bop_left_distributive S rS mulS addS)
      (ldT : bop_left_distributive T rT mulT addT)
      (annT : bop_is_ann T rT mulT argT)      
      (a_nselS : bop_not_selective S rS addS) 
      (m_idemS : bop_idempotent S rS mulS) :       
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct a_nselS as [[s1 s2] [H1 H2]].
       exists ((s1, t1), ((s2, t2), (s2, t3))). compute.
       assert (H3 := ldS s1 s2 s2). rewrite H3.
       assert (H4 := m_idemS (s1 +S s2)).
       assert (H5 := tranS _ _ _ H3 H4). 
       assert (H6 : rS s1 (s1 +S (s2 *S s2)) = false). admit. rewrite H6.
       rewrite H2.
       assert (H7 : rS s1 (s1 +S s2) = false). admit. rewrite H7.
       assert (H8 := m_idemS s2).
       case_eq(rS (s1 +S (s2 *S s2)) (s2 *S s2)); intro H9.
       + admit. (* this is a contradiction *) 
       + admit. (* NO *) 
Admitted. 
       
Lemma bop_product_llex_not_left_distributive_v7 (t1 t2 t3 : T) 
      (ldS : bop_left_distributive S rS mulS addS)
      (ldT : bop_left_distributive T rT mulT addT)
      (m_nidemS : bop_not_idempotent S rS mulS) :       
  bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. destruct m_nidemS as [s H1].
       exists ((s, t1), ((s, t2), (s, t3))). compute.
       assert (H2 := ldS s s s).
       assert (H3 := a_idemS s).
       rewrite H2, H3. apply symS in H3. rewrite H3. 
       assert (H4 := m_conS _ _ _ _ H3 H3).
       assert (H5 := tranS _ _ _ H2 (symS _ _ H4)).
       rewrite H5.
       assert (H6 : rS s (s +S (s *S s)) = false).
       {
         case_eq(rS s (s +S (s *S s))); intro H7; auto.
         + rewrite (symS _ _ (tranS _ _ _ H7 H5)) in H1.
           discriminate H1. 
       } 
       rewrite H6. 
       assert (H7 := ldT t1 t2 t3).
       (*  need to find t1, t2, t3 so that 

        (t2 *T t3) <> (t1 +T (t2 *T t3))

        1) +T is anti-right 
        2) t1 = g argT 
           t2, t3 = argT 
           argT = ann for *T 
                = id for +T 
        3) t1 = ann for +T 
              = id for *T 
              = t2 
           t3 = g t1 


        *) 
Admitted. 

       
Definition bop_product_llex_not_left_distributive_decide
           (ldS_d : bop_left_distributive_decidable S rS mulS addS)
           (ldT_d : bop_left_distributive_decidable T rT mulT addT)
           (llaS_d : bops_left_left_absorptive_decidable S rS addS mulS)
           (a_selS_or_annT : (bop_selective S rS addS) + ((bop_not_selective S rS addS) * (bop_is_ann T rT mulT argT)))           
           (m_idemS_d : bop_idempotent_decidable S rS mulS)
           (m_idemT_d : bop_idempotent_decidable T rT mulT)
           (a_nrS : bop_not_is_right S rS addS) (* follows from a_commS + a_idemS *)            
           (CHEAT : bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT)) :
  bop_left_distributive_decidable (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT)
  :=
    match ldS_d with
    | inr nldS => inr (bop_product_llex_not_left_distributive_v1 nldS)  (*OK*)
    | inl ldS =>
      match ldT_d with
      | inr nldT =>
        match m_idemS_d with
        | inl m_idemS => inr (bop_product_llex_not_left_distributive_v2 m_idemS nldT) (*OK*)
        | inr m_nidemS =>
          match llaS_d with
          | inl llaS => inr (bop_product_llex_not_left_distributive_v4 ldS m_nidemS llaS nldT) (*OK*)
          | inr nllaS => inr (bop_product_llex_not_left_distributive_v4_2 ldS m_nidemS nllaS nldT)
          end 
        end 
      | inl ldT =>
        match m_idemS_d with
        | inl m_idemS =>
          match a_selS_or_annT with
          | inl a_selS =>
            match m_idemT_d with
            | inl m_idemT => inr (bop_product_llex_not_left_distributive_v5 wT wT wT ldS ldT a_selS m_idemS m_idemT)
            | inr m_nidemT => inr (bop_product_llex_not_left_distributive_v3 ldS m_idemS a_selS m_nidemT a_nrS) (*OK*)
            end 
          | inr (a_nselS, annT) => inr (bop_product_llex_not_left_distributive_v6 wT wT wT ldS ldT annT a_nselS m_idemS)
          end 
        | inr m_nidemS => inr (bop_product_llex_not_left_distributive_v7 wT wT wT ldS ldT m_nidemS)
        end 
      end
    end.

(*
Definition bop_product_llex_not_left_distributive_decide_v2 
           (ldS_d : bop_left_distributive_decidable S rS mulS addS)
           (ldT_d : bop_left_distributive_decidable T rT mulT addT)
           (a_selS_or_annT : (bop_selective S rS addS) + ((bop_not_selective S rS addS) * (bop_is_ann T rT mulT argT)))
           (m_idemS_d : bop_idempotent_decidable S rS mulS)
           (m_idemT_d : bop_idempotent_decidable T rT mulT)
           (a_nrS : bop_not_is_right S rS addS) : (* follows from a_commS + a_idemS *)            
  bop_left_distributive_decidable (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT) :=
match a_selS_or_annT with
| inl a_selS =>
    match ldS_d with
    | inr nldS => inr (bop_product_llex_not_left_distributive_v1 nldS)
    | inl ldS =>
      match ldT_d with
      | inr nldT =>
        match m_idemS_d with
        | inl m_idemS => inr (bop_product_llex_not_left_distributive_v2 m_idemS nldT) (* not using a_selS *)
        | inr m_nidemS => inr (bop_product_llex_not_left_distributive_v4 ldS m_nidemS nldT) (* not using a_selS *)
        end 
      | inl ldT =>
        match m_idemS_d with
        | inl m_idemS =>
            match m_idemT_d with
            | inl m_idemT => inr (bop_product_llex_not_left_distributive_v5 wT wT wT ldS ldT a_selS m_idemS m_idemT)
            | inr m_nidemT => inr (bop_product_llex_not_left_distributive_v3 ldS m_idemS a_selS m_nidemT a_nrS)
            end 
        | inr m_nidemS => inr (bop_product_llex_not_left_distributive_v7 ldS ldT m_nidemS) (* not using a_selS *)
        end 
      end
    end
| inr (a_nselS, annT) =>   
    match ldS_d with
    | inr nldS => inr (bop_product_llex_not_left_distributive_v1 nldS)
    | inl ldS =>
      match ldT_d with
      | inr nldT =>
        match m_idemS_d with
        | inl m_idemS => inr (bop_product_llex_not_left_distributive_v2 m_idemS nldT)
        | inr m_nidemS => inr (bop_product_llex_not_left_distributive_v4 ldS m_nidemS nldT)
        end 
      | inl ldT =>
        match m_idemS_d with
        | inl m_idemS => inr (bop_product_llex_not_left_distributive_v6 ldS ldT a_nselS m_idemS)
        | inr m_nidemS => inr (bop_product_llex_not_left_distributive_v7 ldS ldT m_nidemS)
        end 
      end
    end
end .
*) 
       



Lemma bop_product_llex_not_left_distributive_COMPLETE (s1 s2 s3 : S) (t1 t2 t3 : T)
      (ldS : bop_left_distributive S rS mulS addS)
      (ldT : bop_left_distributive T rT mulT addT) : 
         bop_not_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. exists ((s1, t1), ((s2, t2), (s3, t3))). compute.
       assert (H1 := ldS s1 s2 s3).
       assert (H2 := ldT t1 t2 t3).        
       rewrite H1.
       case_eq(rS s1 (s1 +S (s2 *S s3))); intro A; 
       case_eq(rS (s1 +S (s2 *S s3)) (s2 *S s3)); intro B;
       case_eq(rS s1 (s1 +S s2)); intro C;
       case_eq(rS (s1 +S s2) s2); intro D;
       case_eq(rS s1 (s1 +S s3)); intro E;
       case_eq(rS (s1 +S s3) s3); intro F.
(*

  >>> CT1: 
  >>> exist ann = ann *T 

  >>> CT2: 
  >>> exists ann = ann *T 
  >>> exists id = id +T           
  >>> id <> ann (!!!) << NB : +S must be selective, since if not a ...

  >>> CT4: 
  >>> not idem *T

  >>> CT5: 
  >>> not idem *T
  >>> exists id +T 

  >>> CT6: 
  >>> exists id *T  
  >>> exists id +T (= argT)






subgoal 2 (ID 828) is:
 rT (t1 +T (t2 *T t3)) ((t1 +T t2) *T t1) = false
subgoal 3 (ID 829) is:
 rT (t1 +T (t2 *T t3)) ((t1 +T t2) *T t3) = false
subgoal 4 (ID 830) is:
 rT (t1 +T (t2 *T t3)) ((t1 +T t2) *T argT) = false
subgoal 5 (ID 831) is:
 rT (t1 +T (t2 *T t3)) (t1 *T (t1 +T t3)) = false
subgoal 6 (ID 832) is:
 rT (t1 +T (t2 *T t3)) (t1 *T t1) = false
subgoal 7 (ID 833) is:
 rT (t1 +T (t2 *T t3)) (t1 *T t3) = false
subgoal 8 (ID 834) is:
 rT (t1 +T (t2 *T t3)) (t1 *T argT) = false
subgoal 9 (ID 835) is:
 rT (t1 +T (t2 *T t3)) (t2 *T (t1 +T t3)) = false
subgoal 10 (ID 836) is:
 rT (t1 +T (t2 *T t3)) (t2 *T t1) = false
subgoal 11 (ID 837) is:
 rT (t1 +T (t2 *T t3)) (t2 *T t3) = false
subgoal 12 (ID 838) is:
 rT (t1 +T (t2 *T t3)) (t2 *T argT) = false
subgoal 13 (ID 839) is:
 rT (t1 +T (t2 *T t3)) (argT *T (t1 +T t3)) = false
subgoal 14 (ID 840) is:
 rT (t1 +T (t2 *T t3)) (argT *T t1) = false
subgoal 15 (ID 841) is:
 rT (t1 +T (t2 *T t3)) (argT *T t3) = false
subgoal 16 (ID 842) is:
 rT (t1 +T (t2 *T t3)) (argT *T argT) = false

(****************************************** CT2 *************************************) 
subgoal 17 (ID 843) is:
 rT t1 ((t1 +T t2) *T (t1 +T t3)) = false
  >>> CT2: 
  >>> t3 = argT = ann *T 
  >>> t1 = id +T           
  >>> id <> ann (!!!)            << NB : +S must be selective, since if not argT = id +T

(****************************************** *************************************) 

(****************************************** CT3 *************************************) 
subgoal 18 (ID 844) is:
 rT t1 ((t1 +T t2) *T t1) = false
  >>> CT3: 
  >>> 
  >>> 
  >>>
(****************************************** *************************************) 

(****************************************** CT1 *************************************) 
subgoal 19 (ID 845) is:
 rT t1 ((t1 +T t2) *T t3) = false
  >>> CT1: 
  >>> t3 = argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 20 (ID 846) is:
 rT t1 ((t1 +T t2) *T argT) = false
  >>> CT1: 
  >>> argT = ann *T 
  >>> t1 = g argT 
  >>>
(*******************************************************************************) 

(****************************************** CT5 *************************************) 
subgoal 21 (ID 847) is:
 rT t1 (t1 *T (t1 +T t3)) = false
  >>> CT5: 
  >>> 
  >>> t1 witness to not idem *T
  >>> t3 = id +T 
  >>>
(****************************************** *************************************) 


(****************************************** CT4 *************************************) 
subgoal 22 (ID 848) is:
 rT t1 (t1 *T t1) = false
  >>> CT4: 
  >>> 
  >>> t1 witness to not idem *T
  >>>
(****************************************** *************************************) 

(****************************************** CT1 *************************************) 
subgoal 23 (ID 849) is:
 rT t1 (t1 *T t3) = false
  >>> CT1: 
  >>> t3 = argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 24 (ID 850) is:
 rT t1 (t1 *T argT) = false
  >>> CT1: 
  >>> t2 = argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 25 (ID 851) is:
 rT t1 (t2 *T (t1 +T t3)) = false
  >>> CT1: 
  >>> t2 = argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 26 (ID 852) is:
 rT t1 (t2 *T t1) = false
  >>> CT1: 
  >>> t2 = argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 27 (ID 853) is:
 rT t1 (t2 *T t3) = false
  >>> CT1: 
  >>> t2 = argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 28 (ID 854) is:
 rT t1 (t2 *T argT) = false
  >>> CT1: 
  >>> argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 29 (ID 855) is:
 rT t1 (argT *T (t1 +T t3)) = false
  >>> CT1: 
  >>> argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 30 (ID 856) is:
 rT t1 (argT *T t1) = false
  >>> CT1: 
  >>> argT = ann *T 
  >>> t1 = g argT 
  >>>

subgoal 31 (ID 857) is:
 rT t1 (argT *T t3) = false
  >>> CT1: 
  >>> argT = ann *T 
  >>> t1 = g argT 
  >>>


subgoal 32 (ID 858) is:
 rT t1 (argT *T argT) = false
  >>> CT1: 
  >>> argT = ann *T 
  >>> t1 = g argT 
  >>>

(*******************************************************************************) 
subgoal 33 (ID 859) is:
 rT (t2 *T t3) ((t1 +T t2) *T (t1 +T t3)) = false
subgoal 34 (ID 860) is:
 rT (t2 *T t3) ((t1 +T t2) *T t1) = false
subgoal 35 (ID 861) is:
 rT (t2 *T t3) ((t1 +T t2) *T t3) = false
subgoal 36 (ID 862) is:
 rT (t2 *T t3) ((t1 +T t2) *T argT) = false
subgoal 37 (ID 863) is:
 rT (t2 *T t3) (t1 *T (t1 +T t3)) = false
subgoal 38 (ID 864) is:
 rT (t2 *T t3) (t1 *T t1) = false
subgoal 39 (ID 865) is:
 rT (t2 *T t3) (t1 *T t3) = false
subgoal 40 (ID 866) is:
 rT (t2 *T t3) (t1 *T argT) = false
subgoal 41 (ID 867) is:
 rT (t2 *T t3) (t2 *T (t1 +T t3)) = false
subgoal 42 (ID 868) is:
 rT (t2 *T t3) (t2 *T t1) = false
subgoal 43 (ID 869) is:
 rT (t2 *T t3) (t2 *T t3) = false
subgoal 44 (ID 870) is:
 rT (t2 *T t3) (t2 *T argT) = false
subgoal 45 (ID 871) is:
 rT (t2 *T t3) (argT *T (t1 +T t3)) = false
subgoal 46 (ID 872) is:
 rT (t2 *T t3) (argT *T t1) = false
subgoal 47 (ID 873) is:
 rT (t2 *T t3) (argT *T t3) = false
subgoal 48 (ID 874) is:
 rT (t2 *T t3) (argT *T argT) = false



subgoal 49 (ID 875) is:
 rT argT ((t1 +T t2) *T (t1 +T t3)) = false
  >>> CT?: 
  >>>
  >>> 
  >>> 
  >>>

subgoal 50 (ID 876) is:
 rT argT ((t1 +T t2) *T t1) = false
subgoal 51 (ID 877) is:
 rT argT ((t1 +T t2) *T t3) = false
subgoal 52 (ID 878) is:
 rT argT ((t1 +T t2) *T argT) = false

subgoal 53 (ID 879) is:
 rT argT (t1 *T (t1 +T t3)) = false
  >>> CT?: 
  >>>
  >>> 
  >>> 
  >>> 
  >>>


subgoal 54 (ID 880) is:
 rT argT (t1 *T t1) = false

(****************************************** CT6 *************************************) 
subgoal 55 (ID 881) is:
 rT argT (t1 *T t3) = false
  >>> CT6: 
  >>>
  >>> t1 = id *T  
  >>> argT = id +T 
  >>> t3 = g arg T 
  >>>
(****************************************** *************************************) 

subgoal 56 (ID 882) is:
 rT argT (t1 *T argT) = false

subgoal 57 (ID 883) is:
 rT argT (t2 *T (t1 +T t3)) = false

subgoal 58 (ID 884) is:
 rT argT (t2 *T t1) = false

subgoal 59 (ID 885) is:
 rT argT (t2 *T t3) = false

subgoal 60 (ID 886) is:
 rT argT (t2 *T argT) = false

subgoal 61 (ID 887) is:
 rT argT (argT *T (t1 +T t3)) = false

subgoal 62 (ID 888) is:
 rT argT (argT *T t1) = false

subgoal 63 (ID 889) is:
 rT argT (argT *T t3) = false

subgoal 64 (ID 890) is:
 rT argT (argT *T argT) = false

*) 



       
       + admit. (* must avoid this case! 

what can we do with just an id on +S ? 

let s1 = id 
    s2 = s3 = f s1 

  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  A : s1 =S (s1 +S (s2 *S s3))
         =S (s2 *S s3) 
         =S (s2 *S s2) 
         ???? how ???? 

  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)  << TRUE 
  C : s1 =S (s1 +S s2)   << FALSE 
  D : (s1 +S s2) =S s2   << TRUE
  E : s1 =S (s1 +S s3)   << FALSE 
  F : rS (s1 +S s3) s3   << TRUE 

OR 
s2 = s3 = id 
s1 = f id 
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
                          =S (id *S id)
  A : s1 =S (s1 +S (s2 *S s3))  <<< ???  << FALSE (if ann *S = id +S)
  B : (s1 +S (s2 *S s3)) =S (id *S id) <<< TRUE 
  C : s1 =S (s1 +S s2)   << True 
  D : (s1 +S s2) =S s2   <<FALSE
  E : s1 =S (s1 +S s3)   << True 
  F : rS (s1 +S s3) s3   <<FALSE


what can we do with just an ann on +S ? 

s1 = s2 = ann +S 
s3 = f ann 

  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
                          =S (ann *S ann)
                          =S ann (if ann = id *S)
  A : s1 =S (s1 +S (s2 *S s3))  << TRUE (if ann = id *S)
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)  
                         =S s3 << FALSE if ann = id 
  C : s1 =S (s1 +S s2)   << True
  D : (s1 +S s2) =S s2   << TRUE 
  E : s1 =S (s1 +S s3)   << True
  F : rS (s1 +S s3) s3   << FALSE 


BUT, use in combo with below? 

CI(S || s) -> k l r q y z 
k = cancel                          s * t = s* u and t <> u
l= left         (implied by C)      s * t <> s 
r = right       (implied by C)      s * t <> t 
q = constant                        s * t <> s * u 
y = anti-left   (implied by I)      s * t = s 
z = anti-right  (implied by I)      s * t = t 


*) 
       + (* 2 : 
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false
  ============================
  rT (t1 +T (t2 *T t3)) ((t1 +T t2) *T t1) = false

  t1 = id +T = ann *T 
  t3 = g t1 
  t2 = id *T
  OK 

  s1 = s2 
  A : s1 =S (s1 +S (s1 *S s3))
         =S ((s1 +S s1) *S (s1 +S s3))
         = s1 *S (s1 +S s3)
         = s1 *S s1 
         = s1                   <<<<< idem *S 
  B : (s1 +S (s1 *S s3)) =S (s1 *S s3)
      NEED s1 = s1 *S s3  ??????????????????????????????
  C : s1 =S (s1 +S s1)
  D : (s1 +S s1) =S s1

  E : s1 =S (s1 +S s3)          << from selective +S 
  F : rS (s1 +S s3) s3 = false  << from not right 

  **** OR **** 
  s1 = id + = ann * 
  s3 = f s1 
  get A and B.   
  YES

         *) 
         admit.
       + (* 3 : 
          rT (t1 +T (t2 *T t3)) ((t1 +T t2) *T t3) = false
              ann+                ann+         g t1
                                   id*
  t1 = ann +T = id *T 
  t3 = g t1 
  t2 = anything 
 
  otherwise, similar to 2 
          *)
         admit.
       + (* 4: 
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false  << from not-selective +S 
  F : rS (s1 +S s3) s3 = false  << 
  ============================
  rT (t1 +T (t2 *T t3)) ((t1 +T t2) *T argT) = false




          *) 
         admit.
       + (* 5 *) admit. 
       + (* 6
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)          <<< from selective 
  D : rS (s1 +S s2) s2 = false  <<< from not right 
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false
  ============================
  rT (t1 +T (t2 *T t3)) (t1 *T t1) = false

  s2 = s3 = f s1
  s1 = id + 


          *) 
 
         admit.
       + (* 7 *) admit.
       + (* 8 *) admit.
       + (* 9 *) admit. 
       + (* 10 *) admit.
       + (* 11 *) admit.
       + (* 12 *) admit.
       + (* 13 *) admit. 
       + (* 14 *) admit.
       + (* 15 *) admit.
       + (* 16 *) admit.
       + (* 17 *) admit. 
       + (* 18 *) admit.
       + (* 19 
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : s1 =S (s1 +S s2)
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
          *) admit.
       + (* 20 
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : s1 =S (s1 +S s2)
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false
  ============================
  rT t1 ((t1 +T t2) *T argT) = false

          *) admit.
       + (* 21 *) admit. 
       + (* 22 
OK OK OK OK OK OK OK OK OK OK OK OK OK 

SEE ABOVE 
Can also get this case with 
s1 = s2 = ann +S = id *S 
s3 = f ann 
*T not idempotent 

This is Lemma bop_product_llex_not_left_distributive_v3
      (ldS : bop_left_distributive S rS mulS addS)
      (m_idemS : bop_idempotent S rS mulS)
      (a_selS : bop_selective S rS addS)                  
      (m_nidemT : bop_not_idempotent T rT mulT)



  CASE NOT IDEM *T
  A : s1 =S (s1 +S (s2 *S s3))
         =S (s1 +S s2) *S (s1 +S s3)
         =S s1 *S s1 OK 
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false ???
  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false   from not right
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false  from not right
  ============================
  rT t1 (t1 *T t1) = false
 
  s2 = s3
  
  B : rS (s1 +S (s2 *S s2)) (s2 *S s2) = false
  B : rS (s1 *S s1) (s2 *S s2) = false
  B : rS s1 s2 = false OK (from C D) 

  need idem( *S ) ! 

  SO: Not Sel *T
          idem *S 

          *) 
         admit.
       + (* 23 
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
  ============================
  rT t1 (t1 *T t3) = false

     t3 = ann *T 
     t1 = g t3 

          *)
         admit.
       + (* 24 
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false
  ============================
  rT t1 (t1 *T argT) = false

     t3 = ann *T 
     t1 = g t3 


   argT is ann 
   t1 = g argT
   +S not selective via (s1, s3) 
   +S has top (id) 
   s2 = top

   need A,B,C,D 

  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false
  what if s2 = top? 
       then s1 <> s2, OK 

  A : s1 =S (s1 +S (s2 *S s3)) ?? 
  A : s1 =S (s1 +S (id *S s3)) ?? 
  A : s1 =S (s1 +S  s3)   NOOOOOOOOOOOOO ***E 

          *) 
         admit.
       + (* 25 
H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : (s1 +S s3) =S s3
  ============================
  rT t1 (t2 *T (t1 +T t3)) = false

          *) admit. 
       + (* 26 
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false
  ============================
  rT t1 (t2 *T t1) = false
          *)
         admit.
       + (* 27
            *********************************************
  A : s1 =S (s1 +S (s2 *S s3))
         =S (s1 +S s2) *S (s1 +S s3)
         = s2 *S s3
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
  ============================
  rT t1 (t2 *T t3) = false

  let t1 = g (wT * wT) 

  NO!  this case is self-***

          ************************************************)
         admit.
       + (* 28 
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false
  ============================
  rT t1 (t2 *T argT) = false

   argT is ann 
   t1 = g argT
   +S not selective via (s1, s3) 
   +S has bottom (ann) s2 = ann 

  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2 
  OK 

  A : s1 =S (s1 +S (s2 *S s3))
         =S (s1 +S s2) *S (s1 +S s3)
         =S s2 *S (s1 +S s3)
         =S (s1 +S s3)            if ann = *S id BUT OK if ann +S = ann *S
         **** E 

  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
      AH, s2 can't be ID of *S ! 

          *)
         admit.
       + (* 29
**************************************************
  FOR NON-SeLECtIVE CASE 

  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F : (s1 +S s3) =S s3
  ============================
  rT t1 (argT *T (t1 +T t3)) = false

     t1 = g (argT)
     let s1 = s3 

  A : s1 =S (s1 +S (s2 *S s1))
         =S (s1 +S s2) *S (s1 +S s1)
         =S (s1 +S s2) *S s1 
  B : rS (s1 +S (s2 *S s1)) (s2 *S s1) = false
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s1)
  F : (s1 +S s1) =S s1

          ****************************************************)
         admit. 
       + (* 30 
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false
  ============================
  rT t1 (argT *T t1) = false
          *)
         admit.
       + (* 31 
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
  ============================
  rT t1 (argT *T t3) = false
          *)
         admit.
       + (* 32 
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false
  ============================
  rT t1 (argT *T argT) = false
          *)
         admit.

(******************* A = false *******************************)          
       + admit. 
       + admit.
       + admit.
       + admit.
       + admit. 
       + (*
  H1 : (s1 +S (s2 *S s3)) =S ((s1 +S s2) *S (s1 +S s3))
  H2 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3))
  A : rS s1 (s1 +S (s2 *S s3)) = false
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false
  ============================
  rT (t2 *T t3) (t1 *T t1) = false

  this is case outlined above. 
s2 = s3 = id 
s1 = f id 
ann *S = id +S

BUT, how to achieve 
  rT (t2 *T t3) (t1 *T t1) = false? 

  1) t1 witness to not idem *T 
     t2 = id *T 
     t3 = t1 

  2) t1 = ann *T
     t2 = t3 = id *T


          *) 
         admit.
       + admit.
       + admit.
       + admit. 
       + admit.
       + admit.
       + admit.
       + admit. 
       + admit.
       + admit.
       + admit.
       + admit. 
       + admit.
       + admit.
       + admit.
       + admit. 
       + admit.
       + admit.
       + admit.
       + admit. 
       + admit.
       + admit.
       + admit.
       + admit. 
       + admit.
       + admit.
       + admit.
Admitted. 






Lemma bop_product_llex_left_distributive_v0
      (ldS : bop_left_distributive S rS mulS addS)
      (ldT : bop_left_distributive T rT mulT addT) : 
  bop_left_distributive (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. intros [s1 t1] [s2 t2] [s3 t3]. compute. rewrite ldS. 
       case_eq(rS s1 (s1 +S (s2 *S s3))); intro A;
       case_eq(rS (s1 +S (s2 *S s3)) (s2 *S s3)); intro B;
       case_eq(rS s1 (s1 +S s2)); intro C;
       case_eq(rS (s1 +S s2) s2); intro D;
       case_eq(rS s1 (s1 +S s3)); intro E;
       case_eq(rS (s1 +S s3) s3); intro F.
       + (* 1 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T (t1 +T t3)) *)
         apply ldT.
       + (* 2: (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T t1)
  A : s1 =S (s1 +S (s2 *S s3))
  B :       (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D :       (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : rS    (s1 +S s3) s3 = false

  s1 = s2 = = (s1 +S s2) = (s1 +S s3) = (s2 *S s3)  = s1 * s3 

  A' : s1 =S (s1 +S s2) *S (s1 +S s3) = s1 *S s1 

  A'' : s1 =S (s1 +S (s1 *S s3))
           =S (s1 *S (s1 +S s3))  by L2 
           =S (s1 * s3) 
  if LC s1 + s3 = s3  *** 
  if LK : use ldT, OK 

          *)
         admit.
       + (* 3 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T t3)
  A : s1 =S (s1 +S (s2 *S s3))
  B :       (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D :       (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3

  A'' : s1 =S (s1 +S (s1 *S s3))
           =S (s1 *S (s1 +S s3))  by L2 
           =S (s1 * s3) 
  if LC s1 + s3 = s3  *** 
  if LK : use ldT, OK 
          *)
         admit. 
       + (* 4 : (t1 +T (t2 *T t3)) =T ((t1 +T t2) *T argT) 
  A : s1 =S (s1 +S (s2 *S s3))
  B :       (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D :       (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false

  s1 = s2 = (s2 *S s3) = (s1 +S s2) *S (s1 +S s3)

  A'' : s1 =S (s1 +S (s1 *S s3))
           =S (s1 *S (s1 +S s3))  by L2 
           =S (s1 * s3) 

  case LC L s3 = s1 + s3 *** 
  case LK : use, ldT, OK 
          *) 
         admit.
       + (* 5 :  (t1 +T (t2 *T t3)) =T (t1 *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B :       (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : rS    (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F :       (s1 +S s3) =S s3

  s1 = s3 = (s1 +S s2) = (s2 *S s3) = (s1 +S s3)

  A : s1 =S (s1 +S (s2 *S s1))
  B :       (s1 +S (s2 *S s1)) =S (s2 *S s1)
  C : s1 =S (s1 +S s2)
  D : rS    (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s1)
  A : s1 =S (s1 +S (s2 *S s1))
         =S (s1 +S s2) *S (s1 +S s1)
         =S (s1 +S s2) *S s1
         =S s1 *S s1

  ??????????????????????????????????????????????????????
          *)
         admit.
       + (* 6 :  (t1 +T (t2 *T t3)) =T (t1 *T t1)

  A : s1 =S (s1 +S (s2 *S s3))
  B :       (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : rS    (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F : rS    (s1 +S s3) s3 = false

  ??????????????????????????????????????????????????????
          *)
         admit.
       + (* 7 :  (t1 +T (t2 *T t3)) =T (t1 *T t3)
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
  ??????????????????????????????????????????????????????
          *)
         admit.
       + (* 8 :  (t1 +T (t2 *T t3)) =T (t1 *T argT)
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : s1 =S (s1 +S s2)
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false

  A : s1 =S (s1 +S (s2 *S s3))
         =S (s1 +S s2) *S (s1 +S s3)
         =S s1 *S (s1 +S s3)
  ??????????????????????????????????????????????????????
          *)
         admit. 
       + (* 9 : (t1 +T (t2 *T t3)) =T (t2 *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : (s1 +S s3) =S s3

          *)
         admit.
       + (* 10 :  (t1 +T (t2 *T t3)) =T (t2 *T t1)
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false

          *)
         admit.
       + (* 11 :  (t1 +T (t2 *T t3)) =T (t2 *T t3)
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
          *)
         admit. 
       + (* 12 :  (t1 +T (t2 *T t3)) =T (t2 *T argT)
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : (s1 +S s2) =S s2
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false
          *)
         admit.
       + (* 13 :  (t1 +T (t2 *T t3)) =T (argT *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F : (s1 +S s3) =S s3
          *)
         admit.
       + (* 14 :  (t1 +T (t2 *T t3)) =T (argT *T t1) 
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false
          *)
         admit.
       + (* 15 :  (t1 +T (t2 *T t3)) =T (argT *T t3)

  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : (s1 +S s3) =S s3
          *)
         admit.
       + (* 16 :  (t1 +T (t2 *T t3)) =T (argT *T argT)
  A : s1 =S (s1 +S (s2 *S s3))
  B : (s1 +S (s2 *S s3)) =S (s2 *S s3)
  C : rS s1 (s1 +S s2) = false
  D : rS (s1 +S s2) s2 = false
  E : rS s1 (s1 +S s3) = false
  F : rS (s1 +S s3) s3 = false
          *)
         admit.
       + (* 17 :  t1 =T ((t1 +T t2) *T (t1 +T t3))
  A : s1 =S (s1 +S (s2 *S s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : s1 =S (s1 +S s2)
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : (s1 +S s3) =S s3

 should get ***
          *)
         admit.
       + (* 18 :  t1 =T ((t1 +T t2) *T t1)
  A : s1 =S (s1 +S (s2 *pS s3))
  B : rS (s1 +S (s2 *S s3)) (s2 *S s3) = false
  C : s1 =S (s1 +S s2)
  D : (s1 +S s2) =S s2
  E : s1 =S (s1 +S s3)
  F : rS (s1 +S s3) s3 = false

  s1 = s2 

  A' : s1 =S (s1 +S (s1 *S s3))
          =S (s1 *S (s1 +S s3))
          =S (s1 *S s1) 
  B' : rS    (s1 +S (s1 *S s3)) (s1 *S s3) = false

          *)
         admit. 
 (*


subgoal 19 (ID 436) is:
 t1 =T ((t1 +T t2) *T t3)
subgoal 20 (ID 437) is:
 t1 =T ((t1 +T t2) *T argT)
subgoal 21 (ID 438) is:
 t1 =T (t1 *T (t1 +T t3))
subgoal 22 (ID 439) is:
 t1 =T (t1 *T t1)
subgoal 23 (ID 440) is:
 t1 =T (t1 *T t3)
subgoal 24 (ID 441) is:
 t1 =T (t1 *T argT)
subgoal 25 (ID 442) is:
 t1 =T (t2 *T (t1 +T t3))
subgoal 26 (ID 443) is:
 t1 =T (t2 *T t1)
subgoal 27 (ID 444) is:
 t1 =T (t2 *T t3)
subgoal 28 (ID 445) is:
 t1 =T (t2 *T argT)
subgoal 29 (ID 446) is:
 t1 =T (argT *T (t1 +T t3))
subgoal 30 (ID 447) is:
 t1 =T (argT *T t1)
subgoal 31 (ID 448) is:
 t1 =T (argT *T t3)
subgoal 32 (ID 449) is:
 t1 =T (argT *T argT)
subgoal 33 (ID 450) is:
 (t2 *T t3) =T ((t1 +T t2) *T (t1 +T t3))
subgoal 34 (ID 451) is:
 (t2 *T t3) =T ((t1 +T t2) *T t1)
subgoal 35 (ID 452) is:
 (t2 *T t3) =T ((t1 +T t2) *T t3)
subgoal 36 (ID 453) is:
 (t2 *T t3) =T ((t1 +T t2) *T argT)
subgoal 37 (ID 454) is:
 (t2 *T t3) =T (t1 *T (t1 +T t3))
subgoal 38 (ID 455) is:
 (t2 *T t3) =T (t1 *T t1)
subgoal 39 (ID 456) is:
 (t2 *T t3) =T (t1 *T t3)
subgoal 40 (ID 457) is:
 (t2 *T t3) =T (t1 *T argT)
subgoal 41 (ID 458) is:
 (t2 *T t3) =T (t2 *T (t1 +T t3))
subgoal 42 (ID 459) is:
 (t2 *T t3) =T (t2 *T t1)
subgoal 43 (ID 460) is:
 (t2 *T t3) =T (t2 *T t3)
subgoal 44 (ID 461) is:
 (t2 *T t3) =T (t2 *T argT)
subgoal 45 (ID 462) is:
 (t2 *T t3) =T (argT *T (t1 +T t3))
subgoal 46 (ID 463) is:
 (t2 *T t3) =T (argT *T t1)
subgoal 47 (ID 464) is:
 (t2 *T t3) =T (argT *T t3)
subgoal 48 (ID 465) is:
 (t2 *T t3) =T (argT *T argT)
subgoal 49 (ID 466) is:
 argT =T ((t1 +T t2) *T (t1 +T t3))
subgoal 50 (ID 467) is:
 argT =T ((t1 +T t2) *T t1)
subgoal 51 (ID 468) is:
 argT =T ((t1 +T t2) *T t3)
subgoal 52 (ID 469) is:
 argT =T ((t1 +T t2) *T argT)
subgoal 53 (ID 470) is:
 argT =T (t1 *T (t1 +T t3))
subgoal 54 (ID 471) is:
 argT =T (t1 *T t1)
subgoal 55 (ID 472) is:
 argT =T (t1 *T t3)
subgoal 56 (ID 473) is:
 argT =T (t1 *T argT)
subgoal 57 (ID 474) is:
 argT =T (t2 *T (t1 +T t3))
subgoal 58 (ID 475) is:
 argT =T (t2 *T t1)
subgoal 59 (ID 476) is:
 argT =T (t2 *T t3)
subgoal 60 (ID 477) is:
 argT =T (t2 *T argT)
subgoal 61 (ID 478) is:
 argT =T (argT *T (t1 +T t3))
subgoal 62 (ID 479) is:
 argT =T (argT *T t1)
subgoal 63 (ID 480) is:
 argT =T (argT *T t3)
subgoal 64 (ID 481) is:
 argT =T (argT *T argT)
*) 
Admitted.        







Lemma bop_llex_product_left_distributive_TEST
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT):
         bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       compute. rewrite ldS.
       case_eq(rS s2 (s2 +S s3)); intro A;
       case_eq(rS (s2 +S s3) s3); intro B;
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro C;            
       case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro D.
       + apply ldT.
       + (* (t1 *T (t2 +T t3)) =T (t1 *T t2) 
  A : s2 =S (s2 +S s3)
  B : (s2 +S s3) =S s3
  C : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
  D : rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3) = false
         s1 * s3 <> s1 * (s2 + s3)
                 = s1 * s3 
          *** 
          *)
         admit.
       + (*  (t1 *T (t2 +T t3)) =T (t1 *T t3)
A : s2 =S (s2 +S s3)
  B : (s2 +S s3) =S s3
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  D : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
  *** Similar to above 
          *)
         admit.
       + (*  (t1 *T (t2 +T t3)) =T argT
  A : s2 =S (s2 +S s3)
  B : (s2 +S s3) =S s3
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
      so (s1 *S s2) <> s1 *S (s2 + s3) = s1 *S s2 ***
          *)
         admit.
       + (*  (t1 *T t2) =T ((t1 *T t2) +T (t1 *T t3))

  A : s2 =S (s2 +S s3)
  B : rS (s2 +S s3) s3 = false
  C : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
  D : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
    so (s1 *S s2) = (s1 *S s3)
    if LC, then contradiction. ***
    if LK ((t1 *T t2) +T (t1 *T t3)) = t1 * (t2 + t3) 
                                     = t1 * t2 
          OK 
          *)
         admit.
       + (* (t1 *T t2) =T (t1 *T t2) *)
         apply refT.
       + (*  (t1 *T t2) =T (t1 *T t3)
A : s2 =S (s2 +S s3)
  B : rS (s2 +S s3) s3 = false
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  D : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)

  from C : (s1 *S s2) <> s1 * (s2 + s3) 
                      <> s1 * s2 
                      ***   
                      *)
         admit.
       + (*  (t1 *T t2) =T argT
  A : s2 =S (s2 +S s3)
  B : rS (s2 +S s3) s3 = false
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  
  *** same as above 
          *)
         admit.
       + (* (t1 *T t3) =T ((t1 *T t2) +T (t1 *T t3))
A : rS s2 (s2 +S s3) = false
  B : (s2 +S s3) =S s3
  C : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
  D : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
  
      if LC, then *** 
      if LK, then OK with ldT 

          *)
         admit.
       + (* (t1 *T t3) =T (t1 *T t2)

A : rS s2 (s2 +S s3) = false
  B : (s2 +S s3) =S s3
  C : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
  D : rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3) = false
     
       so s1 * s3 <> (s1 * (s2 + s3) 
                  = s1 * s3 
                  ***  
          *)
         admit.
       + (*  (t1 *T t3) =T (t1 *T t3) *)
         apply refT.
       + (*  (t1 *T t3) =T argT
A : rS s2 (s2 +S s3) = false
  B : (s2 +S s3) =S s3
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  D : rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3) = false
  
   *** as above 
          *)
         admit.
       + (* (t1 *T argT) =T ((t1 *T t2) +T (t1 *T t3))
  A : rS s2 (s2 +S s3) = false
  B : rS (s2 +S s3) s3 = false
  C : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
  D : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)

  so, (s1 *S s2) =S (s1 *S s3) 
  if LC, then s2 = s3, and A, B *** idem 
  if LK.  use ldT.... OK 

  *)
         admit.
       + (*  (t1 *T argT) =T (t1 *T t2)

  A : rS s2 (s2 +S s3) = false
  B : rS (s2 +S s3) s3 = false
  C : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
  D : rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3) = false

  if LC : (s1 *S s2) = s1 * (s2 + s3) 
          so s2 = s2 + s3 
          *** 
  if LK, OK   
          *)
         admit.
       + (*  (t1 *T argT) =T (t1 *T t3)
  A : rS s2 (s2 +S s3) = false
  B : rS (s2 +S s3) s3 = false
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  D : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
  *** same as above 
          *)
         admit.
       + (*  (t1 *T argT) =T argT
A : rS s2 (s2 +S s3) = false
  B : rS (s2 +S s3) s3 = false
  C : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
  D : rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3) = false
  
must be in not sel case, so argT is ann. 
OK 
          *)
         admit.
Admitted.


Lemma bops_product_llex_left_left_absorptive
      (laS : bops_left_left_absorptive S rS mulS addS)
      (ilT : bop_is_left T rT mulT) : 
         bops_left_left_absorptive (S * T) (rS <*> rT)  (mulS [*] mulT) (addS [+] addT).
Proof. intros [s1 t1] [s2 t2]; compute.
       assert (H := laS s1 s2). 
       - rewrite H. 
         case_eq(rS s1 (s1 +S s2)); intro A; case_eq(rS (s1 +S s2) s2); intro B. 
         + exact (symT _ _ (ilT t1 (t1 +T t2))). 
         + exact (symT _ _ (ilT t1 t1)). 
         + exact (symT _ _ (ilT t1 t2)). 
         + exact (symT _ _ (ilT t1 argT)). 
Qed.

Lemma bops_product_llex_not_left_left_absorptive_v1
      (nlaS : bops_not_left_left_absorptive S rS mulS addS) : 
  bops_not_left_left_absorptive (S * T) (rS <*> rT)  (mulS [*] mulT) (addS [+] addT).
Proof. destruct nlaS as [[s1 s2] A].
       exists ((s1, wT), (s2, wT)). compute. 
       rewrite A. reflexivity.
Defined.

Lemma bops_product_llex_not_left_left_absorptive_v2
      (nselS : bop_not_selective S rS addS)
      (annT : bop_is_ann T rT mulT argT)
      (laS : bops_left_left_absorptive S rS mulS addS) : 
         bops_not_left_left_absorptive (S * T) (rS <*> rT)  (mulS [*] mulT) (addS [+] addT).
Proof. destruct nselS as [[s1 s2] [A  B]].
       exists ((s1, g argT), (s2, argT)). compute.
       rewrite laS. rewrite B.
       case_eq(rS s1 (s1 +S s2)); intro C.
       + apply symS in C. rewrite C in A. discriminate A. 
       + destruct (annT (g argT)) as [D E].
         case_eq(rT (g argT) (g argT *T argT)); intro F; auto.
         ++ assert (H := tranT _ _ _ F E).
            destruct (ntT argT) as [I J].
            rewrite H in J.
            discriminate J.
Defined.             


Lemma bops_product_llex_not_left_left_absorptive_v3 
      (selS : bop_selective S rS addS) 
      (laS : bops_left_left_absorptive S rS mulS addS)
      (nilT : bop_not_is_left T rT mulT) : 
  bops_not_left_left_absorptive (S * T) (rS <*> rT)  (mulS [*] mulT) (addS [+] addT).
Proof. destruct nilT as [[t1 t2] A].
       destruct (selS wS (f wS)) as [B | B].
       + exists ((f wS, t1), (wS, t2)); compute.
         rewrite laS.
         assert (C := a_commS (f wS) wS). 
         rewrite (tranS _ _ _ C B). 
         case_eq(rS (f wS) (f wS +S wS)); intro D.
         ++ assert (E := tranS _ _ _ D (tranS _ _ _ C B)).
            destruct (ntS wS) as [F G].
            rewrite E in G. discriminate G. 
         ++ case_eq(rT t1 (t1 *T t2)); intro E; auto.
            +++  apply symT in E. rewrite E in A.
                 discriminate A.
       + exists ((wS, t1), (f wS, t2)); compute.
         rewrite laS.
         rewrite B. 
         case_eq(rS wS (wS +S f wS)); intro D.
         ++ assert (E := tranS _ _ _ D B). 
            destruct (ntS wS) as [F G].
            rewrite E in F. discriminate F. 
         ++ case_eq(rT t1 (t1 *T t2)); intro E; auto.
            +++  apply symT in E. rewrite E in A.
                 discriminate A.
Defined.

Definition bops_product_llex_left_left_absorptive_decidable
      (selS_or_annT : (bop_selective S rS addS) + ((bop_not_selective S rS addS) * (bop_is_ann T rT mulT argT)))
      (laS_d : bops_left_left_absorptive_decidable S rS mulS addS)
      (ilT_d : bop_is_left_decidable T rT mulT) : 
  bops_left_left_absorptive_decidable (S * T) (rS <*> rT)  (mulS [*] mulT) (addS [+] addT) :=
match laS_d with
| inl laS => match selS_or_annT with
             | inl selS => match ilT_d with
                           | inl ilT => inl (bops_product_llex_left_left_absorptive laS ilT)
                           | inr nilT => inr (bops_product_llex_not_left_left_absorptive_v3 selS laS nilT)
                           end 
             | inr (nselS, annT) => inr (bops_product_llex_not_left_left_absorptive_v2 nselS annT laS)
             end 
| inr nlaS => inr (bops_product_llex_not_left_left_absorptive_v1 nlaS)
end.

End Theory. 
(***************************************************************************************************)
