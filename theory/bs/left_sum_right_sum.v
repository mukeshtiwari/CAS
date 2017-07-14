
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.brel.sum. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties.
Require Import CAS.theory.bop.left_sum.
Require Import CAS.theory.bop.right_sum.
Require Import CAS.theory.facts. 

Section LeftSumRightSum. 


(*  
    (inl a) + (inl b) = inl (a +_S b) 
    (inr a) + (inr b) = inr (a +_T b) 
    (inl a) * (inr b) = inl a
    (inr a) * (inl b) = inl b 

    (inl a) * (inl b) = inl (a *_S b) 
    (inr a) * (inr b) = inr (a *_T b) 
    (inr a) * (inl b) = inr a 
    (inl a) * (inr b) = inr b 

compare to 

     (a, b) |> inl c = inl (a *_S c) 
     (a, b) |> inr c = inr (b *_T c) 

or to (with different +) 

     (inl c) |> (a, b)  = (c * _S a, b) 
     (inr c) |> (a, b)  = (a, c * _T b) 

which is a sub-algebra of product 
      
     (c, id) x (a, b)  = (c * _S a, b) 
     (id, c) x (a, b)  = (a, c * _T b) 

Think of scoped product: 

     (inl (c, d)) |> (a, b)  = (c * _S a, d) = (c * _S a, d left b) 
     (inr c) |> (a, b)       = (a, c * _T b) = (c right a, c * _T b) =  (id *_S a, c * _T b) =  

Generalize scoped product: 

     (inl (c, d)) |> (a, b)  = (c * _S a, d) = (c * _S a, d left b) 
     (inr (c, d)) |> (a, b)  = (c * _S a, d *_T b) 
      
*) 


Variable S T : Type.
Variable rS : brel S.
Variable rT : brel T.
Variable addS  mulS : binary_op S.
Variable addT mulT : binary_op T. 
 
Variable congS: brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS. 

Variable congT: brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT. 
Variable tranT : brel_transitive T rT.

Notation "x [+] y"  := (brel_sum _ _ x y) (at level 15).
Notation "x <+] y"  := (bop_left_sum _ _ x y) (at level 15).
Notation "x [+> y"  := (bop_right_sum _ _ x y) (at level 15).

Lemma bop_left_sum_right_sum_left_distributive : 
  bop_idempotent T rT addT →
  bop_left_distributive S rS addS mulS → 
  bop_left_distributive T rT addT mulT →
  bops_left_left_absorptive T rT addT mulT →
  bops_right_left_absorptive T rT addT mulT →              
         bop_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros idemT ldS ldT llaT rlaT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply ldS. apply refS. apply refS. apply refT. apply symT. apply idemT. apply llaT. apply rlaT. apply ldT. Qed.

Lemma bop_left_sum_right_sum_not_left_distributive_v1 ( s : S) : 
  bop_not_idempotent T rT addT →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [t Pt]. exists ((inr t), (inl s, inl s)). compute.
       rewrite (sym_as_rewrite symT). assumption.
Qed.        


Lemma bop_left_sum_right_sum_not_left_distributive_v2 : 
  bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_left_distributive_v3 : 
  bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_left_distributive_v4 (s : S) : 
  bops_not_left_left_absorptive T rT addT mulT →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inl s, inr t2)). compute. assumption. Qed.        


Lemma bop_left_sum_right_sum_not_left_distributive_v5 (s : S) : 
  bops_not_right_left_absorptive T rT addT mulT →
         bop_not_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inr t2, inl s)). compute. assumption. Qed.        


Lemma bop_left_sum_right_sum_right_distributive : 
  bop_idempotent T rT addT →
  bop_right_distributive S rS addS mulS → 
  bop_right_distributive T rT addT mulT →
  bops_left_right_absorptive T rT addT mulT →
  bops_right_right_absorptive T rT addT mulT →              
         bop_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros idemT rdS rdT lraT rraT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply rdS. apply refS. apply refS. apply refT.
       apply symT. apply idemT. apply lraT. apply rraT. apply rdT.        
Qed. 


Lemma bop_left_sum_right_sum_not_right_distributive_v1 ( s : S) : 
  bop_not_idempotent T rT addT →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [t Pt]. exists ((inr t), (inl s, inl s)). compute.
       rewrite (sym_as_rewrite symT). assumption.
Qed.        


Lemma bop_left_sum_right_sum_not_right_distributive_v2 : 
  bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_right_distributive_v3 : 
  bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Qed.        

Lemma bop_left_sum_right_sum_not_right_distributive_v4 (s : S) : 
  bops_not_left_right_absorptive T rT addT mulT →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inl s, inr t2)). compute. assumption. Qed.        


Lemma bop_left_sum_right_sum_not_right_distributive_v5 (s : S) : 
  bops_not_right_right_absorptive T rT addT mulT →
         bop_not_right_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inr t2, inl s)). compute. assumption. Qed.        


Lemma bop_left_sum_right_sum_id_equals_ann :
  bops_id_equals_ann T rT addT mulT →
         bops_id_equals_ann (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof.  intros [ [idT iT] [ [ annT aT] E ] ]. simpl in E.
        assert (I := bop_left_sum_exists_id S T rS rT addS addT refS (existT _ idT iT)). 
        assert (A := bop_right_sum_exists_ann S T rS rT mulS mulT refT (existT _ annT aT)).
        exists I. exists A.        
        destruct I as [i Pi].
        destruct A as [a Pa].
        simpl.
        assert (C1: brel_sum S T rS rT i (inr idT) = true).
           apply (bop_left_sum_id_is_inr S T rS rT addS addT symT tranT i Pi idT iT). 
        assert (C2: brel_sum S T rS rT a (inr annT) = true).
           apply (bop_right_sum_ann_is_inr S T rS rT mulS mulT symT tranT a Pa annT aT).
        assert (C3: brel_sum S T rS rT (inr annT) a = true).
           apply (brel_sum_symmetric _ _ _ _ symS symT _ _ C2).
        assert (P1 : brel_sum S T rS rT (inr annT) (inr idT) = true).
           compute. apply symT. exact E.
        assert (P2 : brel_sum S T rS rT a a = true).
           apply brel_sum_reflexive. exact refS. exact refT.    
        assert (C4: brel_sum S T rS rT (inr idT) a = true).
           rewrite <- (brel_sum_congruence _ _ _ _ congS congT (inr annT) a (inr idT) a P1 P2). exact C3. 
        apply (brel_sum_transitive _ _ _ _ tranS tranT _ _ _ C1 C4).
Qed. 


Lemma bop_left_sum_right_sum_not_id_equals_ann (t' : T) :
  bops_not_id_equals_ann T rT addT mulT →
         bops_not_id_equals_ann (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros F [i1 | i1] [a2 | a2] I A; compute.
       apply bop_left_sum_extract_id in I. 
       destruct I as [t [iT eT]]. compute in eT. discriminate eT. exact refT. exact t'. 
       reflexivity.
       reflexivity.
       apply bop_right_sum_extract_ann in A.
       destruct A as [t [aT eT]]. compute in eT.
       case_eq (rT i1 a2); intro H.
          assert (K := tranT _ _ _ H eT).
          apply bop_left_sum_extract_id in I. 
          destruct I as [t'' [iT' eT']]. compute in eT'.
          apply symT in K.
          assert (K' := tranT _ _ _ K eT'). apply symT in K'. 
          unfold bops_not_id_equals_ann in F.
          assert (J := F t'' t iT' aT). rewrite K' in J. exact J. 
          exact refT. exact t'.
          reflexivity.
          exact refT. exact t'.          
Qed.

Lemma bop_left_sum_right_sum_id_equals_ann_dual :
  bops_id_equals_ann S rS mulS addS →
             bops_id_equals_ann (S + T) (rS [+] rT) (mulS [+> mulT) (addS <+] addT).
Proof.  intros [ [idS iS] [ [ annS aS] E ] ]. simpl in E.
        assert (I := bop_right_sum_exists_id S T rS rT mulS mulT refT (existT _ idS iS)). 
        assert (A := bop_left_sum_exists_ann S T rS rT addS addT refS (existT _ annS aS)).
        exists I. exists A.        
        destruct I as [i Pi].
        destruct A as [a Pa].
        simpl.
        assert (C1: brel_sum S T rS rT i (inl idS) = true).
           apply (bop_right_sum_id_is_inl S T rS rT mulS mulT symS tranS i Pi idS iS). 
        assert (C2: brel_sum S T rS rT a (inl annS) = true).
           apply (bop_left_sum_ann_is_inl S T rS rT addS addT symS tranS a Pa annS aS).
        assert (C3: brel_sum S T rS rT (inl annS) a = true).
           apply (brel_sum_symmetric _ _ _ _ symS symT _ _ C2).
        assert (P1 : brel_sum S T rS rT (inl annS) (inl idS) = true).
           compute. apply symS. exact E.
        assert (P2 : brel_sum S T rS rT a a = true).
           apply brel_sum_reflexive. exact refS. exact refT.    
        assert (C4: brel_sum S T rS rT (inl idS) a = true).
           rewrite <- (brel_sum_congruence _ _ _ _ congS congT (inl annS) a (inl idS) a P1 P2). exact C3. 
        apply (brel_sum_transitive _ _ _ _ tranS tranT _ _ _ C1 C4).
Qed. 

Lemma bop_left_sum_right_sum_not_id_equals_ann_dual (s' : S) :
  bops_not_id_equals_ann S rS mulS addS →
             bops_not_id_equals_ann (S + T) (rS [+] rT) (mulS [+> mulT) (addS <+] addT).
Proof. intros F [i1 | i1] [a2 | a2] I A; compute.
       apply bop_left_sum_extract_ann in A.
       destruct A as [s [aS eS]]. compute in eS.
       case_eq (rS i1 a2); intro H.
          assert (K := tranS _ _ _ H eS).
          apply bop_right_sum_extract_id in I. 
          destruct I as [s'' [aS' eS']]. compute in eS'.
          apply symS in K.
          assert (K' := tranS _ _ _ K eS'). apply symS in K'. 
          unfold bops_not_id_equals_ann in F.
          assert (J := F s'' s aS' aS). rewrite K' in J. exact J. 
          exact refS. exact s'.
          reflexivity.
          exact refS. exact s'.          
       reflexivity.
       reflexivity.
       apply bop_right_sum_extract_id in I. 
       destruct I as [s [iS eS]]. compute in eS. discriminate eS. exact refS. exact s'. 
Qed.

Lemma bop_left_sum_right_sum_left_left_absorptive :
  bop_idempotent T rT addT →   
  bops_left_left_absorptive S rS addS mulS →   
  bops_left_left_absorptive T rT addT mulT →    
         bops_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT llaS llaT. unfold bops_left_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply llaS. apply refS. apply symT. apply idemT. apply llaT.
Qed. 


Lemma bop_left_sum_right_sum_not_left_left_absorptive_v1 (s : S) :
  bop_not_idempotent T rT addT →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl s). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_left_absorptive_v2 :
  bops_not_left_left_absorptive S rS addS mulS →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_left_absorptive_v3 :
  bops_not_left_left_absorptive T rT addT mulT →   
         bops_not_left_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_left_right_absorptive :
  bop_idempotent T rT addT →   
  bops_left_right_absorptive S rS addS mulS →   
  bops_left_right_absorptive T rT addT mulT →      
         bops_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT lraS lraT. unfold bops_left_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply lraS. apply refS. apply symT. apply idemT. apply lraT.
Qed.        

Lemma bop_left_sum_right_sum_not_left_right_absorptive_v1 (s : S) :
  bop_not_idempotent T rT addT →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl s). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_right_absorptive_v2 :
  bops_not_left_right_absorptive S rS addS mulS →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_left_right_absorptive_v3 :
  bops_not_left_right_absorptive T rT addT mulT →   
         bops_not_left_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_right_left_absorptive :
  bop_idempotent T rT addT →   
  bops_right_left_absorptive S rS addS mulS →   
  bops_right_left_absorptive T rT addT mulT →      
         bops_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT rlaS rlaT. unfold bops_right_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply rlaS. apply refS. apply symT. apply idemT. apply rlaT.
Qed.

Lemma bop_left_sum_right_sum_not_right_left_absorptive_v1 (s : S) :
  bop_not_idempotent T rT addT →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl s). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 

Lemma bop_left_sum_right_sum_not_right_left_absorptive_v2 :
  bops_not_right_left_absorptive S rS addS mulS →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_right_left_absorptive_v3 :
  bops_not_right_left_absorptive T rT addT mulT →   
         bops_not_right_left_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_right_right_absorptive :
  bop_idempotent T rT addT →   
  bops_right_right_absorptive S rS addS mulS →   
  bops_right_right_absorptive T rT addT mulT →      
         bops_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT rraS rraT. unfold bops_right_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply rraS. apply refS. apply symT. apply idemT. apply rraT.
Qed.        

Lemma bop_left_sum_right_sum_not_right_right_absorptive_v1 (s : S) :
  bop_not_idempotent T rT addT →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl s). compute. rewrite (sym_as_rewrite symT). assumption. Qed. 


Lemma bop_left_sum_right_sum_not_right_right_absorptive_v2 :
  bops_not_right_right_absorptive S rS addS mulS →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Qed. 

Lemma bop_left_sum_right_sum_not_right_right_absorptive_v3 :
  bops_not_right_right_absorptive T rT addT mulT →   
         bops_not_right_right_absorptive (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Qed. 

End LeftSumRightSum. 