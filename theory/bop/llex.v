Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.cef. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.llte_llt. 


Lemma bop_llex_exists_id : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        brel_reflexive T rT -> 
        bop_exists_id S rS bS -> 
        bop_exists_id T rT bT -> 
        bop_commutative S rS bS -> 
           bop_exists_id (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT).
Proof. unfold bop_exists_id. intros S T rS rT bS bT symS transS refT [iS pS] [iT pT] commS. 
       exists (iS, iT). intros (s, t). unfold brel_product, bop_llex. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr.  simpl. 
       case_eq(rS iS s); intro Q. 
          rewrite Tl.  apply symS in Q. rewrite Q. rewrite Tr. auto. 

          unfold brel_llt. unfold brel_conjunction, brel_llte, brel_negate, brel_dual.  
          rewrite Q.  rewrite (brel_symmetric_implies_dual _ _ symS _ _ Q). 
          apply symS in Sr. rewrite Sr. 
          apply (brel_symmetric_implies_dual _ _ symS) in Q. 
          assert (fact := brel_transititivity_implies_dual _ _ transS _ _ _ Sr Q).          
          assert (fact2 := commS s iS). 
          assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact2 fact). 
          apply (brel_symmetric_implies_dual _ _ symS) in fact3. 
          rewrite fact3. simpl. rewrite (refT t). auto. 
Defined. 


Lemma bop_llex_exists_ann : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        brel_reflexive T rT -> 
        bop_exists_ann S rS bS -> 
        bop_exists_ann T rT bT -> 
        bop_commutative S rS bS -> 
           bop_exists_ann (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT).
Proof. unfold bop_exists_id. intros S T rS rT bS bT symS transS refT [iS pS] [iT pT] commS. 
       exists (iS, iT). intros (s, t). unfold brel_product, bop_llex. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr.  simpl. 
       case_eq(rS iS s); intro Q. 
          rewrite Tl.  apply symS in Q. rewrite Q. rewrite Tr. auto. 

          unfold brel_llt. unfold brel_conjunction, brel_llte, brel_negate, brel_dual.  
          rewrite Q.  rewrite (brel_symmetric_implies_dual _ _ symS _ _ Q). 
          apply symS in Sl. rewrite Sl.
          apply symS in Sr.  
          assert (fact := brel_transititivity_implies_dual _ _ transS _ _ _ Sr Q).          
          apply (brel_symmetric_implies_dual _ _ symS) in fact. rewrite fact. 
          simpl. rewrite (refT iT). auto. 
Defined. 



Lemma bop_llex_not_exists_ann_left : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        brel_reflexive S rS -> 
        bop_not_exists_ann S rS bS -> 
           bop_not_exists_ann (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT).
Proof. unfold bop_not_exists_ann. 
       intros S T rS rT bS bT refS pS (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. simpl. rewrite F. simpl. reflexivity. 
          exists (x, t). right. simpl. rewrite F. simpl. reflexivity. 
Defined. 


Lemma bop_llex_not_exists_ann_right : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        brel_reflexive S rS -> 
        bop_not_exists_ann T rT bT -> 
           bop_not_exists_ann (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT).
Proof. unfold bop_not_exists_ann. 
       intros S T rS rT bS bT refS pT (s, t). 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. simpl. rewrite (refS s). rewrite F. apply andb_comm. 
          exists (s, x). right. simpl. rewrite (refS s). rewrite F. apply andb_comm. 
Defined. 


Lemma bop_llex_not_exists_id_left : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        brel_reflexive S rS -> 
        bop_not_exists_id S rS bS -> 
           bop_not_exists_id (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT).
Proof. unfold bop_not_exists_ann. 
       intros S T rS rT bS bT refS pS (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. simpl. rewrite F. simpl. reflexivity. 
          exists (x, t). right. simpl. rewrite F. simpl. reflexivity. 
Defined. 


Lemma bop_llex_not_exists_id_right: 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        brel_reflexive S rS -> 
        bop_not_exists_id T rT bT -> 
           bop_not_exists_id (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT).
Proof. unfold bop_not_exists_ann. 
       intros S T rS rT bS bT refS pT (s, t). 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. simpl. rewrite (refS s). rewrite F. apply andb_comm. 
          exists (s, x). right. simpl. rewrite (refS s). rewrite F. apply andb_comm. 
Defined. 


Lemma bop_llex_congruence : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_congruence S rS rS → brel_congruence T rT rT →
      bop_congruence S rS bS → bop_congruence T rT bT → 
      bop_congruence (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
    intros S T rS rT bS bT congS congT. 
    unfold bop_congruence.  
    intros cS cT [s1 t1] [s2 t2] [s3 t3] [s4 t4]; intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       assert (hS := congS _ _ _ _ C1 C3). 
       assert (hT := congT _ _ _ _ C2 C4). 
       assert (qS := cS _ _ _ _ C1 C3). 
       assert (qT := cT _ _ _ _ C2 C4). 
       assert (hS2 := congS _ _ _ _ C1 qS). 
       simpl. unfold brel_llt. unfold brel_conjunction, brel_llte, brel_negate.  
             unfold brel_dual. 
       rewrite hS, hS2. 
       apply andb_is_true_right. split.  
          assumption. 
          case_eq (rS s3 s4); intro Q1. 
             assumption. 

             case_eq (rS s3 (bS s3 s4)); intro Q2; simpl. 
                assumption. 
                assumption. 
Defined. 

Lemma bop_llex_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_reflexive S rS → 
      brel_reflexive T rT → 
      bop_idempotent S rS bS → 
      bop_idempotent T rT bT → 
      bop_idempotent (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT refS refT. unfold bop_idempotent. intros L R (s, t). 
   simpl. rewrite L. simpl. rewrite (refS s). rewrite R. reflexivity.
Defined. 

Lemma bop_llex_not_idempotent_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (t : T), 
      bop_not_idempotent S rS bS → 
      bop_not_idempotent (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT t. unfold bop_not_idempotent. intros [s P]. 
   exists (s, t). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_llex_not_idempotent_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (choose : S), 
      brel_reflexive S rS → 
      bop_not_idempotent T rT bT → 
      bop_not_idempotent (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT s refS [t P]. exists (s, t). simpl. 
   rewrite (refS s). rewrite P. rewrite andb_comm. simpl. reflexivity. 
Defined. 

Lemma bop_llex_not_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (chooseS : S) (chooseT : T),  
      brel_reflexive S rS → 
      (bop_not_idempotent S rS bS) +  (bop_not_idempotent T rT bT) → 
      bop_not_idempotent (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT chooseS chooseT refS. intro d. destruct d. 
   apply bop_llex_not_idempotent_left. apply chooseT. assumption. 
   apply bop_llex_not_idempotent_right. apply chooseS. assumption. assumption. 
Defined. 



Lemma bop_llex_not_commutative_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (choose : T), 
      bop_not_commutative S rS bS → 
      bop_not_commutative (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT choose. unfold bop_not_commutative. intros [ [s t] P]. 
   exists ((s, choose), (t, choose)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_llex_not_commutative_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (choose : S), 
      brel_reflexive S rS → 
      bop_not_commutative T rT bT → 
      bop_not_commutative (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT choose refS. unfold bop_not_commutative. intros [ [s t] P]. 
   exists ((choose, s), (choose, t)). simpl. apply andb_is_false_right.  right. 
   rewrite (refS choose). assumption. 
Defined. 

Lemma bop_llex_not_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (chooseS : S) (chooseT : T),  
      brel_reflexive S rS → 
      (bop_not_commutative S rS bS) +  (bop_not_commutative T rT bT) → 
      bop_not_commutative (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT chooseS chooseT refS. intro d. destruct d. 
   apply bop_llex_not_commutative_left. apply chooseT. assumption. 
   apply bop_llex_not_commutative_right. apply chooseS. assumption. assumption. 
Defined. 

Lemma bop_llex_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_congruence S rS rS → 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS →
      brel_reflexive T rT →  
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      bop_commutative T rT bT → 
      bop_commutative (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT congS refS symS transS refT selS commS commT (s1, t1) (s2, t2).  
   simpl. unfold brel_bop_to_lte_left. 
   assert (cS := commS s1 s2).  
   assert (cT := commT t1 t2).
   apply andb_is_true_right. split.  
      assumption.   
      case_eq (rS s1 s2); intro Q1. 
         rewrite (symS _ _ Q1). assumption. 
         assert (Q4 := congS _ _ _ _ (refS s2) cS). 
         rewrite (brel_symmetric_implies_dual _ _ symS _ _ Q1). 
            unfold brel_llt. unfold brel_conjunction, brel_llte, brel_dual. 
            case_eq (rS s1 (bS s1 s2)); intro Q2; case_eq (rS s2 (bS s2 s1)); intro Q3.

               rewrite Q3 in Q4. 
               assert (Q5 : rS (bS s1 s2) s2 = true). apply symS. assumption. 
               rewrite (transS _ _ _ Q2 Q5) in Q1. discriminate. 

               rewrite Q1. simpl. apply refT. 

               apply (brel_symmetric_implies_dual _ _ symS) in Q1. 
               rewrite Q1. simpl. apply refT. 

               case (selS s1 s2); intro Q5. 
                  apply symS in Q5. rewrite Q5 in Q2. discriminate. 
                  apply symS in Q5. 
                  assert (Q6 := congS _ _ _ _ (refS s2) cS).
                  rewrite Q3, Q5 in Q6. discriminate. 
Defined. 


Lemma bop_llex_not_is_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_witness T rT -> 
     brel_transitive S rS -> 
     brel_symmetric S rS -> 
     bop_commutative S rS bS → 
     bop_selective S rS bS → 
      bop_not_is_left (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
   intros S T rS rT bS bT ntS [t _] transS symS commS selS. unfold bop_not_is_left. 
   destruct (brel_nontrivial_witness _ _ ntS) as [s1 Ps1]. 
   destruct (brel_nontrivial_negate _ _ ntS) as [f Pf]. 
   exists (cef_bop_llex_not_is_left S T rS bS s1 f t). 
   unfold cef_bop_llex_not_is_left. 
   assert (fact := Pf s1).  destruct fact as [P Q]. 
   destruct (selS s1 (f s1)) as [H | H].
      rewrite H. simpl. 
      assert (K := commS s1 (f s1)). 
      apply symS in H. assert (K1 := brel_transititivity_implies_dual _ _ transS _ _ _ H P). 
      assert (K2 := brel_transititivity_implies_dual _ _ transS _ _ _ K K1). 
      rewrite K2. simpl. reflexivity. 

      apply (brel_symmetric_implies_dual _ _ symS) in P. apply symS in H. 
      assert (K1 := brel_transititivity_implies_dual _ _ transS _ _ _ H P). 
      rewrite K1. simpl. 
      rewrite K1. simpl. reflexivity. 
Defined. 

Lemma bop_llex_not_is_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_witness T rT -> 
     brel_transitive S rS -> 
     brel_symmetric S rS -> 
     bop_commutative S rS bS → 
     bop_selective S rS bS → 
      bop_not_is_right (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof.
   intros S T rS rT bS bT ntS [t _] transS symS commS selS. unfold bop_not_is_right. 
   destruct (brel_nontrivial_witness _ _ ntS) as [s1 Ps1]. 
   destruct (brel_nontrivial_negate _ _ ntS) as [f Pf]. 
   exists (cef_bop_llex_not_is_right S T rS bS s1 f t). 
   unfold cef_bop_llex_not_is_right. 
   assert (fact := Pf s1).  destruct fact as [P Q]. 
   destruct (selS s1 (f s1)) as [H | H]. 
      rewrite H. simpl. 
      apply symS in H. assert (K1 := brel_transititivity_implies_dual _ _ transS _ _ _ H P). 
      rewrite K1. simpl. reflexivity. 

      apply (brel_symmetric_implies_dual _ _ symS) in P. apply symS in H. 
      assert (K1 := brel_transititivity_implies_dual _ _ transS _ _ _ H P). 
      apply symS in H. 
      assert (K2 := brel_transititivity_implies_dual _ _ transS _ _ _ H K1). 
      assert (K := commS s1 (f s1)). 
      assert (K3 := brel_transititivity_implies_dual _ _ transS _ _ _ K K1). 
      rewrite K1. simpl. rewrite K3. simpl. reflexivity. 
Defined. 


Lemma bop_llex_not_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S), 
     brel_reflexive S rS → 
     bop_selective S rS bS → 
     bop_not_selective T rT bT → 
        bop_not_selective (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. intros S T rS rT bS bT s refS selS [ [t1 t2] P]. unfold bop_not_selective. 
       assert (idemS := bop_selective_implies_idempotent S rS bS selS). 
       exists ((s, t1), (s, t2)). unfold brel_product, bop_llex. 
       rewrite (idemS s). rewrite (refS s). simpl. assumption. 
Defined.  

Lemma bop_llex_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
     brel_reflexive S rS → 
     brel_symmetric S rS → 
     brel_transitive S rS →
     brel_reflexive T rT →  
     brel_congruence S rS rS → 
     bop_congruence S rS bS → 
     bop_commutative S rS bS → 
     bop_selective S rS bS → 
     bop_selective T rT bT → 
        bop_selective (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. unfold bop_congruence. 
    intros S T rS rT bS bT refS symS transS refT r_cong congS commS. 
    unfold bop_selective. intros  selS selT [s1 t1] [s2 t2]. 
    assert (idemS := bop_selective_implies_idempotent S rS bS selS). 
    unfold brel_product, bop_llex. unfold brel_llt, brel_conjunction, brel_llte, brel_dual. 
    destruct (selS s1 s2) as [H | H]; destruct (selT t1 t2) as [Q | Q]. 
      left. rewrite H. apply symS in H. simpl. rewrite H. simpl. 
      case_eq(rS s1 s2); intro J. 
         assumption. (* Q *) 
         simpl. apply refT.

      case_eq(rS s1 s2); intro J. 
         right. rewrite Q. assert (I := idemS s2). 
         assert (K := congS s1 s2 s2 s2 J (refS s2)). apply symS in H. 
         assert (K1 := transS _ _ _ H K). apply symS in H. 
         assert (K2 : rS (bS s1 s2) s2 = true). apply (transS _ _ _ H J). rewrite K2. simpl. 
         reflexivity. 

         left.  rewrite H. simpl. apply symS in H. 
                rewrite H. simpl. 
                apply (brel_symmetric_implies_dual _ _ symS) in J. apply refT.

      case_eq(rS s1 s2); intro J. 
         left.  rewrite Q. simpl. apply symS in J. rewrite (transS _ _ _ H J). simpl. reflexivity. 
         right. rewrite H. simpl. 
                case_eq (rS s1 (bS s1 s2)); intro K. 
                   rewrite (transS _ _ _ K H) in J. discriminate. 
                   apply refT. 

      right. rewrite H. simpl. 
      case_eq(rS s1 s2); intro J. 
         assumption. (* Q *) 
         case_eq (rS s1 (bS s1 s2)); intro K. 
            rewrite (transS _ _ _ K H) in J. discriminate. 
            apply refT. 
Defined.  


(* 

r' x y = true  <-> r x (b x y) 
Definition brel_bop_to_lte_left : ∀ (S : Type) (r : brel S) (b : binary_op S), brel S 
:= λ S r b x y, r x (b x y). 

Definition bop_llex : ∀ S T : Type, brel S → binary_op S → binary_op T → binary_op (S * T) 
:= λ S T eq b1 b2 x y,  
   match x, y with
    | (a, b), (c, d) => 
        (b1 a c, 
         if eq a c 
         then (b2 b d)
         else if brel_llt _ eq b1 a c 
              then b 
              else d)
   end.

(a, b) + (c, d) == (a + c, T(a, b, c d)) 
 T(a, b, c d)   == 
         if eq a c 
         then (b2 b d)
         else if brel_llt _ eq b1 a c 
              then b 
              else d 
*) 


(* Proof plan 

LHS = ((s1, t1) + (s2, t2)) + (s3, t3)
    = (s1 + s2, T(s1, t1, s2, t2)) + (s3, t3)
    = ((s1 + s2) + s3, T(s1 + s2, T(s1, t1, s2, t2), s3, t3)) 

RHS = (s1, t1) + ((s2, t2) + (s3, t3))
    = (s1, t1) + (s2 + s3, T(s2, t2, s3, t3)) 
    = (s1 + (s2 + s3), T(s1, t1, s2, + s3, T(s2, t2, s3, t3))

So we must show that 

LHS' = T(s1 + s2, T(s1, t1, s2, t2), s3, t3)
     = T(s1, t1, s2, + s3, T(s2, t2, s3, t3))
     = RHS' 
   
LHS' = if (s1 + s2) = s3 
       then (b2 (T(s1, t1, s2, t2)) t3)
       else if (s1 + s2) < s3 
            then T(s1, t1, s2, t2)
            else t3

     = if  (s1 + s2) = s3 
       then (b2 (if s1 = s2 
                 then (b2 t1 t2) 
                 else if s1 < s2 then t1 else t2)
                t3)
       else if (s1 + s2) < s3 
            then (if s1 = s2 
                 then (b2 t1 t2) 
                 else if s1 < s2 then t1 else t2)
            else t3

RHS' = T(s1, t1, s2, + s3, T(s2, t2, s3, t3))
     = if s1 = (s2, + s3)
       then (b2 t1 T(s2, t2, s3, t3))
       else if s1 < (s2, + s3)
            then t1 
            else T(s2, t2, s3, t3)
     = if s1 = (s2, + s3)
       then (b2 t1 (if s2 = s3 then (b2 t2 t3) else if s2 < s3 then t2 else t3))
       else if s1 < (s2, + s3)
            then t1 
            else if s2 = s3 then (b2 t2 t3) else if s2 < s3 then t2 else t3

So we want 

      if A1 
      then bT (if B1 then bT t1 t2 else if B2 then t1 else t2)  t3
      else if A2 
           then (if B1 then bT t1 t2 else if B2 then t1 else t2)
           else t3
     = if C1 
       then bT t1 (if D1 then bT t2 t3 else if D2 then t2 else t3)
       else if C2 
            then t1
             else if D1 then bT t2 t3 else if D2 then t2 else t3

Where             

        1                 2            
   ------------------------------------
A) (s1 + s2) = s3    (s1 + s2) < s3    
B) s1 = s2           s1 < s2           

C) s1 = (s2 + s3)    s1 < (s2 + s3)    
D) s2 = s3           s2 <  s3          

Using brel_bop_to_lt_left_total_order_split we 
generate  9 cases. 

   [(A1, !A2) | (!A1, A2) | (!A1, !A2)] *  [(B1, !B2) | (!B1, B2) | (!B1, !B2)]

This results in the following table. In each case the "needed" column 
shows what is requied to to make LHS' = RHS'. 


case                  needed             order             LHS' = RHS' = 
-----------------------------------------------------------------------------
1) A1 !A2  B1 !B2  => C1 D1              s1 = s2 = s3           t1 + t2 + t3 
2) A1 !A2 !B1 B2   => C1 !D1 !D2         s1 = s3 < s2           t1 + t3 
3) A1 !A2 !B1 !B2  => !C1 !C2 D1         s2 = s3 < s1           t2 + t3 
4) !A1 A2  B1 !B2  => C1 !D1 D2          s1 = s2 < s3           t1 + t2 
5) !A1 A2 !B1 B2   => !C1 C2             s1 < s2, s1 < s3       t1 
6) !A1 A2 !B1 !B2  => !C1 !C2 !D1 D2     s2 < s1, s2 < s3       t2 

7) !A1 !A2  B1 !B2 => !C1 !C2 !D1 !D2    s3 < s1 = s2           t3 
8) !A1 !A2 !B1 B2  => !C1 !C2 !D1 !D2    s3 < s1 < s2           t3 
9) !A1 !A2 !B1 !B2 => !C1 !C2 !D1 !D2    s3 < s2 < s1           t3 

Here are the forms of the properties that are best suited for 
rewriting easily obtain LHS' = RHS'. 

 A1 == r (b s1 s2) s3 = true
!A1 == r (b s1 s2) s3 = false 
 A2 == brel_bop_to_lt_left S r b (b s1 s2) s3 = true
!A2 == brel_bop_to_lt_left S r b (b s1 s2) s3 = false

 B1 == r s1 s2 = true
!B1 == r s1 s2 = false
 B2 == brel_bop_to_lt_left S r b s1 s2 = true
!B2 == brel_bop_to_lt_left S r b s1 s2 = false

 C1 == r s1 (b s2 s3) = true
!C1 == r s1 (b s2 s3) = false 
 C2 == brel_bop_to_lt_left S r b s1 (b s2 s3) = true
!C2 == brel_bop_to_lt_left S r b s1 (b s2 s3) = false 

 D1 == r s2 s3 = true
!D1 == r s2 s3 = false
 D2 == brel_bop_to_lt_left S r b s2 s3 = true
!D2 == brel_bop_to_lt_left S r b s2 s3 = false 

*) 

(* not used yet.  Should sym be DEFINED this way? *) 
Lemma brel_sym_eq : ∀ (S : Type) (r : brel S),  brel_symmetric S r → 
                     ∀ (s1 s2 : S), r s1 s2 = r s2 s1. 
Proof. intros S r symS s1 s2. 
       case_eq(r s1 s2); intro H. 
            rewrite (symS _ _ H). reflexivity. 
            rewrite (brel_symmetric_implies_dual _ _ symS _ _ H). reflexivity. 
Defined. 



(* 
1) A1 !A2  B1 !B2  => C1 D1              s1 = s2 = s3           t1 + t2 + t3 

   (s1 + s2) = s3 -> s1 = s2 ->  (s1 = (s2 + s3)) * (s2 = s3) 
2
*) 
Lemma lex_lemma_case_1 : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 s3 : S), 
          brel_reflexive S r → 
          brel_symmetric S r → 
          brel_transitive S r → 
          bop_congruence S r b → 
          bop_idempotent S r b → 
          (* A1 *) r (b s1 s2) s3 = true -> 
          (* B1 *) r s1 s2 = true -> 
             (* C1 *) (r s1 (b s2 s3) = true) * 
             (* D1 *) (r s2 s3 = true). 
Proof. intros S r b s1 s2 s3 refS symS transS congS idemS A1 B1. unfold bop_congruence in congS. 
       (* I : s2 + s2 = s2      *) assert (I := idemS s2). apply symS in I. 
       assert (D1 : r s2 s3 = true). 
       (* K : s2 + s2 = s1 + s2 *) assert (K := congS s1 s2 s2 s2 B1 (refS s2)). apply symS in K.
       (* L : s2 = s1 + s2      *) assert (L := transS _ _ _ I K).             
       (*     s2 = s3           *) apply (transS _ _ _ L A1). 

       assert (C1 : r s1 (b s2 s3) = true). 
       (* N : s2 + s2 = s2 + s3 *) assert (N := congS _ _ _ _ (refS s2) D1).     
       (* O : s1 = s2 + s2      *) assert (O := transS _ _ _ B1 I).             
       (*     s1 = s2 + s3      *) apply (transS _ _ _ O N).  
       split. 
          assumption. (* C1 *) 
          assumption. (* D1 *) 
Defined. 


(* 
2) A1 !A2 !B1 B2   => C1 !D1 !D2         s1 = s3 < s2           t1 + t3 

  
   (s1 + s2) = s3 -> -> s1 <> s2 -> s1 < s2 -> 
     (s1 = (s2 + s3)) * (s2 <> s3) * (s2 !< s3) 

*)

Lemma lex_lemma_case_2 : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 s3 : S), 
          brel_reflexive S r → 
          brel_symmetric S r → 
          brel_transitive S r → 
          bop_congruence S r b → 
          bop_commutative S r b → 
          bop_selective S r b → 
            (* A1  *) r (b s1 s2) s3 = true -> 
            (* !B1 *) r s1 s2 = false -> 
            (* B2  *) brel_llt S r b s1 s2 = true -> 
                 (* C1  *) (r s1 (b s2 s3) = true) * 
                 (* !D1 *) (r s2 s3 = false) * 
                 (* !D2  *) (brel_llt S r b s2 s3 = false). 
Proof. intros S r b s1 s2 s3 refS symS transS b_cong commS selS A1 notB1 B2. 
       destruct (brel_llt_true_elim S r b s1 s2 B2) as [A C]. 
       assert (C1 : r s1 (b s2 s3) = true). 
          assert(fact1 := transS _ _ _ A A1). 
          destruct (selS s2 s3) as [Q | Q]. 
             assert (fact2 := b_cong _ _ _ _ (refS s2) fact1). 
             assert (fact3 := commS s1 s2). 
             assert (fact4 := transS _ _ _ fact3 fact2). 
             apply (transS _ _ _ A fact4). 

             apply symS in Q. apply (transS _ _ _ fact1 Q). 

       split. split. 
       assumption. 

       assert (B := transS _ _ _ A A1). 
       assert (D := brel_transititivity_implies_dual S r transS _ _ _ B C). 
       apply (brel_symmetric_implies_dual S r symS) in D.
       assumption. 

       apply brel_llt_false_intro. left. 
       assert (fact := brel_transititivity_implies_dual _ _ transS _ _ _ C1 notB1). 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 



(* 
not(s1 < s2) -> s2 <= s1 
*) 
Lemma brel_llt_false_elim2 : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          brel_reflexive S r → 
          brel_transitive S r → 
          brel_symmetric S r → 
          brel_congruence S r r → 
          bop_commutative S r b → 
          bop_selective S r b → 
            ∀ (s1 s2 : S), 
                 brel_llt S r b s1 s2 = false -> brel_llte S r b s2 s1 = true. 
Proof. 
       intros S r b refS transS symS r_cong commS selS s1 s2 H. 
       assert (fact1 := commS s2 s1). 
       apply brel_llte_true_intro. 
       apply brel_llt_false_elim in H. 
       destruct H as [H | H]; destruct (selS s2 s1) as [J | J]. 
         apply symS. assumption. 
         apply symS in J. assert (fact2 := transS _ _ _ J fact1). 
            rewrite fact2 in H. discriminate. 
         apply symS. assumption. 
         apply symS in H. apply symS in J. apply (transS _ _ _ H J). 
Defined. 

(* 
(s1 < s2) -> s1 = (s1 + s2)  

Lemma brel_llt_to_glb : ∀ (S : Type) (r : brel S) (b : binary_op S), 
            ∀ (s1 s2 : S), 
                 brel_llt S r b s1 s2 = true -> r s1 (b s1 s2) = true. 
Proof. unfold brel_llt, brel_bop_to_lte_left.
       intros S r b s1 s2 H. apply andb_is_true_left in H.  destruct H as [H1 H2]. 
       assumption. 
Defined. 
*) 

(* 

3) A1 !A2 !B1 !B2  => !C1 !C2 D1         s2 = s3 < s1           t2 + t3 

 A1 : s1 + s2 = s3 
!A2 : s1 + s2 !< s3 
!B1 : s1 <> s2
!B2 : s1 !< s2 

!C1 : s1 <> (s2 + s3) 
!C2 : s1 !< (s2 + s3) 
 D1 : s2 = s3 

*) 
Lemma lex_lemma_case_3 : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          brel_reflexive S r → 
          brel_transitive S r → 
          brel_symmetric S r → 
          brel_congruence S r r → 
          bop_commutative S r b → 
          bop_selective S r b → 
          bop_congruence S r b → 
            ∀ (s1 s2 s3 : S), 
                 (* A1  *) r (b s1 s2) s3 = true -> 
                 (* !A2 *) brel_llt S r b (b s1 s2) s3 = false -> 
                 (* !B1 *) r s1 s2 = false -> 
                 (* !B2 *) brel_llt S r b s1 s2 = false -> 
                    (* !C1 *) (r s1 (b s2 s3) = false) * 
                    (* !C2 *) (brel_llt S r b s1 (b s2 s3) = false) * 
                    (* D1  *) (r s2 s3 = true). 
Proof. 
       intros S r b refS transS symS r_cong commS selS b_cong s1 s2 s3 A1 notA2 notB1 notB2. 
       assert (fact0 := bop_selective_implies_idempotent _ _ _ selS s2). 
       assert (fact1 := brel_llt_false_elim2 _ _ _ refS transS symS r_cong commS selS _ _ notB2). 
       assert (fact2 := commS s2 s1). 
       unfold brel_bop_to_lte_left in fact1. 
       assert (fact3 := transS _ _ _ fact1 fact2).
       assert(D1 := transS _ _ _ fact3 A1).        
       assert (fact4 := b_cong _ _ _ _ (refS s2) D1). apply symS in fact0. 
       assert (fact5 := transS _ _ _ fact0 fact4). 
       rewrite (brel_sym_eq _ _ symS) in notB1. 
       assert (notC1 := brel_transititivity_implies_dual _ _ transS _ _ _ fact5 notB1). 
       rewrite (brel_sym_eq _ _ symS) in notC1. 

       assert (notC2 : brel_llt S r b s1 (b s2 s3) = false). 
       apply brel_llt_false_intro. left. 
       assert (fact6 := b_cong _ _ _ _ (refS s1) fact5). 
       assert (fact7 := transS _ _ _ fact3 fact6). 
       assert (fact8 := brel_transititivity_implies_dual _ _ transS _ _ _ fact7 notB1).
       rewrite brel_sym_eq; auto. 
     
       split. split.  assumption. assumption. assumption. 
Defined. 



(* 

4) !A1 A2  B1 !B2  => C1 !D1 D2          s1 = s2 < s3           t1 + t2 
    
  (s1 + s2) <> s3 ->  (s1 + s2) < s3 ->   s1 = s2 
     ->  s1 = (s2 + s3) * (s2 <> s3) * s2 < s3 

   C1  : D2 ==> s2 = s2 + s3 ==> s1 = (s2 + s3)
   !D1 : D2 ==> s2 <> s3 
   D2  : s1 = s2 ==> (s2 + s2) < s3 ==> s2 < s3 

*) 
Lemma lex_lemma_case_4 : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          brel_reflexive S r → 
          brel_transitive S r → 
          brel_symmetric S r → 
          brel_congruence S r r → 
          bop_congruence S r b → 
          bop_selective S r b → 
           ∀ (s1 s2 s3 : S), 
             (* !A1 *) r (b s1 s2) s3 = false -> 
             (* A2  *) brel_llt S r b (b s1 s2) s3 = true -> 
             (* B1 *) r s1 s2 = true ->  
                 (* C1  *) (r s1 (b s2 s3) = true) * 
                 (* !D1 *) (r s2 s3 = false) * 
                 (* D2  *) (brel_llt S r b s2 s3 = true). 
Proof. intros S r b refS transS symS r_cong b_cong selS s1 s2 s3 notA1 A2 B1. 
       assert (idemS := bop_selective_implies_idempotent _ _ _ selS).
       assert (I := idemS s2). 
       assert (D2    : brel_llt S r b s2 s3 = true). 
          assert (A := b_cong _ _ _ _ B1 (refS s2)). 
          assert (B := transS _ _ _ A I). 
          rewrite (brel_llt_congruence S r r b r_cong b_cong _ _ _ _ B (refS s3)) in A2. 
          assumption. 
       destruct (brel_llt_true_elim S r b _ _ D2) as [A notD1].
       assert (C1    : r s1 (b s2 s3) = true). 
          rewrite (r_cong _ _ _ _ B1 (refS (b s2 s3))). 
          assumption. 
       rewrite C1, notD1, D2. auto. 
Defined. 



              
(*  

5) !A1 A2 !B1 B2   => !C1 C2             s1 < s2, s1 < s3       t1 

!A1 : (s1 + s2) <> s3
 A2 : (s1 + s2) < s3
!B1 : s1 <> s2
 B2 : s1 < s2


 C2 : B2, A2 
     -> s1 < s3
     -> s1 < (s2 + s3) brel_llt_compatible_right

!C1 : brel_llt_elim1 C2 
     -> s1 <> (s2 + s3) 


NOT USED: 
brel_llt_compatible_right : brel_bop_compatible_right S (brel_llt S r b) b. 

Definition brel_bop_compatible_right (S : Type) (r : brel S) (b : binary_op S) := 
   ∀ (s u v : S), r s u = true -> r s v = true -> r s (b u v) = true.

s1 < s2, s1 < s3 
*) 
Lemma lex_lemma_case_5 : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 s3 : S), 
          brel_congruence S r r → 
          bop_congruence S r b → 
          bop_associative S r b → 
          brel_reflexive S r → 
          brel_symmetric S r → 
          brel_transitive S r → 
          bop_commutative S r b → 
          bop_selective S r b → 
            (* !A1 *) r (b s1 s2) s3 = false ->        
            (* A2  *) brel_llt S r b (b s1 s2) s3 = true -> 
            (* !B1 *) r s1 s2 = false -> 
            (* B2  *) brel_llt S r b s1 s2 = true -> 
                     (* !C1 *) (r s1 (b s2 s3) = false) * 
                     (* C2  *) (brel_llt S r b s1 (b s2 s3) = true). 
Proof. intros S r b s1 s2 s3 r_cong b_cong assS refS symS transS commS selS notA1 A2 notB1 B2. 
       apply brel_llt_true_elim in A2. destruct A2 as [AL AR].
       apply brel_llt_true_elim in B2. destruct B2 as [BL BR].       
       assert(fact0 : r s1 (b s1 (b s2 s3)) = true). 
             assert(fact1 := transS _ _ _ BL AL). 
             assert(fact2 := assS s1 s2 s3). 
             apply (transS _ _ _ fact1 fact2). 
       assert(fact99 : r s1 (b s2 s3) = false). 
          destruct (selS s2 s3) as [Q | Q]. 
             apply (brel_symmetric_implies_dual _ _ symS) in notB1. apply symS in Q.      
             assert (fact1 := brel_transititivity_implies_dual _ _ transS _ _ _ Q notB1). 
             apply (brel_symmetric_implies_dual _ _ symS). assumption. 

             apply symS in BL.           
             assert (fact1 := brel_transititivity_implies_dual _ _ transS _ _ _ BL notA1).  
             apply (brel_symmetric_implies_dual _ _ symS) in fact1. apply symS in Q.      
             assert (fact2 := brel_transititivity_implies_dual _ _ transS _ _ _ Q fact1).  
             apply (brel_symmetric_implies_dual _ _ symS). assumption. 

       destruct (selS s2 s3) as [Q | Q]; split. 
          apply (brel_symmetric_implies_dual _ _ symS) in notB1. apply symS in Q.             
          assert (fact1 := brel_transititivity_implies_dual _ _ transS _ _ _ Q notB1).           
          apply (brel_symmetric_implies_dual _ _ symS). assumption. 

          apply brel_llt_true_intro; assumption. 

          apply symS in BL. 
          assert (fact1 := brel_transititivity_implies_dual _ _ transS _ _ _ BL notA1).           
          apply (brel_symmetric_implies_dual _ _ symS) in notB1. apply symS in Q.      
          apply (brel_symmetric_implies_dual _ _ symS) in fact1. 
          assert (fact2 := brel_transititivity_implies_dual _ _ transS _ _ _ Q fact1).           
          apply (brel_symmetric_implies_dual _ _ symS). assumption. 

          apply brel_llt_true_intro; assumption. 
Defined. 

(* 
6) !A1 !A2 !B1!B2  => !C1 !C2 !D1 D2     s2 < s1, s2 < s3       t2 

  (s1 + s2) <> s3 ->  (s1 + s2) < s3 -> s1 <> s2 -> s1 !< s2
    -> (s1 <> (s2 + s3)) * (s1 !< (s2 + s3)) * (s2 <> s3) * (s2 < s3) 
!C1 : 
C3  : 
!D1 : 
D2  : 
*)                
Lemma lex_lemma_case_6 : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          brel_reflexive S r → 
          brel_symmetric S r → 
          brel_transitive S r → 
          bop_congruence S r b → 
          bop_associative S r b → 
          bop_selective S r b → 
           ∀ (s1 s2 s3 : S), 
           (* !A1 *) r (b s1 s2) s3 = false -> 
           (* A2  *) brel_llt S r b (b s1 s2) s3 = true -> 
           (* !B1 *) r s1 s2 = false -> 
           (* !B2 *) brel_llt S r b s1 s2 = false -> 
               (* !C1 *) (r s1 (b s2 s3) = false) *
               (* !C2  *) (brel_llt S r b s1 (b s2 s3) = false) * 
               (* !D1 *) (r s2 s3 = false) *
               (* D2  *) (brel_llt S r b s2 s3 = true). 
Proof. intros S r b refS symS transS b_cong assS selS s1 s2 s3 notA1 A2 notB1 notB2.  
       apply brel_llt_false_elim in notB2. destruct notB2 as [notB2  | notB2].
          apply brel_llt_true_elim in A2. destruct A2 as [L R].
          assert (notD1 : r s2 s3 = false). 
             destruct (selS s1 s2) as [Q | Q]. 
                apply symS in Q. rewrite Q in notB2. discriminate.
                assert (fact1 := brel_transititivity_implies_dual _ _ transS _ _ _ Q notA1). 
                assumption.    
          assert (fact1 : r s2 (b s1 s2) = true). 
               destruct (selS s1 s2) as [Q | Q].  
                  apply symS in Q. rewrite Q in notB2. discriminate.
                  apply symS in Q. assumption. 
          assert (fact2 : r s2 (b (b s1 s2) s3) = true). 
              apply (transS _ _ _ fact1 L). 
          assert (fact3 := assS s1 s2 s3).
          assert (fact4 : r s2 (b s1 (b s2 s3)) = true). 
              apply (transS _ _ _ fact2 fact3). 

                        
          split. split. split.
             case_eq(r s1 (b s2 s3)); intro Q. 
                assert (fact5 : r s1 (b s1 (b s2 s3)) = true). 
                    assert (fact6 := bop_selective_implies_idempotent _ _ _ selS s1).
                    apply symS in fact6.
                    assert (fact7 := b_cong _ _ _ _ (refS s1) Q). 
                    apply (transS _ _ _ fact6 fact7).
                assert ( fact6 := transS _ _ _ fact2 fact3). 
                apply symS in fact6. 
                assert ( fact7 := transS _ _ _ fact5 fact6). 
                rewrite fact7 in notB1. discriminate. 

                reflexivity. 

             apply brel_llt_false_intro. left.
             apply (brel_symmetric_implies_dual _ _ symS) in notB2. 
             assert (fact5 := brel_transititivity_implies_dual _ _ transS _ _ _ L notB2).    
             assert (fact6 := assS s1 s2 s3).
             assert (fact7 := brel_transititivity_implies_dual _ _ transS _ _ _ fact6 fact5).
             apply (brel_symmetric_implies_dual _ _ symS). assumption. 

             assumption.    

             apply brel_llt_true_intro. 
                destruct (selS s2 s3) as [Q | Q]. 
                   apply symS. assumption. 
                   assert(fact5 : r (b s1 (b s2 s3)) (b s1 s3) = true). 
                      apply (b_cong _ _ _ _ (refS s1) Q). 
                   assert (fact6 := transS _ _ _ fact4 fact5). 
                   destruct (selS s1 s3) as [J | J].               
                       assert (fact7 := transS _ _ _ fact6 J). apply symS in fact7. 
                       rewrite fact7 in notB1. discriminate. 
                       assert (fact7 := transS _ _ _ fact6 J). 
                       rewrite fact7 in notD1. discriminate. 
                assumption.                 
          rewrite notB2 in notB1. discriminate.
Defined.  



(*  

7) !A1 !A2  B1 !B2 => !C1 !C2 !D1 !D2    s3 < s1 = s2           t3 


(s1 + s2) <> s3  -> (s1 + s2) !< s3  ->  s1 = s2 
  ->  (s1 <> s2 + s3) * (s1 !< (s2 + s3)) * (s2 <> s3) * (s2 !< s3) 

!C1 : 
C3  : !D1, D3 =>   s3 < s2 => s3 < s1 
!D1 : s1 = s2 ==> (s2 + s2) <> s3 => s2 <> s3 
D3  : s1 = s2 ==> (s2 + s2) !< s3 ==> s2 !< s3 

*) 
Lemma lex_lemma_case_7 : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 s3 : S), 
          brel_reflexive S r → 
          brel_symmetric S r  -> 
          brel_transitive S r → 
          brel_congruence S r r → 
          bop_congruence S r b → 
          bop_selective S r b → 
          (* !A1 *) r (b s1 s2) s3 = false -> 
          (* A3 *) brel_llt S r b (b s1 s2) s3 = false → 
          (* B1 *) r s1 s2 = true → 
               (* !C1 *) (r s1 (b s2 s3) = false) * 
               (* C3  *) (brel_llt S r b s1 (b s2 s3) = false) * 
               (* !D1 *) (r s2 s3 = false)  * 
               (* D3  *) (brel_llt S r b s2 s3 = false). 
Proof. intros S r b s1 s2 s3 refS symS transS r_cong b_cong selS notA1 A3 B1. 
       assert (idemS := bop_selective_implies_idempotent _ _ _ selS).

       assert (A := idemS s2).
       assert (B := b_cong _ _ _ _ B1 (refS s2)). 
       assert (C := transS _ _ _ B A). 
       assert (D3 : brel_llt S r b s2 s3  = false). 
          rewrite (brel_llt_congruence S r r b r_cong b_cong _ _ _ _ C (refS s3)) in A3. 
          assumption. 
       assert (notD1 : r s2 s3 = false).
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ C notA1). 
            assert (C3 : brel_llt S r b s1 (b s2 s3) = false). 
         destruct (selS s2 s3) as [D | D]. 
            rewrite (brel_llt_congruence S r r b r_cong b_cong _ _ _ _ B1 D).
            rewrite (brel_llt_irreflexive S r b refS). reflexivity. 

            rewrite (brel_llt_congruence S r r b r_cong b_cong _ _ _ _ B1 D).
            assumption.
       assert (notC1 : r s1 (b s2 s3) = false). 
         destruct (brel_llt_false_elim _ _ _ _ _ D3) as [D | D]. 
            rewrite(r_cong _ _ _ _ B1 (refS (b s2 s3))). assumption.
            rewrite D in notD1. discriminate. 

       split. split.  split. assumption. assumption. assumption. assumption. 
Defined. 


(* 

8) !A1 !A2 !B1 B2  => !C1 !C2 !D1 !D2    s3 < s1 < s2           t3 


Assume
!A1 : (s1 + s2) <> s3 
 A3 : (s1 + s2) !< s3 
!B1 : s1 <> s2    
 B2 : s1 < s2 

H1 : B2 -> s1 = (s1 + s2) 
H2 : s1 <> s3   (from H1, !A1) 
H3 : s1 !< s3   (H1, A3) 
H4 : s3 <= s1   (H3) 
H5 : s3 < s1    (H4, H2) 

Show 
!C1 : s1 <> s2 and s1 <> s3 
      -> (s1 <> (s2 + s3)
 C3 : (s1 + s2) !< s3 
         -> s3 <= (s1 + s2) 
         -> s3 = (s1 + s2) + s3
         -> s2 + s3 = s1 + s2 + s3 
         -> (s2 + s3) <= s1 
         -> s1 !< (s2 + s3)
!D1 : s2 = s3 
      -> s1 < s3 ****
      -> s2 <> s3   
 D3 : A3 
      ->  s3 <= (s1 + s2) 
      ->  s3 <= s2 
      -> s2 !<  s3

*) 
Lemma lex_lemma_case_8 : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 s3 : S), 
          brel_reflexive S r → 
          brel_symmetric S r → 
          brel_transitive S r → 
          brel_congruence S r r → 
          bop_congruence S r b → 
          bop_associative S r b → 
          bop_selective S r b → 
             (* !A1 *) r (b s1 s2) s3 = false -> 
             (* A3  *) brel_llt S r b (b s1 s2) s3 = false -> 
             (* !B1 *) r s1 s2 = false -> 
             (* B2  *) brel_llt S r b s1 s2 = true-> 
                 (* !C1 *) (r s1 (b s2 s3) = false) * 
                 (* !C2  *) (brel_llt S r b s1 (b s2 s3) = false) * 
                 (* !D1 *) (r s2 s3 = false) * 
                 (* !D2  *) (brel_llt S r b s2 s3 = false). 
Proof. intros S r b s1 s2 s3 refS symS transS r_cong b_cong assS selS notA1 A3 notB1 B2. 
       apply brel_llt_false_elim in A3. 
       apply brel_llt_true_elim in B2.  destruct B2 as [fact1 _]. apply symS in fact1. 
       assert (fact2 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 notA1). 
       assert (notC1 : r s1 (b s2 s3) = false). 
          destruct(selS s2 s3) as [Q | Q].
             apply symS in Q.  apply (brel_symmetric_implies_dual _ _ symS) in notB1.
             assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ Q notB1). 
             apply (brel_symmetric_implies_dual _ _ symS).  assumption. 

             apply symS in Q.  apply (brel_symmetric_implies_dual _ _ symS) in fact2.     
             assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ Q fact2).          
             apply (brel_symmetric_implies_dual _ _ symS).  assumption. 
       assert (notC2 : brel_llt S r b s1 (b s2 s3) = false). 
          apply brel_llt_false_intro. 
             destruct A3 as [A3 | A3]. 
                assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 A3). 
                assert (fact4 := assS s1 s2 s3). 
                apply (brel_symmetric_implies_dual _ _ symS) in fact3.
                assert (fact5 := brel_transititivity_implies_dual _ _ transS _ _ _ fact4 fact3). 
                left. apply (brel_symmetric_implies_dual _ _ symS). assumption. 

                apply symS in fact1. assert (fact3 := transS _ _ _ fact1 A3). 
                rewrite fact2 in fact3. discriminate. 

          assert (notD1 : r s2 s3 = false). 
              case_eq(r s2 s3); intro J; destruct A3 as [A3 | A3]. 

                 assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 A3). 
                 assert (fact4 := assS s1 s2 s3). 
                 apply (brel_symmetric_implies_dual _ _ symS) in fact3.
                 assert (fact5 := brel_transititivity_implies_dual _ _ transS _ _ _ fact4 fact3). 
                 assert (fact6 := bop_selective_implies_idempotent _ _ _ selS s2). 
                 assert (fact7 := b_cong _ _ _ _ (refS s2) J). apply symS in fact6. 
                 assert (fact8 := transS _ _ _ fact6 fact7). 
                 assert (fact9 := b_cong _ _ _ _ (refS s1) fact8). apply symS in fact1. 
                 assert (fact10 := transS _ _ _ fact1 fact9). apply symS in fact10. 
                 rewrite fact10 in fact5. discriminate.                  

                 rewrite A3 in notA1. discriminate.                  

                 reflexivity.                  
                 reflexivity. 

          assert(notD2 : brel_llt S r b s2 s3 = false). 
             apply brel_llt_false_intro. left. 
             assert (fact3 : r s3 (b s2 s3) = true). 
                case_eq(r s3 (b s2 s3)); intro J. 
                   reflexivity. 
                   destruct (selS s2 s3) as [H | H]. 
                      destruct A3 as [A3 | A3]. 
                         assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 A3). 
                         assert (fact4 := assS s1 s2 s3). 
                         apply (brel_symmetric_implies_dual _ _ symS) in fact3.
                         assert (fact5 := brel_transititivity_implies_dual _ _ transS _ _ _ fact4 fact3). 
                         assert (fact6 := bop_selective_implies_idempotent _ _ _ selS s2). 
                         assert (fact7 := b_cong _ _ _ _ (refS s1) H). 
                         assert (fact8 := brel_transititivity_implies_dual _ _ transS _ _ _ fact7 fact5). 
                         rewrite fact8 in fact1. discriminate.                  

                         rewrite A3 in notA1. discriminate.                  
                      apply symS in H. rewrite H in J. discriminate.                  
             apply (brel_symmetric_implies_dual _ _ symS) in notD1.
             assert (fact4 := brel_transititivity_implies_dual _ _ transS _ _ _ fact3 notD1). 
             apply (brel_symmetric_implies_dual _ _ symS). assumption.

      split. split. split. assumption. assumption. assumption. assumption. 
Defined. 


(* 

9) !A1 A3 B3 => !C1 C3 !D1 D3      s3 < s2 < s1           t3 

  ((s1 + s2) <> s3) -> (s1 + s2) !< s3 -> s1 !< s2 
    -> (s1 <> (s2 + s3)) * (s1 !< (s2 + s3)) * (s2 <> s3) * (s2 !< s3) 

F1 : A3 ==> s3 <= (s1 + s2) ==> s3 = s1 + s2 + s3 

!C1 : s1 = s2 + s3 * F1 ==> s3 = s1 =(A1)=> s3 <> s1  ****
C3  : F1 ==> s2 + s3 = s1 + s2 + s3 ==> s2 + s3 <= s1 ==> C3
!D1 : s2 = s3 * F1 ==> s3 = s1 + s2  *** !A1 *** 
D3  : B3 => s2 <= s1 ==> s2 = s2 + s1 =(F1)=> s3 = s2 + s3 ==> s3 <= s2 ==> D3 
*) 
Lemma lex_lemma_case_9 : ∀ (S : Type) (r : brel S) (b : binary_op S),
                 brel_reflexive S r → 
                 brel_symmetric S r -> 
                 brel_transitive S r -> 
                 bop_congruence S r b → 
                 bop_selective S r b -> 
                 bop_commutative S r b -> 
                 bop_associative S r b -> 
                 ∀  (s1 s2 s3 : S), 
                (* !A1 *) r (b s1 s2) s3 = false -> 
                (* !A2  *) brel_llt S r b (b s1 s2) s3 = false -> 
                (* !B1 *) r s1 s2 = false -> 
                (* !B2  *) brel_llt S r b s1 s2 = false -> 
                     (* !C1 *) (r s1 (b s2 s3) = false) *
                     (* C3  *) (brel_llt S r b s1 (b s2 s3) = false) *
                     (* !D1 *) (r s2 s3 = false) *
                     (* D3  *) (brel_llt S r b s2 s3 = false). 
Proof. intros S r b refS symS transS b_cong selS commS assS s1 s2 s3 notA1 notA2 notB1 notB2. 
       apply brel_llt_false_elim in notA2. 
       apply brel_llt_false_elim in notB2. 
       destruct notA2 as [H | H]; destruct notB2 as [K | K].
          destruct (selS s1 s2) as [J | J]. 
             apply symS in J. rewrite J in K. discriminate. 
             split. split. split. 
                 assert(fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ J notA1).
                 destruct (selS s2 s3) as [L | L].    
                    apply symS in L. 
                    apply (brel_symmetric_implies_dual _ _ symS) in notB1. 
                    assert(fact4 := brel_transititivity_implies_dual _ _ transS _ _ _ L notB1). 
                    apply (brel_symmetric_implies_dual _ _ symS) in fact4. assumption. 
                    case_eq(r s1 (b s2 s3)); intro Q.
                       assert (fact4 := transS _ _ _ Q L). 
                       assert (fact5 := b_cong _ _ _ _ fact4 (refS s2)). apply symS in J. 
                       assert (fact6 := transS _ _ _ J fact5).   
                       assert (fact7 := commS s3 s2).
                       assert (fact8 := transS _ _ _ fact6 fact7).   apply symS in Q. 
                       assert (fact9 := transS _ _ _ fact8 Q). apply symS in fact9. 
                       rewrite fact9 in notB1. assumption. 
                       reflexivity. 
                 apply brel_llt_false_intro. left.  
                    destruct (selS s2 s3) as [L | L]. 
                       assert(fact1 := b_cong _ _ _ _ (refS s1) L). 
                       apply symS in fact1. apply symS in J. 
                       assert(fact2 := transS _ _ _ J fact1). 
                       apply (brel_symmetric_implies_dual _ _ symS) in notB1. 
                       assert(fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact2 notB1).                        
                       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
                       



                 case_eq(r s1 (b s1 (b s2 s3))); intro Q. 
                    assert (fact1 := assS s1 s2 s3). apply symS in fact1. 
                    assert (fact2 := transS _ _ _ Q fact1). 
                    assert (fact3 : r (b (b s1 s2) s3) (b s2 s3)= true). 
                       apply (b_cong _ _ _ _ J (refS s3)). 
                    assert (fact4 := transS _ _ _ fact2 fact3). 
                    assert (fact5 := transS _ _ _ fact4 L). 
                    assert (fact6 : r (b s1 s2) (b s2 s3) = true). 
                       assert (fact7 := b_cong _ _ _ _ fact5 (refS s2)). 
                       assert (fact8 := commS s3 s2). 
                       assert (fact9 := transS _ _ _ fact7 fact8). assumption. 
                    apply symS in fact6. 
                    assert (fact7 := transS _ _ _ fact4 fact6). 
                    assert (fact8 := transS _ _ _ fact7 J). 
                    rewrite fact8 in notB1. assumption. 
                    reflexivity. 

                 apply(brel_transititivity_implies_dual _ _ transS _ _ _ J notA1). 
                 apply brel_llt_false_intro. left. 
                    assert(fact1 := brel_transititivity_implies_dual _ _ transS _ _ _ J H). 
                    assert(fact2 := b_cong _ _ _ _ J (refS s3)). 
                    apply (brel_symmetric_implies_dual _ _ symS) in fact1. 
                    assert(fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact2 fact1). 
                    apply (brel_symmetric_implies_dual _ _ symS). assumption. 
                
         rewrite K in notB1. discriminate.  
         rewrite H in notA1. discriminate.  
         rewrite K in notB1. discriminate.  
Defined. 

Lemma bop_llex_associative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
     brel_reflexive S rS → 
     brel_symmetric S rS → 
     brel_transitive S rS → 
     brel_congruence S rS rS → 

     bop_congruence S rS bS → 
     bop_commutative S rS bS → 
     bop_selective S rS bS → 
     bop_associative S rS bS → 

     bop_associative T rT bT → 
     brel_reflexive T rT → 

      bop_associative (S * T) (brel_product _ _ rS rT) (bop_llex _ _ rS bS bT). 
Proof. 
    intros S T rS rT bS bT refS symS transS r_cong b_cong commS selS assS assT refT [s1 t1] [s2 t2] [s3 t3].
    unfold brel_product, bop_llex. 
    assert (idemS := bop_selective_implies_idempotent _ _ _ selS).
    apply andb_is_true_right. split. 
       apply assS. 
       destruct (brel_llt_total_order_split S rS bS refS symS transS b_cong selS (bS s1 s2) s3) as [[[Aeq Alt] | [Aeq Alt]] | [Aeq Alt]]; 
       destruct (brel_llt_total_order_split S rS bS refS symS transS b_cong selS s1 s2)         as [[[Beq Blt] | [Beq Blt]] | [Beq Blt]]. 
          destruct (lex_lemma_case_1 S rS bS s1 s2 s3 refS symS transS b_cong idemS Aeq Beq) 
             as [E1 E2]. rewrite E1, E2, Aeq, Beq. apply assT. 
          destruct (lex_lemma_case_2 S rS bS s1 s2 s3 refS symS transS b_cong commS selS Aeq Beq Blt)
             as [[E1 E2] E3]. rewrite E1, E2, E3.  rewrite Aeq, Beq, Blt. apply refT. 
          destruct (lex_lemma_case_3 S rS bS refS transS symS r_cong commS selS b_cong s1 s2 s3 Aeq Alt Beq Blt) as [[E1 E2] E3]. 
              rewrite E1, E2, E3.  rewrite Aeq, Beq, Blt. apply refT. 
          destruct (lex_lemma_case_4 S rS bS refS transS symS r_cong b_cong selS s1 s2 s3 Aeq Alt Beq) as [[E1 E2] E3]. rewrite E1, E2, E3.  rewrite Aeq, Alt, Beq. apply refT. 
          destruct (lex_lemma_case_5 S rS bS s1 s2 s3 r_cong b_cong assS refS symS transS commS selS Aeq Alt Beq Blt) as [E1 E2]. rewrite E1, E2.  rewrite Aeq, Alt, Beq, Blt. apply refT. 
          destruct (lex_lemma_case_6 S rS bS refS symS transS b_cong assS selS s1 s2 s3 Aeq Alt Beq Blt) as [[[E1 E2] E3] E4]. rewrite E1, E2, E3, E4, Aeq, Alt, Beq, Blt. apply refT. 
          destruct (lex_lemma_case_7 S rS bS s1 s2 s3 refS symS transS r_cong b_cong selS Aeq Alt Beq) as [[[E1 E2] E3] E4]. rewrite E1, E2, E3, E4, Aeq, Alt. apply refT. 
          destruct (lex_lemma_case_8 S rS bS s1 s2 s3 refS symS transS r_cong b_cong assS selS Aeq Alt Beq Blt) as [[[E1 E2] E3] E4]. rewrite E1, E2, E3, E4, Aeq, Alt. apply refT. 
          destruct (lex_lemma_case_9 S rS bS refS symS transS b_cong selS commS assS s1 s2 s3 Aeq Alt Beq Blt) as [[[E1 E2] E3] E4]. rewrite E1, E2, E3, E4, Aeq, Alt. apply refT. 
Defined.  



Lemma brel_llt_true_elim_to_false : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
      brel_symmetric S r → 
      brel_transitive S r → 
      bop_commutative S r b → 
        brel_llt S r b s1 s2 = true -> brel_llt S r b s2 s1 = false. 
Proof. unfold brel_llt. unfold brel_conjunction, brel_dual, brel_llte. 
       intros S r b s1 s2 symS transS commS H. 
       apply andb_is_true_left in H. destruct H as [L R]. 
       case_eq(r s1 s2); intro J. 
          apply symS in J. rewrite J. rewrite andb_comm. simpl. reflexivity. 
          assert (fact1 := commS s1 s2). 
          assert (fact2 := transS _ _ _ L fact1). 
          assert (F : r s2 (b s2 s1) = false). 
             assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact2 J). 
             apply (brel_symmetric_implies_dual _ _ symS) in fact3. assumption. 
          rewrite F. simpl. reflexivity. 
Defined. 

(* 
   s1 <> s2 = f s1 
   t1 <> t2 = g t1 

   1) s1 < s2 :  (s1 ,t1) * (s2, t1) =  (s1 ,t1) * (s2, f t1) 
   2) s2 < s1 :  (s2 ,t1) * (s1, t1) =  (s2 ,t1) * (s1, f t1) 
   3) s2 = s1 : contradiction. 


   if s < f s 
   then ((s ,t), (f s, t), (f s, g t))
   else ((f s ,t), (s, t), (s, g t))

*) 

Lemma bop_llex_not_left_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_nontrivial T rT -> 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_congruence S rS bS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_left_cancellative (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT. 
       destruct (Pf s) as [Ls Rs]. destruct (Pg t) as [Lt Rt]. 
       assert (fact1 := brel_llt_total_order_split S rS bS refS symS transS congS selS s (f s)). 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       exists ((s, t), ((f s, t), (f s, g t))); simpl. 
          rewrite (refS (bS s (f s))). rewrite eq, lt. 
          rewrite (refS (f s)). rewrite (refT t). rewrite Lt. auto. 
       exists ((f s, t), ((s, t), (s, g t))); simpl. 
          rewrite (refS (bS (f s) s)). rewrite Rs. 
          rewrite (refS s). rewrite Lt. simpl. 
          apply brel_llt_false_elim in lt. 
          unfold brel_llt, brel_conjunction, brel_dual, brel_llte.
          destruct lt as [lt | lt]. 
             rewrite Rs. 
             assert (fact2 := selS s (f s)). 
             destruct fact2 as [J | K]. 
                apply symS in J. rewrite J in lt. discriminate. 
                apply symS in K. 
                assert (fact3 := commS s (f s)). 
                assert (fact4 := transS _ _ _ K fact3). 
                rewrite fact4. simpl. rewrite (refT t). auto. 
       rewrite lt in eq. discriminate.        
Defined. 


Lemma bop_llex_not_left_cancellative_v2 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_nontrivial T rT -> 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_congruence S rS bS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_left_cancellative (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT. 
       exists (cef_bop_llex_not_cancellative S T rS bS s f t g). 
       destruct (Pf s) as [Ls Rs]. destruct (Pg t) as [Lt Rt]. 
       assert (fact1 := brel_llt_total_order_split S rS bS refS symS transS congS selS s (f s)). 
       unfold cef_bop_llex_not_cancellative. 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt. simpl. 
          rewrite (refS (bS s (f s))). rewrite eq, lt. 
          rewrite (refS (f s)). rewrite (refT t). rewrite Lt. auto. 
       rewrite lt. simpl. 
          rewrite (refS (bS (f s) s)). rewrite Rs. 
          rewrite (refS s). rewrite Lt. simpl. 
          apply brel_llt_false_elim in lt. 
          unfold brel_llt, brel_conjunction, brel_dual, brel_llte.
          destruct lt as [lt | lt]. 
             rewrite Rs. 
             assert (fact2 := selS s (f s)). 
             destruct fact2 as [J | K]. 
                apply symS in J. rewrite J in lt. discriminate. 
                apply symS in K. 
                assert (fact3 := commS s (f s)). 
                assert (fact4 := transS _ _ _ K fact3). 
                rewrite fact4. simpl. rewrite (refT t). auto. 
       rewrite lt in eq. discriminate.        
Defined. 


Lemma bop_llex_not_left_cancellative_projT1 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T)
     (ntS : brel_nontrivial S rS)
     (ntT : brel_nontrivial T rT)
     (refS : brel_reflexive S rS)
     (symS : brel_symmetric S rS)
     (trnS : brel_transitive S rS)
     (conS : bop_congruence S rS bS)
     (selS : bop_selective S rS bS)
     (comS : bop_commutative S rS bS)
     (refT : brel_reflexive T rT), 
         projT1(bop_llex_not_left_cancellative_v2 S T rS rT bS bT 
                ntS ntT refS symS trnS conS selS comS refT)
         = cef_bop_llex_not_cancellative S T rS bS 
            (projT1 (brel_nontrivial_witness S rS ntS)) 
            (projT1 (brel_nontrivial_negate S rS ntS)) 
            (projT1 (brel_nontrivial_witness T rT ntT)) 
            (projT1 (brel_nontrivial_negate T rT ntT)). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS trnS conS selS comS refT. 
   simpl. reflexivity. 
Defined. 


Lemma bop_llex_not_right_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_nontrivial T rT -> 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_congruence S rS bS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_right_cancellative (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT. 
       exists (cef_bop_llex_not_cancellative S T rS bS s f t g). 
       destruct (Pf s) as [Ls Rs]. destruct (Pg t) as [Lt Rt]. 
       assert (fact1 := brel_llt_total_order_split S rS bS refS symS transS congS selS s (f s)). 
       unfold cef_bop_llex_not_cancellative. 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt. simpl. 
          rewrite (refS (bS (f s) s)). rewrite (refS (f s)). rewrite Lt, Rs. 
          apply brel_llt_true_elim_to_false in lt; auto. rewrite lt; auto. 
       rewrite lt. simpl. 
          rewrite (refS (bS s (f s))). rewrite Ls. 
          rewrite (refS s). rewrite lt, Lt. simpl. rewrite (refT t); auto. 
Defined. 



(* 
   s1 <> s2 = f s1 
   t1 <> t2 = g t1 

   1) s1 < s2 :  (s2 ,t1) * (s1, t1) <>  (s2 ,t1) * (s1, g t1) 
   2) s2 < s1 :  (s1 ,t1) * (s2, t1) <>  (s1 ,t1) * (s2, g t1) 
   3) s2 = s1 : contradiction. 

*) 
Lemma bop_llex_not_left_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_nontrivial T rT -> 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_congruence S rS bS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_left_constant (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT. 
       exists (cef_bop_llex_not_constant S T rS bS s f t g). 
       unfold cef_bop_llex_not_constant. 
       destruct (Pf s) as [Ls Rs]. destruct (Pg t) as [Lt Rt]. 
       assert (fact1 := brel_llt_total_order_split S rS bS refS symS transS congS selS s (f s)). 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt; simpl. 
          rewrite (refS (bS (f s) s)). rewrite Rs. 
          apply brel_llt_true_elim_to_false in lt; auto. rewrite lt, Lt. auto. 
       rewrite lt; simpl. 
          rewrite (refS (bS s (f s))). rewrite Ls. rewrite lt, Lt. auto. 
Defined. 
   



Lemma bop_llex_not_right_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_nontrivial T rT -> 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_congruence S rS bS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_right_constant (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS symS transS congS selS commS refT. 
       exists (cef_bop_llex_not_constant S T rS bS s f t g). 
       unfold cef_bop_llex_not_constant. 
       destruct (Pf s) as [Ls Rs]. destruct (Pg t) as [Lt Rt]. 
       assert (fact1 := brel_llt_total_order_split S rS bS refS symS transS congS selS s (f s)). 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt; simpl. 
          rewrite (refS (bS s (f s))). rewrite Ls. rewrite lt, Lt. auto. 
       rewrite lt; simpl. 
          rewrite (refS (bS (f s) s)). rewrite Rs. 
          apply brel_llt_false_elim in lt; auto. 
          destruct lt as [lt | lt].
             unfold brel_llt, brel_conjunction, brel_llte, brel_dual. rewrite Rs. 
             assert (fact1 : rS (f s) (bS (f s) s) = true). 
                destruct (selS s (f s)) as [fact2 | fact2].
                   apply symS in fact2.  rewrite fact2 in lt. discriminate. 
                   assert (fact3 := commS s (f s)). apply symS in fact2. 
                   apply (transS _ _ _ fact2 fact3). 
             rewrite fact1; auto.          
       rewrite eq in lt. discriminate. 
Defined. 

Lemma bop_llex_not_anti_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_witness T rT -> 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_anti_left (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [t Pt] symS transS selS commS refT. 
       exists (cef_bop_llex_not_anti_left S T rS bS s f t). 
       unfold cef_bop_llex_not_anti_left. 
       destruct (Pf s) as [Ls Rs]. 
       unfold bop_not_anti_left, brel_product, bop_llex. 
       unfold brel_llt. unfold brel_conjunction, brel_llte, brel_dual. 
       assert (fact1 := commS s (f s)). 
       assert (H := selS s (f s)). 
       destruct H as [H | H]. 
          rewrite H, Ls.  simpl. apply symS in H. rewrite H. simpl. apply refT. 
          assert (fact2 : rS (bS s (f s)) s = false). 
             apply symS in H. 
             assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ H Rs).              
             rewrite fact3. reflexivity. 
          rewrite fact2. apply symS in H. 
          assert (fact3 := transS _ _ _ H fact1). rewrite fact3, Rs. simpl. apply refT. 
Defined. 


Lemma bop_llex_not_anti_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS -> 
      brel_witness T rT -> 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_selective S rS bS → 
      bop_commutative S rS bS → 
      brel_reflexive T rT → 
         bop_not_anti_right (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT). 
Proof. 
   intros S T rS rT bS bT [[s Ps] [f Pf]] [t Pt] symS transS selS commS refT. 
       exists (cef_bop_llex_not_anti_right S T rS bS s f t). 
       unfold cef_bop_llex_not_anti_right. 
       destruct (Pf s) as [Ls Rs]. 
       unfold bop_not_anti_right, brel_product, bop_llex. 
       unfold brel_llt. unfold brel_conjunction, brel_llte, brel_dual. 
       assert (fact1 := commS s (f s)). 
       assert (H := selS s (f s)). 
       destruct H as [H | H]. 
          rewrite H. apply symS in H. 
          assert (fact2 := transS _ _ _ H fact1). 
          assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ fact2 Ls). 
          apply (brel_symmetric_implies_dual _ _ symS) in fact3. 
          rewrite Rs, fact2, fact3. simpl. apply refT. 

          assert (fact2 : rS (bS s (f s)) s = false).
             apply symS in H. 
             assert (fact3 := brel_transititivity_implies_dual _ _ transS _ _ _ H Rs).              
             rewrite fact3. reflexivity. 
          rewrite fact2, Ls.  
          apply symS in H. rewrite H. simpl. 
          case_eq(rS s (bS s (f s))); intro J. 
             simpl. apply refT. 
             simpl. apply refT. 
Defined. 


(* projections *) 

Lemma bop_llex_is_id_left : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_id (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT) (s, t))
       ->  bop_is_id S rS bS s.  
Proof. intros S T rS rT bS bT s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_llex_is_id_right : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (refS : brel_reflexive S rS) 
     (s : S )
     (t : T ),         
     (bop_is_id (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT) (s, t))
       ->  bop_is_id T rT bT t.  
Proof. intros S T rS rT bS bT refS s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite (refS s) in RL. rewrite (refS s) in RR. 
       rewrite RL, RR. auto.        
Defined.                         


Lemma bop_llex_is_ann_left : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_ann (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT) (s, t))
       ->  bop_is_ann S rS bS s.  
Proof. intros S T rS rT bS bT s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_llex_is_ann_right : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (refS : brel_reflexive S rS) 
     (s : S )
     (t : T ),         
     (bop_is_ann (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT) (s, t))
       ->  bop_is_ann T rT bT t.  
Proof. intros S T rS rT bS bT refS s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite (refS s) in RL. rewrite (refS s) in RR.        
       rewrite RL, RR. auto. 
Defined.                         



