Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts. 

Section RightSum.

  Variable S T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable bS : binary_op S.
  Variable bT: binary_op T.    

  Variable refS : brel_reflexive S rS.  
  Variable symS : brel_symmetric S rS.  
  Variable tranS : brel_transitive S rS.

  Variable refT : brel_reflexive T rT.  
  Variable symT : brel_symmetric T rT.  
  Variable tranT : brel_transitive T rT.
  
  Variable congS : bop_congruence S rS bS.
  Variable assS : bop_associative S rS bS.

  Variable congT : bop_congruence T rT bT.  
  Variable assT : bop_associative T rT bT. 

Lemma bop_right_sum_congruence : 
      bop_congruence (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof.  intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl.
   apply congS. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. assumption. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. assumption. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   apply congT. 
Qed. 

Lemma bop_right_sum_associative : 
      bop_associative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl.
       apply assS. apply refT. apply refT. apply refT. apply refT. apply refT. apply refT. apply assT. 
Qed. 

Lemma bop_right_sum_idempotent : 
      bop_idempotent S rS bS → 
      bop_idempotent T rT bT → 
      bop_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros L R [s | t]; simpl. apply L. apply R. Qed. 

Lemma bop_right_sum_not_idempotent_left : 
      bop_not_idempotent S rS bS → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [s P]. exists (inl _ s). simpl. exact P. Defined. 

Lemma bop_right_sum_not_idempotent_right : 
      bop_not_idempotent T rT bT → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [t P]. exists (inr _ t). simpl. exact P. Defined. 

Lemma bop_right_sum_not_idempotent : 
      (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → 
      bop_not_idempotent (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [L | R]. apply (bop_right_sum_not_idempotent_left L). apply (bop_right_sum_not_idempotent_right R). Defined. 


Lemma bop_right_sum_commutative : 
      bop_commutative S rS bS → 
      bop_commutative T rT bT → 
      bop_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. apply refT. apply refT. apply R. Defined. 

Lemma bop_right_sum_not_commutative_left : 
      bop_not_commutative S rS bS → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [ [s t] P]. exists (inl _ s, inl _ t). simpl. exact P. Defined. 

Lemma bop_right_sum_not_commutative_right : 
      bop_not_commutative T rT bT → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t). simpl. exact P. Defined. 

Lemma bop_right_sum_not_commutative : 
      (bop_not_commutative S rS bS) + (bop_not_commutative T rT bT) → 
      bop_not_commutative (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [L | R]. apply (bop_right_sum_not_commutative_left L). apply (bop_right_sum_not_commutative_right R). Defined. 

Lemma bop_right_sum_selective : 
      bop_selective S rS bS → 
      bop_selective T rT bT → 
      bop_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. right. apply refT. left. apply refT. apply R. Defined. 

Lemma bop_right_sum_not_selective_left : 
      bop_not_selective S rS bS → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof.  intros [ [s1 s2] P]. exists (inl _ s1, inl _ s2). simpl. exact P. Defined. 

Lemma bop_right_sum_not_selective_right : 
      bop_not_selective T rT bT → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [ [t1 t2] P]. exists (inr _ t1, inr _ t2). simpl. exact P. Defined. 

Lemma bop_right_sum_not_selective : 
      (bop_not_selective S rS bS) + (bop_not_selective T rT bT) → 
      bop_not_selective (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [L | R]. apply (bop_right_sum_not_selective_left L). apply (bop_right_sum_not_selective_right R). Defined. 

Lemma bop_right_sum_not_is_left : 
      brel_witness S rS ->   brel_witness T rT ->  
      bop_not_is_left (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [s _] [t _]. exists (inl _ s, inr _ t). simpl. reflexivity. Defined. 

Lemma bop_right_sum_not_is_right : 
      brel_witness S rS ->   brel_witness T rT ->  
      bop_not_is_right (S + T) (brel_sum _ _ rS rT) (bop_right_sum _ _ bS bT). 
Proof. intros [s _] [t _]. exists (inr _ t, inl _ s). simpl. reflexivity. Defined. 

Lemma bop_right_sum_exists_id : 
         (bop_exists_id S rS bS) -> bop_exists_id (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. intros [iS pS]. exists (inl _ iS). intros [s | t]; compute. apply (pS s). rewrite (refT t); auto. Defined. 


Lemma bop_right_sum_id_is_inl : ∀ i : S + T, (bop_is_id _ (brel_sum S T rS rT) (bop_right_sum S T bS bT) i) ->
                                        ∀ idS : S, bop_is_id _ rS bS idS -> brel_sum _ _ rS rT i (inl idS) = true.
Proof. intros [s | t] P idS Q; compute. 
       assert (C : bop_is_id _ rS bS s). intro s2. assert (F := P (inl s2)). compute in F. exact F.
       apply (bop_is_id_equal _ rS symS tranS bS s idS C Q).
       assert (F := P (inl idS)). compute in F. destruct F as [F _]. discriminate F.       
Qed.        

Lemma bop_right_sum_simplify_id : ∀ s : S, 
    bop_is_id (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT) (inl s) -> bop_is_id S rS bS s.
Proof. intros s H. intro s'. apply (H (inl s')). Qed .   

Lemma bop_right_sum_extract_id (s' : S) : ∀ i : S + T, 
    bop_is_id (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT) i ->
       {s : S & (bop_is_id S rS bS s) * (brel_sum S T rS rT i (inl s) = true) }.
Proof. intros [s1 | t1] H; simpl.
       exists s1. split. apply bop_right_sum_simplify_id. exact H. apply refS.       
       assert (F := H (inl s')). compute in F. destruct F as [F _]. discriminate F. 
Qed.        

Lemma bop_right_sum_not_exists_id (wS : S)  : 
         (bop_not_exists_id S rS bS) -> 
           bop_not_exists_id (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. intros pS [s | t].
          destruct (pS s) as [x D]. exists (inl _ x). compute. exact D. 
          exists (inl _ wS). compute. auto. 
Defined. 

Lemma bop_right_sum_exists_ann : 
         (bop_exists_ann T rT bT) -> 
           bop_exists_ann (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. intros [annT pT]. exists (inr _ annT). intros [s | t]; compute. rewrite (refT annT); auto. apply (pT t). Defined. 

Lemma bop_right_sum_ann_is_inr : ∀ i : S + T, (bop_is_ann _ (brel_sum S T rS rT) (bop_right_sum S T bS bT) i) ->
                                        ∀ annT : T, bop_is_ann _ rT bT annT -> brel_sum _ _ rS rT i (inr annT) = true.
Proof. intros [s | t] P annT Q; compute. 
       assert (F := P (inr annT)). compute in F. destruct F as [F _]. discriminate F. 
       assert (C : bop_is_ann _ rT bT t). intro t2. assert (F := P (inr t2)). compute in F. exact F.
          apply (bop_is_ann_equal _ rT symT tranT bT t annT C Q). 
Qed.

Lemma bop_right_sum_simplify_ann : ∀ t : T, 
    bop_is_ann (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT) (inr t) -> bop_is_ann T rT bT t.
Proof. intros t H. intro t'. apply (H (inr t')). Qed .   

Lemma bop_right_sum_extract_ann (t' : T) : ∀ i : S + T, 
    bop_is_ann (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT) i ->
       {t : T & (bop_is_ann T rT bT t) * (brel_sum S T rS rT i (inr t) = true) }.
Proof. intros [s1 | t1] H; simpl.
       assert (F := H (inr t')). compute in F. destruct F as [F _]. discriminate F. 
       exists t1. split. apply bop_right_sum_simplify_ann. exact H. apply refT.
Qed.        



Lemma bop_right_sum_not_exists_ann (witness : T) : 
         (bop_not_exists_ann T rT bT) -> 
           bop_not_exists_ann (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT).
Proof. intros pT [s | t].
       exists (inr _ witness). compute; auto.  
       destruct (pT t) as [x D].  exists (inr _ x). compute. exact D. 
Defined. 

Lemma bop_right_sum_not_left_cancellative : 
      brel_witness T rT -> 
      brel_nontrivial S rS -> 
      bop_not_left_cancellative (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros [t Pt] [[s Ps] [f Pf]].
       destruct (Pf s) as [L _].
       exists ((inr _ t), ((inl s), (inl (f s)))). simpl. split. apply refT. exact L. 
Defined. 

Lemma bop_right_sum_not_right_cancellative : 
      brel_witness T rT -> 
      brel_nontrivial S rS -> 
      bop_not_right_cancellative (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros [t Pt] [[s Ps] [f Pf]]. 
       destruct (Pf s) as [L _]. 
       exists ((inr _ t), ((inl s), (inl (f s)))). simpl.  split. apply refT. exact L. 
Defined. 

Lemma bop_right_sum_not_left_constant : 
      brel_witness S rS -> 
      brel_nontrivial T rT -> 
      bop_not_left_constant (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros [s Ps] [[t Pt] [f Pf]]. 
       destruct (Pf t) as [L _]. 
       exists (inl s, (inr t, inr (f t))). simpl.  exact L. 
Defined. 

Lemma bop_right_sum_not_right_constant : 
      brel_witness S rS -> 
      brel_nontrivial T rT -> 
      bop_not_right_constant (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros [s Ps] [[t Pt] [f Pf]]. 
       destruct (Pf t) as [L _]. 
       exists (inl s, (inr t, inr (f t))). simpl.  exact L. 
Defined. 


Lemma bop_right_sum_not_anti_left : 
      brel_witness S rS -> 
      brel_witness T rT -> 
      bop_not_anti_left (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros [s _] [t Pt]. exists (inr t, inl s); simpl. exact Pt. Defined. 

Lemma bop_right_sum_not_anti_right : 
      brel_witness S rS -> 
      brel_witness T rT -> 
      bop_not_anti_right (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT). 
Proof. intros [s _] [t Pt]. exists (inr t, inl s); simpl. exact Pt. Defined. 

End RightSum. 