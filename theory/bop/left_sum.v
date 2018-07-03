Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties.

Section LeftSum.

  Variable S T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable bS : binary_op S.
  Variable bT: binary_op T.    

  Variable wS : S.
  Variable f : S -> S.                
  Variable Pf : brel_not_trivial S rS f. 

  Variable refS : brel_reflexive S rS.
  Variable symS : brel_symmetric S rS.  
  Variable tranS : brel_transitive S rS.

  Variable wT : T.
  Variable g : T -> T.                
  Variable Pg : brel_not_trivial T rT g. 
  
  Variable refT : brel_reflexive T rT.
  Variable symT : brel_symmetric T rT.  
  Variable tranT : brel_transitive T rT.
  
  Variable congS : bop_congruence S rS bS.
  Variable assS : bop_associative S rS bS.

  Variable congT : bop_congruence T rT bT.  
  Variable assT : bop_associative T rT bT. 

  Notation "a <+> b"  := (brel_sum a b)                (at level 15).
  Notation "a [+] b"  := (bop_left_sum a b)            (at level 15).  
  Notation "a == b"   := (brel_sum rS rT a b = true)  (at level 15).  
  
Lemma bop_left_sum_congruence : bop_congruence (S + T) (rS <+> rT) (bS [+] bT). 
Proof. 
   unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl.
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


Lemma bop_left_sum_associative : bop_associative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl.
      apply assS. apply refS. apply refS. apply refS. apply refS. apply refS. apply refS. apply assT. 
Qed. 

Lemma bop_left_sum_idempotent : bop_idempotent S rS bS → bop_idempotent T rT bT → bop_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R d.  destruct d; simpl. apply L. apply R. Qed. 

Lemma bop_left_sum_not_idempotent_left : bop_not_idempotent S rS bS → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [s P]. exists (inl _ s). simpl. assumption. Defined. 

Lemma bop_left_sum_not_idempotent_right : bop_not_idempotent T rT bT → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [t P]. exists (inr _ t). simpl. assumption. Defined. 

Lemma bop_left_sum_idempotent_comp : 
      (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R].  apply (bop_left_sum_not_idempotent_left L). apply (bop_left_sum_not_idempotent_right R). Defined. 

Lemma bop_left_sum_commutative : 
      bop_commutative S rS bS → bop_commutative T rT bT → bop_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. apply refS. apply refS. apply R. Qed. 

Lemma bop_left_sum_not_commutative_left : bop_not_commutative S rS bS → bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [s t] P]. exists (inl _ s, inl _ t). simpl. exact P. Defined. 

Lemma bop_left_sum_not_commutative_right : bop_not_commutative T rT bT → bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t). simpl. exact P. Defined. 

Lemma bop_left_sum_not_commutative : (bop_not_commutative S rS bS) + (bop_not_commutative T rT bT) → 
          bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_left_sum_not_commutative_left L). apply (bop_left_sum_not_commutative_right R). Defined. 

Lemma bop_left_sum_selective : bop_selective S rS bS → bop_selective T rT bT → bop_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. left. apply refS. right. apply refS. apply R. Defined. 

Lemma bop_left_sum_not_selective_left : bop_not_selective S rS bS → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof.  intros [ [s1 s2] P]. exists (inl _ s1, inl _ s2). simpl. exact P. Defined. 

Lemma bop_left_sum_not_selective_right : bop_not_selective T rT bT → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [t1 t2] P]. exists (inr _ t1, inr _ t2). simpl. exact P. Defined. 

Lemma bop_left_sum_not_selective : 
      (bop_not_selective S rS bS) + (bop_not_selective T rT bT) → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_left_sum_not_selective_left L). apply (bop_left_sum_not_selective_right R). Defined. 

Lemma bop_left_sum_not_is_left (s : S) (t : T) : bop_not_is_left (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inr _ t, inl _ s). simpl. reflexivity. Defined. 

Lemma bop_left_sum_not_is_right (s : S) (t : T) : bop_not_is_right (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl _ s, inr _ t). simpl. reflexivity. Defined. 


Lemma bop_left_sum_is_id : ∀ i: T, bop_is_id T rT bT i -> bop_is_id (S + T) (rS <+> rT) (bS [+] bT) (inr _ i).
Proof. intros i pT [s | t]; compute. rewrite (refS s). split; reflexivity. apply (pT t). Defined. 

Lemma bop_left_sum_exists_id : (bop_exists_id T rT bT) -> bop_exists_id (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros [i pT]. exists (inr _ i). apply bop_left_sum_is_id; auto. Defined. 

Lemma bop_left_sum_id_is_inr : ∀ i : S + T, (bop_is_id _ (rS <+> rT) (bS [+] bT) i) ->
                                            ∀ idT : T, bop_is_id _ rT bT idT -> i == (inr idT).
Proof. intros [s | t] P idT Q.
       assert (F := P (inr idT)). compute in F. destruct F as [F _]. discriminate F.
       compute. assert (C : bop_is_id _ rT bT t). intro t2. assert (F := P (inr t2)). compute in F. exact F.
       apply (bop_is_id_equal _ rT symT tranT bT t idT C Q). 
Qed.

Lemma bop_left_sum_simplify_id : ∀ t : T, 
    bop_is_id (S + T) (rS <+> rT) (bS [+] bT) (inr t) -> bop_is_id T rT bT t.
Proof. intros t H. intro t'. apply (H (inr t')). Qed .   

Lemma bop_left_sum_extract_id (t' : T) : ∀ i : S + T, 
    bop_is_id (S + T) (rS <+> rT) (bS [+] bT) i ->
       {t : T & (bop_is_id T rT bT t) * (i == (inr t)) }.
Proof. intros [s1 | t1] H; simpl.
       assert (F := H (inr t')). compute in F. destruct F as [F _]. discriminate F. 
       exists t1. split. apply bop_left_sum_simplify_id. exact H. apply refT.
Qed.        

Lemma bop_left_sum_not_exists_id : (bop_not_exists_id T rT bT) -> bop_not_exists_id (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros pT [s | t]. exists (inr _ wT). compute. auto. destruct (pT t) as [x D]. exists (inr _ x). compute. exact D. Defined. 


Lemma bop_left_sum_is_ann : ∀ a : S, bop_is_ann S rS bS a -> bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) (inl _ a).
Proof. intros a pS [s | t]; compute. apply (pS s). rewrite (refS a). split; reflexivity. Defined. 

Lemma bop_left_sum_exists_ann : (bop_exists_ann S rS bS) -> bop_exists_ann (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros [a pS]. exists (inl _ a). apply bop_left_sum_is_ann; auto. Defined. 

Lemma bop_left_sum_ann_is_inl : ∀ i : S + T, (bop_is_ann _ (rS <+> rT) (bS [+] bT) i) ->
                                        ∀ annS : S, bop_is_ann _ rS bS annS -> i == (inl annS).
Proof. intros [s | t] P annS Q; compute. 
       assert (C : bop_is_ann _ rS bS s). intro s2. assert (F := P (inl s2)). compute in F. exact F.
       apply (bop_is_ann_equal _ rS symS tranS bS s annS C Q).
       assert (F := P (inl annS)). compute in F. destruct F as [F _]. discriminate F.       
Qed.

Lemma bop_left_sum_simplify_ann : ∀ s : S, 
    bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) (inl s) -> bop_is_ann S rS bS s.
Proof. intros s H. intro s'. apply (H (inl s')). Qed .

Lemma bop_left_sum_extract_ann (s' : S) : ∀ i : S + T, 
    bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) i ->
       {s : S & (bop_is_ann S rS bS s) * (brel_sum rS rT i (inl s) = true) }.
Proof. intros [s1 | t1] H; simpl.
       exists s1. split. apply bop_left_sum_simplify_ann. exact H. apply refS.       
       assert (F := H (inl s')). compute in F. destruct F as [F _]. discriminate F. 
Qed.        

Lemma bop_left_sum_not_exists_ann : (bop_not_exists_ann S rS bS) -> bop_not_exists_ann (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros pS [s | t]. 
       destruct (pS s) as [x D].  exists (inl _ x). compute. exact D. 
       exists (inl _ wS). compute; auto.  
Defined. 

Lemma bop_left_sum_not_left_cancellative : bop_not_left_cancellative (S + T) (rS <+> rT) (bS [+] bT). 
Proof.  exists ((inl _ wS), ((inr wT), (inr (g wT)))). simpl. split. apply (refS wS).
        destruct (Pg wT) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_right_cancellative : bop_not_right_cancellative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists ((inl _ wS), ((inr wT), (inr (g wT)))). simpl.  split. apply (refS wS).
        destruct (Pg wT) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_left_constant : bop_not_left_constant (S + T) (rS <+> rT) (bS [+] bT). 
Proof.   exists (inr wT, (inl wS, inl (f wS))). simpl.  destruct (Pf wS) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_right_constant : bop_not_right_constant (S + T) (rS <+> rT) (bS [+] bT). 
Proof.   exists (inr wT, (inl wS, inl (f wS))). simpl. destruct (Pf wS) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_anti_left : bop_not_anti_left (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl wS, inr wT); simpl. apply refS. Defined. 

Lemma bop_left_sum_not_anti_right : bop_not_anti_right (S + T) (rS <+> rT) (bS [+] bT).
Proof. exists (inl wS, inr wT); simpl. apply refS. Defined. 

Definition bop_left_sum_idempotent_decide : 
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable T rT bT  → 
         bop_idempotent_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_left_sum_idempotent commS commT)
     | inr not_commT => inr _ (bop_left_sum_not_idempotent_right not_commT)
     end 
   | inr not_commS   => inr _ (bop_left_sum_not_idempotent_left not_commS)
   end. 

Definition bop_left_sum_commutative_decide : 
     bop_commutative_decidable S rS bS  → bop_commutative_decidable T rT bT  → 
        bop_commutative_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_left_sum_commutative commS commT)
     | inr not_commT => inr _ (bop_left_sum_not_commutative_right not_commT)
     end 
   | inr not_commS   => inr _ (bop_left_sum_not_commutative_left not_commS)
   end. 

Definition bop_left_sum_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable T rT bT  → 
        bop_selective_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl selS => 
     match dT with 
     | inl selT     => inl _ (bop_left_sum_selective selS selT)
     | inr not_selT => inr _ (bop_left_sum_not_selective_right not_selT)
     end 
   | inr not_selS   => inr _ (bop_left_sum_not_selective_left not_selS)
   end. 

Definition bop_left_sum_exists_id_decide : bop_exists_id_decidable T rT bT  → bop_exists_id_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dT,  
   match dT with 
   | inl eid  => inl _ (bop_left_sum_exists_id eid)
   | inr neid => inr _ (bop_left_sum_not_exists_id neid)
   end. 


Definition bop_left_sum_exists_ann_decide : bop_exists_ann_decidable S rS bS  → bop_exists_ann_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS,     
   match dS with 
   | inl eann  => inl _ (bop_left_sum_exists_ann eann)
   | inr neann => inr _ (bop_left_sum_not_exists_ann neann)
   end. 

End LeftSum.
