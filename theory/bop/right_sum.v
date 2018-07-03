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

  Notation "a <+> b"  := (brel_sum a b)               (at level 15).
  Notation "a [+] b"  := (bop_right_sum a b)          (at level 15).  
  Notation "a == b"   := (brel_sum rS rT a b = true)  (at level 15).  


Lemma bop_right_sum_congruence : bop_congruence (S + T) (rS <+> rT) (bS [+] bT). 
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

Lemma bop_right_sum_associative : bop_associative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl.
       apply assS. apply refT. apply refT. apply refT. apply refT. apply refT. apply refT. apply assT. 
Qed. 

Lemma bop_right_sum_idempotent : bop_idempotent S rS bS → bop_idempotent T rT bT → bop_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s | t]; simpl. apply L. apply R. Qed. 

Lemma bop_right_sum_not_idempotent_left : bop_not_idempotent S rS bS → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [s P]. exists (inl _ s). simpl. exact P. Defined. 

Lemma bop_right_sum_not_idempotent_right : bop_not_idempotent T rT bT → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [t P]. exists (inr _ t). simpl. exact P. Defined. 

Lemma bop_right_sum_not_idempotent : 
      (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → 
      bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_right_sum_not_idempotent_left L). apply (bop_right_sum_not_idempotent_right R). Defined. 


Lemma bop_right_sum_commutative : 
      bop_commutative S rS bS → bop_commutative T rT bT → bop_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. apply refT. apply refT. apply R. Defined. 

Lemma bop_right_sum_not_commutative_left : 
      bop_not_commutative S rS bS →  bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [s t] P]. exists (inl _ s, inl _ t). simpl. exact P. Defined. 

Lemma bop_right_sum_not_commutative_right : 
      bop_not_commutative T rT bT → bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t). simpl. exact P. Defined. 

Lemma bop_right_sum_not_commutative : 
      (bop_not_commutative S rS bS) + (bop_not_commutative T rT bT) → bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_right_sum_not_commutative_left L). apply (bop_right_sum_not_commutative_right R). Defined. 

Lemma bop_right_sum_selective : 
      bop_selective S rS bS → bop_selective T rT bT → bop_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. right. apply refT. left. apply refT. apply R. Defined. 

Lemma bop_right_sum_not_selective_left : 
      bop_not_selective S rS bS → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof.  intros [ [s1 s2] P]. exists (inl _ s1, inl _ s2). simpl. exact P. Defined. 

Lemma bop_right_sum_not_selective_right : 
      bop_not_selective T rT bT → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [t1 t2] P]. exists (inr _ t1, inr _ t2). simpl. exact P. Defined. 

Lemma bop_right_sum_not_selective : 
      (bop_not_selective S rS bS) + (bop_not_selective T rT bT) → 
      bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_right_sum_not_selective_left L). apply (bop_right_sum_not_selective_right R). Defined. 

Lemma bop_right_sum_not_is_left : bop_not_is_left (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl _ wS, inr _ wT). simpl. reflexivity. Defined. 

Lemma bop_right_sum_not_is_right : bop_not_is_right (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inr _ wT, inl _ wS). simpl. reflexivity. Defined. 


Lemma bop_right_sum_is_id : ∀ i : S, bop_is_id S rS bS i -> bop_is_id (S + T) (rS <+> rT) (bS [+] bT) (inl _ i).
Proof. intros i pS [s | t]; compute. apply (pS s). rewrite (refT t); auto. Defined. 


Lemma bop_right_sum_exists_id : (bop_exists_id S rS bS) -> bop_exists_id (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros [iS pS]. exists (inl _ iS). apply bop_right_sum_is_id; auto. Defined. 

Lemma bop_right_sum_id_is_inl : ∀ i : S + T, (bop_is_id _ (rS <+> rT) (bS [+] bT) i) ->
                                        ∀ idS : S, bop_is_id _ rS bS idS -> i == (inl idS). 
Proof. intros [s | t] P idS Q; compute. 
       assert (C : bop_is_id _ rS bS s). intro s2. assert (F := P (inl s2)). compute in F. exact F.
       apply (bop_is_id_equal _ rS symS tranS bS s idS C Q).
       assert (F := P (inl idS)). compute in F. destruct F as [F _]. discriminate F.       
Qed.        

Lemma bop_right_sum_simplify_id : ∀ s : S, 
    bop_is_id (S + T) (rS <+> rT) (bS [+] bT) (inl s) -> bop_is_id S rS bS s.
Proof. intros s H. intro s'. apply (H (inl s')). Qed .   

Lemma bop_right_sum_extract_id (s' : S) : ∀ i : S + T, 
    bop_is_id (S + T) (rS <+> rT) (bS [+] bT) i ->
       {s : S & (bop_is_id S rS bS s) * (i == (inl s))}.
Proof. intros [s1 | t1] H; simpl.
       exists s1. split. apply bop_right_sum_simplify_id. exact H. apply refS.       
       assert (F := H (inl s')). compute in F. destruct F as [F _]. discriminate F. 
Qed.        

Lemma bop_right_sum_not_exists_id : (bop_not_exists_id S rS bS) -> bop_not_exists_id (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros pS [s | t]. destruct (pS s) as [x D]. exists (inl _ x). compute. exact D. 
       exists (inl _ wS). compute. auto. 
Defined. 

Lemma bop_right_sum_is_ann : ∀ a : T, bop_is_ann T rT bT a -> bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) (inr _ a).
Proof. intros a pT [s | t]; compute. rewrite (refT a); auto. apply (pT t). Defined. 

Lemma bop_right_sum_exists_ann : (bop_exists_ann T rT bT) -> bop_exists_ann (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros [annT pT]. exists (inr _ annT). apply  bop_right_sum_is_ann; auto. Defined. 

Lemma bop_right_sum_ann_is_inr : ∀ i : S + T, (bop_is_ann _ (rS <+> rT) (bS [+] bT) i) ->
                                        ∀ annT : T, bop_is_ann _ rT bT annT -> i == (inr annT).
Proof. intros [s | t] P annT Q; compute. 
       assert (F := P (inr annT)). compute in F. destruct F as [F _]. discriminate F. 
       assert (C : bop_is_ann _ rT bT t). intro t2. assert (F := P (inr t2)). compute in F. exact F.
          apply (bop_is_ann_equal _ rT symT tranT bT t annT C Q). 
Qed.

Lemma bop_right_sum_simplify_ann : ∀ t : T, 
    bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) (inr t) -> bop_is_ann T rT bT t.
Proof. intros t H. intro t'. apply (H (inr t')). Qed .   

Lemma bop_right_sum_extract_ann (t' : T) : ∀ i : S + T, 
    bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) i ->
       {t : T & (bop_is_ann T rT bT t) * (i == (inr t)) }.
Proof. intros [s1 | t1] H; simpl.
       assert (F := H (inr t')). compute in F. destruct F as [F _]. discriminate F. 
       exists t1. split. apply bop_right_sum_simplify_ann. exact H. apply refT.
Qed.        

Lemma bop_right_sum_not_exists_ann : (bop_not_exists_ann T rT bT) -> bop_not_exists_ann (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros pT [s | t]. exists (inr _ wT). compute; auto.  
       destruct (pT t) as [x D].  exists (inr _ x). compute. exact D. 
Defined. 

Lemma bop_right_sum_not_left_cancellative : bop_not_left_cancellative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists ((inr _ wT), ((inl wS), (inl (f wS)))). simpl. split. apply refT. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_right_sum_not_right_cancellative : bop_not_right_cancellative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists ((inr _ wT), ((inl wS), (inl (f wS)))). simpl. split. apply refT. destruct (Pf wS) as [L _]. exact L. Defined. 

Lemma bop_right_sum_not_left_constant : bop_not_left_constant (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl wS, (inr wT, inr (g wT))). simpl.  destruct (Pg wT) as [L _]. exact L. Defined. 

Lemma bop_right_sum_not_right_constant : bop_not_right_constant (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl wS, (inr wT, inr (g wT))). simpl.  destruct (Pg wT) as [L _]. exact L. Defined. 

Lemma bop_right_sum_not_anti_left : bop_not_anti_left (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inr wT, inl wS); simpl. apply refT. Defined. 

Lemma bop_right_sum_not_anti_right : bop_not_anti_right (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inr wT, inl wS); simpl. apply refT. Defined. 


(* Decide *) 

Definition bop_right_sum_idempotent_decide : 
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable T rT bT  → 
        bop_idempotent_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_right_sum_idempotent commS commT)
     | inr not_commT => inr _ (bop_right_sum_not_idempotent_right not_commT)
     end 
   | inr not_commS   => inr _ (bop_right_sum_not_idempotent_left not_commS)
   end. 


Definition bop_right_sum_commutative_decide : 
     bop_commutative_decidable S rS bS  → bop_commutative_decidable T rT bT  → 
        bop_commutative_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_right_sum_commutative commS commT)
     | inr not_commT => inr _ (bop_right_sum_not_commutative_right not_commT)
     end 
   | inr not_commS   => inr _ (bop_right_sum_not_commutative_left not_commS)
   end. 

Definition bop_right_sum_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable T rT bT  → bop_selective_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl selS => 
     match dT with 
     | inl selT     => inl _ (bop_right_sum_selective selS selT)
     | inr not_selT => inr _ (bop_right_sum_not_selective_right not_selT)
     end 
   | inr not_selS   => inr _ (bop_right_sum_not_selective_left not_selS)
   end. 


Definition bop_right_sum_exists_id_decide : bop_exists_id_decidable S rS bS  → bop_exists_id_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS,  
   match dS with 
   | inl eid  => inl _ (bop_right_sum_exists_id eid)
   | inr neid => inr _ (bop_right_sum_not_exists_id neid)
   end. 

Definition bop_right_sum_exists_ann_decide : bop_exists_ann_decidable T rT bT  → bop_exists_ann_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dT,  
   match dT with 
   | inl eann  => inl _ (bop_right_sum_exists_ann eann)
   | inr neann => inr _ (bop_right_sum_not_exists_ann neann)
   end. 

End RightSum.