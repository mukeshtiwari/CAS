Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts. 
Require Import CAS.coq.eqv.sum. 

Section Theory.


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

End Theory.

Section ACAS.

Definition sg_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_proofs S rS bS -> sg_proofs T rT bT -> 
        sg_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_associative   := bop_left_sum_associative S T rS rT bS bT refS (A_sg_associative _ _ _ sgS) (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_left_sum_congruence S T rS rT bS bT (A_sg_congruence _ _ _ sgS) (A_sg_congruence _ _ _ sgT) 

; A_sg_commutative_d := bop_left_sum_commutative_decide S T rS rT bS bT refS (A_sg_commutative_d _ _ _ sgS) (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT refS (A_sg_selective_d _ _ _ sgS) (A_sg_selective_d _ _ _ sgT) 
; A_sg_idempotent_d  := bop_left_sum_idempotent_decide S T rS rT bS bT (A_sg_idempotent_d _ _ _ sgS) (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_exists_id_d _ _ _ sgT) 
; A_sg_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_exists_ann_d _ _ _ sgS)

; A_sg_is_left_d        := inr _ (bop_left_sum_not_is_left S T rS rT bS bT s t)
; A_sg_is_right_d       := inr _ (bop_left_sum_not_is_right S T rS rT bS bT s t)
; A_sg_left_cancel_d    := inr _ (bop_left_sum_not_left_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_right_cancel_d   := inr _ (bop_left_sum_not_right_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_left_constant_d  := inr _ (bop_left_sum_not_left_constant S T rS rT bS bT s f Pf t)
; A_sg_right_constant_d := inr _ (bop_left_sum_not_right_constant S T rS rT bS bT s f Pf t)
; A_sg_anti_left_d      := inr _ (bop_left_sum_not_anti_left S T rS rT bS bT s refS t)
; A_sg_anti_right_d     := inr _ (bop_left_sum_not_anti_right S T rS rT bS bT s refS t)
|}. 


Definition sg_C_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_C_proofs S rS bS -> sg_C_proofs T rT bT -> 
        sg_C_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_C_associative   := bop_left_sum_associative S T rS rT bS bT refS (A_sg_C_associative _ _ _ sgS) (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_left_sum_congruence S T rS rT bS bT (A_sg_C_congruence _ _ _ sgS) (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative   := bop_left_sum_commutative S T rS rT bS bT refS (A_sg_C_commutative _ _ _ sgS) (A_sg_C_commutative _ _ _ sgT) 

; A_sg_C_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT refS (A_sg_C_selective_d _ _ _ sgS) (A_sg_C_selective_d _ _ _ sgT)
; A_sg_C_idempotent_d  := bop_left_sum_idempotent_decide S T rS rT bS bT (A_sg_C_idempotent_d _ _ _ sgS) (A_sg_C_idempotent_d _ _ _ sgT) 
; A_sg_C_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_C_exists_id_d _ _ _ sgT) 
; A_sg_C_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_C_exists_ann_d _ _ _ sgS) 
                         
; A_sg_C_left_cancel_d    := inr _ (bop_left_sum_not_left_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_C_right_cancel_d   := inr _ (bop_left_sum_not_right_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_C_left_constant_d  := inr _ (bop_left_sum_not_left_constant S T rS rT bS bT s f Pf t)
; A_sg_C_right_constant_d := inr _ (bop_left_sum_not_right_constant S T rS rT bS bT s f Pf t)
; A_sg_C_anti_left_d      := inr _ (bop_left_sum_not_anti_left S T rS rT bS bT s refS t)
; A_sg_C_anti_right_d     := inr _ (bop_left_sum_not_anti_right S T rS rT bS bT s refS t)
|}. 

Definition sg_CI_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CI_proofs S rS bS -> sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s t eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_CI_associative := bop_left_sum_associative S T rS rT bS bT refS (A_sg_CI_associative _ _ _ sgS) (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence  := bop_left_sum_congruence S T rS rT bS bT (A_sg_CI_congruence _ _ _ sgS) (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative := bop_left_sum_commutative S T rS rT bS bT refS (A_sg_CI_commutative _ _ _ sgS) (A_sg_CI_commutative _ _ _ sgT) 
                         
; A_sg_CI_selective_d  := bop_left_sum_selective_decide S T rS rT bS bT refS (A_sg_CI_selective_d _ _ _ sgS) (A_sg_CI_selective_d _ _ _ sgT) 
; A_sg_CI_idempotent   := bop_left_sum_idempotent S T rS rT bS bT (A_sg_CI_idempotent _ _ _ sgS) (A_sg_CI_idempotent _ _ _ sgT) 
; A_sg_CI_exists_id_d  := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_CI_exists_id_d _ _ _ sgT) 
; A_sg_CI_exists_ann_d := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS  (A_sg_CI_exists_ann_d _ _ _ sgS) 
|}.

Definition sg_CS_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CS_proofs S rS bS -> sg_CS_proofs T rT bT -> 
        sg_CS_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s t eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_CS_associative := bop_left_sum_associative S T rS rT bS bT refS (A_sg_CS_associative _ _ _ sgS) (A_sg_CS_associative _ _ _ sgT) 
; A_sg_CS_congruence  := bop_left_sum_congruence S T rS rT bS bT (A_sg_CS_congruence _ _ _ sgS) (A_sg_CS_congruence _ _ _ sgT) 
; A_sg_CS_commutative := bop_left_sum_commutative S T rS rT bS bT refS (A_sg_CS_commutative _ _ _ sgS) (A_sg_CS_commutative _ _ _ sgT) 
; A_sg_CS_selective   := bop_left_sum_selective S T rS rT bS bT refS (A_sg_CS_selective _ _ _ sgS) (A_sg_CS_selective _ _ _ sgT) 

; A_sg_CS_exists_id_d   := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_CS_exists_id_d _ _ _ sgT) 
; A_sg_CS_exists_ann_d  := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_CS_exists_ann_d _ _ _ sgS) 
|}. 

Definition A_sg_left_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
let eqvS := A_sg_eq S sgS in
let eqvT := A_sg_eq T sgT in
let bS   := A_sg_bop S sgS in
let bT   := A_sg_bop T sgT in 
{| 
     A_sg_eq        := A_eqv_sum S T eqvS eqvT
   ; A_sg_bop       := bop_left_sum  bS bT
   ; A_sg_proofs    := sg_proofs_left_sum S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT)
   ; A_sg_bop_ast   := Ast_bop_left_sum (A_sg_bop_ast S sgS, A_sg_bop_ast T sgT)                           
   ; A_sg_ast       := Ast_sg_left_sum (A_sg_ast S sgS, A_sg_ast T sgT)
|}. 

Definition A_sg_C_left_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
let eqvS := A_sg_C_eqv S sgS in 
let eqvT := A_sg_C_eqv T sgT in
let bS   := A_sg_C_bop S sgS in
let bT   := A_sg_C_bop T sgT in 
{| 
     A_sg_C_eqv       := A_eqv_sum S T eqvS eqvT
   ; A_sg_C_bop       := bop_left_sum bS bT
   ; A_sg_C_proofs    := sg_C_proofs_left_sum S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT)
   ; A_sg_C_bop_ast   := Ast_bop_left_sum (A_sg_C_bop_ast S sgS, A_sg_C_bop_ast T sgT)                                                      
   ; A_sg_C_ast       := Ast_sg_C_left_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
|}. 


Definition A_sg_CI_left_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT,
let eqvS := A_sg_CI_eqv S sgS in 
let eqvT := A_sg_CI_eqv T sgT in
let bS   := A_sg_CI_bop S sgS in
let bT   := A_sg_CI_bop T sgT in 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T eqvS eqvT
   ; A_sg_CI_bop       := bop_left_sum bS bT 
   ; A_sg_CI_proofs    := sg_CI_proofs_left_sum S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT)
   ; A_sg_CI_bop_ast   := Ast_bop_left_sum (A_sg_CI_bop_ast S sgS, A_sg_CI_bop_ast T sgT)                      
   ; A_sg_CI_ast       := Ast_sg_CI_left_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
|}. 

Definition A_sg_CS_left_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
let eqvS := A_sg_CS_eqv S sgS in 
let eqvT := A_sg_CS_eqv T sgT in
let bS   := A_sg_CS_bop S sgS in
let bT   := A_sg_CS_bop T sgT in 
{| 
     A_sg_CS_eqv       := A_eqv_sum S T eqvS eqvT
   ; A_sg_CS_bop       := bop_left_sum bS bT
   ; A_sg_CS_proofs    := sg_CS_proofs_left_sum S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT)
   ; A_sg_CS_bop_ast   := Ast_bop_left_sum (A_sg_CS_bop_ast S sgS, A_sg_CS_bop_ast T sgT)                                        
   ; A_sg_CS_ast       := Ast_sg_CS_left_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
|}. 

End ACAS.

Section CAS.

Definition check_exists_id_left_sum : ∀ {S T : Type}, @check_exists_id T -> @check_exists_id (S + T)
:= λ {S T} cT,  
      match cT with 
      | Certify_Exists_Id t    => Certify_Exists_Id (inr S t) 
      | Certify_Not_Exists_Id  => Certify_Not_Exists_Id
      end. 

Definition check_exists_ann_left_sum : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := (S + T)))
:= λ {S T} cS,  
      match cS with 
      | Certify_Exists_Ann s    => Certify_Exists_Ann (inl T s)
      | Certify_Not_Exists_Ann => Certify_Not_Exists_Ann 
      end.

Definition check_idempotent_left_sum : ∀ {S T : Type}, 
             (check_idempotent (S := S)) -> 
             (check_idempotent (S := T)) -> 
                (check_idempotent (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent (inl _ s1)
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent (inr _ t1)
      end. 


Definition check_selective_left_sum : ∀ {S T : Type}, 
             (check_selective (S := S)) -> 
             (check_selective (S := T)) -> 
                (check_selective (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Selective, Certify_Selective => Certify_Selective 
      | Certify_Not_Selective (s1, s2), _    => Certify_Not_Selective ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Selective (t1, t2)    => Certify_Not_Selective ((inr _ t1), (inr _ t2))
      end. 

Definition check_commutative_left_sum : ∀ {S T : Type}, 
             (check_commutative (S := S)) -> 
             (check_commutative (S := T)) -> 
                (check_commutative (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative 
      | Certify_Not_Commutative (s1, s2), _  => Certify_Not_Commutative ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Commutative (t1, t2)  => Certify_Not_Commutative ((inr _ t1), (inr _ t2))
      end. 




Definition sg_certs_left_sum : ∀ {S T : Type},  S -> (S -> S) -> T -> (T -> T) -> @sg_certificates S -> @sg_certificates T -> @sg_certificates (S + T) 
:= λ {S T} s f t g cS cT,  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := check_commutative_left_sum 
                            (sg_commutative_d cS) 
                            (sg_commutative_d cT)
; sg_idempotent_d     := check_idempotent_left_sum 
                            (sg_idempotent_d cS) 
                            (sg_idempotent_d cT)
; sg_selective_d      := check_selective_left_sum 
                            (sg_selective_d cS) 
                            (sg_selective_d cT)
; sg_is_left_d        := Certify_Not_Is_Left (inr t, inl s) 
; sg_is_right_d       := Certify_Not_Is_Right (inl s, inr t) 
; sg_exists_id_d      := check_exists_id_left_sum (sg_exists_id_d  cT)
; sg_exists_ann_d     := check_exists_ann_left_sum (sg_exists_ann_d cS)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (inl s, (inr t, inr (g t)))
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (inl s, (inr t, inr (g t)))
; sg_left_constant_d  := Certify_Not_Left_Constant (inr t, (inl s, inl (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant (inr t, (inl s, inl (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left (inl s, inr t) 
; sg_anti_right_d     := Certify_Not_Anti_Right (inl s, inr t) 
|}.

Definition sg_C_certs_left_sum : ∀ {S T : Type}, S -> (S -> S) -> T -> (T -> T) -> @sg_C_certificates S -> @sg_C_certificates T -> @sg_C_certificates (S + T) 
:= λ {S T} s f t g cS cT,  
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence  
; sg_C_commutative      := Assert_Commutative  
; sg_C_idempotent_d     := check_idempotent_left_sum 
                            (sg_C_idempotent_d cS) 
                            (sg_C_idempotent_d cT)
; sg_C_selective_d      := check_selective_left_sum 
                            (sg_C_selective_d cS) 
                            (sg_C_selective_d cT)
; sg_C_exists_id_d      := check_exists_id_left_sum (sg_C_exists_id_d cT)
; sg_C_exists_ann_d     := check_exists_ann_left_sum (sg_C_exists_ann_d cS)
; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative (inl s, (inr t, inr (g t)))
; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative (inl s, (inr t, inr (g t)))
; sg_C_left_constant_d  := Certify_Not_Left_Constant (inr t, (inl s, inl (f s)))
; sg_C_right_constant_d := Certify_Not_Right_Constant (inr t, (inl s, inl (f s)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left (inl s, inr t) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (inl s, inr t) 
|}.


Definition sg_CI_certs_left_sum : ∀ {S T : Type},  sg_CI_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S + T)) 
:= λ {S T} cS cT,  
{|
  sg_CI_associative  := Assert_Associative   
; sg_CI_congruence   := Assert_Bop_Congruence  
; sg_CI_commutative  := Assert_Commutative  
; sg_CI_idempotent   := Assert_Idempotent  
; sg_CI_selective_d  := check_selective_left_sum (sg_CI_selective_d cS) (sg_CI_selective_d cT)
; sg_CI_exists_id_d  := check_exists_id_left_sum (sg_CI_exists_id_d cT)
; sg_CI_exists_ann_d := check_exists_ann_left_sum (sg_CI_exists_ann_d cS)
|}.

Definition sg_CS_certs_left_sum : ∀ {S T : Type},  sg_CS_certificates (S := S) -> sg_CS_certificates (S := T) -> sg_CS_certificates (S := (S + T)) 
:= λ {S T} cS cT,  
{|
  sg_CS_associative  := Assert_Associative   
; sg_CS_congruence   := Assert_Bop_Congruence  
; sg_CS_commutative  := Assert_Commutative  
; sg_CS_selective    := Assert_Selective  
; sg_CS_exists_id_d  := check_exists_id_left_sum (sg_CS_exists_id_d cT)
; sg_CS_exists_ann_d := check_exists_ann_left_sum (sg_CS_exists_ann_d cS)
|}.

Definition sg_left_sum : ∀ {S T : Type},  sg (S := S) -> sg (S := T) -> sg (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_eq     := eqv_sum (sg_eq sgS) (sg_eq sgT) 
   ; sg_bop    := bop_left_sum (sg_bop sgS) (sg_bop sgT) 
   ; sg_certs := sg_certs_left_sum 
                    (eqv_witness (sg_eq sgS)) (eqv_new (sg_eq sgS))
                    (eqv_witness (sg_eq sgT)) (eqv_new (sg_eq sgT)) 
                    (sg_certs sgS) 
                    (sg_certs sgT)
   ; sg_bop_ast   := Ast_bop_left_sum (sg_bop_ast sgS, sg_bop_ast sgT)                                                     
   ; sg_ast    := Ast_sg_left_sum (sg_ast sgS, sg_ast sgT)
   |}. 


Definition sg_C_left_sum : ∀ {S T : Type},  sg_C (S := S) -> sg_C (S := T) -> sg_C (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_C_eqv       := eqv_sum (sg_C_eqv sgS) (sg_C_eqv sgT) 
   ; sg_C_bop       := bop_left_sum (sg_C_bop sgS) (sg_C_bop sgT) 
   ; sg_C_certs    := sg_C_certs_left_sum 
                           (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS)) 
                           (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT)) 
                           (sg_C_certs sgS) 
                           (sg_C_certs sgT)
   ; sg_C_bop_ast   := Ast_bop_left_sum (sg_C_bop_ast sgS, sg_C_bop_ast sgT)                                 
   ; sg_C_ast       := Ast_sg_C_left_sum (sg_C_ast sgS, sg_C_ast sgT)
   |}. 

Definition sg_CI_left_sum : ∀ {S T : Type},  sg_CI (S := S) -> sg_CI (S := T) -> sg_CI (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CI_eqv       := eqv_sum (sg_CI_eqv sgS) (sg_CI_eqv sgT) 
   ; sg_CI_bop       := bop_left_sum (sg_CI_bop sgS) (sg_CI_bop sgT) 
   ; sg_CI_certs    := sg_CI_certs_left_sum (sg_CI_certs sgS) (sg_CI_certs sgT)
   ; sg_CI_bop_ast   := Ast_bop_left_sum (sg_CI_bop_ast sgS, sg_CI_bop_ast sgT)                                                  
   ; sg_CI_ast       := Ast_sg_CI_left_sum (sg_CI_ast sgS, sg_CI_ast sgT)
   |}. 

Definition sg_CS_left_sum : ∀ {S T : Type},  sg_CS (S := S) -> sg_CS (S := T) -> sg_CS (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CS_eqv       := eqv_sum (sg_CS_eqv sgS) (sg_CS_eqv sgT) 
   ; sg_CS_bop       := bop_left_sum (sg_CS_bop sgS) (sg_CS_bop sgT) 
   ; sg_CS_certs     := sg_CS_certs_left_sum (sg_CS_certs sgS) (sg_CS_certs sgT)
   ; sg_CS_bop_ast   := Ast_bop_left_sum (sg_CS_bop_ast sgS, sg_CS_bop_ast sgT)      
   ; sg_CS_ast       := Ast_sg_CS_left_sum (sg_CS_ast sgS, sg_CS_ast sgT)
   |}. 
  

End CAS.

Section Verify.

Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable wT : T.
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_check_commutative_left_sum :  ∀ (dS : bop_commutative_decidable S rS bS) (dT : bop_commutative_decidable T rT bT),
         
         check_commutative_left_sum 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_commutative_decide S T rS rT bS bT refS dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_left_sum : ∀ (dS : bop_idempotent_decidable S rS bS) (dT : bop_idempotent_decidable T rT bT),
         
         check_idempotent_left_sum 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_idempotent_decide S T rS rT bS bT dS dT). 
Proof. intros [cS | [s4 ncS]] [cT | [t4 ncT]]; compute; reflexivity. Defined. 

Lemma correct_check_selective_left_sum : ∀ (dS : bop_selective_decidable S rS bS) (dT : bop_selective_decidable T rT bT),
         
         check_selective_left_sum 
            (p2c_selective_check S rS bS dS)
            (p2c_selective_check T rT bT dT)
         = 
         p2c_selective_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_selective_decide S T rS rT bS bT refS dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 

Lemma correct_check_exists_id_left_sum : ∀ (dT : bop_exists_id_decidable T rT bT),
    
         check_exists_id_left_sum (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S + T) 
            (brel_sum rS rT)
            (bop_left_sum bS bT)
            (bop_left_sum_exists_id_decide S T rS rT bS bT refS wT dT).
Proof. intros [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_exists_ann_left_sum : ∀ (dS : bop_exists_ann_decidable S rS bS), 
         check_exists_ann_left_sum (p2c_exists_ann_check S rS bS dS)
         =
         p2c_exists_ann_check (S + T) 
            (brel_sum rS rT)
            (bop_left_sum bS bT)
            (bop_left_sum_exists_ann_decide S T rS rT bS bT wS refS dS).
Proof. intros [[s sP] | nS ]; compute; reflexivity. Defined. 


End ChecksCorrect. 

Section ProofsCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable eS : eqv_proofs S rS.
  Variable eT : eqv_proofs T rT. 


Lemma correct_sg_certs_left_sum : ∀ (pS : sg_proofs S rS bS) (pT : sg_proofs T rT bT),

      sg_certs_left_sum wS f wT g (P2C_sg S rS bS pS) (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_proofs_left_sum S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_proofs_left_sum, sg_certs_left_sum, P2C_sg; simpl. 
       rewrite <- correct_check_commutative_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum.
       reflexivity.        
Defined. 

Lemma correct_sg_C_certs_left_sum : ∀ (pS : sg_C_proofs S rS bS) (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_left_sum wS f wT g (P2C_sg_C S rS bS pS) (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_C_proofs_left_sum S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_left_sum, sg_C_certs_left_sum, P2C_sg_C; simpl. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_left_sum : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CS_proofs T rT bT),
        
      sg_CS_certs_left_sum (P2C_sg_CS S rS bS pS) (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_CS_proofs_left_sum S T rS rT bS bT wS wT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CS_proofs_left_sum, sg_CS_certs_left_sum, P2C_sg_CS; simpl. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Defined. 

Lemma correct_sg_CI_certs_left_sum : ∀ (pS : sg_CI_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_left_sum (P2C_sg_CI S rS bS pS) (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S + T) (brel_sum rS rT) 
                     (bop_left_sum bS bT) 
                     (sg_CI_proofs_left_sum S T rS rT bS bT wS wT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CI_proofs_left_sum, sg_CI_certs_left_sum, P2C_sg_CI; simpl. 
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       reflexivity. 
Defined.

End ProofsCorrect. 


Theorem correct_sg_left_sum : ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
      
         sg_left_sum (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S + T) (A_sg_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_left_sum, A2C_sg. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_certs_left_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_C_left_sum : ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
      
         sg_C_left_sum (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_left_sum, A2C_sg_C. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_C_certs_left_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_left_sum : ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
      
         sg_CS_left_sum (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_left_sum, A2C_sg_CS. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_CS_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CI_left_sum : ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
      
         sg_CI_left_sum (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_left_sum, A2C_sg_CI. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_CI_certs_left_sum. 
       reflexivity. 
Qed. 
  
 
End Verify.   
  