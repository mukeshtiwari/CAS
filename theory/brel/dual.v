Require Import Coq.Arith.Arith.     
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 

Lemma brel_dual_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S), 
         brel_congruence S r1 r2 -> brel_congruence S r1 (brel_dual S r2). 
Proof. intros S r1 r2 cong s t u v H1 H2. apply cong; auto. Qed. 

Lemma brel_dual_irreflexive : ∀ (S : Type) (r : brel S), 
          brel_irreflexive S r -> brel_irreflexive S (brel_dual S r).  
Proof. intros S r H s. unfold brel_dual. apply H. Qed. 

Lemma brel_dual_reflexive : ∀ (S : Type) (r : brel S), 
          brel_reflexive S r -> brel_reflexive S (brel_dual S r).  
Proof. intros S r H s. unfold brel_dual. apply H. Qed. 

Lemma brel_dual_transitive : ∀ (S : Type) (rS : brel S),  
    (brel_transitive _ rS) → brel_transitive S (brel_dual S rS). 
Proof. unfold brel_dual. intros S rS transS s1 s2 s3 H1 H2. apply (transS _ _ _ H2 H1). Qed. 

Lemma brel_dual_antisymmetric : ∀ (S : Type) (eqS rS : brel S),  
      brel_antisymmetric _ eqS rS → brel_antisymmetric S eqS (brel_dual S rS). 
Proof. unfold brel_dual. intros S eqS rS symS s1 s2 H1 H2. apply symS; auto. Qed. 

Lemma brel_dual_not_antisymmetric : ∀ (S : Type) (eqS rS : brel S),  
      brel_not_antisymmetric _ eqS rS → brel_not_antisymmetric S eqS (brel_dual S rS). 
Proof.  unfold brel_dual. intros S eqS rS [[s t] [[H1 H2] H3]]. exists (s, t); auto. Defined. 

Lemma brel_dual_total : ∀ (S : Type) (rS : brel S),  
      (brel_total _ rS) → brel_total S (brel_dual S rS). 
Proof.  unfold brel_dual. intros S rS symS s t.  destruct (symS s t) as [L | R]; auto. Qed. 

Lemma brel_dual_not_total : ∀ (S : Type) (rS : brel S),  
      (brel_not_total _ rS) → brel_not_total S (brel_dual S rS). 
Proof.  intros S rS [[s t] H]. exists (s, t). compute. destruct H as [P Q]. split; assumption. 
Defined. 

Definition brel_dual_total_decide : 
   ∀ (S : Type) 
     (r : brel S), 
     brel_total_decidable S r -> 
         brel_total_decidable S (brel_dual S r)
:= λ S r d, 
   match d with 
   | inl totS     => inl _ (brel_dual_total S r totS)
   | inr not_totS => inr _ (brel_dual_not_total S r not_totS)
   end. 



Lemma brel_dual_exists_top : ∀ (S : Type) (rS : brel S),  
             brel_exists_bottom S rS -> brel_exists_top S (brel_dual S rS). 
Proof.  intros S rS [t P]. exists t. intro s. apply P. Defined. 


Lemma brel_dual_not_exists_top : ∀ (S : Type) (rS : brel S), 
             brel_not_exists_bottom S rS -> brel_not_exists_top S (brel_dual S rS). 
Proof.  intros S rS P s. exists (projT1 (P s)). destruct (P s) as [w F]. compute; auto. Defined. 

Lemma brel_dual_exists_bottom : ∀ (S : Type) (rS : brel S),  
             brel_exists_top S rS -> brel_exists_bottom S (brel_dual S rS). 
Proof.  intros S rS [t P]. exists t. intro s. apply P. Defined. 

Lemma brel_dual_not_exists_bottom : ∀ (S : Type) (rS : brel S), 
             brel_not_exists_top S rS -> brel_not_exists_bottom S (brel_dual S rS). 
Proof.  intros S rS P s. exists (projT1 (P s)). destruct (P s) as [w F]. compute; auto. Defined. 








