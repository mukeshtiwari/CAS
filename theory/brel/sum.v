Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties.

Section Sum. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.

Variable wS : S. 
Variable wT : T.

Variable conS : brel_congruence S rS rS.
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.
Variable tranT : brel_transitive T rT.

Notation "a <+> b"  := (brel_sum a b) (at level 15).

(*
Lemma brel_sum_witness : 
              ((brel_witness S rS)  + (brel_witness _ rT)) 
               → brel_witness (S + T) (rS <+> rT). 
Proof. 
     intros [[s Ps] | [t Pt]]. 
        exists (inl _ s). simpl. rewrite Ps. reflexivity. 
        exists (inr _ t). simpl. rewrite Pt. reflexivity. 
Defined. 

Lemma brel_sum_negate : 
              (brel_witness S rS) -> (brel_witness T rT)
               → brel_negate (S + T) (rS <+> rT). 
Proof. 
     intros [s Ps] [t Pt]. 
       exists (λ (d : S + T), match d with | inl _ => inr S t | inr _ => inl T s end). 
       induction s0; simpl; auto. 
Defined. 

Definition brel_sum_nontrivial : 
       (brel_witness S rS) -> (brel_witness T rT) → 
         brel_nontrivial (S + T) (rS <+> rT)
:= λ wS wT, 
     {| 
        brel_nontrivial_witness  := brel_sum_witness (inl _ wS)
      ; brel_nontrivial_negate   := brel_sum_negate wS wT
     |} .
 *)


Lemma brel_sum_not_trivial :  
        brel_not_trivial (S + T) (rS <+> rT) (λ (d : S + T), match d with | inl _ => inr wT | inr _ => inl wS end).
Proof. intros [ s | t ]; compute; auto. Defined. 


Lemma brel_sum_reflexive : brel_reflexive (S + T) (rS <+> rT). 
Proof. intros [s |  t]; simpl. rewrite (refS s). reflexivity. rewrite (refT t). reflexivity. Qed. 


Lemma brel_sum_symmetric : brel_symmetric (S + T) (rS <+> rT). 
Proof. intros [s1 | t1] [s2 | t2]; simpl; intros.  
        apply (symS _ _ H). exact H. exact H. apply (symT _ _ H).         
Qed. 

Lemma brel_sum_transitive : brel_transitive (S + T) (rS <+> rT). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros.  
        apply (tranS _ _ _ H H0). 
        exact H0. discriminate H. exact H. exact H. discriminate H. exact H0. 
        apply (tranT _ _ _ H H0). 
Qed. 


Lemma brel_sum_congruence : brel_congruence (S + T) (rS <+> rT) (rS <+> rT). 
Proof. intros [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto; discriminate. Qed. 


Lemma brel_sum_rep_correct : 
       ∀ (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_correct S rS repS) → 
              (brel_rep_correct T rT repT) → 
                 brel_rep_correct (S + T) (rS <+> rT) (uop_sum repS repT). 
Proof. 
     intros repS repT RS RT [s | t]; compute. 
         rewrite (RS s); auto.  
         rewrite (RT t); auto.
Qed. 

Lemma brel_sum_rep_idempotent : 
       ∀ (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_idempotent S rS repS) → 
              (brel_rep_idempotent T rT repT) → 
                 brel_rep_idempotent (S + T) (rS <+> rT) (uop_sum repS repT). 
Proof. 
     intros repS repT RS RT [s | t]; compute. 
         rewrite (RS s); auto.  
         rewrite (RT t); auto.
Qed. 

Lemma brel_sum_not_total_ : ∀ (s : S) (t : T),  brel_not_total (S + T) (rS <+> rT). 
Proof. intros s t. exists ((inl _ s), (inr _ t)); simpl. split; reflexivity. Defined. 

End Sum.