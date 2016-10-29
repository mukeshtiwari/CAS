Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 

Lemma brel_sum_witness : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              ((brel_witness S rS)  + (brel_witness _ rT)) 
               → brel_witness (S + T) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT [[s Ps] | [t Pt]]. 
        exists (inl _ s). simpl. rewrite Ps. reflexivity. 
        exists (inr _ t). simpl. rewrite Pt. reflexivity. 
Defined. 

Lemma brel_sum_negate : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_witness S rS) -> (brel_witness T rT)
               → brel_negate (S + T) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT [s Ps] [t Pt]. 
       exists (λ (d : S + T), match d with | inl _ => inr S t | inr _ => inl T s end). 
       induction s0; simpl; auto. 
Defined. 

Definition brel_sum_nontrivial : ∀ (S T : Type) (rS : brel S) (rT : brel T), 
       (brel_witness S rS) -> (brel_witness T rT) → 
         brel_nontrivial (S + T) (brel_sum S T rS rT)
:= λ S T rS rT wS wT, 
     {| 
        brel_nontrivial_witness  := brel_sum_witness S T rS rT (inl _ wS)
      ; brel_nontrivial_negate   := brel_sum_negate S T rS rT wS wT
     |} .

Lemma brel_sum_reflexive : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_reflexive _ rS) → (brel_reflexive _ rT) 
               → brel_reflexive (S + T) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT. unfold brel_reflexive. intros RS RT [s |  t]; simpl. 
     rewrite (RS s). reflexivity. 
     rewrite (RT t). reflexivity. 
Defined. 


Lemma brel_sum_rep_correct : 
       ∀ (S T: Type) (rS : brel S) (rT : brel T) (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_correct S rS repS) → 
              (brel_rep_correct T rT repT) → 
                 brel_rep_correct (S + T) (brel_sum S T rS rT) (uop_sum S T repS repT). 
Proof. 
     intros S T rS rT repS repT RS RT [s | t]; compute. 
         rewrite (RS s); auto.  
         rewrite (RT t); auto.
Defined. 

Lemma brel_sum_rep_idempotent : 
       ∀ (S T: Type) (rS : brel S) (rT : brel T) (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_idempotent S rS repS) → 
              (brel_rep_idempotent T rT repT) → 
                 brel_rep_idempotent (S + T) (brel_sum S T rS rT) (uop_sum S T repS repT). 
Proof. 
     intros S T rS rT repS repT RS RT [s | t]; compute. 
         rewrite (RS s); auto.  
         rewrite (RT t); auto.
Defined. 



Lemma brel_sum_symmetric : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_symmetric _ rS) → (brel_symmetric _ rT) 
               → brel_symmetric (S + T) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT. 
     unfold brel_symmetric. intros RS RT [s1 | t1] [s2 | t2]; simpl; intros.  
        apply (RS _ _ H). 
        assumption. 
        assumption. 
        apply (RT _ _ H). 
Defined. 


Lemma brel_sum_transitive : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_transitive _ rS) → (brel_transitive _ rT) 
               → brel_transitive (S + T) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT. 
     unfold brel_transitive. intros RS RT [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros.  
        apply (RS _ _ _ H H0). 
        assumption. 
        discriminate H. 
        assumption. 
        assumption. 
        discriminate H. 
        assumption. 
        apply (RT _ _ _ H H0). 
Defined. 

Lemma brel_sum_not_total_ : ∀ (S T: Type) (rS : brel S) (rT : brel T) (s : S) (t : T),  
              brel_not_total (S + T) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT s t. exists ((inl _ s), (inr _ t)); simpl. 
     split. reflexivity. reflexivity.
Defined. 


Lemma brel_sum_congruence : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
       brel_congruence S rS rS → brel_congruence T rT rT → 
         brel_congruence (S + T) (brel_sum S T rS rT) (brel_sum S T rS rT). 
Proof. 
     intros S T rS rT. unfold brel_congruence. intros congS congT. 
     intros [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto. 
        discriminate Q. 
        discriminate H. 
        discriminate H. 
        discriminate Q. 
        discriminate H. 
        discriminate H. 
        discriminate Q. 
        discriminate H. 
        discriminate H. 
        discriminate Q. 
Defined. 

