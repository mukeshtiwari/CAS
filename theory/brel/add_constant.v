Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop.
Require Import CAS.theory.brel_properties. 



Lemma brel_add_constant_congruence : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
       brel_congruence S rS rS → 
         brel_congruence (with_constant S) 
                         (brel_add_constant S rS c) 
                         (brel_add_constant S rS c). 
Proof. unfold brel_congruence. 
     intros S rS c congS [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto. 
     discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
Defined. 

Lemma brel_add_constant_witness : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
              (brel_witness S rS) → brel_witness (with_constant S) (brel_add_constant S rS c). 
Proof. 
     intros S rS c [s Ps]. exists (inr _ s). simpl. rewrite Ps. reflexivity. 
Defined. 

Lemma brel_add_constant_negate : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
              (brel_witness S rS) 
               → brel_negate (with_constant S) (brel_add_constant S rS c). 
Proof. 
     intros S rS c [s Ps]. 
       exists (λ (d : with_constant S), match d with | inl _ => inr _ s  | inr _ => inl S c end). 
       induction s0; simpl; auto. 
Defined. 

Definition brel_add_constant_nontrivial : ∀ (S : Type) (rS : brel S) (c : cas_constant), 
       (brel_nontrivial S rS) → 
         brel_nontrivial (with_constant S) (brel_add_constant S rS c)
:= λ S rS c ntS, 
   let wS := brel_nontrivial_witness S rS ntS in 
     {| 
        brel_nontrivial_witness  := brel_add_constant_witness S rS c wS
      ; brel_nontrivial_negate   := brel_add_constant_negate S rS c wS
     |} .


Lemma brel_add_constant_rep_correct : ∀ (S : Type)(eq : brel S)(rep : unary_op S) (c : cas_constant), 
          brel_rep_correct S eq rep →
              brel_rep_correct (with_constant S) (brel_add_constant S eq c) (uop_with_constant S rep). Proof. intros S eq rep c P [a | b]. 
       simpl. reflexivity. 
       simpl. apply P. 
Defined. 

Lemma brel_add_constant_rep_idempotent : 
        ∀ (S : Type)(eq : brel S)(rep : unary_op S) (c : cas_constant), 
          brel_rep_idempotent S eq rep →
              brel_rep_idempotent (with_constant S) (brel_add_constant S eq c) (uop_with_constant S rep). Proof. intros S eq rep c P [a | b]. 
       simpl. reflexivity. 
       simpl. apply P. 
Defined. 


Lemma brel_add_constant_reflexive : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
          brel_reflexive S rS → brel_reflexive (with_constant S) (brel_add_constant S rS c). 
Proof. unfold brel_reflexive. intros S rS c refS [a | b]. 
       simpl. reflexivity. 
       simpl. apply refS. 
Defined. 

Lemma brel_add_constant_symmetric : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
      (brel_symmetric _ rS) → brel_symmetric (with_constant S) (brel_add_constant S rS c). 
Proof.  unfold brel_symmetric. intros S rS c symS [c1 | s1] [c2 | s2]; simpl; intro H; auto. 
Defined. 

Lemma brel_add_constant_transitive : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
    (brel_transitive _ rS) → brel_transitive (with_constant S) (brel_add_constant S rS c). 
Proof. unfold brel_transitive. 
     intros S rS c transS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros H1 H2; auto. 
     discriminate. apply (transS _ _ _ H1 H2). 
Defined. 

