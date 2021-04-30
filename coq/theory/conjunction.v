Require Import Coq.Bool.Bool.
Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.po.properties. 
Require Import CAS.coq.theory.facts. 

Section Conjunction. 

Variable S  : Type. 
Variable r1 : brel S.
Variable r2 : brel S. 

Notation "a <&> b"  := (brel_conjunction a b) (at level 15).


Lemma brel_conjunction_congruence : 
         ∀ (eq : brel S), brel_congruence S eq r1  → brel_congruence S eq r2  → 
               brel_congruence S eq (r1 <&> r2). 
Proof. unfold brel_congruence, brel_conjunction. 
       intros eq C1 C2 s t u v H K. 
       rewrite (C1 _ _ _ _ H K). rewrite (C2 _ _ _ _ H K). 
       reflexivity. 
Defined.

Lemma brel_conjunction_reflexive : 
              (brel_reflexive S r1) → (brel_reflexive S r2) 
               → brel_reflexive S (r1 <&> r2). 
Proof. unfold brel_reflexive, brel_conjunction. 
       intros ref1 ref2 s. rewrite (ref1 s), (ref2 s). simpl. reflexivity. 
Defined. 

Lemma brel_conjunction_not_reflexive_left : 
              (brel_not_reflexive S r1) 
               → brel_not_reflexive S (r1 <&> r2). 
Proof. unfold brel_not_reflexive, brel_conjunction. 
       intros [s P]. exists s. rewrite P. reflexivity. 
Defined. 


Lemma brel_conjunction_symmetric : 
              (brel_symmetric S r1) → (brel_symmetric S r2) 
               → brel_symmetric S (r1 <&> r2). 
Proof. unfold brel_symmetric, brel_conjunction. 
     intros sym1 sym2 s1 s2 H.  
     apply andb_is_true_left in H. destruct H as [H_l H_r].  
     rewrite (sym1 _ _ H_l). rewrite (sym2 _ _ H_r). compute. reflexivity. 
Defined. 


Lemma brel_conjunction_transitive : 
        brel_transitive S r1 -> 
        brel_transitive S r2 -> 
            brel_transitive S (r1 <&> r2). 
Proof. unfold brel_transitive, brel_conjunction.  
     intros trans1 trans2 s1 s2 s3 H1 H2. 
     apply andb_is_true_left in H1. apply andb_is_true_left in H2. 
     destruct H1 as [L1 R1]. destruct H2 as [L2 R2]. 
     rewrite (trans1 _ _ _ L1 L2). rewrite (trans2 _ _ _ R1 R2). compute. reflexivity. 
Defined. 




Lemma brel_conjunction_irreflexive_left : ∀ (rS1 : brel S) (rS2 : brel S),  
        brel_irreflexive S rS1 -> 
           brel_irreflexive S (rS1 <&> rS2). 
Proof. 
     unfold brel_irreflexive, brel_conjunction. 
     intros rS1 rS2 irr s. rewrite (irr s). reflexivity. 
Defined. 


Lemma brel_conjunction_irreflexive_right : ∀ (rS1 : brel S) (rS2 : brel S),  
        brel_irreflexive S rS2 -> 
           brel_irreflexive S (rS1 <&> rS2). 
Proof. 
     unfold brel_irreflexive, brel_conjunction. 
     intros rS1 rS2 irr s. rewrite (irr s). apply andb_comm. 
Defined. 

Lemma brel_conjunction_irreflexive : 
        ((brel_irreflexive S r1) + (brel_irreflexive S r2)) -> 
           brel_irreflexive S (r1 <&> r2). 
Proof. intros [L | R]. 
       apply brel_conjunction_irreflexive_left; auto. 
       apply brel_conjunction_irreflexive_right; auto. 
Defined. 



(*


Lemma brel_conjunction_not_reflexive_right : 
              (brel_not_reflexive S r2) 
               → brel_not_reflexive S (r1 <&> r2). 
Proof. unfold brel_not_reflexive, brel_conjunction. 
       intros [s P]. exists s. rewrite P. apply andb_comm. 
Defined. 

Definition brel_conjunction_reflexive_decide: 
   ∀ (S : Type) 
     (r1 : brel S) 
     (r2 : brel S),   
     brel_reflexive_decidable S r1 → 
     brel_reflexive_decidable S r2 → 
        brel_reflexive_decidable S (r1 <&> r2)
:= λ S r1 r2 d1 d2,  
       match d1 with 
       | inl ref1 => 
         match d2 with 
         | inl ref2     => inl _ (brel_conjunction_reflexive S r1 r2 ref1 ref2)
         | inr not_ref2 => inr _ (brel_conjunction_not_reflexive_right S r1 r2 not_ref2)
         end 
       | inr not_ref1   => inr _ (brel_conjunction_not_reflexive_left S r1 r2 not_ref1)
       end. 


Lemma brel_conjunction_asymmetric_left : ∀ (S : Type) (r1 : brel S) (r2 : brel S),  
              (brel_asymmetric S r1) → 
                  brel_asymmetric S (r1 <&> r2). 
Proof. unfold brel_asymmetric, brel_conjunction.  
     intros S r1 r2 asy s t H. apply andb_is_true_left in H. destruct H as [L _]. 
     rewrite (asy _ _ L). compute. reflexivity. 
Defined. 

Lemma brel_conjunction_asymmetric_right : ∀ (S : Type) (r1 : brel S) (r2 : brel S),  
              (brel_asymmetric S r2) → 
                  brel_asymmetric S (r1 <&> r2). 
Proof. unfold brel_asymmetric, brel_conjunction.  
     intros S r1 r2 asy s t H. apply andb_is_true_left in H. destruct H as [_ R]. 
     rewrite (asy _ _ R). apply andb_comm.  
Defined. 


Lemma brel_conjunction_antisymmetric : 
         ∀ (S : Type) (eq : brel S) (r1 : brel S) (r2 : brel S),  
              (brel_antisymmetric S eq r1) + (brel_antisymmetric S eq r2) → 
              
              brel_antisymmetric S eq (r1 <&> r2). 
Proof. unfold brel_antisymmetric, brel_conjunction. 
     intros S eq r1 r2 [anti | anti] s t H1 H2. 
        destruct (andb_is_true_left _ _ H1) as [L1 _]; 
        destruct (andb_is_true_left _ _ H2) as [L2 _]. apply (anti _ _ L1 L2). 

        destruct (andb_is_true_left _ _ H1) as [_ R1]; 
        destruct (andb_is_true_left _ _ H2) as [_ R2]. apply (anti _ _ R1 R2). 
Defined. 
*) 

End Conjunction. 