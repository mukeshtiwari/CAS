Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 


Lemma brel_add_top_congruence : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
       brel_congruence S rS rS → 
         brel_congruence (with_constant S) 
                         (brel_add_constant S rS c) 
                         (brel_add_top S rS c). 
Proof. intros S rS c congS [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto; discriminate. Qed. 
Lemma brel_add_top_witness : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
              (brel_witness S rS) → brel_witness (with_constant S) (brel_add_top S rS c). 
Proof.  intros S rS c [s Ps]. exists (inr _ s). simpl. rewrite Ps. reflexivity. Defined. 

Lemma brel_add_top_reflexive : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
          brel_reflexive S rS → brel_reflexive (with_constant S) (brel_add_top S rS c). 
Proof. intros S rS c refS [a | b]; simpl. reflexivity. apply refS. Qed. 

Lemma brel_add_top_transitive : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
    (brel_transitive _ rS) → brel_transitive (with_constant S) (brel_add_top S rS c). 
Proof. unfold brel_transitive. 
     intros S rS c transS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros H1 H2; auto. 
     discriminate. apply (transS _ _ _ H1 H2). 
Qed. 

Lemma brel_add_top_antisymmetric : ∀ (S : Type) (eqS rS : brel S) (c : cas_constant),  
      (brel_antisymmetric _ eqS rS) → 
         brel_antisymmetric (with_constant S) (brel_add_constant S eqS c)(brel_add_top S rS c). 
Proof. intros S eqS rS c symS [c1 | s1] [c2 | s2]; simpl; intro H; auto. Qed. 


Lemma brel_add_top_not_antisymmetric : ∀ (S : Type) (eqS rS : brel S) (c : cas_constant),  
      (brel_not_antisymmetric _ eqS rS) → 
         brel_not_antisymmetric (with_constant S) (brel_add_constant S eqS c)(brel_add_top S rS c). 
Proof.  unfold brel_symmetric. intros S eqS rS c [[s t] P]. 
        exists (inr _ s, inr _ t). compute. assumption. 
Defined. 


Lemma brel_add_top_total : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
      (brel_total _ rS) → brel_total (with_constant S) (brel_add_top S rS c). 
Proof.  intros S rS c symS [c1 | s1] [c2 | s2]; simpl; auto.  Qed. 

Lemma brel_add_top_not_total : ∀ (S : Type) (rS : brel S) (c : cas_constant),  
      (brel_not_total _ rS) → brel_not_total (with_constant S) (brel_add_top S rS c). 
Proof.  intros S rS c [[s t] P]. exists (inr _ s, inr _ t). compute. assumption. Defined. 




