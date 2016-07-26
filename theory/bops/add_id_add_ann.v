Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.properties. 


Lemma bops_add_id_add_ann_id_equals_ann :    
      ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S), 
      brel_reflexive S r -> 
           bops_id_equals_ann 
              (with_constant S) 
              (brel_add_constant S r c) 
              (bop_add_id S b1 c) 
              (bop_add_ann S b2 c). 
Proof. unfold bops_id_equals_ann. intros S r c b1 b2 refS. 
       assert (is_id : bop_is_id (with_constant S) (brel_add_constant S r c) 
                          (bop_add_id S b1 c) (inl c)). 
           intros [c' | s ]; compute; auto. 
       assert (is_ann : bop_is_ann (with_constant S) (brel_add_constant S r c) 
                          (bop_add_ann S b2 c) (inl c)). 
           intros [c' | s ]; compute; auto. 
       exists (existT _ (inl _ c) is_id). exists (existT _ (inl _ c) is_ann). 
       compute. reflexivity. 
Defined. 

Lemma bops_add_id_add_ann_ann_equals_id :    
      ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S), 
      brel_reflexive S r -> 
      bops_id_equals_ann S r b2 b1 -> 
           bops_id_equals_ann 
              (with_constant S) 
              (brel_add_constant S r c) 
              (bop_add_ann S b2 c)
              (bop_add_id S b1 c). 
Proof. unfold bops_id_equals_ann. intros S r c b1 b2 refS
       [ [i Pi] [[a Pa] P]]. compute in P.  
       assert (is_id : bop_is_id (with_constant S) (brel_add_constant S r c) 
                          (bop_add_ann S b2 c) (inr i)). 
           intros [c' | s ]; compute; auto. 
       assert (is_ann : bop_is_ann (with_constant S) (brel_add_constant S r c) 
                          (bop_add_id S b1 c) (inr a)). 
           intros [c' | s ]; compute; auto. 
       exists (existT _ (inr _ i) is_id). exists (existT _ (inr _ a) is_ann). 
       compute. assumption. 
Defined. 


Lemma bops_add_id_add_ann_not_ann_equals_id :    
      ∀ (S : Type) (r : brel S) (s : S) (c : cas_constant) (b1 b2 : binary_op S), 
      bops_not_id_equals_ann S r b2 b1 -> 
           bops_not_id_equals_ann 
              (with_constant S) 
              (brel_add_constant S r c) 
              (bop_add_ann S b2 c)
              (bop_add_id S b1 c). 
Proof. unfold bops_not_id_equals_ann. 
       intros S r s c b1 b2 H [ci | i] [ca | a] H_id H_ann; compute; auto. 
       assert (A := H_id (inr s)).  compute in A. destruct A as [L R]. discriminate. 
       assert (Id : bop_is_id S r b2 i). 
          unfold bop_is_id. intro s0. 
          assert (A := H_id (inr s0)).  compute in A.           
          assumption. 
       assert (An : bop_is_ann S r b1 a). 
          unfold bop_is_ann. intro s0. 
          assert (A := H_ann (inr s0)).  compute in A.           
          assumption. 
       apply H; auto.
Defined. 


Lemma bops_add_id_add_ann_left_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_reflexive S r -> 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 refS ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 


Lemma bops_add_id_add_ann_not_left_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 [ [s1 [s2 s3]] nldS]. 
       exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 

Lemma bops_add_id_add_ann_right_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_reflexive S r -> 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 refS ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 [ [s1 [s2 s3]] nldS]. 
       exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 


(* left left *) 
Lemma bops_add_id_add_ann_left_left_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_reflexive S r -> 
     bops_left_left_absorptive S r b1 b2 -> 
        bops_left_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 refS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_left_absorptive : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_left_absorptive S r b1 b2 -> 
        bops_not_left_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

(* left right *) 
Lemma bops_add_id_add_ann_left_right_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_reflexive S r -> 
     bops_left_right_absorptive S r b1 b2 -> 
        bops_left_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 refS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_right_absorptive : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_right_absorptive S r b1 b2 -> 
        bops_not_left_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right left *) 
Lemma bops_add_id_add_ann_right_left_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_reflexive S r -> 
     bops_right_left_absorptive S r b1 b2 -> 
        bops_right_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 refS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_left_absorptive : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_left_absorptive S r b1 b2 -> 
        bops_not_right_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right right *) 
Lemma bops_add_id_add_ann_right_right_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_reflexive S r -> 
     bops_right_right_absorptive S r b1 b2 -> 
        bops_right_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 refS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_right_absorptive : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_right_absorptive S r b1 b2 -> 
        bops_not_right_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_id S b1 c) (bop_add_ann S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 




