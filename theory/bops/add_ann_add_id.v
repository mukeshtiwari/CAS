Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.properties. 


Lemma bops_add_ann_add_id_id_equals_ann :    
      ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S), 
      brel_reflexive S r -> 
      bops_id_equals_ann S r b1 b2 -> 
           bops_id_equals_ann 
              (with_constant S) 
              (brel_add_constant S r c) 
              (bop_add_ann S b1 c) 
              (bop_add_id S b2 c). 
Proof. unfold bops_id_equals_ann. 
       intros S r c b1 b2 refS [[i Pi] [[a Pa] H]]. 
       simpl in H. 
       assert (fact1 : bop_is_id (with_constant S) (brel_add_constant S r c) (bop_add_ann S b1 c) (inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       assert (fact2 : bop_is_ann (with_constant S) (brel_add_constant S r c) (bop_add_id S b2 c) (inr _ a)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       exists (existT _ (inr _ i) fact1). exists (existT _ (inr _ a) fact2). 
       compute. assumption. 
Defined. 



Lemma bops_add_ann_add_id_left_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
(*     brel_congruence S r r -> *) 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 ->          
     bops_left_left_absorptive S r b1 b2 -> 
     bops_right_left_absorptive S r b1 b2 -> 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 refS symS idemS laS raS ld. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. 
Qed. 


Lemma bops_add_ann_add_id_not_left_distributive_v1 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_left_distributive_v2 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_distributive_v3 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_left_absorptive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_left_distributive_v4 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_left_absorptive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 s3] nla]. 
       exists (inr s1, (inr s3, inl c)). compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_right_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
(*     brel_congruence S r r -> *) 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 ->          
     bops_left_right_absorptive S r b1 b2 -> 
     bops_right_right_absorptive S r b1 b2 -> 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 refS symS idemS laS raS rd. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto.  
Qed. 

Lemma bops_add_ann_add_id_not_right_distributive_v1 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_distributive_v2 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_distributive_v3 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_right_absorptive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_right_distributive_v4 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_right_absorptive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 s3] nla]. 
       exists (inr s1, (inr s3, inl c)). compute. assumption. 
Defined. 


(* all new *) 

(* left left *) 
Lemma bops_add_ann_add_id_left_left_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bops_left_left_absorptive S r b1 b2 -> 
        bops_left_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_left_left_absorptive_v1  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bops_not_left_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_left_absorptive_v2  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_left_absorptive S r b1 b2 -> 
        bops_not_left_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 




(* left right *) 
Lemma bops_add_ann_add_id_left_right_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bops_left_right_absorptive S r b1 b2 -> 
        bops_left_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_left_right_absorptive_v1  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bops_not_left_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_right_absorptive_v2  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_right_absorptive S r b1 b2 -> 
        bops_not_left_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right left *) 
Lemma bops_add_ann_add_id_right_left_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bops_right_left_absorptive S r b1 b2 -> 
        bops_right_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_right_left_absorptive_v1  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bops_not_right_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_left_absorptive_v2  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_left_absorptive S r b1 b2 -> 
        bops_not_right_left_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right right *) 
Lemma bops_add_ann_add_id_right_right_absorptive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bops_right_right_absorptive S r b1 b2 -> 
        bops_right_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_right_right_absorptive_v1  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bops_not_right_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_right_absorptive_v2  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_right_absorptive S r b1 b2 -> 
        bops_not_right_right_absorptive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


