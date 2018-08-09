Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties.

Section AddAnnId.

  Variable S : Type.
  Variable r : brel S.
  Variable c : cas_constant.
  Variable b1 b2 : binary_op S.

  Variable wS : S. 
  Variable refS : brel_reflexive S r. 
  Variable symS : brel_symmetric S r.

Notation "a <+> b"    := (brel_add_constant b a) (at level 15).
Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).
  

Lemma bops_add_ann_add_id_id_equals_ann :    
      bops_id_equals_ann S r b1 b2 -> bops_id_equals_ann (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. unfold bops_id_equals_ann. 
       intros [i [Pi Pa]]. exists (inr _ i). 
       assert (fact1 : bop_is_id (with_constant S) (c <+> r) (c [+ann] b1) (inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       assert (fact2 : bop_is_ann (with_constant S) (c <+> r) (c [+id] b2)(inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       split; assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_id_equals_ann :
  bops_not_id_equals_ann S r b1 b2 -> bops_not_id_equals_ann (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2).
Proof. unfold bops_not_id_equals_ann. intros H [cn | s ]. 
       left. unfold bop_not_is_id. exists (inr _ wS). compute; auto.
       destruct (H s) as [ [s'' [L | R]] | [s'' [L | R]]].
       left. exists (inr _ s''). compute. rewrite L. left. reflexivity. 
       left. exists (inr _ s''). compute. rewrite R. right. reflexivity. 
       right. exists (inr _ s''). compute. rewrite L. left. reflexivity. 
       right. exists (inr _ s''). compute. rewrite R. right. reflexivity. 
Defined.    

Lemma bops_add_ann_add_id_left_distributive  : 
     bop_idempotent S r b1 ->          
     bops_left_left_absorptive S r b1 b2 -> 
     bops_right_left_absorptive S r b1 b2 -> 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS laS raS ld. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. 
Qed. 


Lemma bops_add_ann_add_id_not_left_distributive_v1 : 
      bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_left_distributive_v2 : 
     bop_not_idempotent S r b1 -> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_distributive_v3 : 
     bops_not_left_left_absorptive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_distributive_v4 : 
     bops_not_right_left_absorptive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inr s3, inl c)). compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_left_distributive  : 
     (bop_not_idempotent S r b1 + 
     bops_not_left_left_absorptive S r b1 b2 +
     bops_not_right_left_absorptive S r b1 b2 +
     bop_not_left_distributive S r b1 b2)-> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[[NID | NLLA] | NRLA] | NLD].
       apply bops_add_ann_add_id_not_left_distributive_v2; auto.
       apply bops_add_ann_add_id_not_left_distributive_v3; auto.               
       apply bops_add_ann_add_id_not_left_distributive_v4; auto.        
       apply bops_add_ann_add_id_not_left_distributive_v1; auto.        
Qed. 



Lemma bops_add_ann_add_id_right_distributive  : 
     bop_idempotent S r b1 ->          
     bops_left_right_absorptive S r b1 b2 -> 
     bops_right_right_absorptive S r b1 b2 -> 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS laS raS rd. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto.  
Qed. 

Lemma bops_add_ann_add_id_not_right_distributive_v1 : 
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_distributive_v2 : 
     bop_not_idempotent S r b1 -> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_distributive_v3 : 
     bops_not_left_right_absorptive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_right_distributive_v4 : 
     bops_not_right_right_absorptive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inr s3, inl c)). compute. assumption. 
Defined.

Lemma bops_add_ann_add_id_not_right_distributive  : 
     (bop_not_idempotent S r b1 + 
     bops_not_left_right_absorptive S r b1 b2 +
     bops_not_right_right_absorptive S r b1 b2 +
     bop_not_right_distributive S r b1 b2)-> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[[NID | NLLA] | NRLA] | NLD].
       apply bops_add_ann_add_id_not_right_distributive_v2; auto.
       apply bops_add_ann_add_id_not_right_distributive_v3; auto.               
       apply bops_add_ann_add_id_not_right_distributive_v4; auto.        
       apply bops_add_ann_add_id_not_right_distributive_v1; auto.        
Qed. 



(* all new *) 

(* left left *) 
Lemma bops_add_ann_add_id_left_left_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_left_left_absorptive S r b1 b2 -> 
        bops_left_left_absorptive (with_constant S)  (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_left_left_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_left_left_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_left_absorptive_v2  : 
     bops_not_left_left_absorptive S r b1 b2 -> 
        bops_not_left_left_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined.


Lemma bops_add_ann_add_id_not_left_left_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_left_left_absorptive S r b1 b2) -> 
        bops_not_left_left_absorptive (with_constant S)  (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NLLA].
       apply bops_add_ann_add_id_not_left_left_absorptive_v1; auto.
       apply bops_add_ann_add_id_not_left_left_absorptive_v2; auto.   
Qed. 

(* left right *) 
Lemma bops_add_ann_add_id_left_right_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_left_right_absorptive S r b1 b2 -> 
        bops_left_right_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_left_right_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_left_right_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_right_absorptive_v2  : 
     bops_not_left_right_absorptive S r b1 b2 -> 
        bops_not_left_right_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


Lemma bops_add_ann_add_id_not_left_right_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_left_right_absorptive S r b1 b2) -> 
        bops_not_left_right_absorptive (with_constant S)  (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NLRA].
       apply bops_add_ann_add_id_not_left_right_absorptive_v1; auto.
       apply bops_add_ann_add_id_not_left_right_absorptive_v2; auto.   
Qed. 


(* right left *) 
Lemma bops_add_ann_add_id_right_left_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_right_left_absorptive S r b1 b2 -> 
        bops_right_left_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_right_left_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_right_left_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_left_absorptive_v2  : 
     bops_not_right_left_absorptive S r b1 b2 -> 
        bops_not_right_left_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

Lemma bops_add_ann_add_id_not_right_left_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_right_left_absorptive S r b1 b2) -> 
        bops_not_right_left_absorptive (with_constant S)  (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NRLA].
       apply bops_add_ann_add_id_not_right_left_absorptive_v1; auto.
       apply bops_add_ann_add_id_not_right_left_absorptive_v2; auto.   
Qed. 


(* right right *) 
Lemma bops_add_ann_add_id_right_right_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_right_right_absorptive S r b1 b2 -> 
        bops_right_right_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_right_right_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_right_right_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_right_absorptive_v2  : 
     bops_not_right_right_absorptive S r b1 b2 -> 
        bops_not_right_right_absorptive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined.

Lemma bops_add_ann_add_id_not_right_right_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_right_right_absorptive S r b1 b2) -> 
        bops_not_right_right_absorptive (with_constant S)  (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NRRA].
       apply bops_add_ann_add_id_not_right_right_absorptive_v1; auto.
       apply bops_add_ann_add_id_not_right_right_absorptive_v2; auto.   
Qed. 




(* experiment 

Lemma bops_add_ann_add_id_left_left_dependent_distributive  : 
     bop_idempotent S r b1 ->          
     bops_left_left_absorptive S r b1 b2 -> 
     bops_left_left_dependent_distributive S r b1 b2 -> 
        bops_left_left_dependent_distributive (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la ld. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; intro H; auto.  
       discriminate. 
Qed.
 *)



Definition bops_add_one_left_distributive_decide : 
     bop_idempotent_decidable S r b1 -> 
     bops_left_left_absorptive_decidable S r b1 b2 -> 
     bops_right_left_absorptive_decidable S r b1 b2 -> 
     bop_left_distributive_decidable S r b1 b2 -> 
     bop_left_distributive_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2)
:= λ idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | inl ldS  => 
    match llaS_d with 
    | inl llaS   => 
      match rlaS_d with 
      | inl rlaS   => 
         match idemS_d with 
         | inl idemS   => inl _ (bops_add_ann_add_id_left_distributive idemS llaS rlaS ldS)
         | inr nidemS  => inr _ (bops_add_ann_add_id_not_left_distributive_v2 nidemS)
        end 
      | inr nrlaS   => inr _ (bops_add_ann_add_id_not_left_distributive_v4 nrlaS)
      end 
    | inr nllaS  => inr _ (bops_add_ann_add_id_not_left_distributive_v3 nllaS)
    end 
   | inr nldS => inr _ (bops_add_ann_add_id_not_left_distributive_v1 nldS)
   end. 

Definition bops_add_one_right_distributive_decide : 
     bop_idempotent_decidable S r b1 -> 
     bops_left_right_absorptive_decidable S r b1 b2 -> 
     bops_right_right_absorptive_decidable S r b1 b2 -> 
     bop_right_distributive_decidable S r b1 b2 -> 
     bop_right_distributive_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2)
:= λ idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | inl ldS  => 
    match llaS_d with 
    | inl llaS   => 
      match rlaS_d with 
      | inl rlaS   => 
         match idemS_d with 
         | inl idemS   => inl _ (bops_add_ann_add_id_right_distributive idemS llaS rlaS ldS)
         | inr nidemS  => inr _ (bops_add_ann_add_id_not_right_distributive_v2 nidemS)
        end 
      | inr nrlaS   => inr _ (bops_add_ann_add_id_not_right_distributive_v4 nrlaS)
      end 
    | inr nllaS  => inr _ (bops_add_ann_add_id_not_right_distributive_v3 nllaS)
    end 
   | inr nldS => inr _ (bops_add_ann_add_id_not_right_distributive_v1 nldS)
   end. 


Definition bops_add_one_left_left_absorptive_decide : 
     bop_idempotent_decidable S r b1 -> 
     bops_left_left_absorptive_decidable S r b1 b2 -> 
        bops_left_left_absorptive_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2)
:= λ idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_left_left_absorptive idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_left_left_absorptive_v1 nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_left_left_absorptive_v2 nlaS)
   end. 


Definition bops_add_one_left_right_absorptive_decide : 
     bop_idempotent_decidable S r b1 -> 
     bops_left_right_absorptive_decidable S r b1 b2 -> 
     bops_left_right_absorptive_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2)
:= λ idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_left_right_absorptive idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_left_right_absorptive_v1 nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_left_right_absorptive_v2 nlaS)
   end. 

Definition bops_add_one_right_left_absorptive_decide : 
     bop_idempotent_decidable S r b1 -> 
     bops_right_left_absorptive_decidable S r b1 b2 -> 
     bops_right_left_absorptive_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2)
:= λ idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_right_left_absorptive idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_right_left_absorptive_v1 nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_right_left_absorptive_v2 nlaS)
   end. 

Definition bops_add_one_right_right_absorptive_decide : 
     bop_idempotent_decidable S r b1 -> 
     bops_right_right_absorptive_decidable S r b1 b2 -> 
     bops_right_right_absorptive_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2)
:= λ idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_right_right_absorptive idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_right_right_absorptive_v1 nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_right_right_absorptive_v2 nlaS)
   end.


Definition bops_add_one_id_equals_ann_decide :
     bops_id_equals_ann_decidable S r b1 b2 -> 
        bops_id_equals_ann_decidable (with_constant S) (c <+> r) (c [+ann] b1) (c [+id] b2) 
:= λ dS, 
   match dS with 
   | inl pS  => inl _ (bops_add_ann_add_id_id_equals_ann pS)
   | inr npS => inr _ (bops_add_ann_add_id_not_id_equals_ann npS)
   end. 



End AddAnnId.