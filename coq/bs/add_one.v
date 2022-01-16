Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.add_constant.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.
Require Import CAS.coq.sg.cast_up. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 
Require Import CAS.coq.bs.theory. 


Section Theory.

Variable S : Type.
Variable r : brel S.
Variable c : cas_constant.
Variable b1 b2 : binary_op S.

Variable wS : S. 
Variable refS : brel_reflexive S r. 
Variable symS : brel_symmetric S r.

Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).
  

Lemma bops_add_one_exists_id_ann_equal_left :    
  bops_exists_id_ann_equal S r b1 b2 ->
  bops_exists_id_ann_equal (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [i [Pi Pa]]. exists (inr _ i). 
       assert (fact1 : bop_is_id (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       assert (fact2 : bop_is_ann (with_constant S) (brel_sum brel_constant r) (c [+id] b2)(inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       split; assumption. 
Defined.

Lemma bops_add_one_exists_id_ann_equal_right :    
  bops_exists_id_ann_equal (with_constant S) (brel_sum brel_constant r) (c [+id] b2) (c [+ann] b1). 
Proof. exists (inl _ c). split. 
       apply bop_add_id_is_id; auto. 
       apply bop_add_ann_is_ann; auto. 
Defined. 


Lemma bops_add_one_exists_id_ann_not_equal_left :
  bops_exists_id_ann_not_equal S r b1 b2 ->
  bops_exists_id_ann_not_equal (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [[id ann] [[A B] C]]. 
       exists (inr id, inr ann). split. split.
       intros [c' | s]; compute; auto.
       intros [c' | s]; compute; auto.          
       compute; auto. 
Defined.    


Lemma bops_add_one_left_monotone  :
     bop_idempotent S r b1 ->
     bops_left_left_absorptive S r b1 b2 ->   
     bop_left_monotone S r b1 b2 -> 
        bop_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idem lla lm [c1 | s1] [c2 | s2] [c3 | s3]; compute; intro A; auto.
         discriminate A. 
Qed. 

(*
bops_left_left_absorptive  : s = s + st 
bops_right_left_absorptive : s = st + s 


note:  comm(+) * left_abs * idem(+) -> 
       (left_monotone <-> left_distributive)

Why is this here? 
*)

Lemma bops_add_one_not_left_monotone_v1  :
     bop_not_left_monotone S r b1 b2 -> 
     bop_not_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined.

Lemma bops_add_one_not_left_monotone_v2  :
     bop_not_idempotent S r b1 -> 
     bop_not_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. split; auto. 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 

Lemma bops_add_one_not_left_monotone_v3  :
  bops_not_left_left_absorptive S r b1 b2 -> 
     bop_not_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. split; auto. 
Defined. 

Lemma bops_add_one_left_distributive  : 
     bop_idempotent S r b1 ->          
     bops_left_left_absorptive S r b1 b2 -> 
     bops_right_left_absorptive S r b1 b2 -> 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS laS raS ld. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. 
Qed. 


Lemma bops_add_one_not_left_distributive_v1 : 
      bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 


Lemma bops_add_one_not_left_distributive_v2 : 
     bop_not_idempotent S r b1 -> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 

Lemma bops_add_one_not_left_distributive_v3 : 
     bops_not_left_left_absorptive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 

Lemma bops_add_one_not_left_distributive_v4 : 
     bops_not_right_left_absorptive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inr s3, inl c)). compute. assumption. 
Defined. 


Lemma bops_add_one_not_left_distributive  : 
     (bop_not_idempotent S r b1 + 
     bops_not_left_left_absorptive S r b1 b2 +
     bops_not_right_left_absorptive S r b1 b2 +
     bop_not_left_distributive S r b1 b2)-> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[[NID | NLLA] | NRLA] | NLD].
       apply bops_add_one_not_left_distributive_v2; auto.
       apply bops_add_one_not_left_distributive_v3; auto.               
       apply bops_add_one_not_left_distributive_v4; auto.        
       apply bops_add_one_not_left_distributive_v1; auto.        
Defined. 



Lemma bops_add_one_right_distributive  : 
     bop_idempotent S r b1 ->          
     bops_left_right_absorptive S r b1 b2 -> 
     bops_right_right_absorptive S r b1 b2 -> 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS laS raS rd. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto.  
Qed. 

Lemma bops_add_one_not_right_distributive_v1 : 
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 

Lemma bops_add_one_not_right_distributive_v2 : 
     bop_not_idempotent S r b1 -> 
        bop_not_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_one_not_right_distributive_v3 : 
     bops_not_left_right_absorptive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 


Lemma bops_add_one_not_right_distributive_v4 : 
     bops_not_right_right_absorptive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inr s3, inl c)). compute. assumption. 
Defined.

Lemma bops_add_one_not_right_distributive  : 
     (bop_not_idempotent S r b1 + 
     bops_not_left_right_absorptive S r b1 b2 +
     bops_not_right_right_absorptive S r b1 b2 +
     bop_not_right_distributive S r b1 b2)-> 
        bop_not_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[[NID | NLLA] | NRLA] | NLD].
       apply bops_add_one_not_right_distributive_v2; auto.
       apply bops_add_one_not_right_distributive_v3; auto.               
       apply bops_add_one_not_right_distributive_v4; auto.        
       apply bops_add_one_not_right_distributive_v1; auto.        
Defined. 



(* all new *) 

(* left left *) 
Lemma bops_add_one_left_left_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_left_left_absorptive S r b1 b2 -> 
        bops_left_left_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_one_not_left_left_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_left_left_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_one_not_left_left_absorptive_v2  : 
     bops_not_left_left_absorptive S r b1 b2 -> 
        bops_not_left_left_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined.


Lemma bops_add_one_not_left_left_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_left_left_absorptive S r b1 b2) -> 
        bops_not_left_left_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NLLA].
       apply bops_add_one_not_left_left_absorptive_v1; auto.
       apply bops_add_one_not_left_left_absorptive_v2; auto.   
Defined. 

(* left right *) 
Lemma bops_add_one_left_right_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_left_right_absorptive S r b1 b2 -> 
        bops_left_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_one_not_left_right_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_left_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_one_not_left_right_absorptive_v2  : 
     bops_not_left_right_absorptive S r b1 b2 -> 
        bops_not_left_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


Lemma bops_add_one_not_left_right_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_left_right_absorptive S r b1 b2) -> 
        bops_not_left_right_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NLRA].
       apply bops_add_one_not_left_right_absorptive_v1; auto.
       apply bops_add_one_not_left_right_absorptive_v2; auto.   
Defined. 


(* right left *) 
Lemma bops_add_one_right_left_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_right_left_absorptive S r b1 b2 -> 
        bops_right_left_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_one_not_right_left_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_right_left_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_one_not_right_left_absorptive_v2  : 
     bops_not_right_left_absorptive S r b1 b2 -> 
        bops_not_right_left_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

Lemma bops_add_one_not_right_left_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_right_left_absorptive S r b1 b2) -> 
        bops_not_right_left_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NRLA].
       apply bops_add_one_not_right_left_absorptive_v1; auto.
       apply bops_add_one_not_right_left_absorptive_v2; auto.   
Defined. 


(* right right *) 
Lemma bops_add_one_right_right_absorptive  : 
     bop_idempotent S r b1 -> 
     bops_right_right_absorptive S r b1 b2 -> 
        bops_right_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_one_not_right_right_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        bops_not_right_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_one_not_right_right_absorptive_v2  : 
     bops_not_right_right_absorptive S r b1 b2 -> 
        bops_not_right_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined.

Lemma bops_add_one_not_right_right_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_right_right_absorptive S r b1 b2) -> 
        bops_not_right_right_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NRRA].
       apply bops_add_one_not_right_right_absorptive_v1; auto.
       apply bops_add_one_not_right_right_absorptive_v2; auto.   
Defined. 

End Theory.

Section ACAS.

Section Decide.

Variable S : Type.
Variable r : brel S.
Variable c : cas_constant.
Variable b1 b2 : binary_op S.
Variable wS : S. 
Variable eqv : eqv_proofs S r. 

Definition bops_add_one_left_distributive_decide 
     (idemS_d : bop_idempotent_decidable S r b1)
     (llaS_d  : bops_left_left_absorptive_decidable S r b1 b2)
     (rlaS_d  : bops_right_left_absorptive_decidable S r b1 b2)
     (ldS_d   : bop_left_distributive_decidable S r b1 b2) : 
  bop_left_distributive_decidable (with_constant S)
                                  (brel_sum brel_constant r)
                                  (bop_add_ann b1 c)
                                  (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  let ref := A_eqv_reflexive S r eqv in   
   match ldS_d with 
   | inl ldS  => 
    match llaS_d with 
    | inl llaS   => 
      match rlaS_d with 
      | inl rlaS   => 
         match idemS_d with 
         | inl idemS   => inl _ (bops_add_one_left_distributive S r c b1 b2 ref sym idemS llaS rlaS ldS)
         | inr nidemS  => inr _ (bops_add_one_not_left_distributive_v2 S r c b1 b2 sym nidemS)
        end 
      | inr nrlaS   => inr _ (bops_add_one_not_left_distributive_v4 S r c b1 b2 nrlaS)
      end 
    | inr nllaS  => inr _ (bops_add_one_not_left_distributive_v3 S r c b1 b2 nllaS)
    end 
   | inr nldS => inr _ (bops_add_one_not_left_distributive_v1 S r c b1 b2 nldS)
   end. 

Definition bops_add_one_right_distributive_decide 
     (idemS_d : bop_idempotent_decidable S r b1)
     (llaS_d  : bops_left_right_absorptive_decidable S r b1 b2)
     (rlaS_d  : bops_right_right_absorptive_decidable S r b1 b2)
     (ldS_d   : bop_right_distributive_decidable S r b1 b2) : 
 bop_right_distributive_decidable (with_constant S) 
                                  (brel_sum brel_constant r)
                                  (bop_add_ann b1 c)
                                  (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  let ref := A_eqv_reflexive S r eqv in   
  match ldS_d with 
   | inl ldS  => 
    match llaS_d with 
    | inl llaS   => 
      match rlaS_d with 
      | inl rlaS   => 
         match idemS_d with 
         | inl idemS   => inl _ (bops_add_one_right_distributive S r c b1 b2 ref sym idemS llaS rlaS ldS)
         | inr nidemS  => inr _ (bops_add_one_not_right_distributive_v2 S r c b1 b2 sym nidemS)
        end 
      | inr nrlaS   => inr _ (bops_add_one_not_right_distributive_v4 S r c b1 b2 nrlaS)
      end 
    | inr nllaS  => inr _ (bops_add_one_not_right_distributive_v3 S r c b1 b2 nllaS)
    end 
   | inr nldS => inr _ (bops_add_one_not_right_distributive_v1 S r c b1 b2 nldS)
   end. 

Definition bops_add_one_left_left_absorptive_decide  
     (idemS_d : bop_idempotent_decidable S r b1)
     (laS_d   : bops_left_left_absorptive_decidable S r b1 b2) : 
  bops_left_left_absorptive_decidable (with_constant S)
                                      (brel_sum brel_constant r)
                                      (bop_add_ann b1 c)
                                      (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_one_left_left_absorptive S r c b1 b2 sym idemS laS)
     | inr nidemS => inr _ (bops_add_one_not_left_left_absorptive_v1 S r c b1 b2 sym nidemS)
     end 
   | inr nlaS => inr _ (bops_add_one_not_left_left_absorptive_v2 S r c b1 b2 nlaS)
   end. 


Definition bops_add_one_left_right_absorptive_decide
     (idemS_d  : bop_idempotent_decidable S r b1)
     (laS_d    : bops_left_right_absorptive_decidable S r b1 b2) :  
  bops_left_right_absorptive_decidable (with_constant S)
                                       (brel_sum brel_constant r)
                                       (bop_add_ann b1 c)
                                       (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_one_left_right_absorptive S r c b1 b2 sym idemS laS)
     | inr nidemS => inr _ (bops_add_one_not_left_right_absorptive_v1 S r c b1 b2 sym nidemS)
     end 
   | inr nlaS => inr _ (bops_add_one_not_left_right_absorptive_v2 S r c b1 b2 nlaS)
   end. 

Definition bops_add_one_right_left_absorptive_decide 
     (idemS_d : bop_idempotent_decidable S r b1)
     (laS_d   : bops_right_left_absorptive_decidable S r b1 b2) : 
     bops_right_left_absorptive_decidable (with_constant S) 
                                          (brel_sum brel_constant r)
                                          (bop_add_ann b1 c)
                                          (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_one_right_left_absorptive S r c b1 b2 sym idemS laS)
     | inr nidemS => inr _ (bops_add_one_not_right_left_absorptive_v1 S r c b1 b2 sym nidemS)
     end 
   | inr nlaS => inr _ (bops_add_one_not_right_left_absorptive_v2 S r c b1 b2 nlaS)
   end. 

Definition bops_add_one_right_right_absorptive_decide 
     (idemS_d : bop_idempotent_decidable S r b1)
     (laS_d   : bops_right_right_absorptive_decidable S r b1 b2) : 
     bops_right_right_absorptive_decidable (with_constant S) 
                                          (brel_sum brel_constant r)
                                          (bop_add_ann b1 c)
                                          (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_one_right_right_absorptive S r c b1 b2 sym idemS laS)
     | inr nidemS => inr _ (bops_add_one_not_right_right_absorptive_v1 S r c b1 b2 sym nidemS)
     end 
   | inr nlaS => inr _ (bops_add_one_not_right_right_absorptive_v2 S r c b1 b2 nlaS)
   end.

Definition bops_add_one_id_equals_ann_decide_left  
  (dS : exists_id_ann_decidable S r b1 b2) : 
  exists_id_ann_decidable (with_constant S) 
                          (brel_sum brel_constant r)
                          (bop_add_ann b1 c)
                          (bop_add_id b2 c) := 
let ref := A_eqv_reflexive S r eqv in   
match dS with                                 
| Id_Ann_Proof_None _ _ _ _ (nid, nann)           =>
  Id_Ann_Proof_None _ _ _ _ (bop_add_ann_not_exists_id S r c b1 wS nid,
                             bop_add_id_not_exists_ann S r c b2 wS nann)
| Id_Ann_Proof_Id_None _ _ _ _ (id, nann)         =>
  Id_Ann_Proof_Id_None _ _ _ _ (bop_add_ann_exists_id S r c b1 id,
                                bop_add_id_not_exists_ann S r c b2 wS nann)
| Id_Ann_Proof_None_Ann _ _ _ _ (nid, ann)        =>
  Id_Ann_Proof_None_Ann _ _ _ _ (bop_add_ann_not_exists_id S r c b1 wS nid,
                                 bop_add_id_exists_ann S r c b2 ref ann)     
| Id_Ann_Proof_Equal _ _ _ _ id_ann_equal         =>
  Id_Ann_Proof_Equal _ _ _ _ (bops_add_one_exists_id_ann_equal_left S r c b1 b2 ref id_ann_equal)
| Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_equal =>
  Id_Ann_Proof_Not_Equal _ _ _ _ (bops_add_one_exists_id_ann_not_equal_left S r c b1 b2 ref id_ann_not_equal)
end.

End Decide.       

Section Proofs.

Variables (S : Type)
          (rS : brel S)
          (c : cas_constant)
          (plusS timesS : binary_op S)
          (wS : S)
          (eqvS : eqv_proofs S rS). 



Definition id_ann_proofs_add_one 
     (pS : id_ann_proofs S rS plusS timesS) : 
        id_ann_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in 
{|
  A_id_ann_plus_times_d := bops_add_one_id_equals_ann_decide_left  S rS c plusS timesS wS eqvS (A_id_ann_plus_times_d _ _ _ _ pS) 
; A_id_ann_times_plus_d := Id_Ann_Proof_Equal _ _ _ _ (bops_add_one_exists_id_ann_equal_right S rS c plusS timesS ref)
|}.


Definition pann_is_tid_proofs_add_one 
     (pS : id_ann_proofs S rS plusS timesS) : 
        pann_is_tid_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in 
{|
  A_pann_is_tid_plus_times_d := bops_add_one_id_equals_ann_decide_left  S rS c plusS timesS wS eqvS (A_id_ann_plus_times_d _ _ _ _ pS) 
; A_pann_is_tid_times_plus   := bops_add_one_exists_id_ann_equal_right S rS c plusS timesS ref 
|}.


Definition dually_bounded_proofs_add_one 
     (pS : pid_is_tann_proofs  S rS plusS timesS) : 
        dually_bounded_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in
let q := A_pid_is_tann_plus_times _ _ _ _ pS in   
{|
  A_bounded_plus_id_is_times_ann := bops_add_one_exists_id_ann_equal_left S rS c plusS timesS ref q 
; A_bounded_times_id_is_plus_ann := bops_add_one_exists_id_ann_equal_right S rS c plusS timesS ref 
|}.


Definition bs_proofs_add_one 
     (ppS : sg_proofs S rS plusS)
     (pS : bs_proofs S rS plusS timesS) : 
        bs_proofs 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c) :=
let idemS_d := A_sg_idempotent_d S rS plusS ppS in
let LD  := A_bs_left_distributive_d S rS plusS timesS pS in 
let RD  := A_bs_right_distributive_d S rS plusS timesS pS in 
let LLA := A_bs_left_left_absorptive_d S rS plusS timesS pS in
let LRA := A_bs_left_right_absorptive_d S rS plusS timesS pS in 
let RLA := A_bs_right_left_absorptive_d S rS plusS timesS pS in 
let RRA := A_bs_right_right_absorptive_d S rS plusS timesS pS in 
{|
  A_bs_left_distributive_d    := 
     bops_add_one_left_distributive_decide S rS c plusS timesS eqvS idemS_d LLA RLA LD 
; A_bs_right_distributive_d   := 
     bops_add_one_right_distributive_decide S rS c plusS timesS eqvS idemS_d LRA RRA RD 
; A_bs_left_left_absorptive_d      := 
     bops_add_one_left_left_absorptive_decide S rS c plusS timesS eqvS idemS_d LLA 
; A_bs_left_right_absorptive_d      := 
     bops_add_one_left_right_absorptive_decide S rS c plusS timesS eqvS idemS_d LRA 
; A_bs_right_left_absorptive_d     := 
     bops_add_one_right_left_absorptive_decide S rS c plusS timesS eqvS idemS_d RLA 
; A_bs_right_right_absorptive_d     := 
     bops_add_one_right_right_absorptive_decide S rS c plusS timesS eqvS idemS_d RRA 
|}.

(* Note: This is another example (like llex) where we can combine semirings and obtain 
   something that is not a semiring, since distributivity depends on absorption. 

Record semiring_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_semiring_left_distributive        : bop_left_distributive S eq plus times 
; A_semiring_right_distributive       : bop_right_distributive S eq plus times 
; A_semiring_left_left_absorptive_d   : bops_left_left_absorptive_decidable S eq plus times 
; A_semiring_left_right_absorptive_d  : bops_left_right_absorptive_decidable S eq plus times 
}.
*) 

Definition dioid_proofs_add_one 
     (idem : bop_idempotent S rS plusS)
     (comm : bop_commutative S rS plusS)           
     (pS : dioid_proofs S rS plusS timesS) : 
        dioid_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c) :=
let ref := A_eqv_reflexive S rS eqvS in
let sym := A_eqv_symmetric S rS eqvS in
let trn := A_eqv_transitive S rS eqvS in   
let LD  := A_dioid_left_distributive S rS plusS timesS pS in 
let RD  := A_dioid_right_distributive S rS plusS timesS pS in 
let LLA := A_dioid_left_left_absorptive S rS plusS timesS pS in
let LRA := A_dioid_left_right_absorptive S rS plusS timesS pS in
let RLA := bops_left_left_absorptive_implies_right_left S rS plusS timesS trn comm LLA in 
let RRA := bops_left_right_absorptive_implies_right_right S rS plusS timesS trn comm LRA in 
{|
  A_dioid_left_distributive      := bops_add_one_left_distributive S rS c plusS timesS ref sym idem LLA RLA LD 
; A_dioid_right_distributive     := bops_add_one_right_distributive S rS c plusS timesS ref sym idem LRA RRA RD 
; A_dioid_left_left_absorptive   := bops_add_one_left_left_absorptive S rS c plusS timesS sym idem LLA 
; A_dioid_left_right_absorptive  := bops_add_one_left_right_absorptive S rS c plusS timesS sym idem LRA 
|}.


(* lattice proofs? distributed lattice proofs? *) 

End Proofs. 

Section Combinators. 

Definition A_bs_add_one (S : Type) (bsS : A_bs S) (c : cas_constant) : A_bs (with_constant S) := 
let eqvS  := A_bs_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_plus S bsS in
let times := A_bs_times S bsS in
let pproofs := A_bs_plus_proofs S bsS in
let tproofs := A_bs_times_proofs S bsS in 
{| 
     A_bs_eqv           := A_eqv_add_constant S eqvS c 
   ; A_bs_plus          := bop_add_ann plus c
   ; A_bs_times         := bop_add_id times c
   ; A_bs_plus_proofs   := sg_proofs_add_ann S rS c plus s f Pf peqvS pproofs 
   ; A_bs_times_proofs  := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_id_ann_proofs := id_ann_proofs_add_one  S rS c plus times s peqvS (A_bs_id_ann_proofs S bsS)
   ; A_bs_proofs        := bs_proofs_add_one S rS c plus times peqvS pproofs (A_bs_proofs S bsS)
   ; A_bs_ast           := Ast_bs_add_one (c, A_bs_ast S bsS)
|}.

(* the next two need CAS versions ... *) 
Definition A_bs_CI_add_one (S : Type) (bsS : A_bs_CI S) (c : cas_constant) : A_bs_CI (with_constant S) := 
let eqvS  := A_bs_CI_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_CI_plus S bsS in
let times := A_bs_CI_times S bsS in
let pproofs := A_bs_CI_plus_proofs S bsS in
let tproofs := A_bs_CI_times_proofs S bsS in 
{| 
     A_bs_CI_eqv           := A_eqv_add_constant S eqvS c 
   ; A_bs_CI_plus          := bop_add_ann plus c
   ; A_bs_CI_times         := bop_add_id times c
   ; A_bs_CI_plus_proofs   := sg_CI_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_bs_CI_times_proofs  := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_CI_id_ann_proofs := id_ann_proofs_add_one  S rS c plus times s peqvS (A_bs_CI_id_ann_proofs S bsS)
   ; A_bs_CI_proofs        := bs_proofs_add_one S rS c plus times peqvS
                                                (A_sg_proofs_from_sg_CI_proofs S rS plus s f Pf peqvS pproofs)
                                                (A_bs_CI_proofs S bsS)
   ; A_bs_CI_ast           := Ast_bs_add_one (c, A_bs_CI_ast S bsS)
|}.

Definition A_bs_CS_add_one (S : Type) (bsS : A_bs_CS S) (c : cas_constant) : A_bs_CS (with_constant S) := 
let eqvS  := A_bs_CS_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_CS_plus S bsS in
let times := A_bs_CS_times S bsS in
let pproofs := A_bs_CS_plus_proofs S bsS in
let tproofs := A_bs_CS_times_proofs S bsS in 
{| 
     A_bs_CS_eqv           := A_eqv_add_constant S eqvS c 
   ; A_bs_CS_plus          := bop_add_ann plus c
   ; A_bs_CS_times         := bop_add_id times c
   ; A_bs_CS_plus_proofs   := sg_CS_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_bs_CS_times_proofs  := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_CS_id_ann_proofs := id_ann_proofs_add_one  S rS c plus times s peqvS (A_bs_CS_id_ann_proofs S bsS)
   ; A_bs_CS_proofs        := bs_proofs_add_one S rS c plus times peqvS
                                                (A_sg_proofs_from_sg_CS_proofs S rS plus s f Pf peqvS pproofs)
                                                (A_bs_CS_proofs S bsS)
   ; A_bs_CS_ast           := Ast_bs_add_one (c, A_bs_CS_ast S bsS)
|}.


Definition A_add_one_to_pre_dioid : ∀ (S : Type),  A_pre_dioid S -> cas_constant -> A_pre_dioid_with_one (with_constant S) 
:= λ S bsS c,
let eqvS  := A_pre_dioid_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_pre_dioid_plus S bsS in
let times := A_pre_dioid_times S bsS in
let pproofs := A_pre_dioid_plus_proofs S bsS in
let tproofs := A_pre_dioid_times_proofs S bsS in
let idem   := A_sg_CI_idempotent _ _ _ pproofs in
let comm   := A_sg_CI_commutative _ _ _ pproofs in 
{| 
     A_pre_dioid_with_one_eqv          := A_eqv_add_constant S eqvS c 
   ; A_pre_dioid_with_one_plus         := bop_add_ann plus c
   ; A_pre_dioid_with_one_times        := bop_add_id times c
   ; A_pre_dioid_with_one_plus_proofs  := sg_CI_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_pre_dioid_with_one_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_pre_dioid_with_one_id_ann_proofs := pann_is_tid_proofs_add_one S _ c plus times s peqvS (A_pre_dioid_id_ann_proofs S bsS)
   ; A_pre_dioid_with_one_proofs       := dioid_proofs_add_one S rS c plus times peqvS idem comm (A_pre_dioid_proofs S bsS)
   ; A_pre_dioid_with_one_ast          := Ast_bs_add_one (c, A_pre_dioid_ast S bsS) (*FIX*)
|}.

Definition A_add_one_to_pre_dioid_with_zero : ∀ (S : Type),  A_pre_dioid_with_zero S -> cas_constant -> A_dioid (with_constant S) 
:= λ S bsS c,
let eqvS  := A_pre_dioid_with_zero_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_pre_dioid_with_zero_plus S bsS in
let times := A_pre_dioid_with_zero_times S bsS in
let pproofs := A_pre_dioid_with_zero_plus_proofs S bsS in
let tproofs := A_pre_dioid_with_zero_times_proofs S bsS in
let idem   := A_sg_CI_idempotent _ _ _ pproofs in
let comm   := A_sg_CI_commutative _ _ _ pproofs in 
{| 
     A_dioid_eqv          := A_eqv_add_constant S eqvS c 
   ; A_dioid_plus         := bop_add_ann plus c
   ; A_dioid_times        := bop_add_id times c
   ; A_dioid_plus_proofs  := sg_CI_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_dioid_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_dioid_id_ann_proofs := dually_bounded_proofs_add_one S _ c plus times  peqvS (A_pre_dioid_with_zero_id_ann_proofs S bsS)
   ; A_dioid_proofs       := dioid_proofs_add_one S rS c plus times peqvS idem comm (A_pre_dioid_with_zero_proofs S bsS)
   ; A_dioid_ast          := Ast_bs_add_one (c, A_pre_dioid_with_zero_ast S bsS) (*FIX*)
|}.

Definition A_add_one_to_selective_pre_dioid_with_zero : ∀ (S : Type),  A_selective_pre_dioid_with_zero S -> cas_constant -> A_selective_dioid (with_constant S) 
:= λ S bsS c,
let eqvS  := A_selective_pre_dioid_with_zero_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_selective_pre_dioid_with_zero_plus S bsS in
let times := A_selective_pre_dioid_with_zero_times S bsS in
let pproofs := A_selective_pre_dioid_with_zero_plus_proofs S bsS in
let tproofs := A_selective_pre_dioid_with_zero_times_proofs S bsS in
let idem   := bop_selective_implies_idempotent _ _ _ (A_sg_CS_selective _ _ _ pproofs) in
let comm   := A_sg_CS_commutative _ _ _ pproofs in 
{| 
     A_selective_dioid_eqv          := A_eqv_add_constant S eqvS c 
   ; A_selective_dioid_plus         := bop_add_ann plus c
   ; A_selective_dioid_times        := bop_add_id times c
   ; A_selective_dioid_plus_proofs  := sg_CS_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_selective_dioid_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_selective_dioid_id_ann_proofs := dually_bounded_proofs_add_one S _ c plus times  peqvS (A_selective_pre_dioid_with_zero_id_ann_proofs S bsS)
   ; A_selective_dioid_proofs       := dioid_proofs_add_one S rS c plus times peqvS idem comm (A_selective_pre_dioid_with_zero_proofs S bsS)
   ; A_selective_dioid_ast          := Ast_bs_add_one (c, A_selective_pre_dioid_with_zero_ast S bsS) (*FIX*)
|}.


End Combinators. 
End ACAS.

Section AMCAS. 

Open Scope string_scope.
  
Definition A_mcas_bs_add_one (S : Type) (A : A_bs_mcas S) (c : cas_constant) := 
  match (A_bs_mcas_cast_up _ A) with
  | A_BS_bs _ B => A_bs_classify _ (A_BS_bs _ (A_bs_add_one _ B c))
  | A_BS_Error _ str => A_BS_Error _ str                                                           
  | _ => A_BS_Error _ ("internal error : A_bs_mcas_add_one" :: nil) 
  end.

End AMCAS. 


Section CAS. 

Section Certify. 
Definition bops_add_one_left_distributive_check 
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S) 
     (llaS_d  : @check_left_left_absorptive S) 
     (rlaS_d  : @check_right_left_absorptive S) 
     (ldS_d   : @check_left_distributive S) :
           @check_left_distributive (with_constant S) := 
   match ldS_d with 
   | Certify_Left_Distributive  => 
    match llaS_d with 
    | Certify_Left_Left_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Left_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent      => Certify_Left_Distributive 
         | Certify_Not_Idempotent s =>
              Certify_Not_Left_Distributive (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Left_Absorptive (s1, s2) => 
            Certify_Not_Left_Distributive (inr s1, (inr s2, inl c))
      end 
    | Certify_Not_Left_Left_Absorptive (s1, s2) => 
         Certify_Not_Left_Distributive (inr s1, (inl c, inr s2))
    end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (inr s1, (inr s2, inr s3))
   end. 


Definition bops_add_one_right_distributive_check 
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S) 
     (llaS_d  : @check_left_right_absorptive S) 
     (rlaS_d  : @check_right_right_absorptive S) 
     (ldS_d   : @check_right_distributive S) : @check_right_distributive (with_constant S) := 
   match ldS_d with 
   | Certify_Right_Distributive => 
    match llaS_d with 
    | Certify_Left_Right_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Right_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent      =>
              Certify_Right_Distributive 
         | Certify_Not_Idempotent s =>
              Certify_Not_Right_Distributive (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Right_Absorptive (s1, s2) => 
            Certify_Not_Right_Distributive (inr s1, (inr s2, inl c))
      end 
    | Certify_Not_Left_Right_Absorptive (s1, s2) => 
         Certify_Not_Right_Distributive (inr s1, (inl c, inr s2))
    end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (inr s1, (inr s2, inr s3))
   end. 


Definition bops_add_one_left_left_absorptive_check 
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S) 
     (laS_d : @check_left_left_absorptive S) : @check_left_left_absorptive (with_constant S) := 
   match laS_d with 
   | Certify_Left_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Left_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Left_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Left_Left_Absorptive (inr s1, inr s2)
   end. 


Definition bops_add_one_left_right_absorptive_check 
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S) 
     (laS_d : @check_left_right_absorptive S): @check_left_right_absorptive (with_constant S) :=
   match laS_d with 
   | Certify_Left_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Right_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Right_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Left_Right_Absorptive (inr s1, inr s2)
   end. 


Definition bops_add_one_right_left_absorptive_check 
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S) 
     (laS_d : @check_right_left_absorptive S) : @check_right_left_absorptive (with_constant S) :=
   match laS_d with 
   | Certify_Right_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Left_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Left_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Right_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_right_absorptive_check 
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S) 
     (laS_d : @check_right_right_absorptive S) : @check_right_right_absorptive (with_constant S) :=
   match laS_d with 
   | Certify_Right_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Right_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Right_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Right_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive (inr s1, inr s2)
   end.


Definition bops_add_one_id_equals_ann_check_left  
  {S : Type} (c : cas_constant) (dS : @exists_id_ann_certificate S) : @exists_id_ann_certificate (with_constant S) :=
match dS with                                 
| Id_Ann_Cert_None                => Id_Ann_Cert_None
| Id_Ann_Cert_Id_None id          => Id_Ann_Cert_Id_None (inr id) 
| Id_Ann_Cert_None_Ann ann        => Id_Ann_Cert_None_Ann (inr ann) 
| Id_Ann_Cert_Equal id_ann        => Id_Ann_Cert_Equal (inr id_ann) 
| Id_Ann_Cert_Not_Equal (id, ann) => Id_Ann_Cert_Not_Equal (inr id, inr ann)
end.


End Certify.

Section Certificates.


Definition id_ann_certs_add_one
           {S : Type}
           (c : cas_constant)
           (pS : @id_ann_certificates S) : @id_ann_certificates (with_constant S) := 
{|
  id_ann_plus_times_d := bops_add_one_id_equals_ann_check_left c (id_ann_plus_times_d pS) 
; id_ann_times_plus_d := Id_Ann_Cert_Equal (inl c) 
|}.

Definition pann_is_tid_certs_add_one
           {S : Type}
           (c : cas_constant)
           (pS : @id_ann_certificates S) : @pann_is_tid_certificates (with_constant S) := 
{|
  pann_is_tid_plus_times_d := bops_add_one_id_equals_ann_check_left c (id_ann_plus_times_d pS) 
; pann_is_tid_times_plus   := Assert_Exists_Id_Ann_Equal (inl c) 
|}.


Definition dually_bounded_certs_add_one
           {S : Type}
           (c : cas_constant)
           (pS : @pid_is_tann_certificates S) : @dually_bounded_certificates (with_constant S) := 
match pid_is_tann_plus_times pS with
| Assert_Exists_Id_Ann_Equal id => 
{|
  bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal (inr id)       
; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal (inl c) 
|}
end.


Definition bs_certs_add_one 
           {S : Type}
           (c : cas_constant)
           (ppS : @sg_certificates S)
           (pS : @bs_certificates S) : @bs_certificates (with_constant S) :=
let idm := sg_idempotent_d ppS in
let LD  := bs_left_distributive_d pS in
let RD  := bs_right_distributive_d pS in 
let LLA := bs_left_left_absorptive_d pS in 
let LRA := bs_left_right_absorptive_d pS in
let RLA := bs_right_left_absorptive_d pS in
let RRA := bs_right_right_absorptive_d pS in 
{|
  bs_left_distributive_d      := bops_add_one_left_distributive_check c idm LLA RLA LD
; bs_right_distributive_d     := bops_add_one_right_distributive_check c idm LRA RRA RD 
; bs_left_left_absorptive_d   := bops_add_one_left_left_absorptive_check c idm LLA 
; bs_left_right_absorptive_d  := bops_add_one_left_right_absorptive_check c idm LRA 
; bs_right_left_absorptive_d  := bops_add_one_right_left_absorptive_check c idm RLA 
; bs_right_right_absorptive_d := bops_add_one_right_right_absorptive_check c idm RRA 
|}.


Definition dioid_certs_add_one
      {S : Type}
      (c : cas_constant)
      (pS : @dioid_certificates S) : @dioid_certificates (with_constant S)  := 
{|
  dioid_left_distributive      := Assert_Left_Distributive
; dioid_right_distributive     := Assert_Right_Distributive
; dioid_left_left_absorptive   := Assert_Left_Left_Absorptive
; dioid_left_right_absorptive  := Assert_Left_Right_Absorptive
|}.


End Certificates.   

Section Combinators.


Definition bs_add_one {S : Type} (bsS : @bs S) (c : cas_constant) : @bs (with_constant S) :=
let eqvS   := bs_eqv bsS in
let wS     := eqv_witness eqvS in
let f      := eqv_new eqvS in
let plus   := bs_plus bsS in
let times  := bs_times bsS in
let pcerts := bs_plus_certs bsS in
let tcerts := bs_times_certs bsS in 
{| 
     bs_eqv         := eqv_add_constant eqvS c 
   ; bs_plus        := bop_add_ann plus c
   ; bs_times       := bop_add_id times c
   ; bs_plus_certs  := sg_certs_add_ann c wS f pcerts 
   ; bs_times_certs := sg_certs_add_id c wS f tcerts
   ; bs_id_ann_certs := id_ann_certs_add_one c (bs_id_ann_certs bsS)
   ; bs_certs       := bs_certs_add_one c pcerts (bs_certs bsS)
   ; bs_ast         := Ast_bs_add_one (c, bs_ast bsS)
|}.


Definition add_one_to_pre_dioid
           {S : Type}
           (bsS : @pre_dioid S)
           (c : cas_constant) : @pre_dioid_with_one (with_constant S) := 
let eqvS  := pre_dioid_eqv bsS in
let wS    := eqv_witness eqvS  in
let f     := eqv_new eqvS in
let pcerts := pre_dioid_plus_certs bsS in
let tcerts := pre_dioid_times_certs bsS in
{| 
     pre_dioid_with_one_eqv          := eqv_add_constant eqvS c 
   ; pre_dioid_with_one_plus         := bop_add_ann (pre_dioid_plus bsS) c
   ; pre_dioid_with_one_times        := bop_add_id (pre_dioid_times bsS) c
   ; pre_dioid_with_one_plus_certs   := sg_CI_certs_add_ann c pcerts 
   ; pre_dioid_with_one_times_certs  := sg_certs_add_id c wS f tcerts
   ; pre_dioid_with_one_id_ann_certs := pann_is_tid_certs_add_one c (pre_dioid_id_ann_certs bsS)
   ; pre_dioid_with_one_certs        := dioid_certs_add_one c (pre_dioid_certs bsS)
   ; pre_dioid_with_one_ast          := Ast_bs_add_one (c, pre_dioid_ast bsS) (*FIX*)
|}.

Definition add_one_to_pre_dioid_with_zero
           {S : Type}
           (bsS : @pre_dioid_with_zero S)
           (c : cas_constant) : @dioid (with_constant S) := 
let eqvS  := pre_dioid_with_zero_eqv bsS in
let wS    := eqv_witness eqvS  in
let f     := eqv_new eqvS in
let pcerts := pre_dioid_with_zero_plus_certs bsS in
let tcerts := pre_dioid_with_zero_times_certs bsS in
{| 
     dioid_eqv          := eqv_add_constant eqvS c 
   ; dioid_plus         := bop_add_ann (pre_dioid_with_zero_plus bsS) c
   ; dioid_times        := bop_add_id (pre_dioid_with_zero_times bsS) c
   ; dioid_plus_certs   := sg_CI_certs_add_ann c pcerts 
   ; dioid_times_certs  := sg_certs_add_id c wS f tcerts
   ; dioid_id_ann_certs := dually_bounded_certs_add_one c (pre_dioid_with_zero_id_ann_certs bsS)
   ; dioid_certs        := dioid_certs_add_one c (pre_dioid_with_zero_certs bsS)
   ; dioid_ast          := Ast_bs_add_one (c, pre_dioid_with_zero_ast bsS) (*FIX*)
|}.


End Combinators.

End CAS.

Section MCAS. 
Open Scope string_scope.
  
Definition mcas_bs_add_one {S : Type} (A : @bs_mcas S) (c : cas_constant) := 
  match (bs_mcas_cast_up A) with
  | BS_bs B => bs_classify (BS_bs (bs_add_one B c))
  | BS_Error str => BS_Error str                                                           
  | _ => BS_Error ("internal error : A_bs_mcas_add_one" :: nil) 
  end.

End MCAS. 



Section Verify.

Section Certify.

Variables (S : Type)
          (c : cas_constant)
          (wS : S) 
          (rS : brel S)
          (eqvS : eqv_proofs S rS)                 
          (plusS timesS : binary_op S).
  
Lemma bops_add_one_id_equals_ann_check_left_correct  
  (P : exists_id_ann_decidable S rS plusS timesS) : 
  p2c_exists_id_ann (with_constant S)
                    (brel_sum brel_constant rS) 
                    (bop_add_ann plusS c) (bop_add_id timesS c)
                    (bops_add_one_id_equals_ann_decide_left S rS c plusS timesS wS eqvS P) 
  = 
  bops_add_one_id_equals_ann_check_left c (p2c_exists_id_ann S rS plusS timesS P). 
Proof. unfold p2c_exists_id_ann, bops_add_one_id_equals_ann_decide_left,
       bops_add_one_id_equals_ann_check_left; 
       destruct P; simpl. 
         + destruct p as [A B]; reflexivity. 
         + destruct p as [[id A] B]; simpl; reflexivity. 
         + destruct p as [A [ann B]]; simpl; reflexivity. 
         + destruct b as [id_ann [A B]]; simpl; reflexivity. 
         + destruct b as [[id ann] [[A B] C]]; simpl; reflexivity. 
Qed.



Lemma pann_is_tid_certs_add_one_correct 
  (P : id_ann_proofs S rS plusS timesS) : 
  P2C_pann_is_tid (with_constant S)
                  (brel_sum brel_constant rS)
                  (bop_add_ann plusS c) 
                  (bop_add_id timesS c) 
                  (pann_is_tid_proofs_add_one S rS c plusS timesS wS eqvS P)
  = 
  pann_is_tid_certs_add_one c (P2C_id_ann S rS plusS timesS P). 
Proof. unfold P2C_id_ann, P2C_pann_is_tid, 
       pann_is_tid_proofs_add_one, pann_is_tid_certs_add_one;
       destruct P; simpl.
       destruct A_id_ann_plus_times_d; simpl. 
         + destruct p as [A B]; reflexivity. 
         + destruct p as [[id A] B]; simpl; reflexivity. 
         + destruct p as [A [ann B]]; simpl; reflexivity. 
         + destruct b as [id_ann [A B]]; simpl; reflexivity. 
         + destruct b as [[id ann] [[A B] C]]; simpl; reflexivity. 
Qed.   


Lemma dually_bounded_certs_add_one_correct 
    (P : pid_is_tann_proofs S rS plusS timesS) : 
     P2C_dually_bounded (with_constant S)
                  (brel_sum brel_constant rS)
                  (bop_add_ann plusS c) 
                  (bop_add_id timesS c) 
                  (dually_bounded_proofs_add_one S rS c plusS timesS eqvS P)
   = 
   dually_bounded_certs_add_one c (P2C_pid_is_tann S rS plusS timesS  P). 
Proof. unfold P2C_pid_is_tann, P2C_dually_bounded,
       dually_bounded_proofs_add_one, dually_bounded_certs_add_one;
       destruct P; simpl. destruct A_pid_is_tann_plus_times as [id_ann [A B]]; compute. 
       reflexivity. 
Qed.

Lemma bops_add_one_left_distributive_check_correct 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_left_distributive_decidable S rS plusS timesS): 
  p2c_left_distributive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_distributive_decide S rS c plusS timesS eqvS idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_left_distributive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS llaS_d)
     (p2c_right_left_absorptive S rS plusS timesS rlaS_d)
     (p2c_left_distributive S rS plusS timesS ldS_d). 
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ]; 
       destruct llaS_d as [ llaS | [ [s1 s2] nllaS ] ]; 
       destruct rlaS_d as [ rlaS | [ [s6 s7] nrlaS ] ]; 
       destruct ldS_d as [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_right_distributive_check_correct 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_right_distributive_decidable S rS plusS timesS) :  
  p2c_right_distributive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_distributive_decide S rS c plusS timesS eqvS idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_right_distributive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS llaS_d)
     (p2c_right_right_absorptive S rS plusS timesS rlaS_d)
     (p2c_right_distributive S rS plusS timesS ldS_d). 
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ;
       destruct llaS_d as [ llaS | [ [s1 s2] nllaS ] ];
       destruct rlaS_d as [ rlaS | [ [s6 s7] nrlaS ] ];
       destruct ldS_d as [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_left_absorbtive_check_correct 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_left_absorptive_decidable S rS plusS timesS): 
  p2c_left_left_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_left_absorptive_decide S rS c plusS timesS eqvS idmS_d laS_d)
  = 
  bops_add_one_left_left_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS laS_d).
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ;
       destruct laS_d as [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_right_absorbtive_check_correct 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_right_absorptive_decidable S rS plusS timesS) : 
  p2c_left_right_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_right_absorptive_decide S rS c plusS timesS eqvS idmS_d laS_d)
  = 
  bops_add_one_left_right_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS laS_d ).
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ; 
       destruct laS_d as [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_left_absorbtive_check_correct 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_left_absorptive_decidable S rS plusS timesS) : 
  p2c_right_left_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_left_absorptive_decide S rS c plusS timesS eqvS idmS_d laS_d)
  = 
  bops_add_one_right_left_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_left_absorptive S rS plusS timesS laS_d).
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ; 
       destruct laS_d as [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_right_absorbtive_check_correct 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_right_absorptive_decidable S rS plusS timesS) : 
  p2c_right_right_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_right_absorptive_decide S rS c plusS timesS eqvS idmS_d laS_d)
  = 
  bops_add_one_right_right_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_right_absorptive S rS plusS timesS laS_d).
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ;
       destruct laS_d as [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 



End Certify.

Section Certificates. 

Variables (S : Type)
          (c : cas_constant)
          (wS : S)
          (rS : brel S)
          (eqvS : eqv_proofs S rS)            
          (plusS timesS : binary_op S). 


Lemma  correct_id_ann_certs_add_one  
    (bsS : id_ann_proofs S rS plusS timesS) : 
    P2C_id_ann (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_ann plusS c) 
       (bop_add_id timesS c) 
       (id_ann_proofs_add_one S rS c plusS timesS wS eqvS bsS)
    =
    id_ann_certs_add_one c (P2C_id_ann S rS plusS timesS bsS). 
Proof. unfold id_ann_certs_add_one, id_ann_proofs_add_one, P2C_id_ann; simpl.        
       rewrite bops_add_one_id_equals_ann_check_left_correct.        
       reflexivity.
Qed.        
       


Lemma  correct_bs_certs_add_one 
    (sgS : sg_proofs S rS plusS)  (bsS : bs_proofs S rS plusS timesS): 
    P2C_bs (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_ann plusS c) 
       (bop_add_id timesS c) 
       (bs_proofs_add_one S rS c plusS timesS eqvS sgS bsS)
    =
    bs_certs_add_one c (P2C_sg S rS plusS sgS) (P2C_bs S rS plusS timesS bsS). 
Proof. unfold bs_certs_add_one, bs_proofs_add_one, P2C_bs, P2C_sg; simpl. 
       rewrite bops_add_one_left_distributive_check_correct. 
       rewrite bops_add_one_right_distributive_check_correct. 
       rewrite bops_add_one_left_left_absorbtive_check_correct .
       rewrite bops_add_one_left_right_absorbtive_check_correct. 
       rewrite bops_add_one_right_left_absorbtive_check_correct. 
       rewrite bops_add_one_right_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 

Lemma  correct_dioid_certs_add_one
    (idemS : bop_idempotent S rS plusS)
    (commS : bop_commutative S rS plusS)
    (bsS : dioid_proofs S rS plusS timesS): 
    P2C_dioid (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_ann plusS c) 
       (bop_add_id timesS c) 
       (dioid_proofs_add_one S rS c plusS timesS eqvS idemS commS bsS)
    =
    dioid_certs_add_one c (P2C_dioid S rS plusS timesS bsS). 
Proof. unfold P2C_dioid,  dioid_proofs_add_one, dioid_certs_add_one; simpl. 
       reflexivity. 
Defined. 



End Certificates.

Section Combinators.

Theorem correct_bs_add_one (S : Type) (bsS: A_bs S) (c : cas_constant): 
   bs_add_one (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_one S bsS c). 
Proof. unfold bs_add_one, A_bs_add_one, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id. 
       rewrite correct_bs_certs_add_one.
       rewrite correct_id_ann_certs_add_one.        
       reflexivity. 
Qed. 


Theorem correct_add_one_to_pre_dioid (S : Type) (bsS: A_pre_dioid S) (c : cas_constant):
   A2C_pre_dioid_with_one (with_constant S) (A_add_one_to_pre_dioid S bsS c)
   =
   add_one_to_pre_dioid (A2C_pre_dioid S bsS) c. 
Proof. unfold A2C_pre_dioid_with_one, A2C_pre_dioid, add_one_to_pre_dioid, A_add_one_to_pre_dioid; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id. 
       rewrite correct_dioid_certs_add_one. 
       rewrite pann_is_tid_certs_add_one_correct. 
       reflexivity. 
Qed. 


Theorem correct_add_one_to_pre_dioid_with_zero (S : Type) (bsS: A_pre_dioid_with_zero S) (c : cas_constant):
   A2C_dioid (with_constant S) (A_add_one_to_pre_dioid_with_zero S bsS c)
   =
   add_one_to_pre_dioid_with_zero (A2C_pre_dioid_with_zero S bsS) c. 
Proof. unfold A2C_dioid, A2C_pre_dioid_with_zero, 
       add_one_to_pre_dioid_with_zero, A_add_one_to_pre_dioid_with_zero; simpl. 
       rewrite correct_eqv_add_constant.
       rewrite correct_dioid_certs_add_one.        
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id. 
       rewrite dually_bounded_certs_add_one_correct.
       reflexivity. 
Qed.

Theorem correct_mcas_bs_add_one (S : Type) (c : cas_constant) (sgS : A_bs_mcas S) : 
         mcas_bs_add_one (A2C_mcas_bs S sgS) c 
         = 
         A2C_mcas_bs (with_constant S) (A_mcas_bs_add_one S sgS c).
Proof. unfold mcas_bs_add_one, A_mcas_bs_add_one. 
       rewrite correct_bs_mcas_cast_up.       
       destruct (A_bs_cas_up_is_error_or_bs S sgS) as [[l1 A] | [s1 A]]. 
       + rewrite A; simpl. reflexivity. 
       + rewrite A; simpl. rewrite correct_bs_add_one.
         apply correct_bs_classify_bs.          
Qed. 


End Combinators.   
End Verify.   

