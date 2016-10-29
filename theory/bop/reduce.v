Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop.
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.uop_properties. 
Require Import CAS.theory.brel.reduce. 


Lemma bop_reduce_congruence : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           bop_congruence S r b ->        
           bop_congruence S r (bop_reduce S u b).          (**** WRONG r ??? **********) 
Proof. intros S r u b congU congB. unfold bop_congruence, bop_reduce.
       intros s1 s2 t1 t2 H Q. apply congU. apply congB.  
       apply congU. assumption. apply congU. assumption. 
Defined. 

Lemma bop_reduce_congruence_v2 : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_congruence  S r u -> 
           bop_congruence S r b ->        
                bop_congruence S (brel_reduce S r u) (bop_reduce S u b).  
Proof. compute. intros S r u b cong_u cong_b s1 s2 t1 t2 H1 H2.  
       apply cong_u. 
       apply cong_u. 
       apply cong_b; auto. 
Defined. 


Lemma bop_reduce_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         brel_symmetric S r   -> 
         brel_transitive S r -> 
         uop_congruence  S r u -> 
         uop_idempotent  S r u -> 
         bop_idempotent S r b -> 
           bop_idempotent S (brel_reduce S r u) (bop_reduce S u b).
Proof. compute. intros S r u b symS tranS cong_u idem_u idem_b s. 
       assert (fact1 := idem_b (u s)). 
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u s). 
       assert (fact4 := tranS _ _ _ fact2 fact3). 
       assert (fact5 := cong_u _ _ fact4). 
       assert (fact6 := tranS _ _ _ fact5 fact3). 
       assumption. 
Defined. 


Lemma bop_reduce_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_congruence_positive S r u -> 
         bop_commutative S r b -> 
           bop_commutative S r (bop_reduce S u b).
Proof. intros S r u b congS commS. 
       intros s t. unfold bop_reduce. apply congS. apply commS. 
Defined. 


(*
Lemma bop_reduce_not_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_preserves_left_negative S r u -> 
         bop_not_idempotent S r b -> 
           bop_not_idempotent S r (bop_reduce S u b).
Proof. intros S r u b presS idemS. 
       unfold bop_not_idempotent, bop_reduce.
       destruct idemS as [s P]. exists s. 
       apply presS. assumption. 
Defined.

Definition bop_reduce_idempotent_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (u : unary_op S) 
     (b: binary_op S), 
     uop_preserves_left_positive S r u → 
     uop_preserves_left_negative S r u → 
     bop_idempotent_decidable S r b → 
        bop_idempotent_decidable S r (bop_reduce S u b)
:= λ S r u b pp pn d,  
   match d with 
   | inl idemS => inl _ (bop_reduce_idempotent S r u b pp idemS)
   | inr not_idemS => inr _ (bop_reduce_not_idempotent S r u b pn not_idemS)
   end. 

*) 


(* 
Lemma bop_reduce_associative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_idempotent S r u -> 
           uop_congruence_positive S r u -> 
           uop_bop_associative S r u b -> 
           bop_associative S r (bop_reduce S u b).
Proof. unfold bop_reduce, bop_associative.  
       intros S r u b idemS congS assocS. unfold bop_associative. 
       intros s t v. apply congS. unfold bop_reduce. 
       unfold uop_idempotent in idemS. 
       apply assocS. 

   (b (u (u (b (u s) (u t)))) (u v)) 

 = (b (u s) (u (u (b (u t) (u v)))))
 = (b (u s) (u (u (b (u t) (u v)))))
Defined. 
*) 



(*
Lemma bop_reduce_not_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_congruence_negative S r u -> 
         bop_not_commutative S r b -> 
           bop_not_commutative S r (bop_reduce S u b).
Proof. intros S r u b congS not_commS. 
       unfold bop_not_commutative, bop_reduce.
       destruct not_commS as [s [t P]]. exists s. exists t. 
       apply congS. assumption. 
Defined.

Definition bop_reduce_commutative_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (u : unary_op S) 
     (b: binary_op S), 
     uop_congruence_positive S r u → 
     uop_congruence_negative S r u → 
     bop_commutative_decidable S r b → 
        bop_commutative_decidable S r (bop_reduce S u b)
:= λ S r u b cp cn d,  
   match d with 
   | inl commS     =>  inl _ (bop_reduce_commutative S r u b cp commS)
   | inr not_commS =>  inr _ (bop_reduce_not_commutative S r u b cn not_commS)
   end. 


Lemma bop_reduce_selective : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_preserves_left_positive S r u -> 
           bop_selective S r b -> 
           bop_selective S r (bop_reduce S u b).
Proof. intros S r u b presS selS. unfold bop_selective, bop_reduce.
       intros s t. destruct (selS s t) as [Q | Q]. 
          left. apply presS. assumption. 
          right. apply presS. assumption. 
Defined. 


Lemma bop_reduce_not_selective : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_preserves_left_negative S r u -> 
           bop_not_selective S r b -> 
           bop_not_selective S r (bop_reduce S u b).
Proof. intros S r u b presS [s [t P]]. exists s; exists t. unfold bop_reduce. 
       destruct P as [P1 P2]. split. 
         apply presS. assumption. 
         apply presS. assumption. 
Defined. 

(* Definition bop_reduce_selective_decide : *) 


Lemma bop_reduce_not_is_left : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
       uop_preserves_left_negative S r u -> 
       bop_not_is_left S r b ->            
          bop_not_is_left S r (bop_reduce S u b).
Proof. intros S r u b presS [s [t P]]. unfold bop_not_is_left, bop_reduce.
       exists s; exists t. apply presS. assumption. 
Defined. 

Lemma bop_reduce_not_is_right : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
       uop_preserves_left_negative S r u -> 
       bop_not_is_right S r b ->            
          bop_not_is_right S r (bop_reduce S u b).
Proof. intros S r u b presS [s [t P]]. unfold bop_not_is_right, bop_reduce.
       exists s; exists t. apply presS. assumption. 
Defined. 
*) 
