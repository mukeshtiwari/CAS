Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 


Lemma bop_then_unary_congruence : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           bop_congruence S r b -> 
           bop_congruence S r (bop_then_unary S u b).
Proof. intros S r u b congU congB. unfold bop_congruence, bop_then_unary.
       intros s1 s2 t1 t2 H Q. apply congU. apply congB.  assumption. assumption. 
Defined. 

Lemma bop_then_unary_associative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           uop_bop_associative S r u b -> 
           bop_associative S r (bop_then_unary S u b).
Proof. intros S r u b congS assocS. unfold bop_associative, bop_then_unary.
       intros s t v. apply congS.
       apply assocS. 
Defined. 

(*  How to capture reductions? 

(a)  u (u (s * t) * v) =  u (s * (u (t * v)))

dist? 

  a x (b + c) 
= r(a x r(b + c))
= r(a x (b + c))
= r((a x b) + (a x c))
= r(r(a x b) + r(a x c))
= (a x b) + (a x c) 


(A) u(s * t) = u((u(s) * t) 
(B) u(s * t) = u(s * u(t)) 

Prove (a) : 

  u (u (s * t) * v)
= u ((s * t) * v)
= u (s * (t * v)) 
= u (s * u(t * v)) 

*) 

Lemma bop_then_unary_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_preserves_left_positive S r u -> 
         bop_idempotent S r b -> 
           bop_idempotent S r (bop_then_unary S u b).
Proof. 
       intros S r u b presS idemS. 
       unfold bop_then_unary. unfold bop_idempotent. 
       intro s. apply (presS (b s s) s). apply idemS. 
Defined. 

(* 
Lemma bop_then_unary_idempotent_v2 : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         brel_transitive S r -> 
         uop_congruence S r u -> 
         uop_preserves_brel S u r -> 
         bop_idempotent S r b -> 
           bop_idempotent S r (bop_then_unary S u b).
Proof. 
       intros S r u b transS cong  presS idemS. 
       unfold bop_then_unary. unfold bop_idempotent. 
       unfold uop_congruence in cong. 
       unfold uop_preserves_brel in presS. 
       unfold bop_idempotent in idemS. 
       unfold brel_transitive in transS. 

       intro s. assert (H := idemS s). assert(J := cong _ _ H). assert(K := presS s). 
       apply (transS _ _ _ J K).
Defined. 
*) 


Lemma bop_then_unary_not_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
 
         uop_preserves_left_negative S r u -> 
         bop_not_idempotent S r b -> 
           bop_not_idempotent S r (bop_then_unary S u b).
Proof. intros S r u b presS idemS. 
       unfold bop_not_idempotent, bop_then_unary.
       destruct idemS as [s P]. exists s. 
       apply presS. assumption. 
Defined.

Definition bop_then_unary_idempotent_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (u : unary_op S) 
     (b: binary_op S), 
     uop_preserves_left_positive S r u → 
     uop_preserves_left_negative S r u → 
     bop_idempotent_decidable S r b → 
        bop_idempotent_decidable S r (bop_then_unary S u b)
:= λ S r u b pp pn d,  
   match d with 
   | inl idemS => inl _ (bop_then_unary_idempotent S r u b pp idemS)
   | inr not_idemS => inr _ (bop_then_unary_not_idempotent S r u b pn not_idemS)
   end. 

Lemma bop_then_unary_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_congruence_positive S r u -> 
         bop_commutative S r b -> 
           bop_commutative S r (bop_then_unary S u b).
Proof. intros S r u b congS commS. 
       intros s t. unfold bop_then_unary. apply congS. apply commS. 
Defined. 

Lemma bop_then_unary_not_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
         uop_congruence_negative S r u -> 
         bop_not_commutative S r b -> 
           bop_not_commutative S r (bop_then_unary S u b).
Proof. intros S r u b congS not_commS. 
       unfold bop_not_commutative, bop_then_unary.
       destruct not_commS as [ [s t] P]. exists (s, t). 
       apply congS. assumption. 
Defined.

Definition bop_then_unary_commutative_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (u : unary_op S) 
     (b: binary_op S), 
     uop_congruence_positive S r u → 
     uop_congruence_negative S r u → 
     bop_commutative_decidable S r b → 
        bop_commutative_decidable S r (bop_then_unary S u b)
:= λ S r u b cp cn d,  
   match d with 
   | inl commS     =>  inl _ (bop_then_unary_commutative S r u b cp commS)
   | inr not_commS =>  inr _ (bop_then_unary_not_commutative S r u b cn not_commS)
   end. 


Lemma bop_then_unary_selective : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_preserves_left_positive S r u -> 
           bop_selective S r b -> 
           bop_selective S r (bop_then_unary S u b).
Proof. intros S r u b presS selS. unfold bop_selective, bop_then_unary.
       intros s t. destruct (selS s t) as [Q | Q]. 
          left. apply presS. assumption. 
          right. apply presS. assumption. 
Defined. 


Lemma bop_then_unary_not_selective : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
           uop_preserves_left_negative S r u -> 
           bop_not_selective S r b -> 
           bop_not_selective S r (bop_then_unary S u b).
Proof. intros S r u b presS [ [s t] P]. exists (s, t). unfold bop_then_unary. 
       destruct P as [P1 P2]. split. 
         apply presS. assumption. 
         apply presS. assumption. 
Defined. 

(* Definition bop_then_unary_selective_decide : *) 


Lemma bop_then_unary_not_is_left : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
       uop_preserves_left_negative S r u -> 
       bop_not_is_left S r b ->            
          bop_not_is_left S r (bop_then_unary S u b).
Proof. intros S r u b presS [ [s t] P]. unfold bop_not_is_left, bop_then_unary.
       exists (s, t). apply presS. assumption. 
Defined. 

Lemma bop_then_unary_not_is_right : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S), 
       uop_preserves_left_negative S r u -> 
       bop_not_is_right S r b ->            
          bop_not_is_right S r (bop_then_unary S u b).
Proof. intros S r u b presS [ [s t] P]. unfold bop_not_is_right, bop_then_unary.
       exists (s, t). apply presS. assumption. 
Defined. 

