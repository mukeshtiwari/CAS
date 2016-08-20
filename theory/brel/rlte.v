Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.conjunction. 
Require Import CAS.theory.brel.complement. 
Require Import CAS.theory.facts. 


Lemma brel_rlte_reflexive : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r -> 
         bop_idempotent S r b -> 
           brel_reflexive S r →  brel_reflexive S (brel_rlte S r b). 
Proof. unfold brel_reflexive, brel_rlte. 
       intros S r b symS idemS refS s. 
       assert(id := idemS s).  
       apply symS. assumption. 
Defined. 

Lemma brel_rlte_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S) (b : binary_op S),  
       brel_congruence S r1 r2 -> 
       bop_congruence S r1 b -> 
         brel_congruence S r1 (brel_rlte S r2 b). 
Proof. unfold brel_congruence, bop_congruence, brel_rlte. 
       intros S r1 r2 b r_cong b_cong s t u v H1 H2. 
       assert (H3 := b_cong _ _ _ _ H1 H2). 
       assert (H4 := r_cong _ _ _ _ H2 H3). 
       assumption. 
Defined. 


(*
   s <= t    -> t <= u    -> s <= u
   t = s + t -> u = t + u -> u = s + u
   u = t + u = ((s + t) + u) = (s + (t + u)) = s + u
*) 
Lemma brel_rlte_transitive : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_reflexive S r  →  
         brel_symmetric S r  →  
         bop_associative S r b  →  
         bop_congruence S r b  →  
         brel_transitive S r →  
            brel_transitive S (brel_rlte S r b). 
Proof. unfold brel_transitive, brel_rlte, bop_congruence. 
       intros S r b refS symS assS b_cong transS s t u H1 H2. 
       assert (fact1 : r u (b (b s t) u ) = true). 
          assert (C := b_cong _ _ _ _ H1 (refS u)). 
          apply (transS _ _ _ H2 C). 
       assert (fact2 : r u (b s (b t u)) = true).
          assert (A := assS s t u). 
          apply (transS _ _ _ fact1 A). 
       assert (fact3 : r u (b s u) = true). 
          assert (C := b_cong _ _ _ _ (refS s) H2). apply symS in C. 
          apply (transS _ _ _ fact2 C). 
       assumption. 
Defined. 


Lemma brel_rlte_antisymmetric : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r ->  
         brel_transitive S r → 
         bop_commutative S r b -> brel_antisymmetric S r (brel_rlte S r b). 
Proof. unfold brel_antisymmetric, brel_rlte. 
       intros S r b symS transS commS s t H1 H2. 
       assert (fact1 := commS t s). 
       assert (fact2 := transS _ _ _ H2 fact1). apply symS in H1. 
       apply (transS _ _ _ fact2 H1). 
Defined. 


Lemma brel_rlte_total : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r ->  
         brel_transitive S r ->  
         bop_commutative S r b -> 
         bop_selective S r b -> brel_total S (brel_rlte S r b). 
Proof. unfold brel_total, brel_rlte. 
       intros S r b symS transS commS selS s t. 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       destruct (selS s t) as [Q | Q]. 
          right. apply symS in Q. apply (transS _ _ _ Q fact1). 
          left. apply symS. assumption. 

Defined. 

Lemma brel_rlte_not_total : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r ->  
         brel_transitive S r ->  
         bop_commutative S r b -> 
         bop_not_selective S r b -> brel_not_total S (brel_rlte S r b). 
Proof. unfold brel_not_total, brel_rlte. 
       intros S r b symS transS commS [ [s t] P]. 
       exists (s, t). 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       destruct P as [P1 P2]. 
       split. 
          apply (brel_symmetric_implies_dual _ _ symS) in P2. assumption. 
          assert(fact2 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 P1).
          apply (brel_symmetric_implies_dual _ _ symS) in fact2. assumption. 
Defined. 


Definition brel_rlte_total_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     brel_symmetric S r ->  
     brel_transitive S r ->  
     bop_commutative S r b -> 
     bop_selective_decidable S r b -> 
         brel_total_decidable S (brel_rlte S r b)
:= λ S r b symS transS commS d, 
   match d with 
   | inl selS     => inl _ (brel_rlte_total S r b symS transS commS selS)
   | inr not_selS => inr _ (brel_rlte_not_total S r b symS transS commS not_selS) 
   end. 


Lemma brel_rlte_exists_top : ∀ (S : Type) (rS : brel S) (b : binary_op S),  
             brel_symmetric S rS -> 
             bop_exists_ann S rS b -> brel_exists_top S (brel_rlte S rS b). 
Proof.  intros S rS b symS [t P]. 
        exists t. intro s. destruct (P s) as [L R]. compute. 
        apply symS. assumption. 
Defined. 


Lemma brel_rlte_not_exists_top : ∀ (S : Type) (rS : brel S) (b : binary_op S), 
             brel_symmetric S rS -> 
             brel_transitive S rS -> 
             bop_commutative S rS b -> 
                bop_not_exists_ann S rS b -> brel_not_exists_top S (brel_rlte S rS b). 
Proof.  intros S rS b symS transS commS P s. 
        exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           assert (fact1 := commS s w). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ transS _ _ _ fact1 F).
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
Defined. 


Definition brel_rlte_exists_top_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     brel_symmetric S r ->  
     brel_transitive S r ->  
     bop_commutative S r b -> 
     bop_exists_ann_decidable S r b -> 
         brel_exists_top_decidable S (brel_rlte S r b)
:= λ S r b symS transS commS d, 
   match d with 
   | inl idS     => inl _ (brel_rlte_exists_top S r b symS idS)
   | inr no_annS => inr _ (brel_rlte_not_exists_top S r b symS transS commS no_annS) 
   end. 


Lemma brel_rlte_exists_bottom : ∀ (S : Type) (rS : brel S) (b : binary_op S),  
             brel_symmetric S rS -> 
             bop_exists_id S rS b -> brel_exists_bottom S (brel_rlte S rS b). 
Proof.  intros S rS b symS [t P]. 
        exists t. intro s. destruct (P s) as [L R]. compute. 
        apply symS. assumption. 
Defined. 


Lemma brel_rlte_not_exists_bottom : ∀ (S : Type) (rS : brel S) (b : binary_op S), 
             brel_symmetric S rS -> 
             brel_transitive S rS -> 
             bop_commutative S rS b -> 
                bop_not_exists_id S rS b -> brel_not_exists_bottom S (brel_rlte S rS b). 
Proof.  intros S rS b symS transS commS P s. 
        exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
           assert (fact1 := commS w s). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ transS _ _ _ fact1 F).
Defined. 

Definition brel_rlte_exists_bottom_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     brel_symmetric S r ->  
     brel_transitive S r ->  
     bop_commutative S r b -> 
     bop_exists_id_decidable S r b -> 
         brel_exists_bottom_decidable S (brel_rlte S r b)
:= λ S r b symS transS commS d, 
   match d with 
   | inl annS     => inl _ (brel_rlte_exists_bottom S r b symS annS)
   | inr no_idS => inr _ (brel_rlte_not_exists_bottom S r b symS transS commS no_idS) 
   end. 




