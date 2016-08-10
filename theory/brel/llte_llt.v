Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel.conjunction. 
Require Import CAS.theory.brel.complement. 
Require Import CAS.theory.facts. 


(* llte *) 


Lemma brel_llte_true_intro : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
          r s1 (b s1 s2) = true -> brel_llte S r b s1 s2 = true. 
Proof. auto. Defined. 

Lemma brel_llte_false_intro : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
          r s1 (b s1 s2) = false -> brel_llte S r b s1 s2 = false. 
Proof. auto. Defined. 


Lemma brel_llte_true_elim : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
          brel_llte S r b s1 s2 = true -> (r s1 (b s1 s2) = true). 
Proof. auto. Defined. 

Lemma brel_llte_false_elim : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
          brel_llte S r b s1 s2 = false -> (r s1 (b s1 s2) = false). 
Proof. auto. Defined. 

(*
Lemma brel_llte_witness : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_witness S r ->  
         brel_symmetric S r ->  
         bop_idempotent S r b ->  
         brel_witness S (brel_llte S r b). 
Proof. unfold brel_witness, brel_llte. 
       intros S r b [s P] symS idemS. exists s. 
       assert(fact := idemS s). 
       apply symS. assumption. 
Defined. 
*) 


Lemma brel_llte_reflexive : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r -> 
         bop_idempotent S r b -> 
           brel_reflexive S r →  brel_reflexive S (brel_llte S r b). 
Proof. unfold brel_reflexive, brel_llte. 
       intros S r b symS idemS refS s. 
       assert(id := idemS s).  
       apply symS. assumption. 
Defined. 

(* was brel_bop_to_lte_left_congruence *) 
Lemma brel_llte_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S) (b : binary_op S),  
       brel_congruence S r1 r2 -> 
       bop_congruence S r1 b -> 
         brel_congruence S r1 (brel_llte S r2 b). 
Proof. unfold brel_congruence, bop_congruence, brel_llte. 
       intros S r1 r2 b r_cong b_cong s t u v H1 H2. 
       assert (H3 := b_cong _ _ _ _ H1 H2). 
       assert (H4 := r_cong _ _ _ _ H1 H3). 
       assumption. 
Defined. 

(*
   a <= b -> b <= c => a <= c 
   a = a+b -> b = b+c => a = a+c
   a = a +b = a + (b + c) = (a + b) + c = a +c  
*) 
Lemma brel_llte_transitive : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_reflexive S r  →  
         brel_symmetric S r  →  
         bop_associative S r b  →  
         bop_congruence S r b  →  
         brel_transitive S r →  
            brel_transitive S (brel_llte S r b). 
Proof. unfold brel_transitive, brel_llte. 
       intros S r b refS symS assS b_cong transS s t u H1 H2. 
       assert (fact1 : r (b s t) (b s (b t u)) = true).
          apply b_cong. apply refS. assumption. 
       assert (fact2 : r s (b s (b t u)) = true).
          apply (transS _ _ _ H1 fact1). 
       assert (fact3 : r (b (b s t) u) (b s (b t u))  = true). apply assS. 
       assert (fact4 : r (b (b s t) u) (b s u)  = true). 
          apply b_cong. apply symS. assumption. apply refS. 
       apply symS in fact3.          
       assert (fact5 : r (b s (b t u)) (b s u) = true). 
          apply (transS _ _ _ fact3 fact4). 
       apply (transS _ _ _ fact2 fact5). 
Defined. 


Lemma brel_llte_antisymmetric : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r ->  
         brel_transitive S r → 
         bop_commutative S r b -> brel_antisymmetric S r (brel_llte S r b). 
Proof. unfold brel_antisymmetric, brel_llte. 
       intros S r b symS transS commS s t H1 H2. 
       assert (fact1 := commS s t). 
       assert (fact2 : r s (b t s) = true). apply (transS _ _ _ H1 fact1). 
       apply symS in H2. 
       apply (transS _ _ _ fact2 H2). 
Defined. 

Lemma brel_llte_total : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r ->  
         brel_transitive S r ->  
         bop_commutative S r b -> 
         bop_selective S r b -> brel_total S (brel_llte S r b). 
Proof. unfold brel_total, brel_llte. 
       intros S r b symS transS commS selS s t. 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       destruct (selS s t) as [Q | Q]. 
          left. apply symS. assumption. 
          right. apply symS in Q. apply (transS _ _ _ Q fact1). 
Defined. 

Lemma brel_llte_not_total : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r ->  
         brel_transitive S r ->  
         bop_commutative S r b -> 
         bop_not_selective S r b -> brel_not_total S (brel_llte S r b). 
Proof. unfold brel_not_total, brel_llte. 
       intros S r b symS transS commS [ [s t] P]. 
       exists (s, t). 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       destruct P as [P1 P2]. 
       split. 
          apply (brel_symmetric_implies_dual _ _ symS) in P1. assumption. 
          assert(fact2 := brel_transititivity_implies_dual _ _ transS _ _ _ fact1 P2).
          apply (brel_symmetric_implies_dual _ _ symS) in fact2. assumption. 
Defined. 


Definition brel_llte_total_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     brel_symmetric S r ->  
     brel_transitive S r ->  
     bop_commutative S r b -> 
     bop_selective_decidable S r b -> 
         brel_total_decidable S (brel_llte S r b)
:= λ S r b symS transS commS d, 
   match d with 
   | inl selS     => inl _ (brel_llte_total S r b symS transS commS selS)
   | inr not_selS => inr _ (brel_llte_not_total S r b symS transS commS not_selS) 
   end. 




Lemma brel_llte_exists_top : ∀ (S : Type) (rS : brel S) (b : binary_op S),  
             brel_symmetric S rS -> 
             bop_exists_id S rS b -> brel_exists_top S (brel_llte S rS b). 
Proof.  intros S rS b symS [t P]. 
        exists t. intro s. destruct (P s) as [L R]. compute. 
        apply symS. assumption. 
Defined. 


Lemma brel_llte_exists_bottom : ∀ (S : Type) (rS : brel S) (b : binary_op S),  
             brel_symmetric S rS -> 
             bop_exists_ann S rS b -> brel_exists_bottom S (brel_llte S rS b). 
Proof.  intros S rS b symS [t P]. 
        exists t. intro s. destruct (P s) as [L R]. compute. 
        apply symS. assumption. 
Defined. 

Lemma brel_llte_not_exists_top : ∀ (S : Type) (rS : brel S) (b : binary_op S), 
             brel_symmetric S rS -> 
             brel_transitive S rS -> 
             bop_commutative S rS b -> 
                bop_not_exists_id S rS b -> brel_not_exists_top S (brel_llte S rS b). 
Proof.  intros S rS b symS transS commS P s. 
        exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           assert (fact1 := commS s w). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ transS _ _ _ fact1 F).
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
Defined. 


Lemma brel_llte_not_exists_bottom : ∀ (S : Type) (rS : brel S) (b : binary_op S), 
             brel_symmetric S rS -> 
             brel_transitive S rS -> 
             bop_commutative S rS b -> 
                bop_not_exists_ann S rS b -> brel_not_exists_bottom S (brel_llte S rS b). 
Proof.  intros S rS b symS transS commS P s. 
        exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
           assert (fact1 := commS w s). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ transS _ _ _ fact1 F).
Defined. 



(* move *) 

Lemma os_bops_to_llte_bop_left_monotone_v1 : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         brel_reflexive S r  →  
         brel_transitive S r →  
         bop_congruence S r b2 -> 
         bop_left_distributive S r b1 b2 -> 
         os_left_monotone S (brel_llte S r b1) b2. 
Proof. compute. intros S r b1 b2 refS transS cong_b2 ld s t u H. 
       assert (fact1 := ld s t u). 
       assert (fact2 := cong_b2 _ _ _ _ (refS s) H). 
       assert (fact3 := transS _ _ _ fact2 fact1). 
       assumption. 
Defined. 


Lemma os_bops_to_llte_bop_left_monotone_v2 : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         brel_symmetric S r -> 
         bop_is_left S r b1 -> 
         os_left_monotone S (brel_llte S r b1) b2. 
       (* t == (t + u) -> (s * t) = (s * t) + (s * u) *) 
Proof. compute. intros S r b1 b2 symS il s t u H. apply symS. apply il. Defined. 


Lemma os_bops_to_llte_bop_left_monotone : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         brel_symmetric S r -> 
         brel_reflexive S r  →  
         brel_transitive S r →  
         bop_congruence S r b2 -> 
         ((bop_left_distributive S r b1 b2) + (bop_is_left S r b1)) -> 
         os_left_monotone S (brel_llte S r b1) b2. 
       (* t == (t + u) -> (s * t) = (s * t) + (s * u) *) 
Proof. intros S r b1 b2 symS refS transS congS [ld | il]. 
       apply os_bops_to_llte_bop_left_monotone_v1; auto. 
       apply os_bops_to_llte_bop_left_monotone_v2; auto. 
Defined. 


 
Lemma llte_is_lower_bound : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r →  
         brel_symmetric S r →  
         bop_congruence S r b -> 
         brel_transitive S r →  
         bop_associative S r b -> 
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
          ∀ (s t : S), is_lower_bound S (brel_llte S r b) s t (b s t). 
Proof. intros S r b ref sym cong trans assoc comm idem s t. compute. split. 
       (*
             s + t 
             = comm 
             t + s 
             = idem/cong 
             t + (s + s) 
             = assoc 
             (t + s) + s
             = comm/cong 
             (s + t) + s
       *)
       assert (fact1 := comm s t). 
       assert (fact2 := idem s). apply sym in fact2.        
       assert (fact3 := cong _ _ _ _ (ref t) fact2). 
       assert (fact4 := trans _ _ _ fact1 fact3). 
       assert (fact5 := assoc t s s ). apply sym in fact5. 
       assert (fact6 := trans _ _ _ fact4 fact5).       
       assert (fact7 := cong _ _ _ _ fact1 (ref s)). apply sym in fact7. 
       assert (fact8 := trans _ _ _ fact6 fact7).       
       assumption. 
       (*
             s + t 
             = idem/cong 
             s + (t + t) 
             = assoc 
             (s + t) + t
       *)
       assert (fact1 := idem t). apply sym in fact1.        
       assert (fact2 := cong _ _ _ _ (ref s) fact1). 
       assert (fact3 := assoc s t t ). apply sym in fact3. 
       assert (fact4 := trans _ _ _ fact2 fact3).       
       assumption. 
Qed. 

Lemma os_bop_to_llte_bop_is_glb : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r →  
         brel_symmetric S r →  
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_is_glb S (brel_llte S r b) b. 
Proof. intros S r b ref sym trans cong_b assoc_b comm idem. 
       unfold os_is_glb. intros s t. split. 
       apply llte_is_lower_bound; auto. compute. 
       (* note this half just uses associativity *) 
       intros u [L R]. 
       assert (fact1 := cong_b _ _ _ _ L (ref t)). 
       assert (fact2 := assoc_b u s t). 
       assert (fact3 := trans _ _ _ fact1 fact2). 
       assert (fact4 := trans _ _ _ R fact3). 
       assumption. 
Qed. 


Lemma rlte_is_upper_bound : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r →  
         brel_symmetric S r →  
         bop_congruence S r b -> 
         brel_transitive S r →  
         bop_associative S r b -> 
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
          ∀ (s t : S), is_upper_bound S (brel_rlte S r b) s t (b s t). 
Proof. intros S r b ref sym cong trans assoc comm idem s t. compute. split. 
       (*
             s + t 
             = idem/cong 
             (s + s) + t 
             = assoc 
             s + (s + t)
       *)
       assert (fact1 := idem s). apply sym in fact1.        
       assert (fact2 := cong _ _ _ _ fact1 (ref t)). 
       assert (fact3 := assoc s s t ). 
       assert (fact4 := trans _ _ _ fact2 fact3).       
       assumption. 
       (*
             s + t 
             = comm 
             t + s 
             = idem/cong 
             (t + t) + s 
             = assoc 
             t + (t + s)
             = comm/cong 
             t + (s + t)
       *)
       assert (fact1 := comm s t). 
       assert (fact2 := idem t). apply sym in fact2.        
       assert (fact3 := cong _ _ _ _ fact2 (ref s)). 
       assert (fact4 := trans _ _ _ fact1 fact3). 
       assert (fact5 := assoc t t s ). 
       assert (fact6 := trans _ _ _ fact4 fact5).       
       assert (fact7 := cong _ _ _ _ (ref t) fact1). apply sym in fact7. 
       assert (fact8 := trans _ _ _ fact6 fact7).       
       assumption. 
Qed. 

Lemma os_bop_to_rlte_bop_is_lub : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r →  
         brel_symmetric S r →  
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_is_lub S (brel_rlte S r b) b. 
Proof. intros S r b ref sym trans cong_b assoc_b comm idem. 
       unfold os_is_lub. intros s t. split. 
       apply rlte_is_upper_bound; auto. compute. 
       (* note this half just uses associativity *) 
       intros u [L R]. 
       assert (fact1 := cong_b _ _ _ _ (ref s) R). 
       assert (fact2 := assoc_b s t u). apply sym in fact2. 
       assert (fact3 := trans _ _ _ fact1 fact2). 
       assert (fact4 := trans _ _ _ L fact3). 
       assumption. 
Qed. 


Lemma os_bop_to_llte_bop_left_monotone_v1 : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_left_monotone S (brel_llte S r b) b. 
Proof. intros S r b ref sym trans cong assoc comm idem. compute. intros s t u H. 
       (* H : t = t + u 

          s + t 
          = cong/H 
          s + (t + u) 
          = idem/cong 
          (s + s) + (t + u)          
          = assoc 
          s + (s + (t + u))           
          = assoc/cong 
          s + ((s + t) + u)           
          = comm/cong 
          s + ((t + s) + u)           
          = assoc/cong 
          s + (t + (s + u))           
          = assoc 
          (s + t) + (s + u) 
       *) 
      assert (fact1 := cong _ _ _ _ (ref s) H). 
      assert (fact2 := idem s). apply sym in fact2. 
      assert (fact3 := cong _ _ _ _ fact2 H). 
      assert (fact4 := assoc s s (b t u)). apply sym in fact2.       
      assert (fact5 := trans _ _ _ fact3 fact4). 
      assert (fact6 := assoc s t u). apply sym in fact6.       
      assert (fact7 := cong _ _ _ _ (ref s) fact6). 
      assert (fact8 := trans _ _ _ fact5 fact7). 
      assert (fact9 := comm s t). 
      assert (fact10 := cong _ _ _ _ fact9 (ref u)). 
      assert (fact11 := cong _ _ _ _ (ref s) fact10). 
      assert (fact12 := trans _ _ _ fact8 fact11). 
      assert (fact13 := assoc t s u). 
      assert (fact14 := cong _ _ _ _ (ref s) fact13). 
      assert (fact15 := trans _ _ _ fact12 fact14). 
      assert (fact16 := assoc s t (b s u)). apply sym in fact16. 
      assert (fact17 := trans _ _ _ fact15 fact16). 
      assumption. 
Defined. 


Lemma os_bop_to_llte_bop_right_monotone_v1 : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_right_monotone S (brel_llte S r b) b. 
Proof. intros S r b ref sym trans cong assoc comm idem. compute. intros s t u H. 
       (* H : t = t + u 

          t + s 
          = cong/H 
          (t + u) + s 
          = idem/cong 
          (t + u) + (s + s) 
          = assoc 
          t + (u + (s + s)) 
          = assoc/cong 
          t + ((u + s) + s) 
          = comm/cong 
          t + ((s + u) + s) 
          = assoc/cong 
          t + (s + (u + s)) 
          = assoc 
          (t + s) + (u + s) 
       *) 
      assert (fact1 := cong _ _ _ _ H (ref s)). 
      assert (fact2 := idem s). apply sym in fact2. 
      assert (fact3 := cong _ _ _ _ H fact2). 
      assert (fact4 := assoc t u (b s s)). 
      assert (fact5 := trans _ _ _ fact3 fact4). 
      assert (fact6 := assoc u s s). apply sym in fact6.       
      assert (fact7 := cong _ _ _ _ (ref t) fact6). 
      assert (fact8 := trans _ _ _ fact5 fact7). 
      assert (fact9 := comm u s). 
      assert (fact10 := cong _ _ _ _ fact9 (ref s)). 
      assert (fact11 := cong _ _ _ _ (ref t) fact10). 
      assert (fact12 := trans _ _ _ fact8 fact11). 
      assert (fact13 := assoc s u s). 
      assert (fact14 := cong _ _ _ _ (ref t) fact13). 
      assert (fact15 := trans _ _ _ fact12 fact14). 
      assert (fact16 := assoc t s (b u s)). apply sym in fact16. 
      assert (fact17 := trans _ _ _ fact15 fact16). 
      assumption. 
Defined. 




Lemma os_bop_to_rlte_bop_left_monotone_v1 : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_left_monotone S (brel_rlte S r b) b. 
Proof. intros S r b ref sym trans cong assoc comm idem. compute. intros s t u H. 
       (* H : u = t + u 

          s + u 
          = cong/H 
          s + (t + u) 
          = idem/cong 
          (s + s) + (t + u)          
          = assoc 
          s + (s + (t + u))           
          = assoc/cong 
          s + ((s + t) + u)           
          = comm/cong 
          s + ((t + s) + u)           
          = assoc/cong 
          s + (t + (s + u))           
          = assoc 
          (s + t) + (s + u) 
       *) 
      assert (fact1 := cong _ _ _ _ (ref s) H). 
      assert (fact2 := idem s). apply sym in fact2. 
      assert (fact3 := cong _ _ _ _ fact2 H). 
      assert (fact4 := assoc s s (b t u)). apply sym in fact2.       
      assert (fact5 := trans _ _ _ fact3 fact4). 
      assert (fact6 := assoc s t u). apply sym in fact6.       
      assert (fact7 := cong _ _ _ _ (ref s) fact6). 
      assert (fact8 := trans _ _ _ fact5 fact7). 
      assert (fact9 := comm s t). 
      assert (fact10 := cong _ _ _ _ fact9 (ref u)). 
      assert (fact11 := cong _ _ _ _ (ref s) fact10). 
      assert (fact12 := trans _ _ _ fact8 fact11). 
      assert (fact13 := assoc t s u). 
      assert (fact14 := cong _ _ _ _ (ref s) fact13). 
      assert (fact15 := trans _ _ _ fact12 fact14). 
      assert (fact16 := assoc s t (b s u)). apply sym in fact16. 
      assert (fact17 := trans _ _ _ fact15 fact16). 
      assumption. 
Defined. 



Lemma os_bop_to_rlte_bop_right_monotone_v1 : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_right_monotone S (brel_rlte S r b) b. 
Proof. intros S r b ref sym trans cong assoc comm idem. compute. intros s t u H. 
       (* H : u = t + u 

          u + s 
          = cong/H 
          (t + u) + s 
          = idem/cong 
          (t + u) + (s + s) 
          = assoc 
          t + (u + (s + s)) 
          = assoc/cong 
          t + ((u + s) + s) 
          = comm/cong 
          t + ((s + u) + s) 
          = assoc/cong 
          t + (s + (u + s)) 
          = assoc 
          (t + s) + (u + s) 
       *) 
      assert (fact1 := cong _ _ _ _ H (ref s)). 
      assert (fact2 := idem s). apply sym in fact2. 
      assert (fact3 := cong _ _ _ _ H fact2). 
      assert (fact4 := assoc t u (b s s)). 
      assert (fact5 := trans _ _ _ fact3 fact4). 
      assert (fact6 := assoc u s s). apply sym in fact6.       
      assert (fact7 := cong _ _ _ _ (ref t) fact6). 
      assert (fact8 := trans _ _ _ fact5 fact7). 
      assert (fact9 := comm u s). 
      assert (fact10 := cong _ _ _ _ fact9 (ref s)). 
      assert (fact11 := cong _ _ _ _ (ref t) fact10). 
      assert (fact12 := trans _ _ _ fact8 fact11). 
      assert (fact13 := assoc s u s). 
      assert (fact14 := cong _ _ _ _ (ref t) fact13). 
      assert (fact15 := trans _ _ _ fact12 fact14). 
      assert (fact16 := assoc t s (b u s)). apply sym in fact16. 
      assert (fact17 := trans _ _ _ fact15 fact16). 
      assumption. 
Defined. 

Lemma os_bop_to_llte_bop_left_increasing : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_idempotent S r b -> 
         bop_is_left S r b -> 
            os_left_increasing S (brel_llte S r b) b. 
Proof. intros S r b ref sym trans cong assoc idem il. compute. intros s t. 
       (* 
          s 
          = is left 
          s + t 
          = idem/cong 
          (s + s) + t 
          = assoc 
          s + (s + t)
       *) 
       assert (fact1 := il s t). apply sym in fact1. 
       assert (fact2 := cong _ _ _ _ (idem s) (ref t)). apply sym in fact2. 
       assert (fact3 := trans _ _ _ fact1 fact2). 
       assert (fact4 := assoc s s t). 
       assert (fact5 := trans _ _ _ fact3 fact4). 
       assumption. 
Defined. 


Lemma os_bop_to_llte_bop_not_left_increasing : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_idempotent S r b -> 
         bop_not_is_left S r b -> 
            os_not_left_increasing S (brel_llte S r b) b. 
Proof. intros S r b ref sym trans cong assoc idem [[s t] P]. compute. 
       exists (s, t). 
       admit. 
Defined. 




Lemma os_bop_to_rlte_bop_left_increasing : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_left_increasing S (brel_rlte S r b) b. 
Proof. intros S r b ref sym trans cong assoc comm idem. compute. intros s t. 
       (* 
          s + t 
          = idem/cong 
          (s + s) + t
          = assoc 
          s + (s + t) 
       *) 
       admit. 
Defined. 


Lemma os_bop_to_rlte_bop_right_increasing : ∀ (S : Type) (r :brel S) (b : binary_op S),  
         brel_reflexive S r  → 
         brel_symmetric S r →   
         brel_transitive S r →  
         bop_congruence S r b -> 
         bop_associative S r b ->
         bop_commutative S r b -> 
         bop_idempotent S r b -> 
            os_right_increasing S (brel_rlte S r b) b. 
Proof. intros S r b ref sym trans cong assoc comm idem. compute. intros s t. 
       (* 
          t + s 
          = idem/cong 
          t + (s + s)
          = assoc 
          (t + s) + s
          = comm
          (s + t) + s
          = assoc 
          s + (t + s) 
       *) 
       admit. 
Defined. 





(* rlte *) 

Lemma brel_rlte_reflexive : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_symmetric S r -> 
         bop_idempotent S r b -> 
           brel_reflexive S r →  brel_reflexive S (brel_rlte S r b). 
Proof. unfold brel_reflexive, brel_rlte. 
       intros S r b symS idemS refS s. 
       assert(id := idemS s).  
       apply symS. assumption. 
Defined. 

(* was brel_bop_to_lte_left_congruence *) 
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


(* llt *) 


(* 
WAS 
(s1 = s1 + s2) -> (s2 <> (s1 + s2)) -> s1 < s2 

NOW (s1 = s1 + s2) -> (s1 <> s2 -> s1 < s2 

was brel_bop_to_lt_left_true_intro
*) 
Lemma brel_llt_true_intro : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
        (r s1 (b s1 s2) = true) -> 
        (r s1 s2 = false) -> 
           brel_llt S r b s1 s2 = true. 
Proof. intros S r b s1 s2 H1 H2. 
       unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       rewrite H1, H2. simpl. reflexivity. 
Defined. 

(*
((s1 <> s1 + s2) + (s1 = s2)) -> not(s1 < s2)

WAS brel_bop_to_lt_left_false_intro
*) 
Lemma brel_llt_false_intro : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
        (r s1 (b s1 s2) = false) + (r s1 s2 = true) -> 
           brel_llt S r b s1 s2 = false. 
Proof. unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       intros S r b s1 s2 [H | H].        
          rewrite H. simpl. reflexivity. 
          rewrite H. simpl. apply andb_comm. 
Defined. 


(* 
   s1 < s2 -> (s1 = s1 + s2) * (s1 <> s2)

WAS brel_bop_to_lt_left_true_elim

*) 
Lemma brel_llt_true_elim : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
        brel_llt S r b s1 s2 = true -> 
          (r s1 (b s1 s2) = true) * (r s1 s2 = false). 
Proof. unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       intros S r b s1 s2 H. 
       apply andb_is_true_left in H. destruct H as [L R]. 
       apply negb_true_elim in R. rewrite L, R. split; reflexivity. 
Defined. 

(* 
   not(s1 < s2) -> (s1 <> s1 + s2) + (s1 = s2)

WAS brel_bop_to_lt_left_false_elim 

*) 

Lemma brel_llt_false_elim : ∀ (S : Type) (r : brel S) (b : binary_op S) (s1 s2 : S), 
        brel_llt S r b s1 s2 = false -> 
          (r s1 (b s1 s2) = false) + (r s1 s2 = true). 
Proof. unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       intros S r b s1 s2 H. 
       apply andb_is_false_left in H. destruct H as [H | H]. 
          rewrite H. left. reflexivity. 
          apply negb_false_elim in H. rewrite H. right. reflexivity. 
Defined. 


(* was brel_bop_to_lt_left_irreflexive *) 
Lemma brel_llt_irreflexive : ∀ (S : Type) (r : brel S) (b : binary_op S), 
        brel_reflexive S r  -> brel_irreflexive S (brel_llt S r b). 
Proof. unfold brel_llt. intros S r b ref x. 
       apply brel_conjunction_irreflexive_right. 
       apply brel_complement_irreflexive; auto. 
Defined. 


(* was brel_bop_to_lt_left_congruence *) 
Lemma brel_llt_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S) (b : binary_op S),  
       brel_congruence S r1 r2 -> 
       bop_congruence S r1 b -> 
         brel_congruence S r1 (brel_llt S r2 b). 
Proof. unfold brel_llt. 
       intros S r1 r2 b r_cong b_cong.
       apply brel_conjunction_congruence. 
       apply brel_llte_congruence; auto. 
       apply brel_complement_congruence; auto. 
Defined. 

(*  
    s1 < s2 -> s2 < s1 = false 

was brel_bop_to_lt_left_asymmetric
*) 
Lemma brel_llt_asymmetric : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          brel_symmetric S r → 
          brel_transitive S r → 
          bop_commutative S r b → 
             brel_asymmetric S (brel_llt S r b). 
Proof. unfold brel_asymmetric, brel_llt. unfold brel_llte. 
       unfold brel_conjunction, brel_complement. 
       intros S r b symS transS commS s1 s2 H.        
       apply andb_is_true_left in H. destruct H as [H1 H2].
       apply negb_true_elim in H2. 
       assert (C := commS s1 s2).
       assert (D := transS _ _ _ H1 C). 
       assert (E := brel_transititivity_implies_dual _ _ transS _ _ _ D H2). 
       apply (brel_symmetric_implies_dual S r symS) in E.
       rewrite E. simpl. reflexivity. 
Defined. 

(* STUDY! *) 
Lemma brel_llt_asymmetric_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          (∀ s t : S, r s t = false → r t s = true) → 
             brel_asymmetric S (brel_llt S r b). 
Proof. intros S r b Ks1 s2 H. 
       apply brel_conjunction_asymmetric_right. 
       apply brel_complement_asymmetric. assumption. 
Defined. 


(* interesting : commutativity not used *) 

Lemma brel_llt_total_order_split : ∀ (S : Type) (r : brel S) (b : binary_op S ),
     brel_reflexive S r → 
     brel_symmetric S r → 
     brel_transitive S r → 
     bop_congruence S r b → 
     bop_selective S r b → 
      ∀  (x y : S), 
      ((r x y = true)  *  (brel_llt S r b x y = false)) 
    + ((r x y = false) *  (brel_llt S r b x y = true)) 
    + ((r x y = false) *  (brel_llt S r b x y = false)).  
Proof. intros S r b refS symS transS congS selS x y. 
       unfold bop_congruence in congS. 
       assert (idemS := bop_selective_implies_idempotent _ _ _ selS).
       case_eq(r x  y); intro H. 
          left. left. split. 
             reflexivity. 
             unfold brel_llt. assert (Ix := idemS x). assert (Iy := idemS y). 
             assert (K := congS x y x x (refS x) (symS x y H)). 
             assert (Q : r y (b x y) = true). apply symS in K. apply symS in H. apply symS in Ix. 
                   apply (transS _ _ _ H  (transS _ _ _ Ix K)). 
             unfold brel_conjunction, brel_llte, brel_complement. 
             rewrite H. apply andb_comm. 
          unfold brel_llt. unfold brel_conjunction, brel_llte, brel_complement. 
          destruct (selS x y) as [K | K]; apply symS in K. 
             left. right. split.
                reflexivity.                          
                assert (J := brel_transititivity_implies_dual _ _ transS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J. 
                unfold brel_bop_to_lte_left. rewrite K, H. simpl. reflexivity. 
             right. split.
                reflexivity.                          
                apply (brel_symmetric_implies_dual _ _ symS) in H. 
                assert (J := brel_transititivity_implies_dual _ _ transS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J.
                rewrite J. simpl. reflexivity. 
Defined.  



(* rlt *) 

