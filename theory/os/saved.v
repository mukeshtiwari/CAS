Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.conjunction. 
Require Import CAS.theory.brel.complement. 
Require Import CAS.theory.facts. 

(* *********************** (S, b1, b2) ---> (S, <=, b2) **************************** *) 

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


Lemma os_bops_to_llte_bop_left_monotone_v3 : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         brel_reflexive S r  →  
         brel_symmetric S r -> 
         brel_transitive S r →  
         bop_congruence S r b2 -> 
         bop_is_right S r b1 -> 
         os_left_monotone S (brel_llte S r b1) b2. 
       (* t == (t + u) -> (s * t) = (s * t) + (s * u) *) 
Proof. compute. intros S r b1 b2 ref sym trans cong ir s t u H. 
       (*

          H: t = t + u 

          s * t 
          = cong/H
          s * (t + u) 
          = is_right 
          s * u  
          = is_right 
          (s * t) + (s * u) 
*) 
       assert (fact3 := cong _ _ _ _ (ref s) H). 
       assert (fact4 := ir t u). 
       assert (fact5 := cong _ _ _ _ (ref s) fact4). 
       assert (fact6 := trans _ _ _ fact3 fact5).       
       assert (fact7 := ir (b2 s t) (b2 s u)). apply sym in fact7. 
       assert (fact8 := trans _ _ _ fact6 fact7).       
       assumption. 
Defined. 




Lemma os_bops_to_llte_bop_left_monotone : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         brel_symmetric S r -> 
         brel_reflexive S r  →  
         brel_transitive S r →  
         bop_congruence S r b2 -> 
         ((bop_left_distributive S r b1 b2) + (bop_is_left S r b1) + (bop_is_right S r b1)) -> 
         os_left_monotone S (brel_llte S r b1) b2. 
       (* t == (t + u) -> (s * t) = (s * t) + (s * u) *) 
Proof. intros S r b1 b2 symS refS transS congS [[ld | il ] | ir]. 
       apply os_bops_to_llte_bop_left_monotone_v1; auto. 
       apply os_bops_to_llte_bop_left_monotone_v2; auto. 
       apply os_bops_to_llte_bop_left_monotone_v3; auto. 
Defined. 


(* this does not seem to work. 

  One solution : for (S, b1, b2) ---> (S, <=, b2), requre that 
  (S, b1, b2) is both left- and right-distributive. 

  Another solution?  introduce a new bi-semigroup property 

  PL: t == (t + u) -> (s * t) = (s * t) + (s * u)

  Note: left-distributivity (LD) implies P. But PL is weaker. 

  Right version? 

  PR: s == (s + t) -> (s * u) = (s * u) + (s * u)


  Question: is there a Q such that 
   
   PL & Q <---> LD  
   or 
   Q --> (PL <---> LD) 

The other ones : 


Lemma os_bops_to_llte_bop_right_monotone : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         os_right_monotone S (brel_llte S r b1) b2. 
       (* t == (t + u) -> (t * s) = (t * s) + (u * s) *) 

Lemma os_bops_to_rlte_bop_right_monotone : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         os_right_monotone S (brel_rlte S r b1) b2. 
       (* u == (t + u) -> (u * s) = (t * s) + (u * s) *) 

Lemma os_bops_to_rlte_bop_left_monotone : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         os_left_monotone S (brel_rlte S r b1) b2. 
       (* u == (t + u) -> (s * u) = (s * t) + (s * u) *) 




Lemma os_bops_to_llte_bop_not_left_monotone : ∀ (S : Type) (r :brel S) (b1 b2 : binary_op S),  
         brel_symmetric S r -> 
         brel_reflexive S r  →  
         brel_transitive S r →  
         bop_congruence S r b2 -> 
         bop_not_left_distributive S r b1 b2 -> 
         bop_not_is_left S r b1 -> 
         bop_not_is_right S r b1 -> 
            os_not_left_monotone S (brel_llte S r b1) b2. 
Proof. intros S r b1 b2 symS refS transS congS [[s [t u]] P] [[w v] Q] [[x y] R]. compute. 
       case_eq(r t (b1 t u)); intro H. 
          exists (s, (t, u)). split.        
             assumption. 
             admit.      (* OK *)   
          assert (fact1 : r t u = false). admit. 
          assert (fact2 : r x y = false). admit. 
          assert (fact3 : r w v = false). admit. 

Defined. 


*) 





(* *********************** (S, b) ---> (S, <=, b) **************************** *) 
 
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
       assert (fact : r s (b s (b s t)) = true -> r (b s t) s = true). 
          intro H. 
          assert (fact1 := assoc s s t). apply sym in fact1. 
          assert (fact2 := trans _ _ _ H fact1). 
          assert (fact3 := cong _ _ _ _ (idem s) (ref t)). 
          assert (fact4 := trans _ _ _ fact2 fact3). 
          apply sym. assumption. 
       case_eq(r s (b s (b s t))); intro H. 
          apply fact in H. rewrite H in P. assumption. 
          reflexivity. 
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
       assert (fact1 := cong _ _ _ _ (idem s) (ref t)). apply sym in fact1. 
       assert (fact2 := assoc s s t).        
       assert (fact3 := trans _ _ _ fact1 fact2). 
       assumption. 
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
       assert (fact1 := cong _ _ _ _ (ref t) (idem s)). apply sym in fact1. 
       assert (fact2 := assoc t s s).  apply sym in fact2.       
       assert (fact3 := trans _ _ _ fact1 fact2). 
       assert (fact4 := comm t s). 
       assert (fact5 := cong _ _ _ _ fact4 (ref s)). 
       assert (fact6 := trans _ _ _ fact3 fact5). 
       assert (fact7 := assoc s t s).  apply sym in fact2.       
       assert (fact8 := trans _ _ _ fact6 fact7). 
       assumption. 
Defined. 

