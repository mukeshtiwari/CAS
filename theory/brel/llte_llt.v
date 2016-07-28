Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.brel.conjunction. 
Require Import CAS.theory.brel.complement. 
Require Import CAS.theory.facts. 


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


(* 

Lemma brel_llte_negate : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         brel_negate S r ->  
         brel_transitive S r ->  
         bop_idempotent S r b ->  
         bop_not_is_left S r b ->  
         bop_not_is_right S r b ->  
         brel_negate S (brel_llte S r b). 
Proof. unfold brel_negate, brel_llte, bop_not_is_left,  bop_not_is_right. 
       intros S r b [g P] transS idemS [s1 [s2 P1]] [s3 [s4 P2]]. 
       exists  (λ (s : S),(b (g s) (g s))). intro s. 
       assert(fact1 := idemS (g s)). 
       assert(fact2 := P s). destruct fact2 as [L R]. 
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

(* was brel_bop_to_lt_left_irreflexive *) 
Lemma brel_llt_irreflexive : ∀ (S : Type) (r : brel S) (b : binary_op S), 
        brel_reflexive S r  -> brel_irreflexive S (brel_llt S r b). 
Proof. unfold brel_llt. intros S r b ref x. 
       apply brel_conjunction_irreflexive_right. 
       apply brel_complement_irreflexive; auto. 
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
       intros S r b symS transS commS [ [s t] [P1 P2]]. 
       assert (fact1 : r (b s t) (b t s) = true). apply commS. 
       exists (s, t). split. 
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



(**************************************************************************)

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





