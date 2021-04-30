Require Import Coq.Bool.Bool.
Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.theory.conjunction. 
Require Import CAS.coq.theory.complement. 
Require Import CAS.coq.theory.facts. 

Section Llte.

Variable S : Type.
Variable r : brel S.
Variable b : binary_op S.

Variable symS : brel_symmetric S r.
Variable refS : brel_reflexive S r.
Variable tranS : brel_transitive S r. 

Variable assS : bop_associative S r b.
Variable b_cong : bop_congruence S r b. 
         


Notation "x == y"  := (r x y = true)              (at level 30).
Notation "x != y"  := (r x y = false)             (at level 15).
Notation "x <<= y" := (brel_llte r b x y = true)  (at level 15).
Notation "x !<= y" := (brel_llte r b x y = false) (at level 15).
Notation "x << y"  := (brel_llt r b x y = true)   (at level 15).
Notation "x !< y"  := (brel_llt r b x y = false)   (at level 15).
Notation "x @ y"   := (b x y)                     (at level 15).

Lemma brel_llte_true_intro : ∀ (s1 s2 : S), s1 == (s1 @ s2) -> s1 <<= s2. 
Proof. auto. Qed. 

Lemma brel_llte_false_intro : ∀ (s1 s2 : S), s1 != (s1 @ s2) -> s1 !<= s2. 
Proof. auto. Defined. 

Lemma brel_llte_true_elim : ∀ (s1 s2 : S), s1 <<= s2 -> s1 == (s1 @ s2).
Proof. auto. Defined. 

Lemma brel_llte_false_elim : ∀ (s1 s2 : S), s1 !<= s2 -> s1 != (s1 @ s2). 
Proof. auto. Defined. 

Lemma brel_llte_reflexive : bop_idempotent S r b →  brel_reflexive S (brel_llte r b). 
Proof. unfold brel_reflexive, brel_llte. 
       intros idemS s. 
       assert(id := idemS s).  
       apply symS. assumption. 
Defined. 

Lemma brel_llte_congruence : ∀ (r1 : brel S) (r2 : brel S),
       brel_congruence S r1 r2 -> 
       bop_congruence S r1 b -> 
         brel_congruence S r1 (brel_llte r2 b). 
Proof. unfold brel_congruence, bop_congruence, brel_llte. 
       intros r1 r2 congr congb s t u v H1 H2. 
       assert (H3 := congb _ _ _ _ H1 H2). 
       assert (H4 := congr _ _ _ _ H1 H3). 
       assumption. 
Defined. 

(*
   a = a @ b 
     = a @ (b @ c) 
     = (a @ b) @ c 
     = a @ c  
*) 
Lemma brel_llte_transitive : brel_transitive S (brel_llte r b). 
Proof. unfold brel_transitive, brel_llte. 
       intros s t u H1 H2. 
       assert (fact1 : s @ t == s @ (t @ u)).
          apply b_cong. apply refS. assumption. 
       assert (fact2 : s == s @ (t @ u)).
          apply (tranS _ _ _ H1 fact1). 
       assert (fact3 : (s @ t) @ u == s @ (t @ u)). apply assS. 
       assert (fact4 : (s @ t) @ u == s @ u). 
          apply b_cong. apply symS. assumption. apply refS. 
       apply symS in fact3.          
       assert (fact5 : s @ (t @ u) == s @ u). 
          apply (tranS _ _ _ fact3 fact4). 
       apply (tranS _ _ _ fact2 fact5). 
Defined. 


Lemma brel_llte_antisymmetric : bop_commutative S r b -> brel_antisymmetric S r (brel_llte r b). 
Proof. unfold brel_antisymmetric, brel_llte. 
       intros commS s t H1 H2. 
       assert (fact1 := commS s t). 
       assert (fact2 : s == t @ s). apply (tranS _ _ _ H1 fact1). 
       apply symS in H2. 
       apply (tranS _ _ _ fact2 H2). 
Defined. 

Lemma brel_llte_total : bop_commutative S r b -> bop_selective S r b -> brel_total S (brel_llte r b). 
Proof. unfold brel_total, brel_llte. 
       intros commS selS s t. 
       assert (fact1 : s @ t == t @ s). apply commS. 
       destruct (selS s t) as [Q | Q]. 
          left. apply symS. exact Q. 
          right. apply symS in Q. apply (tranS _ _ _ Q fact1). 
Defined. 

Lemma brel_llte_not_total : bop_commutative S r b -> bop_not_selective S r b -> brel_not_total S (brel_llte r b). 
Proof. unfold brel_not_total, brel_llte. 
       intros commS [ [s t] P]. 
       exists (s, t). 
       assert (fact1 : s @ t == t @ s). apply commS. 
       destruct P as [P1 P2]. 
       split. 
          apply (brel_symmetric_implies_dual _ _ symS) in P1. assumption. 
          assert(fact2 := brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 P2).
          apply (brel_symmetric_implies_dual _ _ symS) in fact2. assumption. 
Defined. 

(*
Lemma brel_llte_exists_top : bop_exists_id S r b -> brel_exists_top S (brel_llte r b). 
Proof.  intros [t P]. exists t. intro s. destruct (P s) as [L R]. compute. apply symS. assumption. Defined. 


Lemma brel_llte_not_exists_top : bop_commutative S r b -> bop_not_exists_id S r b -> brel_not_exists_top S (brel_llte r b). 
Proof.  intros commS P s. exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           assert (fact1 := commS s w). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 F).
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
Defined. 



Lemma brel_llte_exists_bottom : bop_exists_ann S r b -> brel_exists_bottom S (brel_llte r b). 
Proof.  intros [t P]. exists t. intro s. destruct (P s) as [L R]. compute. apply symS. assumption. Defined. 


Lemma brel_llte_not_exists_bottom : bop_commutative S r b -> bop_not_exists_ann S r b -> brel_not_exists_bottom S (brel_llte r b). 
Proof.  intros commS P s. exists (projT1 (P s)). 
        destruct (P s) as [w [F | F]]; compute. 
           apply (brel_symmetric_implies_dual _ _ symS); auto. 
           assert (fact1 := commS w s). 
           apply (brel_symmetric_implies_dual _ _ symS). 
           apply (brel_transititivity_implies_dual _ _ tranS _ _ _ fact1 F).
Defined. 

*) 

(* llt *) 

Lemma brel_llt_true_intro : ∀ (s1 s2 : S), (s1 == s1 @ s2) -> (s1 != s2) -> s1 << s2. 
Proof. intros s1 s2 H1 H2. 
       unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       rewrite H1, H2. simpl. reflexivity. 
Defined. 

Lemma brel_llt_false_intro : ∀ (s1 s2 : S), (s1 != (s1 @ s2)) + (s1 == s2) -> s1 !< s2. 
Proof. unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       intros s1 s2 [H | H].        
          rewrite H. simpl. reflexivity. 
          rewrite H. simpl. apply andb_comm. 
Defined. 


Lemma brel_llt_true_elim : ∀ (s1 s2 : S), s1 << s2 -> (s1 == s1 @ s2) * (s1 != s2). 
Proof. unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       intros s1 s2 H. 
       apply andb_is_true_left in H. destruct H as [L R]. 
       apply negb_true_elim in R. rewrite L, R. split; reflexivity. 
Defined. 

Lemma brel_llt_false_elim : ∀ (s1 s2 : S), s1 !< s2 -> (s1 != (s1 @ s2)) + (s1 == s2). 
Proof. unfold brel_llt. unfold brel_conjunction, brel_complement, brel_llte. 
       intros s1 s2 H. 
       apply andb_is_false_left in H. destruct H as [H | H]. 
          rewrite H. left. reflexivity. 
          apply negb_false_elim in H. rewrite H. right. reflexivity. 
Defined. 


Lemma brel_llt_irreflexive : brel_irreflexive S (brel_llt r b). 
Proof. unfold brel_llt. intros x. 
       apply brel_conjunction_irreflexive_right. 
       apply brel_complement_irreflexive; auto. 
Defined. 


Lemma brel_llt_congruence : ∀ (r1 : brel S) (r2 : brel S),  
       brel_congruence S r1 r2 -> 
       bop_congruence S r1 b -> 
         brel_congruence S r1 (brel_llt r2 b). 
Proof. unfold brel_llt. 
       intros r1 r2 cong1 cong2.
       apply brel_conjunction_congruence. 
       apply brel_llte_congruence; auto. 
       apply brel_complement_congruence; auto. 
Defined. 

(*  
    s1 < s2 -> s2 < s1 = false 

*) 
Lemma brel_llt_asymmetric : bop_commutative S r b → brel_asymmetric S (brel_llt r b). 
Proof. unfold brel_asymmetric, brel_llt. unfold brel_llte. 
       unfold brel_conjunction, brel_complement. 
       intros commS s1 s2 H.        
       apply andb_is_true_left in H. destruct H as [H1 H2].
       apply negb_true_elim in H2. 
       assert (C := commS s1 s2).
       assert (D := tranS _ _ _ H1 C). 
       assert (E := brel_transititivity_implies_dual _ _ tranS _ _ _ D H2). 
       apply (brel_symmetric_implies_dual S r symS) in E.
       rewrite E. simpl. reflexivity. 
Defined. 

(* 
Lemma brel_llt_asymmetric_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
          (∀ s t : S, r s t = false → r t s = true) → 
             brel_asymmetric S (brel_llt S r b). 
Proof. intros S r b Ks1 s2 H. 
       apply brel_conjunction_asymmetric_right. 
       apply brel_complement_asymmetric. assumption. 
Defined. 
*) 

(* interesting : commutativity not used *) 

Lemma brel_llt_total_order_split : bop_selective S r b → 
      ∀  (x y : S), 
      ((r x y = true)  *  (brel_llt r b x y = false)) 
    + ((r x y = false) *  (brel_llt r b x y = true)) 
    + ((r x y = false) *  (brel_llt r b x y = false)).  
Proof. intros selS x y. 
       assert (idemS := bop_selective_implies_idempotent _ _ _ selS).
       case_eq(r x  y); intro H. 
          left. left. split. 
             reflexivity. 
             unfold brel_llt. assert (Ix := idemS x). assert (Iy := idemS y). 
             assert (K := b_cong x y x x (refS x) (symS x y H)). 
             assert (Q : r y (b x y) = true). apply symS in K. apply symS in H. apply symS in Ix. 
                   apply (tranS _ _ _ H  (tranS _ _ _ Ix K)). 
             unfold brel_conjunction, brel_llte, brel_complement. 
             rewrite H. apply andb_comm. 
          unfold brel_llt. unfold brel_conjunction, brel_llte, brel_complement. 
          destruct (selS x y) as [K | K]; apply symS in K. 
             left. right. split.
                reflexivity.                          
                assert (J := brel_transititivity_implies_dual _ _ tranS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J. 
                rewrite K, H. simpl. reflexivity. 
             right. split.
                reflexivity.                          
                apply (brel_symmetric_implies_dual _ _ symS) in H. 
                assert (J := brel_transititivity_implies_dual _ _ tranS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J.
                rewrite J. simpl. reflexivity.
Defined.  

(*
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

Definition brel_llte_exists_top_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     brel_symmetric S r ->  
     brel_transitive S r ->  
     bop_commutative S r b -> 
     bop_exists_id_decidable S r b -> 
         brel_exists_top_decidable S (brel_llte S r b)
:= λ S r b symS transS commS d, 
   match d with 
   | inl idS     => inl _ (brel_llte_exists_top S r b symS idS)
   | inr no_idS => inr _ (brel_llte_not_exists_top S r b symS transS commS no_idS) 
   end. 

Definition brel_llte_exists_bottom_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (b : binary_op S), 
     brel_symmetric S r ->  
     brel_transitive S r ->  
     bop_commutative S r b -> 
     bop_exists_ann_decidable S r b -> 
         brel_exists_bottom_decidable S (brel_llte S r b)
:= λ S r b symS transS commS d, 
   match d with 
   | inl annS     => inl _ (brel_llte_exists_bottom S r b symS annS)
   | inr no_annS => inr _ (brel_llte_not_exists_bottom S r b symS transS commS no_annS) 
   end. 

*) 

End Llte. 