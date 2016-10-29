Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.set. 
Require Import CAS.theory.brel.complement
Require Import CAS.theory.brel.conjunction. 
Require Import CAS.theory.brel.dual. 
Require Import CAS.theory.brel.strictify. 
Require Import CAS.theory.brel.subset. 
Require Import CAS.theory.brel.in_set. 
Require Import CAS.theory.bop.list_product. 


Section LessThan. 

Variable S  : Type. 
Variable rS : brel S. 
Variable lte : brel S. 

Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.
Variable cong_rS : brel_congruence S rS rS. 

Variable ref_lte : brel_reflexive S lte. 
Variable trans_lte  : brel_transitive S lte.  
Variable cong_lte: brel_congruence S rS lte. 


Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).

Notation "a <== b"  := (lte a b = true) (at level 15).
Notation "a !<== b"  := (lte a b = false) (at level 15).

Notation "a << b"  := (brel_strictify S lte a b = true) (at level 15).
Notation "a !<< b"  := (brel_strictify S lte a b = false) (at level 15). 
Notation "a # b"  := ( (brel_conjunction _ (brel_complement _ lte) (brel_complement _ (brel_dual _ lte))) a b = true ) (at level 15).

Notation "a !# b"  := ( (brel_conjunction S (brel_complement S lte) (brel_complement S (brel_dual S lte))) a b = false ) (at level 15).


Notation "a ~ b"  := ( ((brel_conjunction S lte) (brel_dual S lte)) a b = true ) (at level 15).
Notation "a !~ b"  := ( ((brel_conjunction S lte) (brel_dual S lte)) a b = false ) (at level 15).




Lemma lt_intro : ∀ a b : S, (a <== b) * (b !<== a) -> a << b. 
Proof. intros a b [L R]. compute. rewrite L. rewrite R. reflexivity. 
Qed. 

Lemma lt_elim : ∀ a b : S, a << b -> (a <== b * b !<== a).  
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 

Lemma not_lt_intro : ∀ a b : S, (a !<== b) + (b <== a) -> a !<< b. 
Proof. intros a b [L | L]; compute; rewrite L. reflexivity. 
       case(lte a b); reflexivity. 
Qed. 

Lemma not_lt_elim : ∀ a b : S, a !<< b -> (a !<== b) + (b <== a).  
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 



Lemma incomp_intro : ∀ a b : S, ((a !<== b) * (b !<== a)) -> (a # b). 
Proof. intros a b [L R]. compute. rewrite L. rewrite R. reflexivity. 
Qed. 

Lemma incomp_elim : ∀ a b : S, a # b -> (a !<== b * b !<== a).  
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 

Lemma not_incomp_elim : ∀ a b : S, a !# b -> (a <== b + b <== a).  
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 


Lemma equiv_intro : ∀ a b : S, (a <== b) * (b <== a) -> a ~ b. 
Proof. intros a b [L R]. compute. rewrite L. rewrite R. reflexivity. 
Qed. 

Lemma equiv_elim : ∀ a b : S, a ~ b -> (a <== b * b <== a).  
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 


Lemma lt_congruence : brel_congruence S rS (brel_strictify S lte). 
Proof. apply brel_strictify_congruence; auto. Qed. 


Lemma incomp_congruence : brel_congruence S rS (brel_conjunction S (brel_complement S lte) (brel_complement S (brel_dual S lte))).  
Proof. apply brel_conjunction_congruence. 
       apply brel_complement_congruence; auto. 
       apply brel_complement_congruence. 
       apply brel_dual_congruence; auto. 
Qed. 


Lemma equiv_congruence : brel_congruence S rS ((brel_conjunction S lte) (brel_dual S lte)). 
Proof. apply brel_conjunction_congruence; auto. 
       apply brel_dual_congruence; auto. 
Qed. 


Lemma lt_irreflexive : ∀ a : S, a !<< a.
Proof. intros a . compute. rewrite (ref_lte a). reflexivity. 
Qed. 

Lemma incomp_irreflexive : ∀ a : S, a !# a.
Proof. intros a . compute. rewrite (ref_lte a). reflexivity. 
Qed. 

Lemma equiv_reflexive : ∀ a : S, a ~ a.
Proof. intros a . compute. rewrite (ref_lte a). reflexivity. 
Qed. 

Lemma lt_asymmetric : ∀ a b : S, a << b -> b !<< a.
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 


Lemma imcomp_symmetric : ∀ a b : S, a # b -> b # a.
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 

Lemma equiv_symmetric : ∀ a b : S, a ~ b -> b ~ a.
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; auto. 
Qed. 

Lemma equiv_transitive : ∀ a b c : S, a ~ b -> b ~ c -> a ~ c. 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := trans_lte _ _ _ H4 H2). rewrite H6 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
         assert (A := trans_lte _ _ _ H4 H2). rewrite H6 in A. assumption. 
Qed. 


Lemma eq_lte_lte_transitive : ∀ a b c : S, a == b -> b <== c -> a <== c. 
Proof. intros a b c H1 H2. 
       assert (A := cong_lte _ _ _ _ H1 (refS c)). rewrite H2 in A. assumption. 
Qed. 

Lemma lte_eq_lte_transitive : ∀ a b c : S, a <== b -> b == c -> a <== c. 
Proof. intros a b c H1 H2. 
       assert (A := cong_lte _ _ _ _ (refS a) H2). rewrite H1 in A. rewrite <- A. reflexivity. 
Qed. 


Lemma lt_lte_lt_transitive : ∀ a b c : S, a << b -> b <== c -> a << c. 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption.         
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
Qed. 

Lemma lte_eq_intro : ∀ a b : S, a == b -> a <== b. 
Proof. intros a b H. case_eq(lte a b); intro J; auto. 
       assert (A := cong_lte _ _ _ _ H (refS b)). rewrite (ref_lte b) in A. 
       rewrite J in A; auto. 
Qed. 

Lemma lte_lt_lt_transitive : ∀ a b c : S, a <== b -> b << c -> a << c. 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := trans_lte _ _ _ H6 H1). rewrite H4 in A. assumption. 
         assert (A := trans_lte _ _ _ H6 H1). rewrite H4 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption.         
Qed. 

Lemma lt_eq_lt_transitive : ∀ a b c : S, a << b -> b == c -> a << c. 
Proof. intros a b c L R. 
       assert (A := lte_eq_intro _ _ R). 
       assert (B := lt_lte_lt_transitive _ _ _ L A). assumption. 
Qed. 

Lemma eq_lt_lt_transitive : ∀ a b c : S, a == b -> b << c -> a << c. 
Proof. intros a b c L R. 
       assert (A := lte_eq_intro _ _ L). 
       assert (B := lte_lt_lt_transitive _ _ _ A R). assumption. 
Qed. 




Lemma lt_transitive : ∀ a b c : S, a << b -> b << c -> a << c. 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := lt_intro _ _ (H1, H2)). 
         assert (B := lt_intro _ _ (H3, H4)). 
         assert (C := lt_lte_lt_transitive _ _ _ B H6). 
         assert (D := lt_asymmetric _ _ A). 
         rewrite D in C.  assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
         assert (A := trans_lte _ _ _ H1 H3). rewrite H5 in A. assumption. 
Qed. 


Lemma  pre_order_three_cases : ∀ a b : S, (a # b) + (a <== b) + (b <== a ). 
Proof. intros a b. compute. case_eq(lte a b); intro H1; case_eq(lte b a); intro H2; auto. Qed. 

Lemma  pre_order_four_cases : ∀ a b : S, (a # b) + (a << b) + (b << a ) + (a ~ b). 
Proof. intros a b. compute. 
       case_eq(lte a b); intro H1; case_eq(lte b a); intro H2; auto. 
Qed. 

Lemma incomp_pseudo_transitive_v1 : 
          ∀ a b c : S, a # b -> b <== c -> (a # c) + (a << c). 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. left. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. left. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. left. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. left. assumption. 
Qed. 


Lemma incomp_pseudo_transitive_v2 : 
          ∀ a b c : S, a # b -> c <== b -> (a # c) + (c << a). 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. left. assumption. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. left. assumption. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. left. assumption. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. left. assumption. 
Qed. 


Lemma incomp_pseudo_transitive_v3 : 
          ∀ a b c : S, a # b -> b ~ c -> (a # c). 
Proof. intros a b c. compute. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; 
       case_eq(lte b c); intro H3; 
       case_eq(lte c b); intro H4; 
       case_eq(lte a c); intro H5; 
       case_eq(lte c a); intro H6; intro J; intro K; auto. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. assumption. 
         assert (A := trans_lte _ _ _ H5 H4). rewrite H1 in A. assumption. 
         assert (A := trans_lte _ _ _ H3 H6). rewrite H2 in A. assumption. 
Qed. 


Lemma lt_is_strict : ∀ a b : S, a << b -> a != b. 
Proof. intros a b. 
       case_eq(lte a b); intro H1; 
       case_eq(lte b a); intro H2; intro L; compute in L. 
          rewrite H1, H2 in L. discriminate. 
          rewrite H1, H2 in L. 
          case_eq(rS a b); intro J. 
             assert (R := ref_lte a). 
             assert (F := cong_lte a a b a J (refS a)). 
             rewrite R in F. rewrite H2 in F. assumption. 
             reflexivity. 
          rewrite H1 in L. discriminate. 
          rewrite H1 in L. discriminate. 
Qed. 


Lemma anti_chain_of_at_most_two_intro : 
      ∀ (a b : S), a !<< b -> b !<< a -> (a # b) + (a ~ b). 
Proof. intros a b H1 H2. 
       case_eq(lte a b); intro J1; case_eq(lte b a); intro J2; auto. 
          right. compute. rewrite J1, J2; auto. 
          compute in H1. rewrite J2, J1 in H1. discriminate. 
          compute in H2. rewrite J2, J1 in H2. discriminate. 
          left. apply incomp_intro. split; auto. 
Qed. 



(*  Now, introduce binary operator, with properties. 
*) 
Variable bS : binary_op S. 
Variable assocS  : bop_associative S rS bS. 
Variable cong_bS : bop_congruence S rS bS.

Notation "a [*] b"  := (bS a b) (at level 10).


Definition brel_bop_left_monotone := 
   ∀ (a b : S), a <== b -> ∀ (c : S), c [*] a  <== c [*] b. 

Definition brel_bop_left_incomp := 
   ∀ (a b : S), a # b -> ∀ (c : S), (c [*] a)  # (c [*] b). 

Definition brel_bop_not_left_incomp := 
   { a : S & {b : S &  (a # b) *  { c : S &  (c [*] a)  !# (c [*] b)}}}.

Definition brel_bop_not_left_monotone := 
   { a : S & {b : S & a <== b * {c : S & c [*] a  !<== c [*] b }}}. 

Definition brel_bop_left_monotone_dual := 
   ∀ (a b c : S), c [*] a  <== c [*] b -> a <== b. 

Definition brel_bop_not_left_monotone_dual := 
   { a : S & { b : S & { c : S &  (c [*] a  <== c [*] b) * (a !<== b) }}}. 

Definition brel_bop_left_strict_monotone := 
   ∀ (a b : S), a << b -> ∀ (c : S), c [*] a  << c [*] b. 

Definition brel_bop_not_left_strict_monotone := 
   {a : S & { b : S & a << b * { c : S & c [*] a !<< c [*] b}}}. 

Definition brel_bop_right_monotone := 
   ∀ (a b : S), a <== b -> ∀ (c : S), a [*] c  <== b [*] c. 

Definition brel_bop_right_strict_monotone := 
   ∀ (a b : S), a << b -> ∀ (c : S), a [*] c  << b [*] c. 

Definition brel_bop_SND := 
   ∀ (a b : S), (a <== a [*]b) + (b <== a [*]b). 

Definition brel_bop_not_SND := 
   { a : S & {b : S & (a !<== a [*]b) * (b !<== a [*]b)}}. 


(* 

  want 

  brel_bop_left_monotone  -> 

   (? <-> brel_bop_strict left_monotone) 

   ? = brel_bop_left_monotone_dual ? 

*) 

Lemma brel_left_monotone_implies_left_strict_monotone : 
      brel_bop_left_monotone -> 
      brel_bop_left_monotone_dual -> 
      brel_bop_left_strict_monotone. 
Proof. intros lm lmd a b J c. 
       apply lt_elim in J.  destruct J as [L R]. 
       apply lt_intro. split. 
          apply lm; auto. 
          case_eq(lte (c[*]b) (c[*]a)); intro K; auto. 
          assert (A := lmd _ _ _ K). rewrite A in R. assumption. 
Qed. 


Lemma brel_not_left_monotone_implies_not_left_strict_monotone_v1 : 
      brel_bop_left_monotone -> 
      brel_bop_not_left_monotone_dual -> 
      brel_bop_not_left_strict_monotone. 
Proof. unfold brel_bop_left_monotone, 
              brel_bop_not_left_strict_monotone, 
              brel_bop_not_left_monotone_dual. 
        intros nlm  nlmd. 
        destruct nlmd as [a [b [c [P1 P2]]]]. 
        case_eq(lte b a); intro K. 
            assert (A := lt_intro _ _ (K, P2)). 
            exists b. exists a. split; auto. exists c. 
            apply not_lt_intro. right. assumption.
            admit. (* NEED  brel_bop_left_incomp *) 
(*

            assert (A := incomp_intro _ _ (P2, K)). 
            assert (B := linc _ _ A c). 
            apply incomp_elim in B. destruct B as [L R]. rewrite L in P1. discriminate. 
*) 
Qed. 


Lemma brel_not_left_monotone_implies_not_left_strict_monotone : 
      (brel_bop_not_left_monotone + 
       (brel_bop_not_left_monotone_dual * brel_bop_left_incomp)) -> 
      brel_bop_not_left_strict_monotone. 
Proof. unfold brel_bop_not_left_monotone, 
              brel_bop_not_left_strict_monotone, 
              brel_bop_left_incomp, 
              brel_bop_not_left_monotone_dual. 
        intros [nlm | [nlmd linc]]. 
        destruct nlm as [a [b [P1 [c P2]]]]. 
        case_eq(lte b a); intro K. 
            admit. 
            assert (A := lt_intro _ _ (P1, K)). 
            exists a. exists b. split; auto. exists c. 
            apply not_lt_intro. left. assumption.
        destruct nlmd as [a [b [c [P1 P2]]]]. 
        case_eq(lte b a); intro K. 
            assert (A := lt_intro _ _ (K, P2)). 
            exists b. exists a. split; auto. exists c. 
            apply not_lt_intro. right. assumption.
            assert (A := incomp_intro _ _ (P2, K)). 
            assert (B := linc _ _ A c). 
            apply incomp_elim in B. destruct B as [L R]. rewrite L in P1. discriminate. 
Qed. 
   

Lemma brel_bop_monotone: 
   brel_bop_left_monotone -> 
   brel_bop_right_monotone -> 
      ∀ (a b c d : S), a <== b -> c <== d -> a [*] c <== b [*] d. 
Proof. intros lm rm a b c d H1 H2. 
       assert (A := rm _ _ H1 c). 
       assert (B := lm _ _ H2 b). 
       assert (C := trans_lte _ _ _ A B). assumption. 
Qed. 


Lemma brel_bop_monotone_and_idempotent_left : 
   brel_bop_left_monotone -> 
   brel_bop_right_monotone -> 
   bop_idempotent S rS bS -> 
      ∀ (a b c : S), a <== b -> a <== c -> a <== b [*] c. 
Proof. intros lm rm idem a b c H1 H2. 
       assert (A := brel_bop_monotone lm rm _ _ _ _ H1 H2). 
       assert (B := idem a). 
       apply symS in B. 
       assert (C := eq_lte_lte_transitive _ _ _ B A). assumption. 
Qed. 


Lemma brel_bop_monotone_and_idempotent_right: 
   brel_bop_left_monotone -> 
   brel_bop_right_monotone -> 
   bop_idempotent S rS bS -> 
      ∀ (a b c : S), a <== c -> b <== c -> a [*] b <== c. 
Proof. intros lm rm idem a b c H1 H2. 
       assert (A := brel_bop_monotone lm rm _ _ _ _ H1 H2). 
       assert (B := idem c). 
       assert (C := lte_eq_lte_transitive _ _ _ A B). assumption. 
Qed. 


Lemma brel_bop_strict_monotone: 
   brel_bop_left_strict_monotone -> 
   brel_bop_right_strict_monotone -> 
      ∀ (a b c d : S), a << b -> c << d -> a [*] c << b [*] d. 
Proof. intros lm rm a b c d H1 H2. 
       assert (A := rm _ _ H1 c). 
       assert (B := lm _ _ H2 b). 
       assert (C := lt_transitive _ _ _ A B). assumption. 
Qed. 




Lemma brel_bop_strict_monotone_and_idempotent_left: 
   brel_bop_left_strict_monotone -> 
   brel_bop_right_strict_monotone -> 
   bop_idempotent S rS bS -> 
      ∀ (a b c : S), a << b -> a << c -> a << (b [*] c).  
Proof. intros lm rm idem a b c H1 H2. 
       assert (A := brel_bop_strict_monotone lm rm _ _ _ _ H1 H2). 
       assert (B := idem a). 
       apply symS in B. 
       assert (C := eq_lt_lt_transitive _ _ _ B A). assumption. 
Qed. 


Lemma brel_bop_strict_monotone_and_idempotent_right: 
   brel_bop_left_strict_monotone -> 
   brel_bop_right_strict_monotone -> 
   bop_idempotent S rS bS -> 
      ∀ (a b c d : S), a << b -> c << b -> a [*] c << b.  
Proof. intros lm rm idem a b c d H1 H2. 
       assert (A := brel_bop_strict_monotone lm rm _ _ _ _ H1 H2). 
       assert (B := idem b). 
       assert (C := lt_eq_lt_transitive _ _ _ A B). assumption. 
Qed. 



End LessThan. 


Section ReductionEqv. 









Open Scope list_scope. 

Variable S  : Type. 
Variable rS : brel S. 
Variable bS : binary_op S. 
Variable uS : unary_op S. 

Variable assocS  : bop_associative S rS bS. 
Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.  
Variable cong_rS : brel_congruence S rS rS. 
Variable cong_bS : bop_congruence S rS bS.
Variable cong_uS : uop_congruence S rS uS. 

Notation "a [*] b"  := (bS a b) (at level 10).
Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).
Notation "A === B"  := (brel_list S rS A B = true) (at level 15).
Notation "A ^* B" := (bop_list_product_left S bS A B) (at level 10, no associativity).
Notation "A *^ B" := (bop_list_product_right S bS A B) (at level 10, no associativity).
Notation "a *> B" := (ltran_list_product S bS a B) (at level 10, no associativity).
Notation "A <* b" := (rtran_list_product S bS A b) (at level 10, no associativity).


(* ***************************************************************************


*) 

 

Definition condition_1 := ∀ s : S, uS s == uS(uS s). 
Definition condition_4 := ∀ s t: S, uS (s [*] t) == uS((uS s) [*] (uS t)). 

Definition uop_bop_reduced_associative := ∀ s t u : S, uS ((s [*] t) [*] u) == uS (s [*] (t [*] u)).

Definition uop_bop_reduced_commutative := ∀ s t : S, uS (s [*] t) == uS (t [*] s). 
Definition uop_bop_not_reduced_commutative := {s : S & {t : S & (uS (s [*] t)) != (uS (t [*] s))}}. 

Definition uop_bop_reduced_selective := ∀ s t : S, (uS (s [*] t) == uS s) + (uS (s [*] t) == uS t).
Definition uop_bop_not_reduced_selective := {s : S & {t : S & (uS (s [*] t) != uS s) * (uS (s [*] t) != uS t)}}.

Definition uop_bop_reduced_idempotence := ∀ s : S, uS (s [*] s) == uS s. 
Definition uop_bop_not_reduced_idempotence := {s : S & uS (s [*] s) != uS s}. 

Definition uop_bop_reduced_exists_id := 
   {i : S & ∀ s : S, (uS (i [*] s)  == uS s) * ((uS (s [*] i)) == (uS s))}. 
Definition uop_bop_not_reduced_exists_id := 
   ∀ i : S, { s : S & (uS (i [*] s)  != uS s) + ((uS (s [*] i)) != (uS s))}.

(* 
; A_sg_exists_ann_d     : bop_exists_ann_decidable S eq bop 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 
; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop 
                                                                                
*) 


(* ***************************************************************************) 

End ReductionEqv. 


Section ReductionProperties. 


Lemma bop_reduce_exists_id : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_reduced_exists_id S rS bS uS -> 
         bop_exists_id S (brel_reduce S rS uS) bS. 
Proof. intros S rS uS bS H. assumption. Qed. 

Lemma bop_reduce_not_exists_id : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_not_reduced_exists_id S rS bS uS -> 
         bop_not_exists_id S (brel_reduce S rS uS) bS. 
Proof. intros S rS uS bS P. assumption. Defined. 


Lemma bop_reduce_idempotent : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_reduced_idempotence S rS bS uS -> 
         bop_idempotent S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_idempotent.
       intros S rS uS bS H s. 
       apply H. 
Qed. 

Lemma bop_reduce_not_idempotent : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_not_reduced_idempotence S rS bS uS -> 
         bop_not_idempotent S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_not_idempotent.
       intros S rS uS bS [s P]. exists s; auto. 
Defined. 


Lemma bop_reduce_selective : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_reduced_selective S rS bS uS -> 
         bop_selective S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_selective.
       intros S rS uS bS H s t. apply H. 
Qed. 

Lemma bop_reduce_not_selective : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_not_reduced_selective S rS bS uS -> 
         bop_not_selective S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_not_selective.
       intros S rS uS bS [s [t [H1 H2]]]. exists (s, t); auto. 
Defined. 


Lemma bop_reduce_commutative : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_reduced_commutative S rS bS uS -> 
         bop_commutative S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_commutative.
       intros S rS uS bS H s t. apply H. 
Qed. 

Lemma bop_not_reduce_commutative : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_not_reduced_commutative S rS bS uS -> 
         bop_not_commutative S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_not_commutative.
       intros S rS uS bS [s [t H]]. exists (s, t); auto. 
Defined. 

Lemma bop_reduce_associative : ∀ (S : Type) (rS : brel S) (uS : unary_op S) (bS : binary_op S), 
         uop_bop_reduced_associative S rS bS uS -> 
         bop_associative S (brel_reduce S rS uS) bS. 
Proof. unfold brel_reduce, bop_associative.
       intros S rS uS bS H s t u. apply H. 
Qed. 

End ReductionProperties. 


Section Dominates. 
Require Import CAS.theory.brel_strictify.

Variable S  : Type. 
Variable rS : brel S. 
Variable lte : brel S. 

Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.  
Variable cong_rS : brel_congruence S rS rS. 
Variable cong_lte: brel_congruence S rS lte. 

Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).
Notation "a <== b"  := (lte a b = true) (at level 15).
Notation "a !<== b"  := (lte a b = false) (at level 15).
Notation "a << b"  := (brel_strictify S lte a b = true) (at level 15).
Notation "a !<< b"  := (brel_strictify S lte a b = false) (at level 15).
Notation  "a <==< X" := (dominates_set S rS lte X a = true) (at level 15).
Notation  "a <=!=< X" := (dominates_set S rS lte X a = false) (at level 15).

Notation "A === B"  := (brel_set S rS A B = true) (at level 15).
Notation "A !== B"  := (brel_set S rS A B = false) (at level 15).
Notation "a @ X"   := (in_set S rS X a = true) (at level 15).



Lemma dominates_set_congruences : 
        ∀ (X Y : finite_set S) (a b : S),  
           (a == b ) -> (X === Y) -> 
             dominates_set S rS lte X a = dominates_set S rS lte Y b. 
Proof. intros X Y a b P Q.  unfold dominates_set. 
       admit. 
Qed. 

Lemma bProp_lift_list_cons_elim : ∀ (f : bProp S), 
        ∀ (X : finite_set S) (a : S),  
            bProp_lift_list S f (a :: X) = true -> 
               (f a = true) * (bProp_lift_list S f (a :: X) = true). 
Proof. intros f X a H. unfold bProp_lift_list in H; fold bProp_lift_list in H. 
       apply andb_is_true_left in H. destruct H as [L R]. split; auto. 
       unfold bProp_lift_list; fold bProp_lift_list.     
       apply andb_is_true_right. split; auto. 
Qed. 



Lemma dominates_set_cons_intro : 
        ∀ (X : finite_set S) (a b : S),  (b !<< a) * (a <==< X) -> a <==< (b :: X). 
Proof. intros X a b [L R]. 
       unfold dominates_set. unfold bProp_lift_list. fold bProp_lift_list. 
       apply andb_is_true_right. split. 
          compute. 
          apply not_lt_elim in L. destruct L as [L | L]; rewrite L. 
            reflexivity. 
            case_eq(lte b a); intro J; auto. 
          assumption. 
Qed. 


Lemma dominates_set_intro : 
   ∀ (X : finite_set S) (a : S), (∀ (b : S), b @ X -> b !<< a) -> a <==< X. 
Proof. intros X. 
       (* unfold dominates_set. *) 
       induction X. 
          compute. intros. reflexivity. 
          intros c H. 
             apply dominates_set_cons_intro. split. 
                apply H. compute. rewrite refS. reflexivity. 
                apply IHX. intros b J. 
                apply H. 
                apply in_set_cons_intro. right. assumption. 
Qed. 

Lemma dominate_set_cons_elim : 
        ∀ (X : finite_set S) (a b : S),  a <==< (b :: X) -> (b !<< a) * (a <==< X).
Proof. intros X a b H. 
       unfold dominates_set in H. 
       unfold bProp_lift_list in H. fold bProp_lift_list in H. 
       apply andb_is_true_left in H. destruct H as [L R]. split. 
          compute. compute in L. 
          case_eq(lte b a); intro J; case_eq(lte a b); intro K; auto. 
             rewrite J, K in L.  discriminate. 
             assumption. 
Qed. 



Lemma dominates_set_elim : 
     ∀  (X : finite_set S) (a : S), (a <==< X) -> ∀ b : S, b @ X -> (b !<< a). 
Proof. intros X. induction X. 
          intros a H b J. compute in J. discriminate.  
          intros c H b J. 
             apply dominate_set_cons_elim in H. destruct H as [L R].              
             apply in_set_cons_elim in J. 
             destruct J as [J | J]. 
                apply symS in J. 
                assert (A := lt_congruence S rS lte cong_lte a c b c J (refS c)).
                rewrite L in A. rewrite <- A. reflexivity. 
                apply IHX; auto. 
Qed. 

Lemma dominates_set_false_intro : 
   ∀ (X : finite_set S) (a : S), {b : S & b @ X * b << a} -> a <=!=< X. 
Proof. intros X a H. 
       admit. 
Qed. 


Lemma dominates_set_false_elim : 
   ∀ (X : finite_set S) (a : S), a <=!=< X -> {b : S & b @ X * b << a}.
Proof. intros X a H. 
       admit. 
Qed. 



(* 
dominates_set S rS lte (uS (a :: X)) c = true

(∀ (b : S), in_set S eq X b = true -> brel_complement S (brel_strictify S lte) b a = true). 
*) 

Lemma dominates_set_union_elim :
      ∀ (X Y: finite_set S) (a : S), 
         (dominates_set S rS lte (X  ++ Y) a = true) -> 
         (dominates_set S rS lte X a = true) *(dominates_set S rS lte Y a = true).
Proof. admit. 
Qed. 

Lemma dominates_set_union_intro : 
      ∀ (X Y: finite_set S) (a : S), 
         (dominates_set S rS lte X a = true) *(dominates_set S rS lte Y a = true) -> 
         (dominates_set S rS lte (X ++ Y) a = true). 
Proof. admit. 
Qed. 


End Dominates. 



Section MinSet. 

(* 
*) 
                                                                                


Variable S  : Type. 
Variable rS : brel S. 
Variable lte : brel S. 

Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.  
Variable cong_rS : brel_congruence S rS rS. 
Variable cong_lte: brel_congruence S rS lte. 
Variable ref_lte    : brel_reflexive S lte. 

Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).
Notation "a <== b"  := (lte a b = true) (at level 15).
Notation "a !<== b"  := (lte a b = false) (at level 15).
Notation "a << b"  := (brel_strictify S lte a b = true) (at level 15).
Notation "a !<< b"  := (brel_strictify S lte a b = false) (at level 15).
Notation  "a <==< X" := (dominates_set S rS lte X a = true) (at level 15).
Notation  "a <=!=< X" := (dominates_set S rS lte X a = false) (at level 15).

Notation "A === B"  := (brel_set S rS A B = true) (at level 15).
Notation "A !== B"  := (brel_set S rS A B = false) (at level 15).
Notation "a @ X"   := (in_set S rS X a = true) (at level 15).
Notation "a !@ X"   := (in_set S rS X a = false) (at level 15).


Definition in_upper_set : brel2 (finite_set S) S
:= λ X a, brel_set S rS (uop_minset (a :: X)) (uop_minset X).   


Lemma dominates_set_false_elim2 : 
   ∀ (X : finite_set S) (a : S), a <=!=< X -> {b : S & b @ (uop_minset X) * b <== a}.
Proof. intros X a H. 
       admit. 
Qed. 


Lemma in_minset_intro : 
   ∀ (X : finite_set S) (a : S),  (a @ X) * (a <==< X) -> a @ (uop_minset X). 
Proof. intros X a [I J]. 
       admit. 
Qed. 

Lemma in_minset_elim : 
   ∀ (X : finite_set S) (a : S),  a @ (uop_minset X) -> (a @ X) * (a <==< X). 
Proof. intros X a H. 
       admit. 
Qed. 


Lemma in_minset_elim_to_in_set : 
   ∀ (X : finite_set S) (a : S),  a @ (uop_minset X) -> (a @ X). 
Proof. intros X a H. apply in_minset_elim in H. 
       destruct H as [H _]. assumption.        
Qed. 

Lemma not_in_minset_intro : ∀ (X : finite_set S) (a : S),  
            (a !@ X) + (a <=!=< X) -> a !@ (uop_minset X). 
Proof. intros X a H. 
       case_eq(in_set S rS (uop_minset X) a); intro J; auto. 
       apply in_minset_elim in J. destruct J as [J1 J2]. destruct H as [H | H]. 
         rewrite J1 in H. assumption.  rewrite J2 in H. assumption. 
Qed. 

Lemma not_in_minset_elim :
   ∀ (X : finite_set S) (a : S),  a !@ (uop_minset X) -> (a !@ X) + (a <=!=< X). 
Proof. intros X a H. 
       admit. 
Qed. 







(* proved in uop_minset.v 
   
   This is condition_1 

*) 
Lemma  uop_minset_idempotent : 
   uop_idempotent (finite_set S) (brel_set S rS) (uop_minset). 
Proof. admit. 
Qed. 

(* proved in uop_minset.v *) 
Lemma uop_minset_congruence : 
         uop_congruence (finite_set S) (brel_set S rS) (uop_minset).  
Proof. admit. 
Qed. 

(******** FROM VILIUS *******) 

(* Notes from Vilius

  DecSetoids/FMinSets.v : 


   Definition minimal_el (a : A) (x : fsetDecSetoid A) : bool :=
      forallb (fun b => negb (b < a)) x.


   Definition min (x : fsetDecSetoid A) : fsetDecSetoid A :=
      filter (fun a => minimal_el a x) x.


   Variable antisym : Antisym A.

   Definition upper_mem (a : A) (x : fsetDecSetoid A) : bool :=
       @equal (fsetDecSetoid A) (min (a :: x)) (min x).

   Lemma min_mem : forall x s, mem x (min s) <-> (mem x s /\ forall y, mem y s -> negb (y < x)).
   Lemma minimal_el_mem : forall x a, mem a x -> minimal_el a x -> mem a (min x).
     min_mem
     minimal_el
     forallb_mem
   Lemma min_exists_le : forall x a, negb (minimal_el a x) -> Exists b, mem b (min x) /\(b <= a).
     complicated ... 

*   Lemma min_exists_mem : forall x a, mem a x -> Exists b, mem b (min x) /\ (b <= a).
     minimal_el_mem
     min_exists_le
*   Lemma upper_mem_elim : forall a x, upper_mem a x -> Exists b, mem b (min x) /\ b <= a.

   Lemma upper_mem_intro2 : forall a x b, mem b x -> b <= a -> upper_mem a x.
*   Lemma upper_mem_intro : forall a x b, mem b (min x) -> b <= a -> upper_mem a x.
 
  Lemma upper_min : forall a x, upper_mem a (min x) = upper_mem a x.
   Lemma upper_eq : forall x y, (forall a, upper_mem a x = upper_mem a y) <-> min x == min y.

  Semigroups/FSetOP.v 

   Definition fset_op (x y : fsetDecSetoid S) : fsetDecSetoid S :=
      map (fun w : (S * S) => let (w1, w2) := w in w1 + w2) (list_prod x y).

   Lemma fset_op_elim : forall a x y, mem a (fset_op x y) -> Exists b c, a == b + c /\ mem b x /\ mem c y.

   Semigroups/FMinSetsOp.v 
   Variable A : OrderSemigroup.
   Variable lmon : LeftMonotonic A.
   Variable rmon : RightMonotonic A.
   Variable antisym : Antisym A.
   
   Definition mset_op (x y : msetDecSetoid A) : msetDecSetoid A := 
      min A (fset_op A x y).

   Lemma upper_op_elim : forall a x y, upper_mem A a (fset_op A x y) -> Exists b c, b + c <= a /\ upper_mem A b x /\ upper_mem A c y.
   Lemma upper_op_intro : forall a x y b c, b + c <= a -> upper_mem A b x -> upper_mem A c y -> upper_mem A a (fset_op A x y).
     fset_op_elim 
     min_exists_mem 
     upper_mem_intro
     upper_mem_elim

   Lemma min_fset_op_l : forall x y, min A (fset_op A x y) == min A (fset_op A (min A x) y).
   Lemma min_fset_op_r : forall x y, min A (fset_op A x y) == min A (fset_op A x (min A y)).
      upper_op_elim
      upper_op_intro 
      upper_min
      upper_eq

   Lemma min_times : forall a b, min A (fset_op A a b) == min A (fset_op A (min A a) (min A b)).
      min_fset_op_l
      min_fset_op_r

   Lemma mset_op_assoc : Associative mset_op.
     min_fset_op_l
     min_fset_op_r
     fset_op_assoc
*) 


Lemma min_exists_mem : ∀ (X : finite_set S) (a : S), 
                     a @ X -> {b : S & b @ (uop_minset X) * (b <== a)}.
Proof. intros X a H. 
       case_eq(in_set _ rS (uop_minset X) a); intro J. 
          exists a; split; auto. 
          apply not_in_minset_elim in J. destruct J as [J | J]. 
             rewrite H in J. discriminate. 
             apply dominates_set_false_elim2 in J. destruct J as [b P]. 
             exists b; auto.      
Defined. 


Lemma upper_mem_elim : ∀ (X : finite_set S) (a : S), 
     in_upper_set X a = true -> {b : S &  b @ (uop_minset X) * b <== a}.
Proof. intros X a H.
       unfold in_upper_set in H. 
       assert (A : a @ (a :: X)). admit. 
       assert (B := min_exists_mem (a :: X) a A). destruct B as [b [P Q]]. 
       exists b; split;auto. 
          admit. (* brel2_in_set_left_congruence ! *) 
Defined. 


Lemma min_intro : ∀ (X Y : finite_set S), 
          brel_subset S rS (uop_minset X) Y = true -> 
          brel_subset S rS (uop_minset Y) X = true -> 
              uop_minset X === uop_minset Y.
Proof. admit. 
Qed. 



(*    same as in_minset_elim followd by dominates_set_elim 
Lemma min_mem : forall x s, 
       mem x (min s) <-> (mem x s /\ forall y, mem y s -> negb (y < x)).
*) 


Lemma upper_mem_intro : brel_antisymmetric S rS lte -> 
     ∀ (X : finite_set S) (a b : S), 
       b @ (uop_minset X) -> b <== a -> in_upper_set X a = true.
Proof. intros anti X a b P Q. 
       unfold in_upper_set. apply min_intro. 
       apply brel_subset_intro; auto. intros c R. 
       apply in_minset_elim in R. destruct R as [R1 R2].
       assert (A : ∀ d : S, d @ (a :: X) -> (d !<< c)).  
           apply dominates_set_elim; auto. 
       apply in_minset_elim in P. destruct P as [P1 P2].
       assert (B : ∀ d : S, d @ X -> (d !<< b)).  
           apply dominates_set_elim; auto. 
       apply in_set_cons_elim in R1. destruct R1 as [R1 | R1]; auto. 
          assert (W : b @ (a :: X)). admit. 
          assert (C : b <== c). admit. 
          assert (R3 := A b W). apply not_lt_elim in R3. destruct R3 as [R3 | R3]. 
             rewrite C in R3. discriminate. 
             assert (D := anti _ _ C R3).  admit. (* cong *) 
       apply brel_subset_intro; auto. intros c R.
       apply in_set_cons_intro. right. apply in_minset_elim_to_in_set; auto. 
Qed. 


Lemma upper_min_left : brel_antisymmetric S rS lte -> 
  ∀ (X : finite_set S) (a : S), 
       in_upper_set X a = true -> in_upper_set (uop_minset X) a = true. 
Proof. intros anti X a J. 
       unfold in_upper_set in J.  
       apply upper_mem_elim in J. destruct J as [b [P Q]].
       assert (Z : b @ uop_minset (uop_minset X)). admit.  
       apply (upper_mem_intro anti (uop_minset X) a b Z Q). 
Qed. 

Lemma upper_min_right : brel_antisymmetric S rS lte -> 
  ∀ (X : finite_set S) (a : S), 
       in_upper_set X a = false -> in_upper_set (uop_minset X) a = false. 
Proof. intros anti X a J. 
       admit. 
Qed. 



   
Lemma upper_min : brel_antisymmetric S rS lte -> 
  ∀ (X : finite_set S) (a : S), 
        in_upper_set (uop_minset X) a = in_upper_set X a. 
Proof. intros anti X a. 
       case_eq(in_upper_set X a); intro J. 
          apply upper_min_left; auto. 
          apply upper_min_right; auto. 
Qed. 


Lemma upper_eq_left : ∀ (X Y : finite_set S), 
    (∀ (a : S), in_upper_set X a = in_upper_set Y a) -> uop_minset X === uop_minset Y.
Proof. intros X Y H. 
       apply brel_set_intro_prop;auto. split. 
          intros a J. apply in_minset_intro. apply in_minset_elim in J. destruct J as [L R]. 
             assert (B : ∀ b : S, b @ X -> (b !<< a)). apply dominates_set_elim; auto. 
             split. 
                admit. 
                apply dominates_set_intro; auto.             
                intros b J. 
                case_eq(in_upper_set X b);intro K. 
                   assert (Q := upper_mem_elim X b K). destruct Q as [c [QL QR]].
                   apply not_lt_intro. 
          admit. 
          admit. 
                
          intros a J. apply in_minset_intro. apply in_minset_elim in J. destruct J as [L R]. split. 
             admit. 
             admit. 
Qed. 


Lemma upper_eq_right : ∀ (X Y : finite_set S), 
     uop_minset X === uop_minset Y -> (∀ (a : S), in_upper_set X a = in_upper_set Y a). 
Proof. admit. 
Qed. 







End MinSet. 


Section MinUnion. 

Variable S  : Type. 
Variable rS : brel S. 
Variable lte : brel S. 
Definition  bS : binary_op (finite_set S) := λ x y, x ++ y. 
Definition uS : unary_op (finite_set S) := uop_minset S rS lte. 

Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.  
Variable cong_rS : brel_congruence S rS rS. 

Variable cong_lte: brel_congruence S rS lte. 
Variable trans_lte  : brel_transitive S lte.  

Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).
Notation "a <== b"  := (lte a b = true) (at level 15).
Notation "a !<== b"  := (lte a b = false) (at level 15).
Notation "a << b"  := (brel_strictify S lte a b = true) (at level 15).
Notation "a !<< b"  := (brel_strictify S lte a b = false) (at level 15).
Notation  "a <==< X" := (dominates_set S rS lte X a = true) (at level 15).
Notation  "a <=!=< X" := (dominates_set S rS lte X a = false) (at level 15).

Notation "A === B"  := (brel_set S rS A B = true) (at level 15).
Notation "A !== B"  := (brel_set S rS A B = false) (at level 15).
Notation "a [*] b"  := (a ++ b) (at level 10).
Notation "a @ X"   := (in_set S rS X a = true) (at level 15).


Lemma in_union_elim : ∀ (X Y: finite_set S) (a : S), a @ X[*]Y -> (a @ X) + (a @ Y).
Proof. admit. 
Qed. 

Lemma in_union_intro : ∀ (X Y: finite_set S) (a : S), ((a @ X) + (a @ Y)) -> a @ X[*]Y.
Proof. admit. 
Qed. 

     

(*   NEED: 
     b @ X -> in_set S rS (uS X) b = false -> {c : S & (in_set S rS (uS X) c = false) * (c << b)} 
*) 

Lemma not_in_minset_elim2 : ∀ (X : finite_set S) (a : S), 
  a @ X -> in_set S rS (uS X) a = false -> {b : S & b @ uS X * b << a}.
Proof. intros X. induction X. compute. intros a F. discriminate. 
       intros b H L. 
       apply not_in_minset_elim in L. 
       destruct L as [L  | L]. 
          rewrite L in H. discriminate. 
          apply dominates_set_false_elim in L. 
          destruct L as [c [L1 L2]].
          case_eq(in_set _ rS (uS X) c); intro P. 
             exists c; split; auto. 
                apply in_set_cons_elim in L1. apply in_set_cons_elim in H. 
                destruct L1 as [L1 | L1]; destruct H as [H | H]. 
                   admit. 
                   admit. 
                   admit. 
                   admit. 
             apply in_set_cons_elim in L1. destruct L1 as [L1 | L1]. 
                admit. 
                assert (B := IHX c L1 P). 
                apply in_set_cons_elim in H. destruct H as [H | H]. 
                   admit. 
                   destruct B as [d [B1 B2]].
                   assert (C : d << b). admit. 
                   exists d. split; auto. 
                   case_eq(in_set S rS (uS X) a); intro K. 
                      admit. 
                      case_eq(in_set S rS X a); intro M. 
                         assert (N := IHX _ M K).  destruct N as [e [N1 N2]]. 
                         admit. 
                         admit. 
Qed. 


Lemma dominates_minset_elim : ∀ (X : finite_set S) (a : S), 
       a <==< (uS X) -> ∀ (b : S), b @ X -> b !<< a. 
Proof. intros X a H. 
       assert (A: ∀ (b : S), b @ (uS X) -> b !<< a).  
           apply dominates_set_elim; auto. 
       intros b J. 
       case_eq(in_set S rS (uS X) b); intro L. 
          apply A; auto. 
          assert (B : {c : S & (c @ (uS X)) * (c << b)} ). admit.                     
          destruct B as [c [P Q]]. 
          assert (C := A c P). 
          apply not_lt_elim in C. apply not_lt_intro. 
          destruct C as [C | C]. 
             case_eq(lte a b); intro D1; case_eq(lte b a); intro D2; auto.         
             assert (M := lt_lte_lt_transitive _ _ trans_lte _ _ _ Q D2).                   
             apply lt_elim in M. destruct M as [M _].  rewrite C in M. right. assumption. 
             right. 
             assert (M := lte_lt_lt_transitive _ _ trans_lte _ _ _ C Q). 
             apply lt_elim in M. destruct M as [M _]. assumption. 
Qed. 


Lemma dominates_minset_implies_dominates_set : ∀ (X : finite_set S) (a : S), 
          a <==< (uS X) -> a <==< X.  
Proof. intros X a H. apply dominates_set_intro; auto. apply (dominates_minset_elim X a H). Qed. 

Lemma dominates_set_implies_dominates_minset : ∀ (X : finite_set S) (a : S), 
          a <==< X -> a <==< (uS X).  
Proof. intros X a H. apply dominates_set_intro; auto. 
       assert (A: ∀ (b : S), b @ X -> b !<< a).  
           apply dominates_set_elim; auto. 
       intros b J. 
          apply A. 
          apply (in_minset_elim_to_in_set _ rS lte X b); auto. 
Qed. 


Lemma min_union_condition_4 : condition_4 (finite_set S) (brel_set S rS) bS uS. 
Proof. unfold condition_4. unfold bS. 
       intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H. (* a @ uS (X[*]Y)  -> a @ uS ((uS X)[*](uS Y)) *) 
          apply in_minset_intro; auto. 
          apply in_minset_elim in H; auto. 
          destruct H as [L R]. 
          apply dominates_set_union_elim in R. destruct R as [RL RR]. 
          apply in_union_elim in L. split. 
             apply in_union_intro.  
             destruct L as [L | L].
                left. apply in_minset_intro. split; assumption. 
                right. apply in_minset_intro. split; assumption.
             apply dominates_set_union_intro. split. 
                apply dominates_set_implies_dominates_minset; auto. 
                apply dominates_set_implies_dominates_minset; auto. 
          intros a H. (* a @ uS ((uS X)[*](uS Y))  ->  a @ uS (X[*]Y)   *) 
             apply in_minset_intro; auto. 
             apply in_minset_elim in H; auto. 
             destruct H as [L R]. 
             apply in_union_elim in L. 
             apply dominates_set_union_elim in R. destruct R as [RL RR]. 
             destruct L as [L | L].
                split. 
                   apply in_union_intro. left. 
                      apply (in_minset_elim_to_in_set _ _ _ _ _ L). 
                      (* a @ uS X   ->  a @ X   *)               
                      apply dominates_set_union_intro. split. 
                        apply dominates_minset_implies_dominates_set; auto. 
                        apply dominates_minset_implies_dominates_set; auto. 
                split. 
                   apply in_union_intro. right. 
                      apply (in_minset_elim_to_in_set _ _ _ _ _ L). 
                      apply dominates_set_union_intro. split. 
                        apply dominates_minset_implies_dominates_set; auto. 
                        apply dominates_minset_implies_dominates_set; auto. 
Qed.  


Lemma minset_union_idempotent : 
    uop_bop_reduced_idempotence (finite_set S) (brel_set S rS) (λ x y, x ++ y) (uop_minset S rS lte). 
Proof. 
       unfold uop_bop_reduced_idempotence. intro X. 
       apply brel_set_intro_prop; auto. split. 
       intros a H. 
          apply in_minset_intro. 
          apply in_minset_elim in H. destruct H as [L R]. 
          apply dominates_set_union_elim in R. destruct R as [RL RR].
          apply in_union_elim in L. 
          destruct L as [L | L]; split; auto. 
       intros a H. 
          apply in_minset_intro. 
          apply in_minset_elim in H. destruct H as [L R]. 
          split. 
            apply in_union_intro. left. assumption. 
            apply dominates_set_union_intro. split; assumption. 
Qed. 

End MinUnion. 



Section ListProduct. 

(* 
     BOP PRODUCT 

*) 


Lemma in_bop_list_product_left_intro : ∀ (S : Type) (eq : brel S) (bS : binary_op S),  
   ∀ (X Y : finite_set S) (x : S), 
    {a : S & { b : S & (in_set S eq X a = true) * 
                          (in_set S eq Y b = true) * 
                          (eq x (bS a b) = true) }}
    -> 
    (in_set S eq (bop_list_product_left S bS X Y) x = true). 
Proof. admit. 
Qed. 


Lemma in_bop_list_product_left_elim : ∀ (S : Type) (eq : brel S) (bS : binary_op S),  
   ∀ (X Y : finite_set S) (x : S), 
    (in_set S eq (bop_list_product_left S bS X Y) x = true) 
    -> {a : S & { b : S & (in_set S eq X a = true) * 
                          (in_set S eq Y b = true) * 
                          (eq x (bS a b) = true) }}. 
Proof. admit. 
Qed. 

End ListProduct. 



Section MinLift. 

(* Now, look at an instance 

   = is brel_set with rep = duplicate_elim 
   . = bs = list_product 
   r = uS = uop_minset 

We need Section 

    4) r(a . b) = r(r(a) . r(b)) 


*) 

Variable S  : Type. 
Variable rS : brel S. 
Variable lte : brel S.
Variable bS : binary_op S.  
Definition uop_min : unary_op (finite_set S) := uop_minset S rS lte. 
Definition  lift : binary_op (finite_set S) := bop_list_product_left S bS.  


Variable refS    : brel_reflexive S rS. 
Variable symS    : brel_symmetric S rS. 
Variable transS  : brel_transitive S rS.  
Variable cong_rS : brel_congruence S rS rS. 


Variable trans_lte  : brel_transitive S lte.  
Variable ref_lte   : brel_reflexive S lte. 
Variable antisym_lte : brel_antisymmetric S rS lte. 
Variable cong_lte : brel_congruence S rS lte. 

Variable cong_bS : bop_congruence S rS bS. 


Notation "a == b"  := (rS a b = true) (at level 15).
Notation "a != b"  := (rS a b = false) (at level 15).
Notation "a <== b"  := (lte a b = true) (at level 15).
Notation "a !<== b"  := (lte a b = false) (at level 15).
Notation "a << b"  := (brel_strictify S lte a b = true) (at level 15).
Notation "a !<< b"  := (brel_strictify S lte a b = false) (at level 15).
Notation  "a <==< X" := (dominates_set S rS lte X a = true) (at level 15).

Notation "A === B"  := (brel_set S rS A B = true) (at level 15).
Notation "A !== B"  := (brel_set S rS A B = false) (at level 15).

Notation "a [*] b"  := (bS a b) (at level 10).
Notation "a @ X"   := (in_set S rS X a = true) (at level 15).
Notation "A ^* B" := (lift A B) (at level 10, no associativity).
Notation "a *> B" := (ltran_list_product S bS a B) (at level 10, no associativity).


(* (∀ a b c : S, a < b -> c[*]a < c[*]b. * *) 
(*
Definition brel_bop_left_strict_monotone (S : Type) (lte : brel S) (bS : binary_op S) := 
   ∀ (a b : S), (brel_strictify S lte a b  = true) -> 
         ∀ (c : S),(brel_strictify S lte (bS c a) (bS c b)  = true). 

Definition brel_bop_not_left_strict_monotone (S : Type) (lte : brel S) (bS : binary_op S) := 
   {p : (S * S ) * S & 
      match p with ((a, b), c) =>  
          (brel_strictify S lte a b  = true) * 
          (brel_strictify S lte (bS c a) (bS c b)  = false)
         end }. 
*) 
(* (∀ a b c : S, a < b -> a[*]b < b[*]c. * *) 
(* 
Definition brel_bop_right_strict_monotone (S : Type) (lte : brel S) (bS : binary_op S) := 
   ∀ (a b : S), (brel_strictify S lte a b  = true) -> 
         ∀ (c : S),(brel_strictify S lte (bS a c) (bS b c)  = true). 

*) 


Definition brel_bop_not_right_strict_monotone (S : Type) (lte : brel S) (bS : binary_op S) := 
   {p : (S * S ) * S & 
      match p with ((a, b), c) =>  
          (brel_strictify S lte a b  = true) * 
          (brel_strictify S lte (bS a c) (bS b c)  = false)
         end }. 


(* (∀ a b c : S, c[*]a < c[*]b -> a < b   *) 
Definition brel_bop_left_strict_monotone_dual (S : Type) (lte : brel S) (bS : binary_op S) := 
∀ (a b c : S), (brel_strictify S lte (bS c a) (bS c b) = true) -> (brel_strictify S lte a b  = true). 

Definition brel_bop_not_left_strict_monotone_dual (S : Type) (lte : brel S) (bS : binary_op S) := 
   {p : (S * S ) * S & 
      match p with ((a, b), c) =>  
          (brel_strictify S lte (bS c a) (bS c b)  = true) * 
          (brel_strictify S lte a b  = false) 
         end }. 

(* (∀ a b c : S, a[*]b < b[*]c -> a < b *) 
Definition brel_bop_right_strict_monotone_dual (S : Type) (lte : brel S) (bS : binary_op S) := 
∀ (a b c : S), (brel_strictify S lte (bS a c) (bS b c)  = true) -> (brel_strictify S lte a b  = true).

Definition brel_bop_not_right_strict_monotone_dual (S : Type) (lte : brel S) (bS : binary_op S) := 
   {p : (S * S ) * S & 
      match p with ((a, b), c) =>  
          (brel_strictify S lte (bS a c) (bS b c)  = true) * 
          (brel_strictify S lte a b  = false) 
         end }. 


Lemma uop_min_subset_intro : ∀ (X Y: finite_set S), 
        ((brel_subset S rS X Y = true) * 
         (∀ (a : S), (dominates_set S rS lte X a = true) -> (dominates_set S rS lte Y a = true)))
         -> brel_subset S rS (uop_min X) (uop_min Y) = true. 
Proof. intros X Y [L R]. 
       apply brel_subset_intro; auto. 
       intros a H. 
       apply in_minset_intro. apply in_minset_elim in H. 
       destruct H as [H1 H2]. 
       split. 
         assert (A := brel_subset_elim _ _ symS transS _ _ L a H1). assumption. 
         apply R; auto. 
Qed. 


Lemma uop_min_subset_intro_v2 : ∀ (X Y: finite_set S), 
        (∀ (a : S), (a @ X * (dominates_set S rS lte X a = true)) -> 
                   a @ Y * (dominates_set S rS lte Y a = true))
         -> brel_subset S rS (uop_min X) (uop_min Y) = true. 
Proof. intros X Y A. 
       apply brel_subset_intro; auto. 
       intros a H. 
       apply in_minset_intro. apply in_minset_elim in H. 
       apply A; auto. 
Qed. 


Lemma dominates_lift_product_elim : ∀ (X Y : finite_set S) (a : S), 
      a <==< (X ^* Y) -> ∀ (x y : S), x @ X -> y @ Y -> (x [*] y) !<< a.  
Proof. intros X Y a H x y J K.
       assert (A: ∀ (b : S), b @ (X ^* Y) -> b !<< a).  
           apply dominates_set_elim; auto. 
       apply A. 
       apply in_bop_list_product_left_intro. 
       exists x; exists y; auto.  
Qed. 
 

Lemma ttestl : brel_bop_right_strict_monotone S lte bS -> 
        ∀ (X Y : finite_set S) (c b : S), 
            c @ X -> b @ Y -> c[*]b <==< X ^* Y -> c <==< X. 
Proof. intros rm X Y c b H J K. 
       apply dominates_set_intro; auto. 
       intros d M. 
       assert (A : ∀ (x y : S), x @ X -> y @ Y -> (x [*] y) !<< c[*]b). 
          apply dominates_lift_product_elim; auto. 
       assert (B := A d b M J). 
       apply not_lt_intro. 
       apply not_lt_elim in B.
       destruct B as [B | B]; 
       case_eq(lte c d); intro C; case_eq(lte d c); intro D; auto. 
          assert (E := lt_intro _ _ _ _ (D, C)). 
          assert (F := rm _ _ E b).   apply lt_elim in F. destruct F as [F _]. 
          rewrite F in B. left. assumption. 
          assert (E := lt_intro _ _ _ _ (D, C)). 
          assert (F := rm _ _ E b). apply lt_elim in F. destruct F as [_ F]. 
          rewrite B in F. left. assumption. 
Qed. 

(*
Lemma ttestl_weak : brel_bop_right_monotone S lte bS -> 
        ∀ (X Y : finite_set S) (c b : S), 
            c @ X -> b @ Y -> c[*]b <==< X ^* Y -> c <==< X. 
Proof. intros rm X Y c b H J K. 
       apply dominates_set_intro; auto. 
       intros d M. 
       assert (A : ∀ (x y : S), x @ X -> y @ Y -> (x [*] y) !<< c[*]b). 
          apply dominates_lift_product_elim; auto. 
       assert (B := A d b M J). 
       apply not_lt_intro. 
       apply not_lt_elim in B.
       destruct B as [B | B]; 
       case_eq(lte c d); intro C; case_eq(lte d c); intro D; auto. 
          assert (E := lt_intro _ _ _ _ (D, C)). 
          assert (F := rm _ _ D b).   
          rewrite F in B. left. assumption. 
          assert (E := lt_intro _ _ _ _ (D, C)). 
          assert (F := rm _ _ D b). 

          OUCH 
Qed. 
*) 

Lemma ttestr : brel_bop_left_strict_monotone S lte bS -> 
        ∀ (X Y : finite_set S) (c b : S), 
            c @ X -> b @ Y -> c[*]b <==< X ^* Y -> b <==< Y. 
Proof. intros lm X Y c b H J K. 
       apply dominates_set_intro; auto. 
       intros d M. 
       assert (A : ∀ (x y : S), x @ X -> y @ Y -> (x [*] y) !<< c[*]b). 
          apply dominates_lift_product_elim; auto. 
       assert (B := A c d H M). 
       apply not_lt_intro. 
       apply not_lt_elim in B.
       destruct B as [B | B]; 
       case_eq(lte b d); intro C; case_eq(lte d b); intro D; auto. 
          assert (E := lt_intro _ _ _ _ (D, C)). 
          assert (F := lm _ _ E c).   apply lt_elim in F. destruct F as [F _]. 
          rewrite F in B. left. assumption. 
          assert (E := lt_intro _ _ _ _ (D, C)). 
          assert (F := lm _ _ E c). apply lt_elim in F. destruct F as [_ F]. 
          rewrite B in F. left. assumption. 
Qed. 



Notation "a # b"  := ( (brel_conjunction S (brel_complement S lte) (brel_complement S (brel_dual S lte))) a b = true ) (at level 15).
Notation "a ~ b"  := ( ((brel_conjunction S lte) (brel_dual S lte)) a b = true ) (at level 15).


Lemma tttest : brel_bop_left_strict_monotone S lte bS -> 
               brel_bop_right_strict_monotone S lte bS -> 
        ∀ (X Y : finite_set S) (a : S), 
        a <==< (uop_min X) ^* (uop_min Y) -> 
        a <==< X ^* Y. 
Proof. intros lsm rsm X Y a J. 
       apply dominates_set_intro; auto. 
       intros b H. 
       apply in_bop_list_product_left_elim in H. 
       destruct H as [c [d [[P1 P2] P3]]]. 
       assert (A := dominates_lift_product_elim _ _ a J). 
       case_eq(in_set S rS (uop_min X) c); intro K1; 
       case_eq(in_set S rS (uop_min Y) d); intro K2; auto.  
         assert (Z := A _ _ K1 K2).  
         assert (C := lt_congruence _ rS lte cong_lte _ _ _ _ P3 (refS a)). rewrite C; auto. 
         apply not_in_minset_elim2 in K2; auto.  destruct K2 as [e [L R]]. 
            unfold uS in L. 
            assert (F := A _ _ K1 L). 
            assert (G := lsm _ _ R c). 
            case_eq (brel_strictify S lte b a); intro Q. 
               assert (C : c[*]d << a). 
                  assert (K := lt_congruence _ rS lte cong_lte _ _ _ _ P3 (refS a)). 
                  rewrite K in Q. assumption. 
               assert (T := lt_transitive _ lte trans_lte _ _ _ G C). rewrite T in F. assumption. 
               reflexivity. 
         apply not_in_minset_elim2 in K1; auto.  destruct K1 as [e [L R]]. 
            unfold uS in L. 
            assert (F := A _ _ L K2). 
            assert (G := rsm _ _ R d). 
            case_eq (brel_strictify S lte b a); intro Q. 
               assert (C : c[*]d << a). 
                  assert (K := lt_congruence _ rS lte cong_lte _ _ _ _ P3 (refS a)). 
                  rewrite K in Q. assumption.  
               assert (T := lt_transitive _ lte trans_lte _ _ _ G C). rewrite T in F. assumption. 
               reflexivity. 
         apply not_in_minset_elim2 in K1; auto.  destruct K1 as [e1 [L1 R1]]. 
         apply not_in_minset_elim2 in K2; auto.  destruct K2 as [e2 [L2 R2]]. 
            unfold uS in L1. unfold uS in L2. 
            assert (F := A _ _ L1 L2). 
            assert (G := brel_bop_strict_monotone _ lte trans_lte bS lsm rsm _ _ _ _ R1 R2). 
            case_eq (brel_strictify S lte b a); intro Q. 
               assert (C : c[*]d << a). 
                  assert (K := lt_congruence _ rS lte cong_lte _ _ _ _ P3 (refS a)). 
                  rewrite K in Q. assumption.  
               assert (T := lt_transitive _ lte trans_lte _ _ _ G C). rewrite T in F. assumption. 
               reflexivity. 
Qed. 

Lemma nextlemma : ∀ (X Y : finite_set S) (a : S), 
      a <==< X ^* Y -> a <==< (uop_min X) ^* (uop_min Y). 
Proof. intros X Y a H. 
       apply dominates_set_intro; auto. intros b J.
       apply in_bop_list_product_left_elim in J.  
       destruct J as [c [d [[P1 P2] P3]]]. 
       apply in_minset_elim_to_in_set in P1. 
       apply in_minset_elim_to_in_set in P2. 
       assert (A : ∀ (u v : S), u @ X -> v @ Y -> (u [*] v) !<< a). 
          apply dominates_lift_product_elim; auto. 
          assert (F := A c d P1 P2). 
          assert (G := lt_congruence _ rS lte cong_lte _ _ _ _ P3 (refS a)). rewrite G; auto. 
Qed.

Lemma newestlemma : ∀ (X Y : finite_set S) (a : S),   
      a @ (uop_min X) ^* (uop_min Y) -> a @ X ^* Y. 
Proof. intros X Y a H. 
       apply in_bop_list_product_left_intro. 
       apply in_bop_list_product_left_elim in H. 
       destruct H as [b [c [[P1 P2] P3]]]. 
       apply in_minset_elim_to_in_set in P1. 
       apply in_minset_elim_to_in_set in P2. 
       exists b; exists c;auto. 
Qed. 
   

Lemma min_lift_condition_4 : 
          brel_bop_left_strict_monotone S lte bS -> 
          brel_bop_right_strict_monotone S lte bS -> 
              condition_4 (finite_set S) (brel_set S rS) lift uop_min. 
Proof. intros lsm rsm X Y. 
       (*    uop_min (X ^* Y) === uop_min ((uop_min X) ^* (uop_min Y)) *) 
       apply brel_set_intro; auto. split. 
          (* brel_subset S rS (uop_min (X ^* Y)) (uop_min ((uop_min X) ^* (uop_min Y))) = true *) 
          apply uop_min_subset_intro_v2. 
          intros a [L R]. split. 
          (* a @ X ^* Y -> a <==< (X ^* Y) -> a @ (uop_min X) ^* (uop_min Y) *) 
             apply in_bop_list_product_left_intro. 
             apply in_bop_list_product_left_elim in L. destruct L as [c [b [[P1 P2] P3]]].
             exists c; exists b. split. split. 
                apply in_minset_intro. split; auto. 
                assert (G : c[*]b <==< X ^* Y). 
                   assert (C := dominates_set_congruences S rS lte _ _ _ _ P3 
                                (brel_set_reflexive S rS refS symS transS (X ^* Y))). 
                   rewrite C in R. assumption. 
                assert (F:= ttestl rsm X Y c b P1 P2 G). assumption. 
                apply in_minset_intro. split; auto. 
                assert (G : c[*]b <==< X ^* Y). 
                   assert (C := dominates_set_congruences S rS lte _ _ _ _ P3 
                                (brel_set_reflexive S rS refS symS transS (X ^* Y))). 
                   rewrite C in R. assumption. 
                assert (F:= ttestr lsm X Y c b P1 P2 G). assumption. 
                assumption. 
          (* a <== (X ^* Y) a -> a <== ((uop_min X) ^* (uop_min Y))  *) 
          apply nextlemma; auto. 
          (* brel_subset S rS  (uop_min ((uop_min X) ^* (uop_min Y))) (uop_min (X ^* Y)) = true*)                apply uop_min_subset_intro_v2.      
          intros a [L R]. split. 
             (* a @ (uop_min X) ^* (uop_min Y) -> a @ X ^* Y *) 
             apply newestlemma; auto. 
            (* a @ (uop_min X) ^* (uop_min Y) -> a <==< (uop_min X) ^* (uop_min Y) -> a <==< X ^* Y *)              apply tttest; auto.  
Qed. 



Lemma min_lift_condition_1 : condition_1 (finite_set S) (brel_set S rS) uop_min. 
Proof. unfold condition_1. 
(*
   ∀ s : finite_set S, uop_min s === uop_min (uop_min s)
*) 
    admit. 
Qed. 

Lemma select_lemma1 : 
   bop_selective S rS bS -> ∀ (X : finite_set S) (a : S), a @ X ^* X  -> a @ X. 
Proof. intros selS X a H. 
       apply in_bop_list_product_left_elim in H. 
       destruct H as [b [c [[P1 P2] P3]]].
       assert (A := selS b c). destruct A as [A | A]. 
         admit. 
         admit. 
Qed. 

Lemma select_lemma2 : 
   bop_selective S rS bS -> ∀ (X : finite_set S) (a : S), a @ X -> a @ X ^* X. 
Proof. intros selS X a H. 
       apply in_bop_list_product_left_intro. 
       exists a; exists a. split; auto. apply symS. 
       assert (A := selS a a). destruct A as [A | A]; auto. 
Qed. 
   
Lemma select_lemma3 : 
  (*    bop_selective S rS bS -> *) 
   ∀ (X : finite_set S) (a : S), a <==< X ^* X -> a <==< X. 
Proof. intros X a H. 
       apply dominates_set_intro; auto. 
       intros b J.
       assert (A : ∀ (x y : S), x @ X -> y @ X -> (x [*] y) !<< a). 
            apply dominates_lift_product_elim; auto. 
       assert (B := A b b J J). 
       admit. 
Qed. 

Lemma select_lemma4 : 
   bop_selective S rS bS -> ∀ (X : finite_set S) (a : S), a <==< X -> a <==< X ^* X. 
Proof. intros selS X a H. 
       apply dominates_set_intro; auto. 
       intros b J.
       apply in_bop_list_product_left_elim in J. 
       destruct J as [c [d [[P1 P2] P3]]].
       assert (A : ∀ b : S, b @ X -> (b !<< a)). 
          apply dominates_set_elim; auto. 
       destruct (selS c d) as [L | L]. 
          assert (B := A c P1). 
             admit.         
          assert (B := A d P2). 
             admit.         
Qed. 


Lemma test2_idempotent_2 : 
   bop_selective S rS bS -> 
   ∀ X : finite_set S, uop_min (X ^* X) === uop_min X. 
Proof. intros selS X. 
       apply brel_set_intro_prop;auto. split. 
          intros a H. 
            unfold uop_min. unfold uop_minset. unfold uop_filter_from_brel2. 
            apply in_set_uop_filter_intro. 
               admit. (* congruence *) 
            unfold uop_min in H. unfold uop_minset in H. unfold uop_filter_from_brel2 in H. 
            apply in_set_uop_filter_elim in H.  destruct H as [L R]. 
            split. 
                 apply select_lemma3; auto. 
                 apply select_lemma1; auto. 
            admit. (* congruence *)            
          intros a H. 
            unfold uop_min. unfold uop_minset. unfold uop_filter_from_brel2. 
            apply in_set_uop_filter_intro. 
               admit. (* congruence *) 
            unfold uop_min in H. unfold uop_minset in H. unfold uop_filter_from_brel2 in H. 
            apply in_set_uop_filter_elim in H.  destruct H as [L R]. 
            split. 
               apply select_lemma4; auto. 
               apply select_lemma2; auto. 
            admit. (* congruence *) 
Qed. 



Lemma idem_lemma2 : 
   bop_idempotent S rS bS -> 
   brel_bop_SND S lte bS -> 
   ∀ (X : finite_set S) (a : S), a @ X -> a @ X ^* X. 
Proof. intros idem snd X a H. 
       apply in_bop_list_product_left_intro. 
       exists a; exists a. split; auto. 
Qed. 
   
Lemma idem_lemma3 : 
(*
   bop_idempotent S rS bS -> 
   brel_bop_SND S lte bS -> 
*) 
   ∀ (X : finite_set S) (a : S), a <==< X ^* X -> a <==< X. 
Proof. intros   X a H. 
       apply dominates_set_intro; auto. 
       intros b J.
       assert (A : ∀ (x y : S), x @ X -> y @ X -> (x [*] y) !<< a). 
            apply dominates_lift_product_elim; auto. 
       assert (B := A b b J J). 
       admit. 
Qed. 

Lemma idem_lemma4 : 
(*
   bop_idempotent S rS bS -> 
*) 
   brel_bop_SND S lte bS -> 
   ∀ (X : finite_set S) (a : S), a <==< X -> a <==< X ^* X. 
Proof. intros snd X a H. 
       apply dominates_set_intro; auto. 
       intros b J.
       apply in_bop_list_product_left_elim in J. 
       destruct J as [c [d [[P1 P2] P3]]].
       assert (A : ∀ b : S, b @ X -> (b !<< a)). 
          apply dominates_set_elim; auto. 
       destruct (snd c d) as [L | L]. 
          assert (B := A c P1). 
             admit.         
          assert (B := A d P2). 
             admit.         
Qed. 


Lemma test2_idempotent_33 : 
   bop_idempotent S rS bS -> 
   brel_bop_SND S lte bS -> 
   ∀ X : finite_set S, uop_min (X ^* X) === uop_min X. 
Proof. intros idem snd X. 
       apply brel_set_intro_prop;auto. split. 
          intros a H. 
            unfold uop_min. unfold uop_minset. unfold uop_filter_from_brel2. 
            apply in_set_uop_filter_intro. 
               admit. (* congruence *) 
            unfold uop_min in H. unfold uop_minset in H. unfold uop_filter_from_brel2 in H. 
            apply in_set_uop_filter_elim in H.  destruct H as [L R]. 
            split. 
                 apply idem_lemma3; auto. 
                 admit. (* apply idem_lemma1; auto.  *) 
            admit. (* congruence *)            
          intros a H. 
            unfold uop_min. unfold uop_minset. unfold uop_filter_from_brel2. 
            apply in_set_uop_filter_intro. 
               admit. (* congruence *) 
            unfold uop_min in H. unfold uop_minset in H. unfold uop_filter_from_brel2 in H. 
            apply in_set_uop_filter_elim in H.  destruct H as [L R]. 
            split. 
               apply idem_lemma4; auto. 
               apply idem_lemma2; auto. 
            admit. (* congruence *) 
Qed. 




Lemma test2_idempotent_44 : 
          brel_bop_left_monotone S lte bS -> 
          brel_bop_right_monotone S lte bS -> 
   ((bop_not_idempotent S rS bS) + 
    ((bop_idempotent S rS bS) *  (brel_bop_not_SND S lte bS)))  -> 
   {X : finite_set S & uop_min (X ^* X) !== uop_min X}. 
Proof. intros lm rm [ [ a P ] | [idem [a [b [P1 P2]]]] ]. 
       exists (a :: nil). compute.  rewrite (ref_lte a), (ref_lte (a [*] a)), P. reflexivity.       
       assert (A := lm). unfold brel_bop_left_monotone in A. 
       assert (B := rm). unfold brel_bop_right_monotone in B. 
       assert (C : ∀ (x y z : S), x <== y -> x <== z -> x <== y [*] z). 
          apply (brel_bop_monotone_and_idempotent_left S rS lte); auto.
       assert (D : (a # b) + (a <== b) + (b <== a )). 
          apply pre_order_three_cases.   
          destruct D as [[D | D] | D]. 
(*             apply incomp_elim in D.  destruct D as [L R].  *) 
             exists (a :: b :: nil). 
             assert (F : uop_min (a :: b :: nil) === (a :: b :: nil)). admit. 
             assert (G : uop_min ((a :: b :: nil) ^* (a :: b :: nil)) 
                         === 
                         uop_min (a :: (a [*] b) :: (b [*] a) :: b :: nil)). admit. 
             assert (H : (a # (a [*] b)) + (a <== (a [*] b)) + ((a [*] b) <== a )). 
                 apply pre_order_three_cases.  
             assert (J : (b # (a [*] b)) + (b <== (a [*] b)) + ((a [*] b) <== b )). 
                 apply pre_order_three_cases.  
           assert (K : ((b [*] a) # (a [*] b)) + ((b [*] a) <== (a [*] b)) + ((a [*] b) <== (b [*] a) )). 
                 apply pre_order_three_cases.  
             destruct H as [[H | H] | H]. 
                destruct J as [[J | J] | J]. 
                   destruct K as [[K | K] | K]. 
                      admit. 
                      admit. 
                      admit. 
                   rewrite J in P2. discriminate. 
                   admit. 
                rewrite H in P1. discriminate. 
                destruct J as [[J | J] | J]. 
                   admit. 
                   rewrite J in P2. discriminate.  
                   admit. 
             assert (E := C _ _ _ (ref_lte a) D). rewrite P1 in E. discriminate. 
             assert (E := C _ _ _ D (ref_lte b)). rewrite P2 in E. discriminate. 
Qed. 





Lemma brel_set_false_intro : ∀ (X Y : finite_set S), 
     (brel_subset S rS X Y = false) + (brel_subset S rS Y X = false)  → brel_set S rS X Y = false. 
Proof. intros X Y [H1 | H2]; unfold brel_set; unfold brel_and_sym; apply andb_is_false_right; auto. 
Defined. 

(*
Lemma test2_not_idempotent_not_P1 : 
   { a : S & {X : list S & 
     (is_minimal_in S rS lte a (bop_list_product_left S bS X X) = true) * 
     (is_minimal_in S rS lte a X = false)}} -> 
    uop_bop_not_reduced_idempotence (finite_set S) (brel_set S rS) (bop_list_product_left S bS) (uop_minset S rS lte). 
Proof. intros [s [X [H1 H2]]]. 
       unfold uop_bop_not_reduced_idempotence. 
(*
       exists a b in X  with s = ab and s is minimal 
       
       ab is not in X.  so a <> s and b <> s 

       let s0 = {a, b} 

        XX = {aa, ab ba, bb} = {aa, s ba, bb}.  s is still minimal 

        so XX <> X. 
*)       
        admit. 
Defined. 



Lemma test2_not_idempotent_not_Q1 : 
   { a : S & {X : list S & 
     (is_minimal_in S rS lte a X = true) * 
     (is_minimal_in S rS lte a (bop_list_product_left S bS X X) = false)
    }} -> 
    uop_bop_not_reduced_idempotence (finite_set S) (brel_set S rS) (bop_list_product_left S bS) (uop_minset S rS lte). 
Proof. intros [s [X [H1 H2]]]. 
       unfold uop_bop_not_reduced_idempotence. 

(* 
       a in X minimal 

       a not minimal in XX 

       case 1: a not in XX 
          s0 = X works 

       case 2 : a = bc, but no longer minimal 
          Violate monotonicity? 
*) 
   admit. 
Defined. 


(* 
      a minimal in X  <--> a minimal in XX 

*) 
Definition P1 (S : Type) (eq lte : brel S) (bS : binary_op S) := 
    ∀ (X : list S) (a : S), 
     is_minimal_in S eq lte a (bop_list_product_left S bS X X) = true -> 
                             (is_minimal_in S eq lte a X = true). 


Definition not_P1 (S : Type) (eq lte : brel S) (bS : binary_op S) := 
   { X : list S & {a : S & 
     (is_minimal_in S eq lte a (bop_list_product_left S bS X X) = true) * 
     (is_minimal_in S eq lte a X = false) }}.
(*

not_idempotent + (idempotent * ??) -> not_P1

not idempotent: 
   aa <> a :  aa minimal in [a][a], not minimal in [a] 

   
idempotent : and   not(a b < a -> b < a) + not(b a < a -> b < a)


Q? 

idempotent * (not idempotent +  ((a b < a -> b < a) * (b a < a -> b < a))) -> P1

    a minimal in XX --> all x all y, not (xy < a) 
    a minimal in X == all x not (x < a) 

*) 


Definition Q1 (S : Type) (eq lte : brel S) (bS : binary_op S) := 
    ∀ (X : list S) (a : S), 
     is_minimal_in S eq lte a X = true -> 
             (is_minimal_in S eq lte a (bop_list_product_left S bS X X) = true). 



Definition not_Q1 (S : Type) (eq lte : brel S) (bS : binary_op S) := 
    {X : list S & { a : S &  
     (is_minimal_in S eq lte a X = true) *  
     (is_minimal_in S eq lte a (bop_list_product_left S bS X X) = false)}}. 


(* 

Now, express this PURELY IN TERMS of (eq, lte bS). 


*) 


*) 
End MinLift. 


Section MinUnionLift. 

End MinUnionLift. 

Section MinLiftUnion . 

End MinLiftUnion. 