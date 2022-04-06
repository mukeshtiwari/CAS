Require Import CAS.coq.common.compute.
Require Import Coq.Strings.String.
Require Import CAS.coq.common.ast. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures. 
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.dual.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.cast_up. 

Section Computation. 

Definition brel_lte_left:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, eq x (b x y). 

Definition brel_lt_left:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y,  below (brel_lte_left eq b) y x.

Definition brel_lte_right:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, eq y (b x y). 

Definition brel_lt_right:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, below (brel_lte_right eq b) y x. 

End Computation.

Section IntroElim.

Variable S  : Type. 
Variable eq : brel S.
Variable b     : binary_op S.

Lemma brel_lt_left_intro (s1 s2 : S) : eq s1 (b s1 s2) = true -> eq s2 (b s2 s1) = false -> brel_lt_left eq b s1 s2 = true. 
Proof. intros A B. compute. rewrite A, B. reflexivity. Qed. 

Lemma brel_lt_left_elim (s1 s2 : S) : brel_lt_left eq b s1 s2 = true -> (eq s1 (b s1 s2) = true) * (eq s2 (b s2 s1) = false). 
Proof. compute. case_eq(eq s1 (b s1 s2)); intro A; case_eq(eq s2 (b s2 s1)); intro B; auto. Qed. 

Lemma brel_lt_left_false_intro (s1 s2 : S) : (eq s1 (b s1 s2) = false) + (eq s2 (b s2 s1) = true) -> brel_lt_left eq b s1 s2 = false. 
Proof. intros [A | A]; compute; rewrite A. reflexivity. case_eq(eq s1 (b s1 s2)); intro B; auto. Qed. 

Lemma brel_lt_left_false_elim (s1 s2 : S) : brel_lt_left eq b s1 s2 = false -> (eq s1 (b s1 s2) = false) + (eq s2 (b s2 s1) = true). 
Proof. compute. case_eq(eq s1 (b s1 s2)); intro A; case_eq(eq s2 (b s2 s1)); intro B; auto. Qed. 


(*
Lemma brel_lte_left_equiv (s t : S)
      (H1 : eq t (bS t s) = true)
      (H2 : eq s (bS s t) = true) : equiv (brel_lte_left eq bS) s t = true. 
Proof. compute.  rewrite H1, H2. reflexivity. Qed.

Lemma brel_lte_left_below (s t : S)
      (H1 : eq t (bS t s) = true)
      (H2 : eq s (bS s t) = false) : below (brel_lte_left eq bS) s t = true. 
Proof. compute.  rewrite H1, H2. reflexivity. Qed. 

Lemma brel_lte_left_incomp (s t : S)
      (H1 : eq t (bS t s) = false)
      (H2 : eq s (bS s t) = false) : incomp (brel_lte_left eq bS) s t = true. 
Proof. compute.  rewrite H1, H2. reflexivity. Qed.
*) 


End IntroElim.

Section Theory.

Variable S  : Type. 

Variable eq : brel S.
Variable eqCong : brel_congruence S eq eq.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable trnS : brel_transitive S eq.
Definition symS_dual := brel_symmetric_implies_dual S eq symS. 

Variable bS     : binary_op S.
Variable congS : bop_congruence S eq bS.

Variable wS : S.
Variable f : S -> S.
Variable Pf   : brel_not_trivial S eq f.

Notation "a == b"    := (eq a b = true) (at level 30).
Notation "a != b"    := (eq a b = false) (at level 30).
Notation "a (+) b"   := (bS a b) (at level 15).


(* seems like this should be derived .... 
   is it used? 
 *)


Lemma brel_lt_left_total_order_split
      (commS : bop_commutative S eq bS)
      (selS : bop_selective S eq bS) : 
      ∀  (x y : S), 
      ((eq x y = true)  *  (brel_lt_left eq bS x y = false)) 
    + ((eq x y = false) *  (brel_lt_left eq bS x y = true)) 
    + ((eq x y = false) *  (brel_lt_left eq bS x y = false)).  
Proof. intros x y. 
       case_eq(eq x  y); intro H. 
          left. left. split. 
             reflexivity. 
             unfold brel_lt_left.
             assert (idemS := bop_selective_implies_idempotent S eq bS selS). 
             assert (Ix := idemS x). assert (Iy := idemS y). 
             assert (K := congS x y x x (refS x) (symS x y H)). 
             assert (Q : eq y (bS x y) = true). apply symS in K. apply symS in H. apply symS in Ix. 
                   apply (trnS _ _ _ H  (trnS _ _ _ Ix K)). 
             unfold below, brel_lte_left. unfold uop_not. 
             apply symS in Ix. apply symS in K. rewrite (trnS _ _ _ Ix K). 
             rewrite (trnS _ _ _ Q (commS x y)). compute. reflexivity. 
             
          unfold brel_lt_left. unfold below, brel_lte_left. unfold uop_not. 
          destruct (selS x y) as [K | K]; apply symS in K. 
             left. right. split.
                reflexivity.                          
                assert (J := brel_transititivity_implies_dual _ _ trnS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J. 
                rewrite K.  case_eq(eq y (bS y x)); intro L; auto.
                assert (M := commS y x). rewrite (trnS _ _ _ L M) in J. 
                discriminate J. 
                
             right. split.
                reflexivity.                          
                apply (brel_symmetric_implies_dual _ _ symS) in H. 
                assert (J := brel_transititivity_implies_dual _ _ trnS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J.
                rewrite J. simpl. reflexivity.
Defined.  

(*********************** PO properties ************************************) 


Lemma brel_lte_left_congruence : brel_congruence S eq (brel_lte_left eq bS).
Proof. compute. intros s t u v H1 H2. apply eqCong; auto. Qed.

Lemma brel_lte_right_congruence : brel_congruence S eq (brel_lte_right eq bS).
Proof. compute. intros s t u v H1 H2. apply eqCong; auto. Qed.

Lemma brel_lt_left_congruence : brel_congruence S eq (brel_lt_left eq bS).
Proof. compute. intros s t u v H1 H2.
       assert (A := congS _ _ _ _ H1 H2).
       assert (B := congS _ _ _ _ H2 H1).        
       rewrite (eqCong _ _ _ _ H1 A).
       rewrite (eqCong _ _ _ _ H2 B).
       reflexivity. 
Qed.

Lemma brel_lte_left_reflexive (idemS : bop_idempotent S eq bS) : brel_reflexive S  (brel_lte_left eq bS).
Proof. compute. intro s. auto. Qed.

Lemma brel_lte_right_reflexive (idemS : bop_idempotent S eq bS) : brel_reflexive S  (brel_lte_right eq bS).
Proof. compute. intro s. auto. Qed.

Lemma brel_lte_left_not_reflexive (idemS : bop_not_idempotent S eq bS) : brel_not_reflexive S  (brel_lte_left eq bS).
Proof. destruct idemS as [a A]. exists a. compute.
       case_eq(eq a (a (+) a)); intro H; auto.
       apply symS in H. rewrite H in A. discriminate A. 
Defined. 

Lemma brel_lte_left_transitive (assoS : bop_associative S eq bS) : brel_transitive S  (brel_lte_left eq bS).
Proof. compute. intros s t u H1 H2.
       assert (A : (s (+) t) == (s (+) (t (+) u))).
          exact (congS _ _ _ _ (refS s) H2). 
       assert (B : (s (+) (t (+) u)) == ((s (+) t) (+) u)).
          exact (symS _ _ (assoS s t u)). 
       assert (C : ((s (+) t) (+) u) == (s (+) u)).
          exact (congS _ _ _ _ (symS _ _ H1) (refS u)).
       exact (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ H1 A) B) C).
Qed.

Lemma brel_lte_right_transitive (assoS : bop_associative S eq bS) : brel_transitive S  (brel_lte_right eq bS).
Proof. compute. intros s t u H1 H2.
       assert (A : (t (+) u) == ((s (+) t) (+) u)). 
          exact (congS _ _ _ _ H1 (refS u)). 
       assert (B : ((s (+) t) (+) u) == (s (+) (t (+) u))).
          exact (assoS s t u). 
       assert (C : (s (+) (t (+) u)) == (s (+) u)).
          exact (congS _ _ _ _ (refS s) (symS _ _ H2)).  
       exact (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ H2 A) B) C).
Qed.

Lemma brel_lte_left_antisymmetric (commS : bop_commutative S eq bS) : brel_antisymmetric S eq (brel_lte_left eq bS).
Proof. intros s t H1 H2.
       assert (A := commS s t). 
       apply symS in H2. 
       assert (B := trnS _ _ _ H1 A).
       assert (C := trnS _ _ _ B H2).
       exact C. 
Qed.

Lemma brel_lte_right_antisymmetric (commS : bop_commutative S eq bS) : brel_antisymmetric S eq (brel_lte_right eq bS).
Proof. intros s t H1 H2.
       assert (A := commS s t). compute in H1, H2. 
       assert (B := trnS _ _ _ H1 A). apply symS in B. 
       exact (trnS _ _ _ H2 B).
Qed.

(* note : need something stronger than not_commutative to get not_antisymmetric. 

Explore this further????

*) 
Lemma brel_lte_left_not_antisymmetric
         (ncommS : {s : S & {t : S & (s (+) t != t (+) s) * s == (s (+) t) * t == (t (+) s) }}) :
             brel_not_antisymmetric S eq (brel_lte_left eq bS).
Proof. destruct ncommS as [a [b [[A B] C]]]. exists (a, b). compute. 
       split; auto. 
       case_eq(eq a b); intro H; auto. apply symS in B. 
       assert (D := trnS _ _ _ B H).
       assert (E := trnS _ _ _ D C).
       rewrite E in A. discriminate A. 
Qed.

(* just checking that this is an iff .... 

Explore this further????
*) 
Lemma brel_lte_left_antisymmetric_v2
      (commS : ∀ s t : S, (s (+) t == t (+) s) + (s != (s (+) t)) + (t != (t (+) s))) :
         brel_antisymmetric S eq (brel_lte_left eq bS).
Proof. compute. intros s t H1 H2.
       destruct (commS s t) as [[A | A] | A].
       + apply symS in H2. 
         assert (B := trnS _ _ _ H1 A).
         assert (C := trnS _ _ _ B H2).
         exact C.
       + rewrite A in H1. discriminate H1.
       + rewrite A in H2. discriminate H2.
Qed.

Lemma brel_lte_left_total
      (commS : bop_commutative S eq bS)
      (selS : bop_selective S eq bS) : brel_total S (brel_lte_left eq bS).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       left. apply symS; auto.        
       right.
       assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A). 
Qed.

Lemma brel_lte_right_total
      (commS : bop_commutative S eq bS)
      (selS : bop_selective S eq bS) : brel_total S (brel_lte_right eq bS).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       right. assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A).        
       left. exact (symS _ _ H). 
Qed.

Lemma brel_lte_left_not_total
      (commS : bop_commutative S eq bS)      
      (nselS : bop_not_selective S eq bS) : brel_not_total S (brel_lte_left eq bS).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute.
       apply symS_dual in A. rewrite A.
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C B). 
       apply symS_dual in D. rewrite D. 
       auto.        
Defined.

Lemma brel_lte_right_not_total
      (commS : bop_commutative S eq bS)      
      (nselS : bop_not_selective S eq bS) : brel_not_total S (brel_lte_right eq bS).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute. split. 
       apply symS_dual in B. exact B. 
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C A). 
       apply symS_dual in D. exact D. 
Defined.

Lemma brel_lte_left_is_top (s : S) (idS : bop_is_id S eq bS s) : brel_is_top S (brel_lte_left eq bS) s. 
Proof. compute. intro t.
       destruct (idS t) as [_ B].
       apply symS. exact B. 
Defined.

Lemma brel_lte_right_is_bottom (s : S) (idS : bop_is_id S eq bS s) : brel_is_bottom S (brel_lte_right eq bS) s. 
Proof. compute. intro t.
       destruct (idS t) as [A B].
       exact (symS _ _ A). 
Defined.

Lemma brel_lte_left_exists_top (idS : bop_exists_id S eq bS) : brel_exists_top S (brel_lte_left eq bS).
Proof. destruct idS as [s A]. exists s.  apply brel_lte_left_is_top; auto. Defined.

Lemma brel_lte_right_exists_bottom (idS : bop_exists_id S eq bS) : brel_exists_bottom S (brel_lte_right eq bS).
Proof. destruct idS as [s A]. exists s.  apply brel_lte_right_is_bottom; auto. Defined.

Lemma brel_lte_left_not_exists_top
      (commS : bop_commutative S eq bS)
      (nidS : bop_not_exists_id S eq bS) : brel_not_exists_top S (brel_lte_left eq bS).
Proof. compute. intros a. destruct (nidS a) as [ c A].  exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined.

Lemma brel_lte_right_not_exists_bottom
      (commS : bop_commutative S eq bS)
      (nidS : bop_not_exists_id S eq bS) : brel_not_exists_bottom S (brel_lte_right eq bS).
Proof. compute. intros a. destruct (nidS a) as [ c A].  exists c. 
       destruct A as [A | A].
       + apply symS_dual. exact A.
       + assert (B := commS a c).
         case_eq(eq c (a (+) c)); intro C; auto.  
         rewrite (symS _ _ (trnS _ _ _ C B)) in A.
         discriminate A. 
Defined.

Lemma brel_lte_left_exists_qo_top
      (commS : bop_commutative S eq bS)      
      (idS : bop_exists_id S eq bS) : brel_exists_qo_top S eq (brel_lte_left eq bS).
Proof. destruct idS as [s A]. exists s. split. 
       apply brel_lte_left_is_top; auto.
       intros a. compute. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined.

Lemma brel_lte_left_not_exists_qo_top
      (commS : bop_commutative S eq bS)      
      (nidS : bop_not_exists_id S eq bS) : brel_not_exists_qo_top S eq (brel_lte_left eq bS).
Proof. compute. intros a. left. 
       destruct (nidS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined.


Lemma brel_lte_left_is_bottom (s : S) (annS : bop_is_ann S eq bS s) : brel_is_bottom S (brel_lte_left eq bS) s.
Proof. intro t. destruct (annS t) as [B _]. compute. apply symS. exact B. Defined.

Lemma brel_lte_right_is_top (s : S) (annS : bop_is_ann S eq bS s) : brel_is_top S (brel_lte_right eq bS) s.
Proof. intro t. destruct (annS t) as [B C]. compute.
       exact (symS _ _ C). 
Defined.

Lemma brel_lte_left_exists_bottom (annS : bop_exists_ann S eq bS) : brel_exists_bottom S (brel_lte_left eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_left_is_bottom; auto. Defined. 

Lemma brel_lte_right_exists_top (annS : bop_exists_ann S eq bS) : brel_exists_top S (brel_lte_right eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_right_is_top; auto. Defined. 


Lemma brel_lte_left_not_exists_bottom
      (commS : bop_commutative S eq bS)      
      (annS : bop_not_exists_ann S eq bS) : brel_not_exists_bottom S (brel_lte_left eq bS).
Proof. intro s. compute. destruct (annS s) as [t [L | R]]; exists t.
       + case_eq(eq s (s (+) t)); intro C; auto. apply symS in C. 
         rewrite C in L. discriminate L. 
       + case_eq(eq s (s (+) t)); intro C; auto.
         assert (D := commS s t). 
         assert (E := trnS _ _ _ C D). apply symS in E.
         rewrite E in R. discriminate R. 
Defined.

Lemma brel_lte_right_not_exists_top
      (commS : bop_commutative S eq bS)      
      (annS : bop_not_exists_ann S eq bS) : brel_not_exists_top S (brel_lte_right eq bS).
Proof. intro s. compute. destruct (annS s) as [t [L | R]]; exists t.
       + case_eq(eq s (t (+) s)); intro C; auto.
         assert (D := commS t s). 
         assert (E := trnS _ _ _ C D). apply symS in E.
         rewrite E in L. discriminate L. 
       + case_eq(eq s (t (+) s)); intro C; auto. apply symS in C. 
         rewrite C in R. discriminate R. 
Defined.


Lemma brel_lte_left_is_qo_bottom
      (s : S)
      (commS : bop_commutative S eq bS)      
      (annS : bop_is_ann S eq bS s) : brel_is_qo_bottom S eq (brel_lte_left eq bS) s.
Proof. compute. split.
       intro t. destruct (annS t) as [B _]. apply symS. exact B. 
       intros a. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined. 

Lemma brel_lte_left_exists_qo_bottom
      (commS : bop_commutative S eq bS)
      (annS : bop_exists_ann S eq bS) : brel_exists_qo_bottom S eq (brel_lte_left eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_left_is_qo_bottom; auto. Defined.

Lemma brel_lte_left_not_exists_qo_bottom
      (commS : bop_commutative S eq bS)
      (annS : bop_not_exists_ann S eq bS) : brel_not_exists_qo_bottom S eq (brel_lte_left eq bS).
Proof. intro s. compute. destruct (annS s) as [t [L | R]]; left; exists t.
       + case_eq(eq s (s (+) t)); intro C; auto. apply symS in C. 
         rewrite C in L. discriminate L. 
       + case_eq(eq s (s (+) t)); intro C; auto.
         assert (D := commS s t). 
         assert (E := trnS _ _ _ C D). apply symS in E.
         rewrite E in R. discriminate R. 
Defined.

(*  WTF is this? 


Lemma brel_lte_left_bottoms_set_is_finite (sif : something_is_finite S eq b) :
       bottoms_set_is_finite S eq (brel_lte_left eq b). 
Proof. destruct sif as [[B w] [Q P]].
       exists (B, w). split. 

       (* is_antichain S eq (brel_lte_left eq b) B *)
       unfold is_antichain.
       intros s A t C. compute.
       assert (D := Q s A t C). 
       destruct D as [[E F] | [E F]]; rewrite E, F; reflexivity. 

       intro s. destruct (P s) as [A | A]. 
          left. exact A. 
          destruct A as [A1 [A2 A3]]. right. split. 
             (* in_set eq B (w s) = true *)
             exact A1. 
             (* below (brel_lte_left eq b) s (w s) = true *)
             compute. rewrite A2, A3. reflexivity. 
Defined.

Lemma brel_lte_left_bottoms_set_not_is_finite (sif : something_not_is_finite S eq b) :
       bottoms_set_not_is_finite S eq (brel_lte_left eq b). 
Proof. destruct sif as [F A].
       unfold bottoms_set_not_is_finite.
       exists F. 
       intros B C.

          assert (D : is_interesting S eq b B).
             unfold is_interesting. unfold is_antichain in C. 
             intros s D t E.
             assert (bC := commS s t). 
             assert (G := C s D t E). apply equiv_or_incomp_elim in G.
             unfold brel_lte_left in G.              
             destruct G as [G | G]. 
                apply equiv_elim in G. left. 
                destruct G as [G1 G2]. split.
                   exact G2. 
                   exact G1. 
                
                apply incomp_elim in G. right. 
                destruct G as [G1 G2]. split.                   
                   exact G2. 
                   exact G1. 
          destruct (A B D) as [E G].
          split. 
            exact E.           
            intros s H.
            assert (I := G s H).
            apply below_false_intro.
            unfold brel_lte_left. 
            exact I. 
Defined. 
*) 


       
(*
Definition from_sg_left_bottoms (a: S) (x: unit)  := a :: nil.
Definition from_sg_left_lower (a b : S) := a.               
Definition from_sg_left_bottoms_finite_witness (a : S) := (from_sg_left_bottoms a, from_sg_left_lower a).


Lemma brel_lte_left_bottoms_finite (annS : bop_exists_ann S eq b) : bottoms_finite S eq (brel_lte_left eq b).
Proof. unfold bottoms_finite. destruct annS as [ c A]. compute in A. 
       exists (from_sg_left_bottoms_finite_witness c). 
       simpl. intro s.
       destruct (A s) as [B C]. unfold from_sg_left_lower. unfold brel_lte_left.
       rewrite refS. simpl. split; auto. 
Defined.

Lemma brel_lte_left_not_bottoms_finite (nannS : bop_not_exists_ann S eq b) : bottoms_finite S eq (brel_lte_left eq b).
Proof. unfold bop_not_exists_ann in nannS. 
*) 


End Theory.

Section ACAS.

Section Decide.

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S).  

Definition brel_lte_left_total_decide
     (plus_comm : bop_commutative S eq plus) 
     (D : bop_selective_decidable S eq plus) : 
          brel_total_decidable S (brel_lte_left eq plus) := 
     let trn := A_eqv_transitive S eq eqvP in 
     let sym := A_eqv_symmetric S eq eqvP in 
     match D with
     | inl sel  => inl (brel_lte_left_total S eq sym trn plus plus_comm sel)
     | inr nsel => inr (brel_lte_left_not_total S eq sym trn plus plus_comm nsel)
     end.

Definition brel_lte_right_total_decide
     (plus_comm : bop_commutative S eq plus) 
     (D : bop_selective_decidable S eq plus) : 
          brel_total_decidable S (brel_lte_right eq plus) := 
     let trn := A_eqv_transitive S eq eqvP in 
     let sym := A_eqv_symmetric S eq eqvP in 
     match D with
     | inl sel  => inl (brel_lte_right_total S eq sym trn plus plus_comm sel)
     | inr nsel => inr (brel_lte_right_not_total S eq sym trn plus plus_comm nsel)
     end.


Definition brel_lte_left_exists_top_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_id_decidable S eq plus) :
                 brel_exists_top_decidable S (brel_lte_left eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl idS  => inl (brel_lte_left_exists_top S eq sym plus idS)
  | inr nidS => inr (brel_lte_left_not_exists_top S eq sym trn plus plus_comm nidS)
  end. 


Definition brel_lte_right_exists_bottom_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_id_decidable S eq plus) :
                 brel_exists_bottom_decidable S (brel_lte_right eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl idS  => inl (brel_lte_right_exists_bottom S eq sym plus idS)
  | inr nidS => inr (brel_lte_right_not_exists_bottom S eq sym trn plus plus_comm nidS)
  end. 


Definition brel_lte_left_exists_bottom_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_ann_decidable S eq plus) :
                 brel_exists_bottom_decidable S (brel_lte_left eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl annS  => inl (brel_lte_left_exists_bottom S eq sym plus annS)
  | inr nannS => inr (brel_lte_left_not_exists_bottom S eq sym trn plus plus_comm nannS)
  end.

Definition brel_lte_right_exists_top_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_ann_decidable S eq plus) :
                 brel_exists_top_decidable S (brel_lte_right eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl annS  => inl (brel_lte_right_exists_top S eq sym plus annS)
  | inr nannS => inr (brel_lte_right_not_exists_top S eq sym trn plus plus_comm nannS)
  end. 

End Decide.

Section Proofs.

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S).
  
Definition po_proofs_from_sg_CI_left_proofs
           (P : sg_CI_proofs S eq plus) : po_proofs S eq ((brel_lte_left eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CI_congruence _ _ _   P in
let assoc := A_sg_CI_associative _ _ _   P in
let idem  := A_sg_CI_idempotent _ _ _   P in
let comm  := A_sg_CI_commutative _ _ _   P in
let nsel  := A_sg_CI_not_selective _ _ _   P in   
{|  
  A_po_congruence    := brel_lte_left_congruence S eq eqcong sym plus cong 
; A_po_reflexive     := brel_lte_left_reflexive S eq sym plus idem 
; A_po_transitive    := brel_lte_left_transitive S eq ref sym trn plus cong assoc 
; A_po_antisymmetric := brel_lte_left_antisymmetric S eq sym trn plus comm 
; A_po_not_total     := brel_lte_left_not_total S eq sym trn plus comm nsel 
|}.

Definition po_proofs_from_sg_CI_right_proofs
           (P : sg_CI_proofs S eq plus) : po_proofs S eq ((brel_lte_right eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CI_congruence _ _ _   P in
let assoc := A_sg_CI_associative _ _ _   P in
let idem  := A_sg_CI_idempotent _ _ _   P in
let comm  := A_sg_CI_commutative _ _ _   P in
let nsel  := A_sg_CI_not_selective _ _ _   P in   
{|  
  A_po_congruence    := brel_lte_right_congruence S eq eqcong sym plus cong 
; A_po_reflexive     := brel_lte_right_reflexive S eq sym plus idem 
; A_po_transitive    := brel_lte_right_transitive S eq ref sym trn plus cong assoc 
; A_po_antisymmetric := brel_lte_right_antisymmetric S eq sym trn plus comm 
; A_po_not_total     := brel_lte_right_not_total S eq sym trn plus comm nsel 
|}.


Definition to_proofs_from_sg_CS_left_proofs
           (P : sg_CS_proofs S eq plus) : to_proofs S eq ((brel_lte_left eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CS_congruence _ _ _   P in
let assoc := A_sg_CS_associative _ _ _   P in
let comm  := A_sg_CS_commutative _ _ _   P in
let sel   := A_sg_CS_selective _ _ _   P in
let idem  := bop_selective_implies_idempotent S eq plus sel in 
{|  
  A_to_congruence    := brel_lte_left_congruence S eq eqcong sym plus cong 
; A_to_reflexive     := brel_lte_left_reflexive S eq sym plus idem 
; A_to_transitive    := brel_lte_left_transitive S eq ref sym trn plus cong assoc 
; A_to_antisymmetric := brel_lte_left_antisymmetric S eq sym trn plus comm 
; A_to_total         := brel_lte_left_total S eq sym trn plus comm sel 
|}.

Definition to_proofs_from_sg_CS_right_proofs
           (P : sg_CS_proofs S eq plus) : to_proofs S eq ((brel_lte_right eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CS_congruence _ _ _   P in
let assoc := A_sg_CS_associative _ _ _   P in
let comm  := A_sg_CS_commutative _ _ _   P in
let sel   := A_sg_CS_selective _ _ _   P in
let idem  := bop_selective_implies_idempotent S eq plus sel in 
{|  
  A_to_congruence    := brel_lte_right_congruence S eq eqcong sym plus cong 
; A_to_reflexive     := brel_lte_right_reflexive S eq sym plus idem 
; A_to_transitive    := brel_lte_right_transitive S eq ref sym trn plus cong assoc 
; A_to_antisymmetric := brel_lte_right_antisymmetric S eq sym trn plus comm 
; A_to_total         := brel_lte_right_total S eq sym trn plus comm sel 
|}.

End Proofs.

Section Combinators.


Definition A_to_from_sg_CS_left {S : Type} (A : A_sg_CS S) : @A_to S :=
let eqv    := A_sg_CS_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CS_bop _ A in
let sgP    := A_sg_CS_proofs _ A in
let nidP   := A_sg_CS_not_exists_id _ A in
let nannP  := A_sg_CS_not_exists_ann _ A in
let comm   := A_sg_CS_commutative  _ _ _ sgP in 
{|
  A_to_eqv               := eqv 
; A_to_lte               := brel_lte_left eq bop 
; A_to_not_exists_top    := brel_lte_left_not_exists_top S eq symS trnS bop comm nidP
; A_to_not_exists_bottom := brel_lte_left_not_exists_bottom S eq symS trnS bop comm nannP
; A_to_proofs            := to_proofs_from_sg_CS_left_proofs S eq eqvP bop sgP 
; A_to_ast               := Ast_or_llte (A_sg_CS_ast _ A) 
|}.
  

Definition A_to_with_top_from_sg_CS_with_id_left {S : Type} (A : A_sg_CS_with_id S) : @A_to_with_top S :=
let eqv    := A_sg_CS_wi_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CS_wi_bop _ A in
let sgP    := A_sg_CS_wi_proofs _ A in
let idP    := A_sg_CS_wi_exists_id _ A in
let nannP  := A_sg_CS_wi_not_exists_ann _ A in
let comm   := A_sg_CS_commutative  _ _ _ sgP in 
{|
  A_to_wt_eqv               := eqv 
; A_to_wt_lte               := brel_lte_left eq bop 
; A_to_wt_exists_top        := brel_lte_left_exists_top S eq symS bop idP
; A_to_wt_not_exists_bottom := brel_lte_left_not_exists_bottom S eq symS trnS bop comm nannP
; A_to_wt_proofs            := to_proofs_from_sg_CS_left_proofs S eq eqvP bop sgP 
; A_to_wt_ast               := Ast_or_llte (A_sg_CS_wi_ast _ A) 
|}.
  

Definition A_to_with_bottom_from_sg_CS_with_ann_left {S : Type} (A : A_sg_CS_with_ann S) : @A_to_with_bottom S :=
let eqv    := A_sg_CS_wa_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CS_wa_bop _ A in
let sgP    := A_sg_CS_wa_proofs _ A in
let nidP   := A_sg_CS_wa_not_exists_id _ A in
let annP   := A_sg_CS_wa_exists_ann _ A in
let comm   := A_sg_CS_commutative  _ _ _ sgP in 
{|
  A_to_wb_eqv               := eqv 
; A_to_wb_lte               := brel_lte_left eq bop 
; A_to_wb_not_exists_top    := brel_lte_left_not_exists_top S eq symS trnS bop comm nidP
; A_to_wb_exists_bottom     := brel_lte_left_exists_bottom S eq symS bop annP
; A_to_wb_proofs            := to_proofs_from_sg_CS_left_proofs S eq eqvP bop sgP 
; A_to_wb_ast               := Ast_or_llte (A_sg_CS_wa_ast _ A) 
|}.

Definition A_to_bounded_from_sg_CS_bounded_left {S : Type} (A : A_sg_BCS S) : @A_to_bounded S :=
let eqv    := A_sg_BCS_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_BCS_bop _ A in
let sgP    := A_sg_BCS_proofs _ A in
let idP    := A_sg_BCS_exists_id _ A in
let annP   := A_sg_BCS_exists_ann _ A in
{|
  A_to_bd_eqv               := eqv 
; A_to_bd_lte               := brel_lte_left eq bop 
; A_to_bd_exists_top        := brel_lte_left_exists_top S eq symS bop idP
; A_to_bd_exists_bottom     := brel_lte_left_exists_bottom S eq symS bop annP
; A_to_bd_proofs            := to_proofs_from_sg_CS_left_proofs S eq eqvP bop sgP 
; A_to_bd_ast               := Ast_or_llte (A_sg_BCS_ast _ A) 
|}.

Definition A_po_from_sg_CI_left {S : Type} (A : A_sg_CI S) : @A_po S :=
let eqv    := A_sg_CI_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CI_bop _ A in
let sgP    := A_sg_CI_proofs _ A in
let nidP   := A_sg_CI_not_exists_id _ A in
let nannP  := A_sg_CI_not_exists_ann _ A in
let comm   := A_sg_CI_commutative  _ _ _ sgP in 
{|
  A_po_eqv               := eqv 
; A_po_lte               := brel_lte_left eq bop 
; A_po_not_exists_top    := brel_lte_left_not_exists_top S eq symS trnS bop comm nidP
; A_po_not_exists_bottom := brel_lte_left_not_exists_bottom S eq symS trnS bop comm nannP
; A_po_proofs            := po_proofs_from_sg_CI_left_proofs S eq eqvP bop sgP 
; A_po_ast               := Ast_or_llte (A_sg_CI_ast _ A) 
|}.
  

Definition A_po_with_top_from_sg_CI_with_id_left {S : Type} (A : A_sg_CI_with_id S) : @A_po_with_top S :=
let eqv    := A_sg_CI_wi_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CI_wi_bop _ A in
let sgP    := A_sg_CI_wi_proofs _ A in
let idP    := A_sg_CI_wi_exists_id _ A in
let nannP  := A_sg_CI_wi_not_exists_ann _ A in
let comm   := A_sg_CI_commutative  _ _ _ sgP in 
{|
  A_po_wt_eqv               := eqv 
; A_po_wt_lte               := brel_lte_left eq bop 
; A_po_wt_exists_top        := brel_lte_left_exists_top S eq symS bop idP
; A_po_wt_not_exists_bottom := brel_lte_left_not_exists_bottom S eq symS trnS bop comm nannP
; A_po_wt_proofs            := po_proofs_from_sg_CI_left_proofs S eq eqvP bop sgP 
; A_po_wt_ast               := Ast_or_llte (A_sg_CI_wi_ast _ A) 
|}.
  

Definition A_po_with_bottom_from_sg_CI_with_ann_left {S : Type} (A : A_sg_CI_with_ann S) : @A_po_with_bottom S :=
let eqv    := A_sg_CI_wa_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CI_wa_bop _ A in
let sgP    := A_sg_CI_wa_proofs _ A in
let nidP   := A_sg_CI_wa_not_exists_id _ A in
let annP   := A_sg_CI_wa_exists_ann _ A in
let comm   := A_sg_CI_commutative  _ _ _ sgP in 
{|
  A_po_wb_eqv               := eqv 
; A_po_wb_lte               := brel_lte_left eq bop 
; A_po_wb_not_exists_top    := brel_lte_left_not_exists_top S eq symS trnS bop comm nidP
; A_po_wb_exists_bottom     := brel_lte_left_exists_bottom S eq symS bop annP
; A_po_wb_proofs            := po_proofs_from_sg_CI_left_proofs S eq eqvP bop sgP 
; A_po_wb_ast               := Ast_or_llte (A_sg_CI_wa_ast _ A) 
|}.

Definition A_po_bounded_from_sg_CI_bounded_left {S : Type} (A : A_sg_BCI S) : @A_po_bounded S :=
let eqv    := A_sg_BCI_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_BCI_bop _ A in
let sgP    := A_sg_BCI_proofs _ A in
let idP    := A_sg_BCI_exists_id _ A in
let annP   := A_sg_BCI_exists_ann _ A in
{|
  A_po_bd_eqv               := eqv 
; A_po_bd_lte               := brel_lte_left eq bop 
; A_po_bd_exists_top        := brel_lte_left_exists_top S eq symS bop idP
; A_po_bd_exists_bottom     := brel_lte_left_exists_bottom S eq symS bop annP
; A_po_bd_proofs            := po_proofs_from_sg_CI_left_proofs S eq eqvP bop sgP 
; A_po_bd_ast               := Ast_or_llte (A_sg_BCI_ast _ A) 
|}.



  
End Combinators.

End ACAS. 



Section AMCAS.

Local Open Scope string_scope.   

Definition A_mcas_left_order_from_sg (S : Type) (A : A_sg_mcas S) : @A_or_mcas S :=
match A with
  | A_MCAS_sg_Error _ sl           => A_OR_Error sl 
  | A_MCAS_sg _ _                  => A_OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | A_MCAS_sg_C _ B                => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_C_with_id _ B        => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_C_with_ann _ B       => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_BC _ B               => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_NC _ B               => A_OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | A_MCAS_sg_NC_with_id _ B       => A_OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | A_MCAS_sg_NC_with_ann _ B      => A_OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | A_MCAS_sg_BNC _ B              => A_OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | A_MCAS_sg_CS _ B               => A_OR_to (A_to_from_sg_CS_left B)
  | A_MCAS_sg_CS_with_id _ B       => A_OR_to_with_top (A_to_with_top_from_sg_CS_with_id_left B)
  | A_MCAS_sg_CS_with_ann _ B      => A_OR_to_with_bottom (A_to_with_bottom_from_sg_CS_with_ann_left B)
  | A_MCAS_sg_BCS _ B              => A_OR_to_bounded (A_to_bounded_from_sg_CS_bounded_left B)
  | A_MCAS_sg_CI _ B               => A_OR_po (A_po_from_sg_CI_left B)
  | A_MCAS_sg_CI_with_id _ B       => A_OR_po_with_top (A_po_with_top_from_sg_CI_with_id_left B)
  | A_MCAS_sg_CI_with_ann _ B      => A_OR_po_with_bottom (A_po_with_bottom_from_sg_CI_with_ann_left B)
  | A_MCAS_sg_BCI _ B              => A_OR_po_bounded (A_po_bounded_from_sg_CI_bounded_left B)
  | A_MCAS_sg_CNI _ B              => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_CNI_with_id _ B      => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_CNI_with_ann _ B     => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_BCNI _ B             => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_CK _ B               => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | A_MCAS_sg_CK_with_id _ B       => A_OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
end.     

End AMCAS.

  
  
Section CAS.

Section Certify.

Definition brel_lte_left_total_certify {S : Type} 
     (D : @check_selective S) : @certify_total S  := 
     match D with
     | Certify_Selective  => Certify_Total 
     | Certify_Not_Selective p  => Certify_Not_Total p 
     end.

Definition brel_lte_right_total_certify {S : Type} 
     (D : @check_selective S) : @certify_total S  := 
     match D with
     | Certify_Selective  => Certify_Total 
     | Certify_Not_Selective p  => Certify_Not_Total p 
     end.


Definition brel_lte_left_exists_top_certify {S : Type} 
           (D : @check_exists_id S) : @certify_exists_top S := 
  match D with
  | Certify_Exists_Id id  => Certify_Exists_Top id 
  | Certify_Not_Exists_Id => Certify_Not_Exists_Top
  end. 


Definition brel_lte_right_exists_bottom_certify {S : Type} 
           (D : @check_exists_id S) : @certify_exists_bottom S := 
  match D with
  | Certify_Exists_Id id  => Certify_Exists_Bottom id 
  | Certify_Not_Exists_Id => Certify_Not_Exists_Bottom
  end. 


Definition brel_lte_left_exists_bottom_certify {S : Type} 
           (D : @check_exists_ann S) : @certify_exists_bottom S := 
  match D with
  | Certify_Exists_Ann ann  => Certify_Exists_Bottom ann 
  | Certify_Not_Exists_Ann => Certify_Not_Exists_Bottom
  end. 


Definition brel_lte_right_exists_top_certify {S : Type} 
           (D : @check_exists_ann S) : @certify_exists_top S := 
  match D with
  | Certify_Exists_Ann ann  => Certify_Exists_Top ann 
  | Certify_Not_Exists_Ann => Certify_Not_Exists_Top
  end. 

End Certify.

Section Certificates.

Definition po_certs_from_sg_CI_left_certs {S : Type} (P : @sg_CI_certificates S) : @po_certificates S :=
{|  
  po_congruence    := Assert_Brel_Congruence 
; po_reflexive     := Assert_Reflexive 
; po_transitive    := Assert_Transitive
; po_antisymmetric := Assert_Antisymmetric 
; po_not_total     := match sg_CI_not_selective P with
                      | Assert_Not_Selective p => Assert_Not_Total p
                      end
|}.

Definition po_certs_from_sg_CI_right_certs {S : Type} (P : @sg_CI_certificates S) : @po_certificates S :=
{|  
  po_congruence    := Assert_Brel_Congruence 
; po_reflexive     := Assert_Reflexive 
; po_transitive    := Assert_Transitive
; po_antisymmetric := Assert_Antisymmetric 
; po_not_total     := match sg_CI_not_selective P with
                      | Assert_Not_Selective p => Assert_Not_Total p
                      end
|}.


Definition to_certs_from_sg_CS_left_certs {S : Type} (P : @sg_CS_certificates S) : @to_certificates S :=
{|  
  to_congruence    := Assert_Brel_Congruence 
; to_reflexive     := Assert_Reflexive 
; to_transitive    := Assert_Transitive
; to_antisymmetric := Assert_Antisymmetric 
; to_total         := Assert_Total
|}.

Definition to_certs_from_sg_CS_right_certs {S : Type} (P : @sg_CS_certificates S) : @to_certificates S :=
{|  
  to_congruence    := Assert_Brel_Congruence 
; to_reflexive     := Assert_Reflexive 
; to_transitive    := Assert_Transitive
; to_antisymmetric := Assert_Antisymmetric 
; to_total         := Assert_Total
|}.

  
End Certificates.

Section Combinators.

Definition to_from_sg_CS_left {S : Type} (A : @sg_CS S) : @to S :=
let eqv    := sg_CS_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_CS_bop A in
let sgP    := sg_CS_certs A in
{|
  to_eqv               := eqv 
; to_lte               := brel_lte_left eq bop 
; to_not_exists_top    := Assert_Not_Exists_Top 
; to_not_exists_bottom := Assert_Not_Exists_Bottom
; to_certs             := to_certs_from_sg_CS_left_certs sgP 
; to_ast               := Ast_or_llte (sg_CS_ast A) 
|}.
  

Definition to_with_top_from_sg_CS_with_id_left {S : Type} (A : @sg_CS_with_id S) : @to_with_top S :=
let eqv    := sg_CS_wi_eqv A in
let eq     := eqv_eq eqv in
{|
  to_wt_eqv               := eqv 
; to_wt_lte               := brel_lte_left eq (sg_CS_wi_bop A)
; to_wt_exists_top        := match sg_CS_wi_exists_id A with
                             | Assert_Exists_Id id => Assert_Exists_Top id
                             end
; to_wt_not_exists_bottom := Assert_Not_Exists_Bottom
; to_wt_certs             := to_certs_from_sg_CS_left_certs(sg_CS_wi_certs A)
; to_wt_ast               := Ast_or_llte (sg_CS_wi_ast A) 
|}.

Definition to_with_bottom_from_sg_CS_with_ann_left {S : Type} (A : @sg_CS_with_ann S) : @to_with_bottom S :=
let eqv    := sg_CS_wa_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_CS_wa_bop A in
let sgP    := sg_CS_wa_certs A in
{|
  to_wb_eqv               := eqv 
; to_wb_lte               := brel_lte_left eq bop 
; to_wb_not_exists_top    := Assert_Not_Exists_Top 
; to_wb_exists_bottom     := match sg_CS_wa_exists_ann A with
                             | Assert_Exists_Ann ann => Assert_Exists_Bottom ann
                             end
; to_wb_certs             := to_certs_from_sg_CS_left_certs sgP 
; to_wb_ast               := Ast_or_llte (sg_CS_wa_ast A) 
|}.

Definition to_bounded_from_sg_CS_bounded_left {S : Type} (A : @sg_BCS S) : @to_bounded S :=
let eqv    := sg_BCS_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_BCS_bop A in
let sgP    := sg_BCS_certs A in
{|
  to_bd_eqv               := eqv 
; to_bd_lte               := brel_lte_left eq bop 
; to_bd_exists_top        := match sg_BCS_exists_id A with
                             | Assert_Exists_Id id => Assert_Exists_Top id 
                             end
; to_bd_exists_bottom     := match sg_BCS_exists_ann A with
                             | Assert_Exists_Ann ann => Assert_Exists_Bottom ann
                             end
; to_bd_certs             := to_certs_from_sg_CS_left_certs sgP 
; to_bd_ast               := Ast_or_llte (sg_BCS_ast A) 
|}.

Definition po_from_sg_CI_left {S : Type} (A : @sg_CI S) : @po S :=
let eqv    := sg_CI_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_CI_bop A in
let sgP    := sg_CI_certs A in
{|
  po_eqv               := eqv 
; po_lte               := brel_lte_left eq bop 
; po_not_exists_top    := Assert_Not_Exists_Top
; po_not_exists_bottom := Assert_Not_Exists_Bottom
; po_certs             := po_certs_from_sg_CI_left_certs sgP 
; po_ast               := Ast_or_llte (sg_CI_ast A) 
|}.

Definition po_with_top_from_sg_CI_with_id_left {S : Type} (A : @sg_CI_with_id S) : @po_with_top S :=
let eqv    := sg_CI_wi_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_CI_wi_bop A in
let sgP    := sg_CI_wi_certs A in
{|
  po_wt_eqv               := eqv 
; po_wt_lte               := brel_lte_left eq bop 
; po_wt_exists_top        := match sg_CI_wi_exists_id A with
                             | Assert_Exists_Id id => Assert_Exists_Top id 
                             end
; po_wt_not_exists_bottom := Assert_Not_Exists_Bottom 
; po_wt_certs             := po_certs_from_sg_CI_left_certs sgP 
; po_wt_ast               := Ast_or_llte (sg_CI_wi_ast A) 
|}.
  

Definition po_with_bottom_from_sg_CI_with_ann_left {S : Type} (A : @sg_CI_with_ann S) : @po_with_bottom S :=
let eqv    := sg_CI_wa_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_CI_wa_bop A in
let sgP    := sg_CI_wa_certs A in
{|
  po_wb_eqv               := eqv 
; po_wb_lte               := brel_lte_left eq bop 
; po_wb_not_exists_top    := Assert_Not_Exists_Top
; po_wb_exists_bottom     := match sg_CI_wa_exists_ann A with
                             | Assert_Exists_Ann ann => Assert_Exists_Bottom ann 
                             end
; po_wb_certs             := po_certs_from_sg_CI_left_certs sgP 
; po_wb_ast               := Ast_or_llte (sg_CI_wa_ast A) 
|}.

Definition po_bounded_from_sg_CI_bounded_left {S : Type} (A : @sg_BCI S) : @po_bounded S :=
let eqv    := sg_BCI_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_BCI_bop A in
let sgP    := sg_BCI_certs A in
{|
  po_bd_eqv               := eqv 
; po_bd_lte               := brel_lte_left eq bop 
; po_bd_exists_top        := match sg_BCI_exists_id A with
                             | Assert_Exists_Id id => Assert_Exists_Top id
                             end
; po_bd_exists_bottom     := match sg_BCI_exists_ann A with
                             | Assert_Exists_Ann ann => Assert_Exists_Bottom ann 
                             end
; po_bd_certs             := po_certs_from_sg_CI_left_certs sgP 
; po_bd_ast               := Ast_or_llte (sg_BCI_ast A) 
|}.
  

End Combinators.

End CAS.


Section MCAS.

Local Open Scope string_scope.   


Definition mcas_left_order_from_sg {S : Type} (A : @sg_mcas S) : @or_mcas S :=
match A with
  | MCAS_sg_Error sl           => OR_Error sl 
  | MCAS_sg _                  => OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | MCAS_sg_C B                => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_C_with_id B        => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_C_with_ann B       => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_BC B               => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_NC B               => OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | MCAS_sg_NC_with_id B       => OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | MCAS_sg_NC_with_ann B      => OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | MCAS_sg_BNC B              => OR_Error ("left_order_from_sg: semirgroup must be commutative and idempotent" :: nil)
  | MCAS_sg_CS B               => OR_to (to_from_sg_CS_left B)
  | MCAS_sg_CS_with_id B       => OR_to_with_top (to_with_top_from_sg_CS_with_id_left B)
  | MCAS_sg_CS_with_ann B      => OR_to_with_bottom (to_with_bottom_from_sg_CS_with_ann_left B)
  | MCAS_sg_BCS B              => OR_to_bounded (to_bounded_from_sg_CS_bounded_left B)
  | MCAS_sg_CI B               => OR_po (po_from_sg_CI_left B)
  | MCAS_sg_CI_with_id B       => OR_po_with_top (po_with_top_from_sg_CI_with_id_left B)
  | MCAS_sg_CI_with_ann B      => OR_po_with_bottom (po_with_bottom_from_sg_CI_with_ann_left B)
  | MCAS_sg_BCI B              => OR_po_bounded (po_bounded_from_sg_CI_bounded_left B)
  | MCAS_sg_CNI B              => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_CNI_with_id B      => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_CNI_with_ann B     => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_BCNI B             => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_CK B               => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
  | MCAS_sg_CK_with_id B       => OR_Error ("left_order_from_sg: semirgroup must be idempotent" :: nil)
end.     

End MCAS.



Section Verify.

Section Proofs.

Variables   
      (S : Type)
      (eq : brel S)
      (eqvP : eqv_proofs S eq)
      (bop : binary_op S). 

Lemma correct_to_certs_from_sg_CS_left_certs
      (P : sg_CS_proofs S eq bop) :
      P2C_to eq (brel_lte_left eq bop) (to_proofs_from_sg_CS_left_proofs S eq eqvP bop P)
      = 
      to_certs_from_sg_CS_left_certs (P2C_sg_CS S eq bop P).
Proof. destruct P; unfold to_proofs_from_sg_CS_left_proofs, to_certs_from_sg_CS_left_certs,
                   P2C_to, P2C_sg_CS; simpl.
       reflexivity. 
Qed. 

Lemma correct_to_certs_from_sg_CS_right_certs
      (P : sg_CS_proofs S eq bop) :
      P2C_to eq (brel_lte_right eq bop) (to_proofs_from_sg_CS_right_proofs S eq eqvP bop P)
      = 
      to_certs_from_sg_CS_right_certs (P2C_sg_CS S eq bop P).
Proof. destruct P; unfold to_proofs_from_sg_CS_right_proofs, to_certs_from_sg_CS_right_certs,
                   P2C_to, P2C_sg_CS; simpl.
       reflexivity. 
Qed. 

Lemma correct_po_certs_from_sg_CI_left_certs
      (P : sg_CI_proofs S eq bop) : 
      P2C_po eq (brel_lte_left eq bop) (po_proofs_from_sg_CI_left_proofs S eq eqvP bop P)
      = 
      po_certs_from_sg_CI_left_certs (P2C_sg_CI S eq bop P). 
Proof. destruct P; unfold po_proofs_from_sg_CI_left_proofs, po_certs_from_sg_CI_left_certs,
                   P2C_po, P2C_sg_CI; simpl.
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]; simpl.
       unfold p2c_not_total_assert. simpl. 
       reflexivity. 
Qed. 

Lemma correct_po_certs_from_sg_CI_right_certs
      (P : sg_CI_proofs S eq bop) : 
      P2C_po eq (brel_lte_right eq bop) (po_proofs_from_sg_CI_right_proofs S eq eqvP bop P)
      = 
      po_certs_from_sg_CI_right_certs (P2C_sg_CI S eq bop P). 
Proof. destruct P; unfold po_proofs_from_sg_CI_right_proofs, po_certs_from_sg_CI_right_certs,
                   P2C_po, P2C_sg_CI; simpl.
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]; simpl.
       unfold p2c_not_total_assert. simpl. 
       reflexivity. 
Qed. 


  
End Proofs.

Section Combinators.

Theorem correct_to_from_sg_CS_left (S : Type) (a : A_sg_CS S) : 
  to_from_sg_CS_left (A2C_sg_CS S a)
  =
  A2C_to (A_to_from_sg_CS_left a). 
Proof. destruct a; unfold to_from_sg_CS_left, A_to_from_sg_CS_left, A2C_to, A2C_sg_CS; simpl. 
       unfold p2c_not_exists_top_assert, p2c_not_exists_bottom_assert.
       rewrite correct_to_certs_from_sg_CS_left_certs. 
       reflexivity. 
Qed. 

Theorem correct_to_with_top_from_sg_CS_with_id_left (S : Type) (a : A_sg_CS_with_id S) : 
  to_with_top_from_sg_CS_with_id_left (A2C_sg_CS_with_id S a)
  =
  A2C_to_with_top (A_to_with_top_from_sg_CS_with_id_left a). 
Proof. destruct a; unfold to_with_top_from_sg_CS_with_id_left,
                   A_to_with_top_from_sg_CS_with_id_left, A2C_to_with_top,
                   A2C_sg_CS_with_id; simpl.
       rewrite correct_to_certs_from_sg_CS_left_certs.        
       unfold p2c_not_exists_bottom_assert.
       destruct A_sg_CS_wi_exists_id as [id P]; simpl.
       unfold p2c_exists_top_assert; simpl. 
       reflexivity. 
Qed. 

  
Theorem correct_to_with_bottom_from_sg_CS_with_ann_left (S : Type) (a : A_sg_CS_with_ann S) : 
  to_with_bottom_from_sg_CS_with_ann_left (A2C_sg_CS_with_ann S a)
  =
  A2C_to_with_bottom (A_to_with_bottom_from_sg_CS_with_ann_left a).
Proof. destruct a; unfold to_with_bottom_from_sg_CS_with_ann_left,
                   A_to_with_bottom_from_sg_CS_with_ann_left, A2C_to_with_bottom,
                   A2C_sg_CS_with_ann; simpl.
       rewrite correct_to_certs_from_sg_CS_left_certs.        
       unfold p2c_not_exists_top_assert.
       destruct A_sg_CS_wa_exists_ann as [ann P]; simpl.
       unfold p2c_exists_bottom_assert; simpl. 
       reflexivity. 
Qed. 

Theorem correct_to_bounded_from_sg_CS_bounded_left (S : Type) (a : A_sg_BCS S) : 
  to_bounded_from_sg_CS_bounded_left (A2C_sg_BCS S a)
  =
  A2C_to_bounded (A_to_bounded_from_sg_CS_bounded_left a).
Proof. destruct a; unfold to_bounded_from_sg_CS_bounded_left,
                   A_to_bounded_from_sg_CS_bounded_left, A2C_to_bounded,
                   A2C_sg_BCS; simpl.
       rewrite correct_to_certs_from_sg_CS_left_certs.        
       destruct A_sg_BCS_exists_ann as [ann P]; simpl.
       unfold p2c_exists_bottom_assert; simpl.
       destruct A_sg_BCS_exists_id as [id Q]; simpl.
       unfold p2c_exists_top_assert; simpl.
       reflexivity. 
Qed. 


Theorem correct_po_from_sg_CI_left (S : Type) (a : A_sg_CI S) : 
  po_from_sg_CI_left (A2C_sg_CI S a)
  =
  A2C_po (A_po_from_sg_CI_left a). 
Proof. destruct a; unfold po_from_sg_CI_left, A_po_from_sg_CI_left, A2C_po, A2C_sg_CI; simpl. 
       unfold p2c_not_exists_top_assert, p2c_not_exists_bottom_assert.
       rewrite correct_po_certs_from_sg_CI_left_certs. 
       reflexivity. 
Qed. 


Theorem correct_po_with_top_from_sg_CI_with_id_left (S : Type) (a : A_sg_CI_with_id S) : 
  po_with_top_from_sg_CI_with_id_left (A2C_sg_CI_with_id S a)
  =
  A2C_po_with_top (A_po_with_top_from_sg_CI_with_id_left a). 
Proof. destruct a; unfold po_with_top_from_sg_CI_with_id_left,
                   A_po_with_top_from_sg_CI_with_id_left, A2C_po_with_top,
                   A2C_sg_CI_with_id; simpl.
       rewrite correct_po_certs_from_sg_CI_left_certs.        
       unfold p2c_not_exists_bottom_assert.
       destruct A_sg_CI_wi_exists_id as [id P]; simpl.
       unfold p2c_exists_top_assert; simpl. 
       reflexivity. 
Qed. 

Theorem correct_po_with_bottom_from_sg_CI_with_ann_left (S : Type) (a : A_sg_CI_with_ann S) : 
  po_with_bottom_from_sg_CI_with_ann_left (A2C_sg_CI_with_ann S a)
  =
  A2C_po_with_bottom (A_po_with_bottom_from_sg_CI_with_ann_left a). 
Proof. destruct a; unfold po_with_bottom_from_sg_CI_with_ann_left,
                   A_po_with_bottom_from_sg_CI_with_ann_left, A2C_po_with_bottom,
                   A2C_sg_CI_with_ann; simpl.
       rewrite correct_po_certs_from_sg_CI_left_certs.        
       unfold p2c_not_exists_top_assert.
       destruct A_sg_CI_wa_exists_ann as [ann P]; simpl.
       unfold p2c_exists_bottom_assert; simpl. 
       reflexivity. 
Qed. 


Theorem correct_po_bounded_from_sg_CI_bounded_left (S : Type) (a : A_sg_BCI S) : 
  po_bounded_from_sg_CI_bounded_left (A2C_sg_BCI S a)
  =
  A2C_po_bounded (A_po_bounded_from_sg_CI_bounded_left a). 
Proof. destruct a; unfold po_bounded_from_sg_CI_bounded_left,
                   A_po_bounded_from_sg_CI_bounded_left, A2C_po_bounded,
                   A2C_sg_BCI; simpl.
       rewrite correct_po_certs_from_sg_CI_left_certs.        
       destruct A_sg_BCI_exists_ann as [ann P]; simpl.
       unfold p2c_exists_bottom_assert; simpl.
       destruct A_sg_BCI_exists_id as [id Q]; simpl.
       unfold p2c_exists_top_assert; simpl.
       reflexivity. 
Qed. 


  
Theorem correct_mcas_left_order_from_sg (S : Type) (sgS : A_sg_mcas S) : 
         mcas_left_order_from_sg (A2C_mcas_sg S sgS) 
         = 
         A2C_mcas_or (A_mcas_left_order_from_sg S sgS).
Proof. destruct sgS; unfold mcas_left_order_from_sg, A_mcas_left_order_from_sg,
       A2C_mcas_sg, A2C_mcas_or; simpl; try reflexivity.
       + rewrite correct_to_with_top_from_sg_CS_with_id_left; reflexivity. 
       + rewrite correct_to_with_bottom_from_sg_CS_with_ann_left; reflexivity. 
       + rewrite correct_to_bounded_from_sg_CS_bounded_left; reflexivity. 
       + rewrite correct_po_from_sg_CI_left; reflexivity. 
       + rewrite correct_po_with_top_from_sg_CI_with_id_left; reflexivity. 
       + rewrite correct_po_with_bottom_from_sg_CI_with_ann_left; reflexivity. 
       + rewrite correct_po_bounded_from_sg_CI_bounded_left; reflexivity. 
Qed. 


End Combinators.

  
End Verify. 
