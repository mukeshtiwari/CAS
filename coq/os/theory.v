Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.properties.

Require Import CAS.coq.os.properties.


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


End IntroElim.   

Section Lte_from_bop. 

Variable S  : Type. 

Variable eq : brel S.
Variable eqCong : brel_congruence S eq eq.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable trnS : brel_transitive S eq.
Definition symS_dual := brel_symmetric_implies_dual S eq symS. 

Variable bS     : binary_op S.
Variable congS : bop_congruence S eq bS.
Variable assoS : bop_associative S eq bS.
Variable idemS : bop_idempotent S eq bS.
Variable commS : bop_commutative S eq bS.

Variable wS : S.
Variable f : S -> S.
Variable Pf   : brel_not_trivial S eq f.

Notation "a == b"    := (eq a b = true) (at level 30).
Notation "a != b"    := (eq a b = false) (at level 30).
Notation "a (+) b"   := (bS a b) (at level 15).
  

(*********************** PO properties ************************************) 


Lemma brel_lte_left_congruence : brel_congruence S eq (brel_lte_left eq bS).
Proof. compute. intros s t u v H1 H2. apply eqCong; auto. Qed.

Lemma brel_lt_left_congruence : brel_congruence S eq (brel_lt_left eq bS).
Proof. compute. intros s t u v H1 H2.
       assert (A := congS _ _ _ _ H1 H2).
       assert (B := congS _ _ _ _ H2 H1).        
       rewrite (eqCong _ _ _ _ H1 A).
       rewrite (eqCong _ _ _ _ H2 B).
       reflexivity. 
Qed.


Lemma brel_lte_left_reflexive : brel_reflexive S  (brel_lte_left eq bS).
Proof. compute. intro s. auto. Qed.

Lemma brel_lt_left_irreflexive : brel_irreflexive S (brel_lt_left eq bS).
Proof. intros s. assert (I := idemS s). apply symS in I. compute. rewrite ! I. reflexivity. Qed. 


(*
Print brel_lte_left_reflexive.

brel_lte_left_reflexive =  λ s : S, symS (b s s) s (idemS s)

*) 

Lemma brel_lte_left_transitive : brel_transitive S  (brel_lte_left eq bS).
Proof. compute. intros s t u H1 H2.
       assert (A : eq (bS s t) (bS s (bS t u)) = true).
          apply congS; auto. 
       assert (B : eq (bS s (bS t u)) (bS (bS s t) u) = true).
          apply symS. apply assoS; auto.    
       assert (C : eq (bS (bS s t) u) (bS s u) = true).
          apply congS; auto.           
       assert (D := trnS _ _ _ H1 A).
       assert (E := trnS _ _ _ D B).
       assert (F := trnS _ _ _ E C).
       exact F.
Qed.

(* 
Print brel_lte_left_transitive. 

brel_lte_left_transitive = 
    λ (s t u : S) (H1 : eq s (b s t) = true) (H2 : eq t (b t u) = true), 
      let A : eq (b s t) (b s (b t u)) = true       := congS s t s (b t u) (refS s) H2 in
      let B : eq (b s (b t u)) (b (b s t) u) = true := symS (b (b s t) u) (b s (b t u)) (assoS s t u) in
      let C : eq (b (b s t) u) (b s u) = true       := congS (b s t) u s u (symS s (b s t) H1) (refS u) in
      let D : eq s (b s (b t u)) = true             := trnS s (b s t) (b s (b t u)) H1 A in
      let E : eq s (b (b s t) u) = true             := trnS s (b s (b t u)) (b (b s t) u) D B in
      let F : eq s (b s u) = true                   := trnS s (b (b s t) u) (b s u) E C in 
      F
: brel_transitive S (brel_lte_left eq b)
*) 

Lemma brel_lte_left_antisymmetric : brel_antisymmetric S eq (brel_lte_left eq bS).
Proof. compute. intros s t H1 H2.
       assert (A := commS s t). 
       apply symS in H2. 
       assert (B := trnS _ _ _ H1 A).
       assert (C := trnS _ _ _ B H2).
       exact C. 
Qed.

Lemma brel_lt_left_asymmetric : brel_asymmetric S (brel_lt_left eq bS).
Proof. intros s1 s2 H.        
       apply brel_lt_left_elim in H. destruct H as [H _].
       apply brel_lt_left_false_intro. 
       right. exact H.
 Qed. 


(*
Print brel_lte_left_antisymmetric.

brel_lte_left_antisymmetric = 
   λ (s t : S) (H1 : eq s (b s t) = true) (H2 : eq t (b t s) = true),
     let A : eq (b s t) (b t s) = true := commS s t in
     let H3 : eq (b t s) t = true      := symS t (b t s) H2 in
     let B : eq s (b t s) = true       := trnS s (b s t) (b t s) H1 A in
     let C : eq s t = true             := trnS s (b t s) t B H3 in C
*) 

Lemma brel_lte_left_total (selS : bop_selective S eq bS) : brel_total S (brel_lte_left eq bS).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       left. apply symS; auto.        
       right.
       assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A). 
Qed.

(*
Print brel_lte_left_total.

brel_lte_left_total = 
   λ (selS : bop_selective S eq b) (s t : S), 
     let s0 := selS s t in
       match s0 with
       | inl H => inl (symS (b s t) s H)
       | inr H => inr (let A : eq (b s t) (b t s) = true := commS s t in
                       let H0 : eq t (b s t) = true      := symS (b s t) t H 
                       in 
                          trnS t (b s t) (b t s) H0 A
                      )
       end
*)

Lemma brel_lte_left_not_total (nselS : bop_not_selective S eq bS) : brel_not_total S (brel_lte_left eq bS).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute.
       apply symS_dual in A. rewrite A.
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C B). 
       apply symS_dual in D. rewrite D. 
       auto.        
Defined.

(*
Print brel_lte_left_not_total.


brel_lte_left_not_total = 
   λ nselS : bop_not_selective S eq b, 
     let (x, x0) := nselS in
     ( 
       let (s, t) as p
       return ((let (s, t) := p in (eq (b s t) s = false) * (eq (b s t) t = false)) → brel_not_total S (brel_lte_left eq b)) 
           := x 
       in λ y : (eq (b s t) s = false) * (eq (b s t) t = false), 
                let (A, B) := y 
                in  existT
                           (λ z : S * S, let (s0, t0) := z in
                              (brel_lte_left eq b s0 t0 = false) *
                              (brel_lte_left eq b t0 s0 = false))
                           (s, t)
                           (let A0 : eq s (b s t) = false := symS_dual (b s t) s A 
                            in
                               eq_ind_r
                                    (λ b0 : bool, (b0 = false) * (eq t (b t s) = false))
                                    (let C : eq (b s t) (b t s) = true := commS s t 
                                     in 
                                        let D : eq (b t s) t = false :=
                                                brel_transititivity_implies_dual S eq trnS (b s t) (b t s) t C B 
                                        in
                                           let D0 : eq t (b t s) = false := symS_dual (b t s) t D 
                                           in
                                              eq_ind_r (λ b : bool, (false = false) * (b = false))
                                                       (eq_refl, eq_refl) D0) A0)
    ) x0

*) 


Lemma brel_lte_left_is_top (s : S) (idS : bop_is_id S eq bS s) : brel_is_top S (brel_lte_left eq bS) s. 
Proof. compute. intro t.
       destruct (idS t) as [_ B].
       apply symS. exact B. 
Defined. 

Lemma brel_lte_left_exists_top (idS : bop_exists_id S eq bS) : brel_exists_qo_top S eq (brel_lte_left eq bS).
Proof. destruct idS as [s A]. exists s. split. 
       apply brel_lte_left_is_top; auto.
       intros a. compute. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined. 

Lemma brel_lte_left_not_exists_top (nidS : bop_not_exists_id S eq bS) : brel_not_exists_qo_top S eq (brel_lte_left eq bS).
Proof. compute. intros a. left. 
       destruct (nidS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined.


Lemma brel_lte_left_is_bottom (s : S) (annS : bop_is_ann S eq bS s) : brel_is_qo_bottom S eq (brel_lte_left eq bS) s.
Proof. compute. split.
       intro t. destruct (annS t) as [B _]. apply symS. exact B. 
       intros a. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined. 

Lemma brel_lte_left_exists_bottom (annS : bop_exists_ann S eq bS) : brel_exists_qo_bottom S eq (brel_lte_left eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_left_is_bottom; auto. Defined. 

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

(*
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
Lemma brel_lte_left_not_exists_bottom (nannS : bop_not_exists_ann S eq b) : brel_not_exists_bottom S (brel_lte_left eq b).
Proof. compute. intros a.
       destruct (nannS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. exact A. 
          apply symS_dual. assert (B := commS c a). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
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


(*  NOTE: we will insist that there is an ann so that from_sg_left has a bottom. 
 *)




(* *)
Lemma brel_lt_left_total_order_split : bop_selective S eq bS → 
      ∀  (x y : S), 
      ((eq x y = true)  *  (brel_lt_left eq bS x y = false)) 
    + ((eq x y = false) *  (brel_lt_left eq bS x y = true)) 
    + ((eq x y = false) *  (brel_lt_left eq bS x y = false)).  
Proof. intros selS x y. 
       case_eq(eq x  y); intro H. 
          left. left. split. 
             reflexivity. 
             unfold brel_lt_left. assert (Ix := idemS x). assert (Iy := idemS y). 
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

(*********************** OS properties ************************************) 

Lemma bop_is_glb_wrt_lte_left : bop_is_glb (brel_lte_left eq bS) bS.
Proof. intros a b. split; compute. split.
       assert (F0 := idemS a). apply symS in F0.
       assert (F1 := commS a b). 
       assert (F2 := congS _ _ _ _ F0 (refS b)).
       assert (F3 := assoS a a b).        
       assert (F4 := congS _ _ _ _ (refS a) F1).
       assert (F5 := assoS a b a).  apply symS in F5.
       assert (R := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F2 F3) F4) F5).
       exact R.

       assert (F0 := idemS b). apply symS in F0. 
       assert (F1 := congS _ _ _ _ (refS a) F0).              
       assert (F2 := assoS a b b).  apply symS in F2.
       assert (R := trnS _ _ _ F1 F2).
       exact R.

       intros c [L R].
       assert (F0 := idemS c). apply symS in F0.
       assert (F1 := congS _ _ _ _ L R).
       assert (F2 := assoS c a (c (+) b)).
       assert (F3 := commS a (c (+) b)).
       assert (F4 := congS _ _ _ _ (refS c) F3).
       assert (F5 := assoS c (c (+) b) a).  apply symS in F5.
       assert (F6 := assoS c c b).  apply symS in F6.
       assert (F7 := congS _ _ _ _ F6 (refS a)).
       assert (F8 := assoS (c (+) c) b a).  
       assert (F9 := commS b a).       apply symS in F0.
       assert (F10 := congS _ _ _ _ F0 F9). apply symS in F0.
       assert (C := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F0 F1) F2) F4) F5) F7) F8) F10).       
       exact C.
Qed. 

Lemma bop_is_lub_wrt_lte_right : bop_is_lub (brel_lte_right eq bS) bS.
Proof. intros a b. split; compute. split.
       assert (F0 := idemS a). apply symS in F0. 
       assert (F1 := congS _ _ _ _ F0 (refS b)).              
       assert (F2 := assoS a a b).  
       assert (R := trnS _ _ _ F1 F2).
       exact R.
       
       assert (F0 := idemS b). apply symS in F0.
       assert (F1 := commS a b). 
       assert (F2 := congS _ _ _ _ (refS a) F0).
       assert (F3 := assoS a b b).  apply symS in F3.      
       assert (F4 := congS _ _ _ _ F1 (refS b)).
       assert (F5 := assoS b a b).  
       assert (R := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F2 F3) F4) F5).        
       exact R. 

       intros c [L R].
       assert (F0 := idemS c). apply symS in F0.
       assert (F1 := congS _ _ _ _ L R).
       assert (F2 := assoS a c (b (+) c)).
       assert (F3 := commS c (b (+) c)).
       assert (F4 := congS _ _ _ _ (refS a) F3).
       assert (F6 := assoS b c c).  
       assert (F7 := congS _ _ _ _ (refS a) F6).
       assert (F8 := assoS a b (c (+) c)).  apply symS in F8. apply symS in F0. 
       assert (F10 := congS _ _ _ _ (refS (a (+) b)) F0). apply symS in F0.
       assert (C := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F0 F1) F2) F4) F7) F8) F10).       
       exact C.
Qed.


(* monotonicity *) 

Lemma os_lte_left_left_monotone : os_left_monotone (brel_lte_left eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := idemS s). apply symS in F0. 
       assert (F1 := congS _ _ _ _ F0 H).  
       assert (F2 : (s (+) s) (+) (t (+) u) == (s (+) t) (+) (s (+) u)).
          (* (s (+) s) (+) (t (+) u)
             assoc = s (+) (s (+) (t (+) u)) 
             assoc = s (+) ((s (+) t) (+) u) 
             comm  = s (+) ((t (+) s) (+) u) 
             assoc = s (+) (t (+) (s (+) u)) 
             assoc = (s (+) t) (+) (s (+) u)
          *) 
          assert (F4 := assoS s s (t (+) u)).           
          assert (F5 := assoS s t u). apply symS in F5.
          assert (F6 := congS _ _ _ _ (refS s) F5).          
          assert (F7 := trnS _ _ _ F4 F6). apply symS in F5.
          assert (F8 := commS s t). 
          assert (F9 := congS _ _ _ _ (refS s) (congS _ _ _ _ F8 (refS u))). 
          assert (F10 := trnS _ _ _ F7 F9).
          assert (F11 := assoS t s u).
          assert (F12 := congS _ _ _ _ (refS s) F11). 
          assert (F13 := trnS _ _ _ F10 F12).          
          assert (F14 := assoS s t (s (+) u)). apply symS in F14. 
          exact (trnS _ _ _ F13 F14).
       exact (trnS _ _ _ F1 F2). 
Qed. 

(*
Lemma os_lte_left_left_strictly_monotone (s t u : S) : os_not_left_strictly_monotone (brel_lte_left eq bS) bS.
Proof. compute. exists (s, (t, u)).
       assert (F0 : t == t (+) u). admit.
       assert (F1 : u != u (+) t). admit. 
       split. split. 
       exact F0. 
       exact F1. 
       case_eq(eq (s (+) t) ((s (+) t) (+) (s (+) u))); intro H1. 
       - right.
         case_eq(eq (s (+) u) ((s (+) u) (+) (s (+) t))); intro H2.
         + reflexivity. 
         + 
       - left. reflexivity. 
*)

Lemma os_lte_right_left_monotone : os_left_monotone (brel_lte_right eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := os_lte_left_left_monotone s u t). compute in F0.
       assert (F1 := commS (s (+) u) (s (+) t)).
       assert (F2 := commS t u).
       assert (F3 := trnS _ _ _ H F2). 
       exact (trnS _ _ _ (F0 F3) F1). 
Qed.

Lemma os_lte_left_right_monotone : os_right_monotone (brel_lte_left eq bS) bS.
Proof. intros s t u. compute. intro H. 
       assert (F0 := os_lte_left_left_monotone s t u). compute in F0.
       assert (F1 := F0 H). 
       assert (F2 := commS t s).
       assert (F3 := commS u s).        
       assert (F4 := trnS _ _ _ F2 F1).
       assert (F5 := congS _ _ _ _ F2 F3). apply symS in F5.
       exact (trnS _ _ _ F4 F5). 
Qed. 

Lemma os_lte_right_right_monotone : os_right_monotone (brel_lte_right eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := os_lte_left_right_monotone s u t). compute in F0.
       assert (F1 := commS (u (+) s) (t (+) s)).
       assert (F2 := commS t u).
       assert (F3 := trnS _ _ _ H F2). 
       exact (trnS _ _ _ (F0 F3) F1). 
Qed.

(* bottoms *)

(* Note: New properties needed! *)

Definition os_bottom_equals_ann {S : Type} (r lte : brel S) (b : binary_op S)
:= { i : S & (brel_is_bottom S lte i) * (bop_is_ann S r b i)}.

Definition os_top_equals_id {S : Type} (r lte : brel S) (b : binary_op S)
  := { i : S & (brel_is_top S lte i) * (bop_is_id S r b i)}. 


Lemma os_lte_left_bottom_equals_ann (annS : bop_exists_ann S eq bS) : os_bottom_equals_ann eq (brel_lte_left eq bS) bS.
Proof. destruct annS as [ann P]. exists ann. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact A. 
Defined. 

Lemma os_lte_left_top_equals_id (idS : bop_exists_id S eq bS) : os_top_equals_id eq (brel_lte_left eq bS) bS.
Proof. destruct idS as [id P]. exists id. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact B. 
Defined. 

Lemma os_lte_right_bottom_equals_id (idS : bop_exists_id S eq bS) : os_bottom_equals_id eq (brel_lte_right eq bS) bS.
Proof. destruct idS as [id P]. exists id. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact A. 
Defined. 

Lemma os_lte_right_top_equals_ann (annS : bop_exists_ann S eq bS) : os_top_equals_ann eq (brel_lte_right eq bS) bS.
Proof. destruct annS as [ann P]. exists ann. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact B. 
Defined. 



(* increasing 

Lemma os_lte_left_not_left_strictly_increasing : os_not_left_strictly_increasing (brel_lte_left eq bS) bS.
Proof. compute. exists (wS, wS). right. Admitted. 

*) 


(* Decide *)

Definition brel_lte_left_total_decide (D : bop_selective_decidable S eq bS) : 
  brel_total_decidable S (brel_lte_left eq bS)
  := match D with
     | inl sel  => inl (brel_lte_left_total sel)
     | inr nsel => inr (brel_lte_left_not_total nsel)
     end.

Definition brel_lte_left_not_exists_top_decide (D : bop_exists_id_decidable S eq bS) : brel_exists_qo_top_decidable S eq (brel_lte_left eq bS) :=
  match D with
  | inl idS  => inl (brel_lte_left_exists_top idS)
  | inr nidS => inr (brel_lte_left_not_exists_top nidS)
  end. 


End Lte_from_bop.

(* Now, do other direction? *) 
