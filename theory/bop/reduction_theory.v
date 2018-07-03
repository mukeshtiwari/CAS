Require Export Coq.Unicode.Utf8.
(* Require Import Coq.Bool.Bool.   *) 
Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.uop_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.facts.
Require Import CAS.theory.brel.reduce. 


(*
      r(r(s) + r(t)) +  r(u)  =_r  r(s) + r(r(t) + r(u)) 
*) 
Definition bop_pseudo_associative (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) 
  := ∀ s t u : S, eq (r (b (r (b (r s) (r t))) (r u))) (r (b (r s) (r (b (r t) (r u))))) = true.

Definition bop_left_uop_invariant (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ s1 s2 : S, eq (b (r s1) s2) (b s1 s2)  = true.

Definition bop_right_uop_invariant (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ s1 s2 : S, eq (b s1 (r s2)) (b s1 s2)  = true.

Lemma brel_transitive_f1 (S : Type) (eq : brel S) (sym : brel_symmetric S eq) (trans : brel_transitive S eq) : 
  ∀ s t u: S, (eq s t = false) → (eq t u = true) → (eq s u = false).
Proof. intros s t u H1 H2.
       case_eq (eq s t); intro J1; case_eq (eq s u); intro J2.
       rewrite J1 in H1. exact H1. 
       reflexivity. 
       apply sym in J2. 
       assert (J3 := trans _ _ _ H2 J2). 
       apply sym in J3.
       rewrite J3 in H1. exact H1. 
       reflexivity. 
Qed.        

Lemma brel_transitive_f2 (S : Type) (eq : brel S) (sym : brel_symmetric S eq) (trans : brel_transitive S eq)  : 
  ∀ s t u: S, (eq s t = true) → (eq t u = false) → (eq s u = false).
Proof. intros s t u H1 H2.
       case_eq (eq t u); intro J1; case_eq (eq s u); intro J2.
       rewrite J1 in H2. exact H2. 
       reflexivity. 
       apply sym in J2. 
       assert (J3 := trans _ _ _ J2 H1). 
       apply sym in J3.
       rewrite J3 in H2. exact H2.
       reflexivity. 
Qed.



Section ReductionTheory.

Lemma observation1 (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  (bop_left_uop_invariant S (brel_reduce eq r) b r)
  <->       
  (bop_left_uop_invariant S eq (bop_reduce r b) r).
Proof. compute. split; auto.   Qed. 

Lemma observation2 (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S) :
  (bop_right_uop_invariant S eq (bop_reduce r b) r)
  <-> 
  (bop_right_uop_invariant S (brel_reduce eq r) b r).
Proof. split; auto.   Qed. 

  

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r : unary_op S.
  Variable eqS    : brel S.    

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable transS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.

  
  Definition transSf1 := brel_transitive_f1 S eqS symS transS. 
  Definition transSf2 := brel_transitive_f2 S eqS symS transS. 

  Variable b_cong : bop_congruence S eqS b. 
  Variable b_ass  : bop_associative S eqS b.

  (* make assumptions about r required to build the reduced semigroup *) 
  Variable r_cong  : uop_congruence S eqS r. 
  Variable r_idem  : uop_idempotent S eqS r.
(*  
*) 
  Definition Pr (x : S) := eqS (r x) x = true.  
  Definition red_Type   := { x : S & Pr x}.

  (* equality on red_Type is just equality on S, but need to project out first components! *) 
  Definition red_eq : brel red_Type := λ p1 p2, eqS ((projT1 p1)) ((projT1 p2)).

  Lemma red_ref : brel_reflexive red_Type red_eq. 
  Proof. intros [s p]. compute. apply refS. Qed.

       
  Lemma red_sym : brel_symmetric red_Type red_eq. 
  Proof. intros [s1 p1] [s2 p2].   compute. apply symS. Qed.

  Lemma red_cong : brel_congruence red_Type red_eq red_eq. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4].   compute. apply eqS_cong. Qed. 


  Lemma red_trans : brel_transitive red_Type red_eq. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute. apply transS. Qed.

  Lemma Pr_br : ∀ (p1 p2 : red_Type), Pr (bop_reduce r b (projT1 p1) (projT1 p2)).
  Proof. intros [s1 p1] [s2 p2]. compute. apply r_idem. Defined. 

  Definition red_bop : binary_op red_Type :=
    λ p1 p2,  existT Pr (bop_reduce r b (projT1 p1) (projT1 p2)) (Pr_br p1 p2).

  Lemma red_bop_cong : bop_congruence red_Type red_eq red_bop.
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute.
         unfold Pr in *.  intros H1 H2.
         apply r_cong.
         apply b_cong; auto.
  Qed.

  Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r.  (* eqS (r (b (r s1) s2)) (r (b s1 s2))  = true. *) 
  Variable r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r. (* eqS (r (b s1 (r s2))) (r (b s1 s2))  = true. *)
  
   Lemma r_left_and_right : ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true. 
    Proof. intros s1 s2. 
           assert (H1 := r_left s1 s2). compute in H1. 
           assert (H2 := r_right (r s1) s2). compute in H2.            
           assert (H3 := transS _ _ _ H2 H1). apply symS. 
           exact H3.            
    Qed. 


  Lemma red_bop_ass : bop_associative red_Type red_eq red_bop. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := r_left (b s1 s2) s3).
         assert (H2 := r_right s1 (b s2 s3)).
         assert (H3 := r_cong _ _ (b_ass s1 s2 s3)).
         apply symS in H2. 
         assert (H4 := transS _ _ _ H3 H2).
         assert (H5 := transS _ _ _ H1 H4).
         exact H5. 
  Qed.

    
  Definition inj (s : S) : red_Type := existT Pr (r s) (r_idem s).

  (*
   f is a homomorphism for b and b' if 
    f(b(x, y)) = b'(f(x), f(y))

   The following show that 
    1) inj is a homomorphism for (bop_full_reduce r b) and red_bop. 
    2) projT1 is a homomorphism for red_bop and (bop_full_reduce r b). 
    3) (inj o projT1) is id on red_Type
    4) (projT1 o inj) is id on r(S), the image of r 

    so we have an isomorphism between (S, (bop_full_reduce r b) and (red_Type, bop_red) 

    HOWEVER, the isomorphism only works on the image of r, r(S). 

*)
  
  Lemma inj_homomorphism : ∀ (s1 s2 : S),  red_eq (inj (bop_full_reduce r b s1 s2)) (red_bop (inj s1) (inj s2)) = true. 
  Proof. intros s1 s2. compute. apply r_idem. Qed.
  
  Lemma proj1_homomorphism : ∀ (p1 p2 : red_Type),  eqS (projT1 (red_bop p1 p2)) (bop_full_reduce r b (projT1 p1) (projT1 p2)) = true. 
  Proof. intros [s1 P1] [s2 P2]. compute. compute in P1. compute in P2.
         apply r_cong.
         assert (K := b_cong _ _ _ _ P1 P2).  apply symS.
         exact K. 
  Qed. 

  Lemma inj_proj1_is_id : ∀ p : red_Type,  red_eq p (inj (projT1 p)) = true.
  Proof. intros [s P]. compute. compute in P. apply symS. exact P. Qed. 
  
  Lemma proj1_inj_is_id_on_image_of_r : ∀ s : S,  eqS (r s) (projT1 (inj (r s))) = true.
  Proof. intro s. compute. apply symS. apply r_idem. Qed.

  Lemma equality_lemma_1 : ∀ (p1 p2 : red_Type),  eqS (projT1 p1) (projT1 p2) = red_eq p1 p2.
  Proof. intros [s1 P1] [s2 P2]. compute. reflexivity. Qed.

  Lemma equality_lemma_2 : ∀ (s1 s2 : S),  eqS (r s1) (r s2) = red_eq (inj s1) (inj s2).
  Proof. intros s1 s2. compute. reflexivity. Qed. 


  (*****************************************************************************************
      Now show that 
      (red_Type, red_eq, red_bop) is "isomorphic" to 

      (S, brel_reduce r eqS, bop_full_reduce r b)
  *******************************************************************************************) 
  

  (*
     Equality 
  *) 

Lemma red_ref_iso : brel_reflexive red_Type red_eq <-> brel_reflexive S (brel_reduce eqS r).
  Proof. split. intros H s. compute.
         assert (K := H (inj s)).
         unfold red_eq in K. simpl in K.
         exact K. 
         intros H [s p]. unfold Pr in p.
         compute.
         assert (J1 := symS _ _ p).
         assert (J2 := transS _ _ _ J1 p).
         exact J2.
Qed.          

Lemma red_sym_iso : brel_symmetric red_Type red_eq <-> brel_symmetric S (brel_reduce eqS r).
  Proof. split. intros H s1 s2. compute.
         assert (K := H (inj s1) (inj s2)).
         unfold red_eq in K. simpl in K.
         exact K. 
         intros H [s1 p1] [s2 p2]. unfold Pr in p1. unfold Pr in p2.
         compute. intro H2. 
         assert (K := symS _ _ H2).
         exact K.
Qed.          

Lemma red_tran_iso : brel_transitive red_Type red_eq <-> brel_transitive S (brel_reduce eqS r).
  Proof. split. intros H s1 s2 s3. compute. intros H1 H2. 
         assert (K := H (inj s1) (inj s2) (inj s3)). compute in K. 
         apply K; auto. 
         intros H [s1 p1] [s2 p2] [s3 p3]. 
         compute. apply transS. 
Qed.          

Lemma red_brel_cong_iso : brel_congruence red_Type red_eq red_eq <-> brel_congruence S (brel_reduce eqS r) (brel_reduce eqS r).
Proof. split. intros H x y m n. compute. intros H1 H2.
       assert (K := H (inj x) (inj y) (inj m) (inj n)). compute in K. 
       apply K; auto.
       intros H [s1 p1] [s2 p2] [s3 p3] [s4 p4].
       compute. apply eqS_cong.
Qed. 

Lemma red_cong_iso : bop_congruence red_Type red_eq red_bop <-> bop_congruence S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. split.
       (* -> *) 
       intros H s1 s2 s3 s4. compute. intros H1 H2. 
       assert (K := H (inj s1) (inj s2) (inj s3) (inj s4)). compute in K.
       apply r_cong.        
       apply K; auto.
       (* <- *) 
       intros H [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute. intros H1 H2. 
       unfold Pr in p1, p2, p3, p4. 
       compute in H.
       assert (J1 := r_cong _ _ H1).
       assert (J2 := r_cong _ _ H2).
       assert (J3 := H _ _ _ _ J1 J2).
       assert (J4 := r_idem (b (r s1) (r s2))).
       assert (J5 := r_idem (b (r s3) (r s4))).
       assert (J6 := transS _ _ _ J3 J5).
       apply symS in J4.
       assert (J7 := transS _ _ _ J4 J6).
       assert (J8 := b_cong _ _ _ _ p1 p2). apply r_cong in J8.
       assert (J9 := b_cong _ _ _ _ p3 p4). apply r_cong in J9.
       assert (J10 := transS _ _ _ J7 J9).
       apply symS in J8.
       assert (J11 := transS _ _ _ J8 J10).
       exact J11.
Qed.


Lemma red_bop_ass_iso : bop_associative red_Type red_eq red_bop <-> bop_pseudo_associative S eqS r b. 
Proof. split; intro H.
         intros s1 s2 s3. 
         assert (H1 := H (inj s1) (inj s2) (inj s3)). compute in H1.
         exact H1. 
         intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := H s1 s2 s3). compute in H1. unfold Pr in p1, p2, p3.
         assert (H2 := b_cong _ _ _ _ p1 p2). apply r_cong in H2. 
         assert (H3 := b_cong _ _ _ _ p2 p3). apply r_cong in H3.
         assert (H4 := b_cong _ _ _ _ H2 p3). apply r_cong in H4. 
         assert (H5 := b_cong _ _ _ _ p1 H3). apply r_cong in H5.
         assert (H6 := transS _ _ _ H1 H5).
         apply symS in H4.
         assert (H7 := transS _ _ _ H4 H6).         
         exact H7.          
Qed.

(* this uses b_ass, r_left, r_right 

   This shows that we have generalised reductions to those that are pseudo-associative! 
*) 
Lemma r_left_right_imply_pseudo_associative : bop_pseudo_associative S eqS r b. 
Proof. intros s1 s2 s3. 
         assert (H1 := b_ass (r s1) (r s2) (r s3)). apply r_cong in H1. 
         assert (H2 := r_left (b (r s1) (r s2)) (r s3)).  compute in H2.
         assert (H3 := r_right (r s1) (b (r s2) (r s3))).  compute in H3.          
         assert (H4 := transS _ _ _ H2 H1). apply symS in H3. 
         assert (H6 := transS _ _ _ H4 H3).         
         exact H6.          
Qed.


Lemma red_comm_iso :  bop_commutative red_Type red_eq red_bop <-> bop_commutative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. split.
         intros H s1 s2. compute.
         assert (K := H (inj s1) (inj s2)). compute in K.
         apply r_cong.
         exact K. 
         intros H1 [s1 p1] [s2 p2]. compute.
         assert (K := H1 s1 s2). compute in K. 
         unfold Pr in p1. unfold Pr in p2.
         assert (J1 := r_idem (b (r s1) (r s2))).
         assert (J2 := r_idem (b (r s2) (r s1))).
         apply symS in J1.
         assert (J3 := transS _ _ _ J1 K).
         assert (J4 := transS _ _ _ J3 J2).
         assert (J5 := b_cong _ _ _ _ p1 p2). apply r_cong in J5. 
         assert (J6 := b_cong _ _ _ _ p2 p1). apply r_cong in J6. 
         assert (J7 := transS _ _ _ J4 J6).         
         apply symS in J5. 
         assert (J8 := transS _ _ _ J5 J7).
         exact J8.
 Qed.

 Lemma red_sel_iso_left :  bop_selective red_Type red_eq red_bop -> bop_selective S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof. intros H s1 s2. compute.
  assert (K := H (inj s1) (inj s2)). compute in K.
  destruct K as [K | K]. left. 
  assert (A := r_idem (b (r s1) (r s2)) ).
  exact (transS _ _ _ A K).
  right. assert (A := r_idem (b (r s1) (r s2)) ).
  exact (transS _ _ _ A K).
 Qed.

 Lemma red_sel_iso_right :  bop_selective S (brel_reduce eqS r) (bop_full_reduce r b) -> bop_selective red_Type red_eq red_bop.
 Proof. intros H1 [s1 p1] [s2 p2]. compute.
  assert (K := H1 s1 s2). compute in K. 
  unfold Pr in p1. unfold Pr in p2.
  destruct K as [K | K]. left. 
  assert (A := r_idem (b (r s1) (r s2)) ). apply symS in A.
  assert (B := transS _ _ _ A K).
  assert (C := b_cong (r s1) (r s2) s1 s2 p1 p2). apply r_cong in C. apply symS in C.
  assert (D := transS _ _ _ C B).
  exact (transS _ _ _ D p1).
  right.
  assert (A := r_idem (b (r s1) (r s2)) ). apply symS in A.
  assert (B := transS _ _ _ A K).
  assert (C := b_cong (r s1) (r s2) s1 s2 p1 p2). apply r_cong in C. apply symS in C.
  assert (D := transS _ _ _ C B).
  exact (transS _ _ _ D p2).
 Qed.

(* 
   Can't use <-> for existentials!  So break up into -> and <- lemmas. 
*) 

Lemma red_not_comm_iso_left :  bop_not_commutative red_Type red_eq red_bop -> bop_not_commutative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof.   intros [[[s1 p1] [s2 p2]]  p3]. compute in p3.  unfold Pr in p1. unfold Pr in p2. 
         exists (s1, s2). compute.
         case_eq(eqS (r (r (b (r s1) (r s2)))) (r (r (b (r s2) (r s1))))); intro J1.
         assert (K : eqS (r (b s1 s2)) (r (b s2 s1)) = true).
            assert (J2 := b_cong _ _ _ _ p1 p2). apply r_cong in J2. apply symS in J2. 
            assert (J3 := r_idem (b (r s1) (r s2))).  apply symS in J3.
            assert (J4 := transS _ _ _ J2 J3).            
            assert (J5 := transS _ _ _ J4 J1).            
            assert (J6 := r_idem (b (r s2) (r s1))). 
            assert (J7 := transS _ _ _ J5 J6).            
            assert (J8 := b_cong _ _ _ _ p2 p1). apply r_cong in J8.
            assert (J9 := transS _ _ _ J7 J8).
            exact J9.
         rewrite K in p3.  discriminate p3. 
         reflexivity. 
Qed. 


Lemma red_not_comm_iso_right :  bop_not_commutative S (brel_reduce eqS r) (bop_full_reduce r b) -> bop_not_commutative red_Type red_eq red_bop. 
Proof.  intros [[s1 s2]  p]. exists (inj s1, inj s2). compute.  
        compute in p. 
        case_eq(eqS (r (b (r s1) (r s2))) (r (b (r s2) (r s1)))); intro J1.
           apply r_cong in J1.
           rewrite J1 in p. discriminate p. 
        reflexivity. 
Qed. 



Lemma red_exists_id_left :  bop_exists_id red_Type red_eq red_bop -> bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros [[id P] Q].
       exists id. intro s; compute. compute in Q.
       destruct (Q (inj s)) as [L R]. compute in L, R. unfold Pr in P.
       split.
       assert (J1 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J1.
       assert (J2 := transS _ _ _ J1 L). apply r_cong in J2.
       assert (J3 := r_idem s).
       assert (J4 := transS _ _ _ J2 J3).
       exact J4.
       assert (J1 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J1.
       assert (J2 := transS _ _ _ J1 R). apply r_cong in J2.
       assert (J3 := r_idem s).
       assert (J4 := transS _ _ _ J2 J3).
       exact J4. 
Qed. 

Lemma red_exists_id_right : bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r b) -> bop_exists_id red_Type red_eq red_bop.
Proof. intros [id Q].
       exists (inj id). intros [s P]; compute. compute in Q.
       destruct (Q s) as [L R].  unfold Pr in P.
       split.
       assert (J1 := b_cong _ _ _ _(refS (r id)) P). apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
       assert (J2 := transS _ _ _ J1 L). 
       assert (J3 := r_idem (b (r id) s)). apply symS in J3. 
       assert (J4 := transS _ _ _ J3 J2).
       assert (J5 := transS _ _ _ J4 P).       
       exact J5.
       assert (J1 := b_cong _ _ _ _ P (refS (r id))). apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
       assert (J2 := transS _ _ _ J1 R). 
       assert (J3 := r_idem (b s (r id))). apply symS in J3. 
       assert (J4 := transS _ _ _ J3 J2).
       assert (J5 := transS _ _ _ J4 P).       
       exact J5.
Qed. 


Lemma red_not_exists_id_left :  bop_not_exists_id red_Type red_eq red_bop -> bop_not_exists_id S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros H s. compute.
       destruct (H (inj s)) as [[s' P] Q]. compute in Q. unfold Pr in P.
       exists s'.
       destruct Q as [Q | Q].
       left.
       case_eq(eqS (r (r (b (r s) (r s')))) (r s')); intro J1.
       assert (K : eqS (r (b (r s) s')) s' = true).
          assert (J2 := transS _ _ _ J1 P).
          assert (J3 := r_idem (b (r s) (r s'))). apply symS in J3.
          assert (J4 := transS _ _ _ J3 J2).
          assert (J5 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J5. apply symS in J5.
          assert (J6 := transS _ _ _ J5 J4).
          exact J6. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
       right. 
       case_eq(eqS (r (r (b (r s') (r s)))) (r s')); intro J1.
       assert (K : eqS (r (b s' (r s))) s' = true).
          assert (J2 := transS _ _ _ J1 P).
          assert (J3 := r_idem (b (r s') (r s))). apply symS in J3.
          assert (J4 := transS _ _ _ J3 J2).
          assert (J5 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J5. apply symS in J5.
          assert (J6 := transS _ _ _ J5 J4).
          exact J6. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
Qed.

Lemma red_not_exists_id_right :  bop_not_exists_id S (brel_reduce eqS r) (bop_full_reduce r b) -> bop_not_exists_id red_Type red_eq red_bop.
Proof. intros H [s P]. compute. unfold Pr in P. 
       destruct (H s) as [s' Q]. compute in Q.
       exists (inj s'). compute. 
       destruct Q as [Q | Q].
       left.
       case_eq(eqS (r (b s (r s'))) (r s')); intro J1.
       assert (K : eqS (r (r (b (r s) (r s')))) (r s') = true).
          assert (J2 := b_cong _ _ _ _ P (refS (r s'))). apply r_cong in J2. 
          assert (J3 := transS _ _ _ J2 J1). apply r_cong in J3. 
          assert (J4 := r_idem s'). 
          assert (J5 := transS _ _ _ J3 J4).
          exact J5. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
       right. 
       case_eq(eqS (r (b (r s') s)) (r s')); intro J1.
       assert (K : eqS (r (r (b (r s') (r s)))) (r s') = true).
          assert (J2 := b_cong _ _ _ _ (refS (r s')) P). apply r_cong in J2. 
          assert (J3 := transS _ _ _ J2 J1). apply r_cong in J3. 
          assert (J4 := r_idem s'). 
          assert (J5 := transS _ _ _ J3 J4).
          exact J5. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
Qed.


  (* 
    Some sufficient conditions ...
  *) 
  
  (* 
    Commutativity 
   *)
  Lemma red_bop_comm : bop_commutative S eqS b -> bop_commutative red_Type red_eq red_bop. 
  Proof. intros H1 [s1 p1] [s2 p2]. compute.
         unfold bop_commutative in H1. 
         apply r_cong. apply H1. 
  Qed.
  (* 
      idempotence 
  *)   
  Lemma red_bop_idem : bop_idempotent S eqS b -> bop_idempotent red_Type red_eq red_bop. 
  Proof. intros idemS [s p]. compute.
         assert (H1 := idemS s).
         unfold Pr in p.
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p). 
         exact H3. 
  Qed.                                  
  (* 
      Selectivity 
  *)   
  Lemma red_bop_sel : bop_selective S eqS b -> bop_selective red_Type red_eq red_bop. 
  Proof. intros selS [s1 p1] [s2 p2]. compute.
         destruct (selS s1 s2) as [H1 | H1].
         left. unfold Pr in p1. 
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p1). 
         exact H3.
         right. unfold Pr in p2. 
         assert (H2 := r_cong _ _ H1).
         assert (H3 := transS _ _ _ H2 p2). 
         exact H3. 
  Qed.                                  
  (* 
      Id 
   *)

  Definition uop_preserves_id (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ (s : S), bop_is_id S eq b s -> eq (r s) s = true.

Definition uop_preserves_ann (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ (s : S), bop_is_ann S eq b s -> eq (r s) s = true.

  Lemma red_bop_id : uop_preserves_id S eqS b r -> bop_exists_id S eqS b -> bop_exists_id red_Type red_eq red_bop. 
  Proof. intros H [id p]. exists (inj id). unfold bop_is_id in p. unfold bop_is_id.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H id p).
          assert (H4 := r_left  id t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := transS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := transS _ _ _ H6 pt).
          exact H7.
          assert (H3 := H id p).
          assert (H4 := r_right  t id). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := transS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := transS _ _ _ H6 pt).
          exact H7.
Qed.
  (* 
      Ann 
  *)   
Lemma red_bop_ann : uop_preserves_ann S eqS b r -> bop_exists_ann S eqS b -> bop_exists_ann red_Type red_eq red_bop. 
  Proof. intros H [ann p]. exists (inj ann). unfold bop_is_ann in p. unfold bop_is_ann.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H ann p).
          assert (H4 := r_left  ann t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := transS _ _ _ H4 H5).
          exact H6.
          assert (H3 := H ann p).
          assert (H4 := r_right  t ann). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := transS _ _ _ H4 H5).
          exact H6.
  Qed.


End ReductionTheory.


