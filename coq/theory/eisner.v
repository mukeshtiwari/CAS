Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.sg.product.


Definition bop_eisner (S : Type) (addS : binary_op S) (mulS : binary_op S) : binary_op (S * S) 
:= λ x y,  
   match x, y with
    | (s1, t1), (s2, t2) => (addS (mulS s1 t2) (mulS t1 s2), mulS t1 t2) 
   end.


Section Test. 
Variable S : Type. 
Variable rS : brel S. 

Variable addS : binary_op S.
Variable mulS: binary_op S.


Definition eisner := bop_eisner S addS mulS.

(* all needed for associativity *)
Variable refS : brel_reflexive S rS. 
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

Variable c_add : bop_congruence S rS addS.
Variable c_mul : bop_congruence S rS mulS.
Variable a_add : bop_associative S rS addS. 
Variable a_mul : bop_associative S rS mulS.

Variable ld : bop_left_distributive S rS addS mulS. 
Variable rd : bop_right_distributive S rS addS mulS. 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a !=S b"  := (rS a b = false) (at level 15).
Notation "a == b"  := (brel_product S S rS rS a b = true) (at level 15).
Notation "a [+] b"  := (addS a b) (at level 15).
Notation "a [*] b"  := (mulS a b) (at level 15).
Notation "a [.] b"  := (bop_eisner S rS a b) (at level 15).


Lemma bop_eisner_associative : bop_associative (S * S) (brel_product rS rS) eisner. 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. simpl.  
       apply andb_is_true_right. split.
(* Interesting : associativity requires left and right distributivity: 
   
         ((s1 [*] t2)         [+]  (t1 [*] s2)) [*] t3  [+]  (t1 [*] t2) [*] s3
=rd=     [(s1 [*] t2) [*] t3  [+]  (t1 [*] s2) [*] t3]  [+]  (t1 [*] t2) [*] s3
=a_add=   (s1 [*] t2) [*] t3  [+]  [(t1 [*] s2) [*] t3  [+]  (t1 [*] t2) [*] s3 ]                                                 
=a_mul=    s1 [*] (t2 [*] t3) [+]  [t1 [*] (s2 [*]  t3) [+]   t1 [*] (t2 [*] s3)]
=ld=       s1 [*] (t2 [*] t3) [+]   t1 [*] ((s2 [*] t3) [+]          (t2 [*] s3))

*)
          assert (E1 := rd t3 (s1 [*] t2) (t1 [*] s2)).
          assert (E2 := a_mul s1 t2 t3).
          assert (E3 := a_mul t1 s2 t3). 
          assert (E4 := a_mul t1 t2 s3).
          assert (E5 := ld t1 (s2 [*] t3) (t2 [*] s3)). apply symS in E5.
          assert (E6 := c_add _ _ _ _ E1 (refS ((t1 [*] t2) [*] s3))).
          assert (E7 := a_add ((s1 [*] t2) [*] t3) ((t1 [*] s2) [*] t3) ((t1 [*] t2) [*] s3)).
          assert (E8 := c_add _ _ _ _ E3 E4).
          assert (E9 := c_add _ _ _ _ E2 E8).
          assert (E10 := c_add _ _ _ _ (refS (s1 [*] (t2 [*] t3))) E5).
          assert (E11 := tranS _ _ _ E6 E7).
          assert (E12 := tranS _ _ _ E11 E9).
          assert (E13 := tranS _ _ _ E12 E10).
          exact E13. 
          apply a_mul.
Qed. 


Lemma bop_eisner_congruence : bop_congruence (S * S) (brel_product rS rS) eisner.
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       apply andb_is_true_right. split.  
          apply c_add; auto. 
          apply c_mul; auto.
Qed.           

Lemma bop_eisner_idempotent :
      (∀ (s t : S), ((s [*] t) [+] (t [*] s)) =S s) → 
      bop_idempotent S rS mulS → 
         bop_idempotent (S * S) (brel_product rS rS) eisner. 
Proof. intros H I (s, t). simpl. apply andb_is_true_right. split. 
       apply H. 
       rewrite I. reflexivity. 
Qed. 

Lemma bop_eisner_fact1 :
  (∀ (s t : S), ((s [*] t) [+] (t [*] s)) =S s) →
      bop_idempotent S rS addS →   
      bop_commutative S rS mulS → 
         bop_is_left S rS mulS. 
Proof. intros H I C s t.
       assert (J := C s t).
       assert (K := I (s [*] t)).
       assert (L := H s t).
       assert (M := c_add _ _ _ _ (refS (s [*] t)) J).
       assert (N := tranS _ _ _ M L). apply symS in K.
       assert (O := tranS _ _ _ K N).
       exact O.
Qed. 

Lemma bop_eisner_fact2 (s : S) (f : S -> S) (Pf : brel_not_trivial S rS f) :
  (∀ (s t : S), ((s [*] t) [+] (t [*] s)) =S s) →
      bop_idempotent S rS addS →   
      bop_commutative_decidable S rS mulS → 
         bop_not_commutative S rS mulS. 
Proof. intros H I [C | NC]. 
       assert (J := bop_eisner_fact1 H I C).
       destruct (bop_commutative_implies_not_is_left S rS mulS s f Pf symS tranS C) as [[s' t'] Q]. 
       assert (L := J s' t'). rewrite L in Q. discriminate Q. 
       exact NC.
Defined. 


Lemma bop_eisner_not_idempotent_v1 (wS : S):
      bop_not_idempotent S rS mulS →       
         bop_not_idempotent (S * S) (brel_product rS rS) eisner. 
Proof. intros [s NI]. exists (wS, s). compute. 
       rewrite NI.
       case_eq(rS ((wS [*] s) [+] (s [*] wS)) wS); intro J1; auto.
Defined.

Lemma bop_eisner_not_idempotent_v2 (a b c d : S):
       { p : S * S &  match p with (s, t) => ((s [*] t) [+] (t [*] s)) !=S s end} → 
         bop_not_idempotent (S * S) (brel_product rS rS) eisner. 
Proof. intros [[s t] N]. exists (s, t). compute. rewrite N; auto.  Defined.


Lemma bop_eisner_product_anti_left :
    bop_anti_left S rS mulS -> 
  bop_anti_left (S * S) (brel_product rS rS) eisner. 
Proof. 
  intros AL [s1 t1] [s2 t2]; simpl. apply andb_is_false_right.
  right. apply AL. 
Qed. 

Lemma bop_eisner_product_anti_left_v2 :
  ((∀ (s1 s2 t1 t2 : S), s1 !=S ((s1 [*] t2) [+] (t1 [*] s2))) + (bop_anti_left S rS mulS)) →
  bop_anti_left (S * S) (brel_product rS rS) eisner. 
Proof. 
  intros [H | H] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
  left. apply H. right. apply H. 
Qed. 

Lemma bop_eisner_anti_right :
  ((∀ (s1 s2 t1 t2 : S), s1 !=S ((s2 [*] t1) [+] (t2 [*] s1))) + (bop_anti_right S rS mulS)) → 
      bop_anti_right (S * S) (brel_product rS rS) eisner. 
Proof. 
  intros [H | H] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
  left. apply H. right. apply H. 
Qed. 


(* 
   
*) 
Lemma bop_eisner_left_cancellative :
  (∀ (s1 s2 s3 t1 t2 t3 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S ((s1 [*] t3) [+] (t1 [*] s3)) -> s2 =S s3) → 
  bop_left_cancellative S rS mulS → 
      bop_left_cancellative (S * S) (brel_product rS rS) eisner. 
Proof. 
   intros J K [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply K in HR. apply J in HL. rewrite HL, HR. simpl. reflexivity. 
Defined.

Lemma bop_eisner_is_left :
      (∀ (s1 s2 t1 t2 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S s1) → 
      bop_is_left S rS mulS → 
      bop_is_left (S * S) (brel_product rS rS) eisner. 
Proof. intros L R (s1, t1) (s2, t2). simpl. apply andb_is_true_right. split.
          apply L. 
          apply R. 
Defined. 



Lemma bop_eisner_is_right :
      (∀ (s1 s2 t1 t2 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S s2) → 
      bop_is_right S rS mulS → 
      bop_is_right (S * S) (brel_product rS rS) eisner. 
Proof. intros L R (s1, t1) (s2, t2). simpl. apply andb_is_true_right. split.
          apply L. 
          apply R. 
Defined.


Lemma bop_eisner_is_right_v2 :
      bop_is_right S rS addS → 
      bop_is_right S rS mulS → 
      bop_is_right (S * S) (brel_product rS rS) eisner. 
Proof. intros L R (s1, t1) (s2, t2). simpl. apply andb_is_true_right. split.
          assert (K := L (s1 [*] t2) (t1 [*] s2)).
          assert (J := R t1 s2).
          assert (M := tranS _ _ _ K J).
          exact M.
          apply R. 
Defined.


Lemma bop_eisner_left_constant : 
      (∀ (s1 s2 s3 t1 t2 t3 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S ((s1 [*] t3) [+] (t1 [*] s3))) → 
      bop_left_constant S rS mulS → 
      bop_left_constant (S * S) (brel_product rS rS) eisner. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
Defined. 


Lemma bop_eisner_right_constant : 
      (∀ (s1 s2 s3 t1 t2 t3 : S), ((s2 [*] t1) [+] (t2 [*] s1)) =S ((s3 [*] t1) [+] (t3 [*] s1))) → 
      bop_right_constant S rS mulS → 
      bop_right_constant (S * S) (brel_product rS rS) eisner. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
Defined.


Lemma bop_eisner_commutative :
   (∀ (s1 s2 t1 t2 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S ((s2 [*] t1) [+] (t2 [*] s1))) → 
   bop_commutative S rS mulS → 
   bop_commutative (S * S) (brel_product rS rS) eisner. 
Proof. intros L R [s1 t1] [s2 t2]; compute. rewrite L, R. reflexivity. Qed. 
       

Lemma bop_eisner_selective :
  (∀ (s1 s2 t1 t2 : S), (((s1 [*] t2) [+] (t1 [*] s2)) =S s1) + (((s1 [*] t2) [+] (t1 [*] s2)) =S s2)) →
  (∀ (s1 s2 t1 t2 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S s1 → (t1 [*] t2) =S t1) →
  (∀ (s1 s2 t1 t2 : S), ((s1 [*] t2) [+] (t1 [*] s2)) =S s2 → (t1 [*] t2) =S t2) →  
   bop_selective (S * S) (brel_product rS rS) eisner. 
Proof. intros H J K [s1 t1] [s2 t2]; compute.
       destruct (H s1 s2 t1 t2) as [Q | Q].
       rewrite Q. left. apply (J _ _ _ _ Q). 
       rewrite Q. right. apply (K _ _ _ _ Q). 
Qed.


Lemma bop_eisner_exists_ann :
  (∀ (a : S), bop_is_ann S rS mulS a -> a [+] a =S a) -> 
  bop_exists_ann S rS mulS ->
         bop_exists_ann (S * S) (brel_product rS rS) eisner. 
Proof. intros H [am Q]. exists (am, am). intros [s2 t2]. compute. 
       destruct (Q t2) as [L1 R1]. destruct (Q s2) as [L2 R2].
       rewrite L1, R1.
       assert (F1 := c_add _ _ _ _ L1 L2).
       assert (F2 := c_add _ _ _ _ R2 R1).        
       assert (F3 := H am Q).
       assert (F4 := tranS _ _ _ F1 F3).
       assert (F5 := tranS _ _ _ F2 F3).        
       rewrite F4, F5. auto. 
Qed.

Lemma bop_eisner_not_exists_ann_v1 :
  bop_not_exists_ann S rS mulS ->
         bop_not_exists_ann (S * S) (brel_product rS rS) eisner. 
Proof. intros H (s, t). unfold bop_not_is_ann.
       destruct(H t) as [t' [Q | Q]]; exists (s, t'); compute.
          left. rewrite Q. case_eq(rS ((s [*] t') [+] (t [*] s)) s); intro F; auto. 
          right. rewrite Q. case_eq(rS ((s [*] t) [+] (t' [*] s)) s); intro F; auto. 
Qed.


Lemma bop_eisner_exists_id :
  (∀ (a : S), bop_is_ann S rS mulS a -> bop_is_id S rS addS a) ->   
  bop_exists_ann S rS mulS ->
  bop_exists_id S rS mulS ->
  bop_exists_id (S * S) (brel_product rS rS) eisner. 
Proof.  intros H [a P] [i Q]. exists (a, i). intros [s t]. compute.
        destruct (P t) as [L1 R1]. destruct (Q t) as [L2 R2]. destruct (Q s) as [L3 R3]. 
        rewrite L2, R2.
        assert (F1 := c_add _ _ _ _ L1 L3).
        assert (F2 := c_add _ _ _ _ R3 R1).
        destruct (H a P s) as [L4 R4].
        assert (F3 := tranS _ _ _ F1 L4).
        assert (F4 := tranS _ _ _ F2 R4).
        rewrite F3, F4. auto.
Defined.

Lemma bop_product_eisner_left_distributive : 
      bop_left_distributive S rS addS mulS → 
             bop_left_distributive (S * S) (brel_product rS rS) (bop_product addS addS) (eisner). 
Proof. intros ldS . unfold bop_left_distributive. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split.
          (*
              ((s1 [*] (t2 [+] t3)) [+] (t1 [*] (s2 [+] s3))) 
            =S (s1 [*] t2) [+] (s1 [*] t3) [+]  (t1 [*] s2)  (t1 [*] s3)
                 ... comm + ... 
           =S (((s1 [*] t2) [+] (t1 [*] s2)) [+] ((s1 [*] t3) [+] (t1 [*] s3)))

           OK 
          *) 
          admit. 
          apply ldS. 
Admitted. 


Lemma bop_product_eisner_left_left_absorption : 
      bops_left_left_absorptive S rS addS mulS → 
             bops_left_left_absorptive (S * S) (brel_product rS rS) (bop_product addS addS) (eisner). 
Proof. intros laS . unfold bops_left_left_absorptive. intros [s1 t1] [s2 t2]. simpl.
       apply andb_is_true_right. split. unfold bops_left_left_absorptive in laS. 
       (* 
        laS : ∀ s t : S, s =S (s [+] (s [*] t))

        so 

        s1 =S s1 [+] (s1 [*] t2) 

        so 
        (s1 [+] ((s1 [*] t2) [+] (t1 [*] s2))) 
        =S 
        s1 [+] (t1 [*] s2)
        
        want 
        s1 =S (s1 [+] ((s1 [*] t2) [+] (t1 [*] s2))) 

       *) 
       admit.  (* NEVER !!! *) 
       apply laS.
Admitted.        


End Test. 

