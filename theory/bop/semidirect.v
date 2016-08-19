Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 


Definition ltr_congruence (S T : Type) (rS : brel S) (rT : brel T) (f : left_transform S T) := 
   ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> rT (f s1 t1) (f s2 t2) = true.

Definition ltr_associative (S T: Type) (rT : brel T) (bS : binary_op S) (f : left_transform S T)
    := ∀ (s1 s2 : S) (t : T), rT (f (bS s1 s2) t) (f s1 (f s2 t)) = true. 

Definition ltr_distributive (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := ∀ (s : S) (t1 t2 : T), rT (f s (bT t1 t2)) (bT (f s t1) (f s t2)) = true. 

(* STRANGE : s1 + (f t1 s2) = s2 + (f t2 s1) *)
Definition ltr_commutative (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := ∀ (s1 s2 : S) (t1 t2 : T), rT (bT t1 (f s1 t2)) (bT t2 (f s2 t1)) = true. 

Definition ltr_not_commutative (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := { z : (S * S) * (T * T) & 
        match z with ((s1, s2), (t1, t2)) => 
              rT (bT t1 (f s1 t2)) (bT t2 (f s2 t1)) = false 
        end 
      }. 
Definition ltr_idempotent (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := ∀ (s : S) (t : T), rT (bT t (f s t)) t = true. 

Definition ltr_not_idempotent (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := { z : (S * T) & 
        match z with (s, t) => 
               rT (bT t (f s t)) t = false 
        end 
      }. 

Section Test. 
Variable S T : Type. 
Variable rS : brel S. 
Variable rT : brel T. 
(* Variable f  : T → (S → S). *) 
Variable f  : left_transform T S.
Variable bS : binary_op S. 
Variable bT: binary_op T. 

Definition bop_semidirect : binary_op (S * T) 
:= λ x y,  
   match x, y with
    | (s1, t1), (s2, t2) => (bS s1 (f t1 s2), bT t1 t2) 
   end.


Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a == b"  := (brel_product S T rS rT a b = true) (at level 15).
Notation "a # b"  := (bT a b) (at level 15).
Notation "a @ b"  := (bS a b) (at level 15).
Notation "a |> b"  := (bop_semidirect a b) (at level 15).

Lemma bop_semidirect_associative : 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS → 
      bop_congruence S rS bS → 
      bop_associative S rS bS → 
      bop_associative T rT bT → 
      ltr_associative T S rS bT f → 
      ltr_distributive T S rS bS f → 
         bop_associative (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. intros refS symS tranS congS assS assT assf dist [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split. 
          (* show ((s1 @ f t1 s2) @ f (t1 # t2) s3) =S (s1 @ f t1 (s2 @ f t2 s3))

               ((s1 @ f t1 s2) @ f (t1 # t2) s3) 
            = {assf} 
               ((s1 @ f t1 s2) @ f t1 (f t2 s3))
            = {assS} 
               s1 @ ((f t1 s2) @ f t1 (f t2 s3)))
            = {diss} 
               s1 @ (f t1 (s2 @ f t2 s3))
          *) 
          assert (fact1 := assf t1 t2 s3). 
          assert (fact2 := dist t1 s2 (f t2 s3)).
          assert (fact3 := congS _ _ _ _ (refS (s1 @ f t1 s2)) fact1). 
          assert (fact4 := assS s1 (f t1 s2) (f t1 (f t2 s3))). 
          assert (fact5 := tranS _ _ _ fact3 fact4). 
          assert (fact6 := congS _ _ _ _ (refS s1) fact2). apply symS in fact6.
          assert (fact7 := tranS _ _ _ fact5 fact6). 
          assumption. 
          apply assT.
Defined.  


Lemma bop_semidirect_congruence : 
      bop_congruence S rS bS → 
      bop_congruence T rT bT → 
      ltr_congruence T S rT rS f → 
      bop_congruence (S * T) (brel_product _ _ rS rT) bop_semidirect.
Proof. 
    intros cS cT cf [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       apply andb_is_true_right. split.  
          apply cS. assumption. apply cf. assumption. assumption. 
          apply cT. assumption. assumption. 
Defined.  

Lemma bop_semidirect_commutative : 
      ltr_commutative T S rS bS f → 
      bop_commutative T rT bT → 
         bop_commutative (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. 
       apply andb_is_true_right. split. 
          rewrite L. reflexivity.           
          rewrite R. reflexivity. 
Defined. 

Lemma bop_semidirec_not_commutative_v1 : 
      ltr_not_commutative T S rS bS f → 
         bop_not_commutative (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. intros [[ [t1 t2] [s1 s2 ] ] P]. 
       exists ((s1, t1), (s2, t2)). simpl. 
       apply andb_is_false_right. left. assumption. 
Defined. 


Lemma bop_semidirec_not_commutative_v2 (s : S) : 
      bop_not_commutative T rT bT → 
         bop_not_commutative (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. intros [ [t1 t2] P]. 
       exists ((s, t1), (s, t2)). simpl. 
       apply andb_is_false_right. right. assumption. 
Defined. 


Lemma bop_semidirect_idempotent : 
      ltr_idempotent T S rS bS f → 
      bop_idempotent T rT bT → 
         bop_idempotent (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. 
   unfold bop_idempotent. intros L R (s, t). simpl. 
   apply andb_is_true_right. split. 
      rewrite L. reflexivity. 
      rewrite R. reflexivity. 
Defined. 


Lemma bop_semidirect_not_idempotent_v1 : 
      ltr_not_idempotent T S rS bS f → 
         bop_not_idempotent (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. intros [ [t s] P]. 
       exists (s, t). simpl. 
       apply andb_is_false_right. left. assumption. 
Defined. 


Lemma bop_semidirect_not_idempotent_v2 (s : S) : 
      bop_not_idempotent T rT bT → 
         bop_not_idempotent (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. intros [ t P ]. 
       exists (s, t). simpl. 
       apply andb_is_false_right. right . assumption. 
Defined. 



(* ids / ann *) 


Lemma bop_semidirect_exists_id (s1 : S) (t1 : T) : 
         bop_exists_id (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. exists (s1, t1). intros [s2 t2]. split; simpl.  
       (* has left id 
           ((s1, t1) |> (s2, t2)) == (s2, t2)

           rS (s1 @ f t1 s2) s2 && rT (t1 # t2) t2 = true
       *) 
       compute. 
       case_eq(rS (s1 @ f t1 s2) s2); intro J; auto. 
          admit. (* need left_id for T *) 
          admit. (* HELP    perhaps we can only expect a left or right id?  
                    need (s1 @ f t1 s2) = s2  to get contradiction 

                    one way : f preserves right_ann s2 ! 

                 *) 
       (* has right id 
           ((s2, t2) |> (s1, t1)) == (s2, t2)

            rS (s2 @ f t2 s1) s2 && rT (t2 # t1) t2 = true
       *) 
       compute. 
       case_eq(rS (s2 @ f t2 s1) s2 ); intro K; auto. 
          admit. (* need right id for T *) 
          admit. (* need f t right_id = right_id for S *) 
Defined. 


Lemma bop_semidirect_exists_ann (s1 : S) (t1 : T) : 
         bop_exists_ann (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. exists (s1, t1). intros [s2 t2]. split; compute. 
       (* has left ann *) 
       case_eq(rS (s1 @ f t1 s2) s1); intro J; auto. 
          admit. (* need left_ann for T *) 
          admit. (* need left_ann for S *) 
       (* has right ann *) 
       case_eq(rS (s2 @ f t2 s1) s1 ); intro K; auto. 
          admit. (* need right ann for T *) 
          admit. (* need f t right_ann = right_ann for S 
                    or (s2 @ f t2 s1) = s1
                  *) 
Defined. 




Lemma bop_semidirect_product_left_cancellative : 
      (∀ (s1 s2 : S) (t : T), rS (f t s1) (f t s2) = true → rS s1 s2 = true) → 
      bop_left_cancellative S rS bS → 
      bop_left_cancellative T rT bT → 
      bop_left_cancellative (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. 
   intros C L R [s1 t1] [s2 t2] [s3 t3] ; simpl. intro H. 
   apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply andb_is_true_right. split. 
      apply L in HL. apply C in HL. assumption. 
      apply R in HR. assumption. 
Defined. 


Lemma bop_semidirect_product_right_cancellative : 
      (((bop_right_cancellative S rS bS) * 
       (∀ (s : S) (t1 t2 : T), rS (f t1 s) (f t2 s)= true)) 
       + (∀ (s1 s2 s3 : S) (t1 t2 : T), 
              rS (bS s2 (f t1 s1)) (bS s3 (f t2 s1)) = true -> rS s2 s3 = true)) → 
      bop_right_cancellative T rT bT → 
      bop_right_cancellative (S * T) (brel_product _ _ rS rT) bop_semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3] ; simpl. intro H. 
   apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply andb_is_true_right. split. 
      destruct L as [ [rcS L ] | L].
         admit. 
         apply (L s1 s2 s3 t2 t3 HL). 
      apply R in HR. assumption. 
Defined. 



Lemma bop_direct_product_is_left : 
      bop_is_left S rS bS → 
      bop_is_left T rT bT → 
      bop_is_left (S * T) (brel_product _ _ rS rT) bop_semidirect_product. 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 


Lemma bop_direct_product_is_right : 
      (((bop_is_right S rS bS) * (∀ (s : S) (t: T), rS (f t s) s = true)) 
       + (∀ (s1 s2 : S) (t: T), rS (bS s1 (f t s2)) s2 = true))   → 
      bop_is_right T rT bT → 
      bop_is_right (S * T) (brel_product _ _ rS rT) bop_semidirect_product. 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite R. simpl.
       destruct L as [ [rcS L ] | L].
         admit. 
         rewrite L. simpl. reflexivity. 
Defined. 


Lemma bop_semidirect_product_left_constant : 
      bop_left_constant S rS bS → 
      bop_left_constant T rT bT → 
      bop_left_constant (S * T) (brel_product _ _ rS rT) bop_semidirect_product. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
Defined. 


Lemma bop_semidirect_product_right_constant : 
      (((bop_right_constant S rS bS) * (∀ (s : S) (t1 t2: T), rS (f t1 s) (f t2 s) = true)) 
         + (∀ (s1 s2 s3 : S) (t1 t2: T), rS (bS s2 (f t1 s1)) (bS s3 (f t2 s1)) = true)) → 
      bop_right_constant T rT bT → 
      bop_right_constant (S * T) (brel_product _ _ rS rT) bop_semidirect_product. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. 
      destruct L as [ [rcS L ] | L].
         admit. 
         rewrite L. simpl. reflexivity. 
      apply R. 
Defined. 


Lemma bop_semidirect_product_anti_left : 
      (bop_anti_left S rS bS) + (bop_anti_left T rT bT) → 
      bop_anti_left (S * T) (brel_product _ _ rS rT) bop_semidirect_product. 
Proof. 
   intros [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. apply P. 
      right. apply P. 
Defined. 


Lemma bop_product_anti_right : 
      ((bop_anti_right S rS bS) * (∀ (s : S) (t : T), rS s (f t s) = true)) 
      + (∀ (s1 s2 : S) (t : T), rS s1 (bS s2 (f t s1)) = false)
      + (bop_anti_right T rT bT) → 
      bop_anti_right (S * T) (brel_product _ _ rS rT) bop_semidirect_product. 
Proof. 
   intros [R | L] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. destruct R as [ [rcS P ] | P].
         admit. 
         rewrite P. simpl. reflexivity. 
      right. apply L. 
Defined. 



End Test. 




Lemma bop_product_not_is_left_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial T rT  → 
      bop_not_is_left S rS bS → 
      bop_not_is_left (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. unfold bop_not_is_left. 
   intros S T rS rT bS bT ntT [ [s t] P]. 
   destruct (brel_nontrivial_witness _ _ ntT) as [wT _]. 
   exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_is_left_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS  → 
      bop_not_is_left T rT bT → 
      bop_not_is_left (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. unfold bop_not_is_left.
   intros S T rS rT bS bT ntS [ [s t] P].  
   destruct (brel_nontrivial_witness _ _ ntS) as [wS _]. 
   exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. 
Defined. 


Lemma bop_product_not_is_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),  
      brel_nontrivial S rS  → 
      brel_nontrivial T rT  → 
      (bop_not_is_left S rS bS) +  (bop_not_is_left T rT bT) → 
      bop_not_is_left (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT ntS ntT. intro d. destruct d. 
   apply bop_product_not_is_left_left. assumption. assumption. 
   apply bop_product_not_is_left_right. assumption. assumption. 
Defined. 


Lemma bop_product_not_is_right_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial T rT  → 
      bop_not_is_right S rS bS → 
      bop_not_is_right (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. unfold bop_not_is_right. 
   intros S T rS rT bS bT ntT [ [s t] P]. 
   destruct (brel_nontrivial_witness _ _ ntT) as [wT _]. 
   exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_is_right_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      brel_nontrivial S rS  → 
      bop_not_is_right T rT bT → 
      bop_not_is_right (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. unfold bop_not_is_right.
   intros S T rS rT bS bT ntS [ [s t] P]. 
   destruct (brel_nontrivial_witness _ _ ntS) as [wS _]. 
   exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. 
Defined. 


Lemma bop_product_not_is_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),  
      brel_nontrivial S rS  → 
      brel_nontrivial T rT  → 
      (bop_not_is_right S rS bS) +  (bop_not_is_right T rT bT) → 
          bop_not_is_right (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT ntS ntT. intro d. destruct d. 
   apply bop_product_not_is_right_left. assumption. assumption. 
   apply bop_product_not_is_right_right. assumption. assumption. 
Defined. 


Lemma bop_not_left_or_not_right : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
   brel_nontrivial S r -> 
   brel_symmetric S r -> 
   brel_transitive S r -> 
   bop_is_left S r b -> 
   bop_is_right S r b -> False. 
     
Proof. intros S r b ntS symS transS ilS irS.
       destruct (brel_nontrivial_pair S r ntS) as [[s1 s2] [P1 P2]].
       assert (H1 := ilS s1 s2).
       assert (H2 := irS s1 s2).
       apply symS in H1.
       assert (H3 := transS _ _ _ H1 H2).
       rewrite P1 in H3. 
       discriminate. 
Qed. 


Lemma bop_product_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      ((bop_is_left S rS bS) * (bop_is_left T rT bT)) 
     + ((bop_is_right S rS bS) * (bop_is_right T rT bT)) → 
      bop_selective (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
    intros S T rS rT bS bT. 
    unfold bop_is_left, bop_is_right, bop_selective.  
    intros [ [L R] | [L R] ] [s1 t1] [s2 t2]; simpl.
       left. rewrite (L s1 s2), (R t1 t2). simpl. reflexivity. 
       right. rewrite (L s1 s2), (R t1 t2). simpl. reflexivity. 
Defined.  

Lemma bop_product_not_selective : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
(* NB *) ((bop_not_is_left S rS bS) + (bop_not_is_right S rS bS)) → 
(* NB *) ((bop_not_is_left T rT bT) + (bop_not_is_right T rT bT)) → 
      ((bop_not_is_left S rS bS) + (bop_not_is_left T rT bT)) 
     * ((bop_not_is_right S rS bS) + (bop_not_is_right T rT bT)) → 
      bop_not_selective (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
    intros S T rS rT bS bT nl_or_nr_S nl_or_nr_T. 
    unfold bop_not_is_left, bop_not_is_right, bop_not_selective.  
    intros [ 
             [ [ [s1 s2] P1 ] | [ [t1 t2] Q1]  ] 
             [ [ [s3 s4] P2 ] | [ [t3 t4] Q2]  ] 
           ]. 
       destruct nl_or_nr_T as [ [ [t5 t6] W1 ]  | [ [t5 t6] W1 ] ]. 
          exists ((s3, t5), (s4, t6)); 
             simpl. rewrite P2, W1. simpl. rewrite andb_comm. simpl. split; reflexivity. 
          exists ((s1, t5), (s2, t6)); 
             simpl. rewrite P1, W1. simpl. rewrite andb_comm. simpl. split; reflexivity.
       exists ((s1, t3), (s2, t4)); 
          simpl. rewrite P1, Q2. simpl. rewrite andb_comm. simpl. split; reflexivity.             
       exists ((s3, t1), (s4, t2)); 
          simpl. rewrite P2, Q1. simpl. rewrite andb_comm. simpl. split; reflexivity.             
       destruct nl_or_nr_S as [ [ [s1 s2] W1]  | [ [s1 s2] W1] ]. 
          exists ((s1, t3), (s2, t4)); 
             simpl. rewrite Q2, W1. simpl. rewrite andb_comm. simpl. split; reflexivity.   
          exists ((s1, t1), (s2, t2)); 
             simpl. rewrite Q1, W1. simpl. rewrite andb_comm. simpl. split; reflexivity. 
Defined.  

Lemma bop_product_left_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_left_cancellative S rS bS → 
      bop_left_cancellative T rT bT → 
      bop_left_cancellative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply L in HL. apply R in HR. rewrite HL, HR. auto. 
Defined. 

Lemma bop_product_not_left_cancellative_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (t : T), 
      brel_reflexive T rT  → 
      bop_not_left_cancellative S rS bS → 
      bop_not_left_cancellative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT t refT [ [s1 [s2 s3]] [L R] ] . 
   exists ((s1, t), ((s2, t), (s3, t))); simpl. split. 
      apply andb_is_true_right. split. 
         assumption.      
         apply refT. 
      rewrite R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_cancellative_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S), 
      brel_reflexive S rS  → 
      bop_not_left_cancellative T rT bT → 
      bop_not_left_cancellative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT s refS [ [t1 [t2 t3]] [L R] ]. 
   exists ((s, t1), ((s, t2), (s, t3))); simpl. split. 
      apply andb_is_true_right. split. 
         apply refS. 
         assumption.      
      rewrite R. rewrite (refS s). simpl. reflexivity. 
Defined. 



Lemma bop_product_not_right_cancellative_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (t : T), 
      brel_reflexive T rT  → 
      bop_not_right_cancellative S rS bS → 
      bop_not_right_cancellative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT t refT [ [s1 [s2 s3]] [L R] ]. 
   exists ((s1, t), ((s2, t), (s3, t))); simpl. split. 
      apply andb_is_true_right. split. 
         assumption.      
         apply refT. 
      rewrite R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_cancellative_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S), 
      brel_reflexive S rS  → 
      bop_not_right_cancellative T rT bT → 
      bop_not_right_cancellative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT s refS [ [t1 [t2 t3]] [L R] ]. 
   exists ((s, t1), ((s, t2), (s, t3))); simpl. split. 
      apply andb_is_true_right. split. 
         apply refS. 
         assumption.      
      rewrite R. rewrite (refS s). simpl. reflexivity. 
Defined. 


Lemma bop_product_not_left_constant_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (t : T), 
      bop_not_left_constant S rS bS → 
      bop_not_left_constant (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT t [ [s1 [s2 s3]] Q ] . 
   exists ((s1, t), ((s2, t), (s3, t))); simpl. 
   apply andb_is_false_right. left. assumption.      
Defined. 


Lemma bop_product_not_left_constant_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S), 
      bop_not_left_constant T rT bT → 
      bop_not_left_constant (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT s [ [t1 [t2 t3]]  Q ]. 
   exists ((s, t1), ((s, t2), (s, t3))); simpl. 
   apply andb_is_false_right. right. assumption.      
Defined. 

Lemma bop_product_not_right_constant_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (t : T), 
      bop_not_right_constant S rS bS → 
      bop_not_right_constant (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT t [ [s1 [s2 s3]] Q ]. 
   exists ((s1, t), ((s2, t), (s3, t))); simpl. 
   apply andb_is_false_right. left. assumption.      
Defined. 


Lemma bop_product_not_right_constant_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S), 
      bop_not_right_constant T rT bT → 
      bop_not_right_constant (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT s [ [t1 [t2 t3]] Q ]. 
   exists ((s, t1), ((s, t2), (s, t3))); simpl. 
   apply andb_is_false_right. right. assumption.      
Defined. 

Lemma bop_product_not_anti_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_anti_left S rS bS → 
      bop_not_anti_left T rT bT → 
      bop_not_anti_left (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [[ s1 s2 ] P ] [ [ t1 t2 ] Q ]. 
   exists ((s1, t1), (s2, t2)); simpl. rewrite P, Q. simpl. reflexivity. 
Defined. 


Lemma bop_product_not_anti_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_anti_right S rS bS → 
      bop_not_anti_right T rT bT → 
      bop_not_anti_right (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [ [s1 s2] P ] [ [t1 t2] Q ]. 
   exists ((s1, t1), (s2, t2)); simpl. rewrite P, Q. simpl. reflexivity. 
Defined. 


