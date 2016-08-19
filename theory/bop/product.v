Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 

Lemma bop_product_congruence : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_congruence S rS bS → bop_congruence T rT bT → 
      bop_congruence (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
    intros S T rS rT bS bT. 
    unfold bop_congruence.  
    intros cS cT [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       apply andb_is_true_right. split.  
          apply cS. assumption. assumption. 
          apply cT. assumption. assumption. 
Defined.  

Lemma bop_product_associative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_associative S rS bS → bop_associative T rT bT → 
      bop_associative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
    intros S T rS rT bS bT. 
    unfold bop_associative.  
    intros assS assT [s1 s2] [t1 t2] [u1 u2]; simpl.
       apply andb_is_true_right. split. apply assS. apply assT.
Defined.  


Lemma bop_product_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_idempotent S rS bS → 
      bop_idempotent T rT bT → 
      bop_idempotent (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_idempotent. intros L R (s, t). 
   simpl. rewrite L, R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_idempotent_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (t : T), 
      bop_not_idempotent S rS bS → 
      bop_not_idempotent (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT t. unfold bop_not_idempotent. intros [s P]. 
   exists (s, t). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_idempotent_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (choose : S), 
      bop_not_idempotent T rT bT → 
      bop_not_idempotent (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT s [t P]. exists (s, t). simpl. rewrite P. rewrite andb_comm. simpl. 
   reflexivity. 
Defined. 

Lemma bop_product_not_idempotent : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (chooseS : S) (chooseT : T),  
      (bop_not_idempotent S rS bS) +  (bop_not_idempotent T rT bT) → 
      bop_not_idempotent (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT chooseS chooseT. intro d. destruct d. 
   apply bop_product_not_idempotent_left. apply chooseT. assumption. 
   apply bop_product_not_idempotent_right. apply chooseS. assumption. 
Defined. 

Lemma bop_product_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_commutative S rS bS → 
      bop_commutative T rT bT → 
      bop_commutative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_commutative. intros L R (s1, t1) (s2, t2). 
   simpl. rewrite L, R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_commutative_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (choose : T), 
      bop_not_commutative S rS bS → 
      bop_not_commutative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT choose. unfold bop_not_commutative. intros [ [s t] P]. 
   exists ((s, choose), (t, choose)). simpl. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_commutative_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (choose : S), 
      bop_not_commutative T rT bT → 
      bop_not_commutative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT choose. unfold bop_not_commutative. intros [ [s t] P]. 
   exists ((choose, s), (choose, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_commutative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (chooseS : S) (chooseT : T),  
      (bop_not_commutative S rS bS) +  (bop_not_commutative T rT bT) → 
      bop_not_commutative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT chooseS chooseT. intro d. destruct d. 
   apply bop_product_not_commutative_left. apply chooseT. assumption. 
   apply bop_product_not_commutative_right. apply chooseS. assumption. 
Defined. 

Lemma bop_product_is_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_is_left S rS bS → 
      bop_is_left T rT bT → 
      bop_is_left (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_is_left. intros L R (s1, t1) (s2, t2). 
   simpl. rewrite L, R. simpl. reflexivity. 
Defined. 

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

Lemma bop_product_is_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_is_right S rS bS → 
      bop_is_right T rT bT → 
      bop_is_right (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT. unfold bop_is_right. intros L R (s1, t1) (s2, t2). 
   simpl. rewrite L, R. simpl. reflexivity. 
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

(*
Lemma bop_product_not_selective_left : 
   ∀ (S T : Type) (t : T) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_not_selective 
      bop_not_selective (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
*) 
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

(*
Lemma bop_product_testing : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
     ((bop_is_left S rS bS) + (bop_not_is_left S rS bS)) → 
     ((bop_is_right S rS bS) + (bop_not_is_right S rS bS)) → 
     ((bop_is_left T rT bT) + (bop_not_is_left T rT bT)) → 
     ((bop_is_right T rT bT) + (bop_not_is_right T rT bT)) →
     ((bop_not_is_left S rS bS) + (bop_not_is_right S rS bS)) * 
     ((bop_not_is_left T rT bT) + (bop_not_is_right T rT bT)). 
Proof. intros S T rS rT bS bT . 
       intros [leftS | not_leftS] [rightS | not_rightS] 
              [leftT | not_leftT] [rightT| not_rightT] ; split.
        left; assumption. 



Lemma bop_product_not_selective_v2 : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
     ((bop_is_left S rS bS) + (bop_not_is_left S rS bS)) → 
     ((bop_is_right S rS bS) + (bop_not_is_right S rS bS)) → 
     ((bop_is_left T rT bT) + (bop_not_is_left T rT bT)) → 
     ((bop_is_right T rT bT) + (bop_not_is_right T rT bT)) → 
      ((bop_not_is_left S rS bS) + (bop_not_is_left T rT bT)) 
     * ((bop_not_is_right S rS bS) + (bop_not_is_right T rT bT)) → 
      bop_not_selective (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. unfold bop_not_is_left, bop_not_is_right, bop_not_selective.  
    intros S T rS rT bS bT 
           left_or_not_leftS right_or_not_rightS left_or_not_leftT right_or_not_rightT. 
    intros [ 
             [ [ [s1 s2] P1 ] | [ [t1 t2] Q1]  ] 
             [ [ [s3 s4] P2 ] | [ [t3 t4] Q2]  ] 
           ]. 
       exists ((s1, t), (s2, t)). simpl. rewrite P1. simpl. 




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
*) 


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


Lemma bop_product_right_cancellative : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_right_cancellative S rS bS → 
      bop_right_cancellative T rT bT → 
      bop_right_cancellative (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply L in HL. apply R in HR. rewrite HL, HR. auto. 
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









Lemma bop_product_left_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_left_constant S rS bS → 
      bop_left_constant T rT bT → 
      bop_left_constant (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
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


Lemma bop_product_right_constant : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      bop_right_constant S rS bS → 
      bop_right_constant T rT bT → 
      bop_right_constant (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
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


Lemma bop_product_anti_left : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_anti_left S rS bS) + (bop_anti_left T rT bT) → 
      bop_anti_left (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. apply P. 
      right. apply P. 
Defined. 


Lemma bop_product_anti_right : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T), 
      (bop_anti_right S rS bS) + (bop_anti_right T rT bT) → 
      bop_anti_right (S * T) (brel_product _ _ rS rT) (bop_product _ _ bS bT). 
Proof. 
   intros S T rS rT bS bT [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. apply P. 
      right. apply P. 
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


(* Elimination *) 

Lemma bop_product_is_id_left : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t))
       ->  bop_is_id S rS bS s.  
Proof. intros S T rS rT bS bT s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_product_is_id_right : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t))
       ->  bop_is_id T rT bT t.  
Proof. intros S T rS rT bS bT s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.                         


Lemma bop_product_is_ann_left : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t))
       ->  bop_is_ann S rS bS s.  
Proof. intros S T rS rT bS bT s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_product_is_ann_right : 
   ∀ (S T : Type) 
     (rS : brel S )
     (rT : brel T )
     (bS : binary_op S )
     (bT : binary_op T )
     (s : S )
     (t : T ),         
     (bop_is_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t))
       ->  bop_is_ann T rT bT t.  
Proof. intros S T rS rT bS bT s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.       



Lemma bop_product_is_id : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        ∀ (s : S) (t : T), 
        bop_is_id S rS bS s -> 
        bop_is_id T rT bT t -> 
           bop_is_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t).
Proof. unfold bop_is_id. intros S T rS rT bS bT iS iT pS pT. 
       intros (s, t). compute. unfold brel_product, bop_product. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr, Tl, Tr. auto. 
Defined. 


Lemma bop_product_not_is_id_left : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        ∀ (s : S) (t : T), 
        bop_not_is_id S rS bS s -> 
           bop_not_is_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t).
Proof. unfold bop_is_id. intros S T rS rT bS bT s t [x Nid]. 
       exists (x, t). compute. destruct Nid as [H | H]. 
       rewrite H. left. reflexivity. 
       rewrite H. right. reflexivity. 
Defined. 

Lemma bop_product_not_is_id_right : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        ∀ (s : S) (t : T), 
        bop_not_is_id T rT bT t -> 
           bop_not_is_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t).
Proof. unfold bop_is_id. intros S T rS rT bS bT s t [x Nid]. 
       exists (s, x). compute. destruct Nid as [H | H]. 
       rewrite H. left. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
       rewrite H. right. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
Defined. 


Lemma bop_product_exists_id : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        bop_exists_id S rS bS -> 
        bop_exists_id T rT bT -> 
           bop_exists_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. unfold bop_exists_id. intros S T rS rT bS bT [iS pS] [iT pT]. 
       exists (iS, iT). apply bop_product_is_id; auto. 
Defined. 

Lemma bop_product_not_exists_id : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        (bop_not_exists_id S rS bS) + (bop_not_exists_id T rT bT) -> 
           bop_not_exists_id (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. unfold bop_not_exists_id, brel_product, bop_product. 
       intros S T rS rT bS bT [pS | pT] (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. rewrite F. simpl. reflexivity. 
          exists (x, t). right. rewrite F. simpl. reflexivity. 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. rewrite F. apply andb_comm. 
          exists (s, x). right. rewrite F. apply andb_comm. 
Defined. 

Lemma bop_product_is_ann: 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        ∀ (s : S) (t : T), 
        bop_is_ann S rS bS s -> 
        bop_is_ann T rT bT t -> 
           bop_is_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t).
Proof. unfold bop_is_ann. intros S T rS rT bS bT iS iT pS pT. 
       intros (s, t). compute. unfold brel_product, bop_product. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr, Tl, Tr. auto. 
Defined. 


Lemma bop_product_not_is_ann_left : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        ∀ (s : S) (t : T), 
        bop_not_is_ann S rS bS s -> 
           bop_not_is_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t).
Proof. unfold bop_is_id. intros S T rS rT bS bT s t [x Nid]. 
       exists (x, t). compute. destruct Nid as [H | H]. 
       rewrite H. left. reflexivity. 
       rewrite H. right. reflexivity. 
Defined. 

Lemma bop_product_not_is_ann_right : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        ∀ (s : S) (t : T), 
        bop_not_is_ann T rT bT t -> 
           bop_not_is_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT) (s, t).
Proof. unfold bop_is_id. intros S T rS rT bS bT s t [x Nid]. 
       exists (s, x). compute. destruct Nid as [H | H]; rewrite H. 
          left. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
          right. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
Defined. 

Lemma bop_product_exists_ann : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        bop_exists_ann S rS bS -> 
        bop_exists_ann T rT bT -> 
           bop_exists_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. unfold bop_exists_id. intros S T rS rT bS bT [annS pS] [annT pT]. 
       exists (annS, annT). apply bop_product_is_ann; auto. 
Defined. 

Lemma bop_product_not_exists_ann : 
     ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT : binary_op T), 
        (bop_not_exists_ann S rS bS) + (bop_not_exists_ann T rT bT) -> 
           bop_not_exists_ann (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. unfold bop_not_exists_ann, brel_product, bop_product. 
       intros S T rS rT bS bT [pS | pT] (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. rewrite F. simpl. reflexivity. 
          exists (x, t). right. rewrite F. simpl. reflexivity. 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. rewrite F. apply andb_comm. 
          exists (s, x). right. rewrite F. apply andb_comm. 
Defined. 

                  

