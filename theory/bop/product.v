Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 


Section Product. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T. 
Variable bS : binary_op S. 
Variable bT : binary_op T.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable transS : brel_transitive S rS. 

Variable wT : T.
Variable g : T -> T.                
Variable Pg : brel_not_trivial T rT g. 

Variable refT :  brel_reflexive T rT. 
Variable symT : brel_symmetric T rT.
Variable transT : brel_transitive T rT. 


Variable conS : bop_congruence S rS bS.
Variable assS : bop_associative S rS bS.

Variable conT : bop_congruence T rT bT. 
Variable assT : bop_associative T rT bT.

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a *S b"  := (bS a b) (at level 15).
Notation "a *T b"  := (bT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).


Lemma bop_product_congruence : bop_congruence (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       apply andb_is_true_right. split.  
          apply conS; auto. 
          apply conT; auto. 
Defined.  

Lemma bop_product_associative : bop_associative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2]; simpl. apply andb_is_true_right. split. apply assS. apply assT. Defined.  

Lemma bop_product_idempotent :  bop_idempotent S rS bS → bop_idempotent T rT bT → bop_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros L R (s, t). compute. rewrite L, R. reflexivity. Qed. 

Lemma bop_product_not_idempotent_left :  bop_not_idempotent S rS bS → bop_not_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [s P]. exists (s, wT). compute. rewrite P. reflexivity. Defined. 

Lemma bop_product_not_idempotent_right : bop_not_idempotent T rT bT → bop_not_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [t P]. exists (wS, t). compute. rewrite P. case_eq(rS (wS *S wS) wS); intro J; reflexivity. Defined. 

Lemma bop_product_not_idempotent :  (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → 
            bop_not_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [L | R]. 
   apply bop_product_not_idempotent_left. exact L. 
   apply bop_product_not_idempotent_right. exact R. 
Defined. 

Lemma bop_product_commutative : bop_commutative S rS bS → bop_commutative T rT bT → bop_commutative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_product_not_commutative_left : bop_not_commutative S rS bS → bop_not_commutative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [s t] P]. exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_commutative_right : bop_not_commutative T rT bT → bop_not_commutative (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [ [s t] P]. exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_commutative : 
      (bop_not_commutative S rS bS) +  (bop_not_commutative T rT bT) → bop_not_commutative (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [L | R]. 
   apply bop_product_not_commutative_left. exact L. 
   apply bop_product_not_commutative_right. exact R. 
Defined. 

Lemma bop_product_is_left : bop_is_left S rS bS → bop_is_left T rT bT → bop_is_left (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_left_left : bop_not_is_left S rS bS → bop_not_is_left (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [ [s t] P]. exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_left_right : bop_not_is_left T rT bT → bop_not_is_left (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [ [s t] P].  exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_left (s : S) (t : T) : 
      (bop_not_is_left S rS bS) +  (bop_not_is_left T rT bT) → 
      bop_not_is_left (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
   intros [L | R]. 
   apply bop_product_not_is_left_left. exact L. 
   apply bop_product_not_is_left_right. exact R. 
Defined. 

Lemma bop_product_is_right : bop_is_right S rS bS → bop_is_right T rT bT → bop_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold bop_is_right. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_right_left : bop_not_is_right S rS bS → bop_not_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold bop_not_is_right. intros  [ [s t] P]. exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_right_right : bop_not_is_right T rT bT → bop_not_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold bop_not_is_right. intros [ [s t] P]. exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. Defined. 


Lemma bop_product_not_is_right : 
      (bop_not_is_right S rS bS) +  (bop_not_is_right T rT bT) → bop_not_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
   intros  [L | R]. 
   apply bop_product_not_is_right_left. exact L. 
   apply bop_product_not_is_right_right. exact R. 
Defined. 

(*
*) 

Lemma bop_product_selective : 
      ((bop_is_left S rS bS) * (bop_is_left T rT bT)) 
     + ((bop_is_right S rS bS) * (bop_is_right T rT bT)) → 
      bop_selective (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
    unfold bop_is_left, bop_is_right, bop_selective.  
    intros [ [L R] | [L R] ] [s1 t1] [s2 t2]; simpl.
       left. rewrite (L s1 s2), (R t1 t2). simpl. reflexivity. 
       right. rewrite (L s1 s2), (R t1 t2). simpl. reflexivity. 
Defined.  

Lemma bop_product_not_selective : 
(* NB *) ((bop_not_is_left S rS bS) + (bop_not_is_right S rS bS)) → 
(* NB *) ((bop_not_is_left T rT bT) + (bop_not_is_right T rT bT)) → 
      ((bop_not_is_left S rS bS) + (bop_not_is_left T rT bT)) 
     * ((bop_not_is_right S rS bS) + (bop_not_is_right T rT bT)) → 
      bop_not_selective (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
    intros  nl_or_nr_S nl_or_nr_T. 
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
        bop_left_cancellative S rS bS → bop_left_cancellative T rT bT → bop_left_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
       intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
       apply L in HL. apply R in HR. rewrite HL, HR. auto. 
Defined. 

Lemma bop_product_not_left_cancellative_left : 
        bop_not_left_cancellative S rS bS → bop_not_left_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [s1 [s2 s3]] [L R] ] . 
       exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. split. 
       apply andb_is_true_right. split. 
         exact L. 
         apply refT. 
      rewrite R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_cancellative_right : 
      bop_not_left_cancellative T rT bT → bop_not_left_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [t1 [t2 t3]] [L R] ]. 
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. split. 
       apply andb_is_true_right. split. 
         apply refS. 
         exact L. 
      rewrite R. rewrite (refS wS). simpl. reflexivity. 
Defined. 


Lemma bop_product_right_cancellative : 
      bop_right_cancellative S rS bS → bop_right_cancellative T rT bT → 
         bop_right_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply L in HL. apply R in HR. rewrite HL, HR. auto. 
Defined. 

Lemma bop_product_not_right_cancellative_left : 
      bop_not_right_cancellative S rS bS → bop_not_right_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [s1 [s2 s3]] [L R] ]. 
       exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. split. 
       apply andb_is_true_right. split. 
         exact L. 
         apply refT. 
      rewrite R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_cancellative_right : 
        bop_not_right_cancellative T rT bT → bop_not_right_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [t1 [t2 t3]] [L R] ]. 
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. split. 
       apply andb_is_true_right. split. 
         apply refS. 
         exact L.      
      rewrite R. rewrite (refS wS). simpl. reflexivity. 
Defined. 

Lemma bop_product_left_constant : 
      bop_left_constant S rS bS → bop_left_constant T rT bT → bop_left_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  L R [s1 t1] [s2 t2] [s3 t3]; simpl. apply andb_is_true_right. split. apply L. apply R. Defined. 

Lemma bop_product_not_left_constant_left : 
          bop_not_left_constant S rS bS → bop_not_left_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [s1 [s2 s3]] Q ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. apply andb_is_false_right. left. exact Q. Defined. 

Lemma bop_product_not_left_constant_right : bop_not_left_constant T rT bT → bop_not_left_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [t1 [t2 t3]]  Q ]. exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. apply andb_is_false_right. right. exact Q. Defined. 

Lemma bop_product_right_constant : bop_right_constant S rS bS → bop_right_constant T rT bT → bop_right_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  L R [s1 t1] [s2 t2] [s3 t3]; simpl. apply andb_is_true_right. split. apply L. apply R. Defined. 

Lemma bop_product_not_right_constant_left : bop_not_right_constant S rS bS → bop_not_right_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [s1 [s2 s3]] Q ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. apply andb_is_false_right. left. exact Q. Defined. 

Lemma bop_product_not_right_constant_right : bop_not_right_constant T rT bT → bop_not_right_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [t1 [t2 t3]] Q ]. exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. apply andb_is_false_right. right. exact Q. Defined. 

Lemma bop_product_anti_left : (bop_anti_left S rS bS) + (bop_anti_left T rT bT) → bop_anti_left (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right. left. apply P. right. apply P. Defined. 

Lemma bop_product_anti_right : (bop_anti_right S rS bS) + (bop_anti_right T rT bT) → bop_anti_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right. left. apply P. right. apply P. Defined. 

Lemma bop_product_not_anti_left : bop_not_anti_left S rS bS → bop_not_anti_left T rT bT → bop_not_anti_left (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [[ s1 s2 ] P ] [ [ t1 t2 ] Q ]. exists ((s1, t1), (s2, t2)); simpl. rewrite P, Q. simpl. reflexivity. Defined. 

Lemma bop_product_not_anti_right : bop_not_anti_right S rS bS → bop_not_anti_right T rT bT → bop_not_anti_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [s1 s2] P ] [ [t1 t2] Q ]. exists ((s1, t1), (s2, t2)); simpl. rewrite P, Q. simpl. reflexivity. Defined. 

(* Elimination *) 

Lemma bop_product_is_id_left : 
   ∀ (s : S ) (t : T ),  (bop_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_id S rS bS s.        
Proof. intros  s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_product_is_id_right : 
   ∀ (s : S ) (t : T ), (bop_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_id T rT bT t.  
Proof. intros  s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.                         


Lemma bop_product_is_ann_left : 
   ∀ (s : S ) (t : T ), (bop_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_ann S rS bS s.         
Proof. intros  s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_product_is_ann_right : 
   ∀ (s : S ) (t : T ), (bop_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_ann T rT bT t.  
Proof. intros  s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply andb_is_true_left in L. apply andb_is_true_left in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.       



Lemma bop_product_is_id : 
        ∀ (s : S) (t : T), bop_is_id S rS bS s -> bop_is_id T rT bT t -> bop_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  iS iT pS pT. 
       intros (s, t). compute. unfold brel_product, bop_product. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr, Tl, Tr. auto. 
Defined. 


Lemma bop_product_not_is_id_left : 
        ∀ (s : S) (t : T), bop_not_is_id S rS bS s -> bop_not_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (x, t). compute. destruct Nid as [H | H]. 
       rewrite H. left. reflexivity. 
       rewrite H. right. reflexivity. 
Defined. 

Lemma bop_product_not_is_id_right : 
        ∀ (s : S) (t : T), bop_not_is_id T rT bT t -> bop_not_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (s, x). compute. destruct Nid as [H | H]. 
       rewrite H. left. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
       rewrite H. right. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
Defined. 


Lemma bop_product_exists_id : 
        bop_exists_id S rS bS -> bop_exists_id T rT bT -> bop_exists_id (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_exists_id. intros  [iS pS] [iT pT]. exists (iS, iT). apply bop_product_is_id; auto. Defined. 

Lemma bop_product_not_exists_id : 
        (bop_not_exists_id S rS bS) + (bop_not_exists_id T rT bT) -> 
           bop_not_exists_id (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_not_exists_id, brel_product, bop_product. 
       intros  [pS | pT] (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. rewrite F. simpl. reflexivity. 
          exists (x, t). right. rewrite F. simpl. reflexivity. 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. rewrite F. apply andb_comm. 
          exists (s, x). right. rewrite F. apply andb_comm. 
Defined. 

Lemma bop_product_is_ann: 
        ∀ (s : S) (t : T), bop_is_ann S rS bS s -> bop_is_ann T rT bT t -> bop_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_ann. intros  iS iT pS pT. 
       intros (s, t). compute. unfold brel_product, bop_product. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr, Tl, Tr. auto. 
Defined. 


Lemma bop_product_not_is_ann_left : 
        ∀ (s : S) (t : T), bop_not_is_ann S rS bS s -> bop_not_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (x, t). compute. destruct Nid as [H | H]. 
       rewrite H. left. reflexivity. 
       rewrite H. right. reflexivity. 
Defined. 

Lemma bop_product_not_is_ann_right : 
        ∀ (s : S) (t : T), bop_not_is_ann T rT bT t -> bop_not_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (s, x). compute. destruct Nid as [H | H]; rewrite H. 
          left. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
          right. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
Defined. 

Lemma bop_product_exists_ann : 
        bop_exists_ann S rS bS -> bop_exists_ann T rT bT -> bop_exists_ann (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_exists_id. intros  [annS pS] [annT pT]. exists (annS, annT). apply bop_product_is_ann; auto. Defined. 

Lemma bop_product_not_exists_ann : 
        (bop_not_exists_ann S rS bS) + (bop_not_exists_ann T rT bT) -> 
           bop_not_exists_ann (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_not_exists_ann, brel_product, bop_product. 
       intros [pS | pT] (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. rewrite F. simpl. reflexivity. 
          exists (x, t). right. rewrite F. simpl. reflexivity. 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. rewrite F. apply andb_comm. 
          exists (s, x). right. rewrite F. apply andb_comm. 
Defined.


(* Decide *) 

Definition bop_product_idempotent_decide : 
     bop_idempotent_decidable S rS bS -> bop_idempotent_decidable T rT bT -> bop_idempotent_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_product_idempotent commS commT)
         | inr not_commT => inr _ (bop_product_not_idempotent_right not_commT)
         end 
       | inr not_commS   => inr _ (bop_product_not_idempotent_left not_commS)
       end.

Definition bop_product_commutative_decide : 
     bop_commutative_decidable S rS bS -> bop_commutative_decidable T rT bT -> bop_commutative_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_product_commutative commS commT)
         | inr not_commT => inr _ (bop_product_not_commutative_right not_commT)
         end 
       | inr not_commS   => inr _ (bop_product_not_commutative_left not_commS)
       end.


Definition bop_product_left_cancellative_decide : 
  bop_left_cancellative_decidable S rS bS -> bop_left_cancellative_decidable T rT bT ->
      bop_left_cancellative_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl canS => 
         match dT with 
         | inl canT     => inl _ (bop_product_left_cancellative canS canT)
         | inr not_canT => inr _ (bop_product_not_left_cancellative_right not_canT)
         end 
       | inr not_canS   => inr _ (bop_product_not_left_cancellative_left not_canS)
       end.

Definition bop_product_right_cancellative_decide : 
  bop_right_cancellative_decidable S rS bS -> bop_right_cancellative_decidable T rT bT -> 
     bop_right_cancellative_decidable (S * T) (rS <*> rT) (bS [*] bT) 
:= λ dS dT,  
       match dS with 
       | inl canS => 
         match dT with 
         | inl canT     => inl _ (bop_product_right_cancellative canS canT)
         | inr not_canT => inr _ (bop_product_not_right_cancellative_right not_canT)
         end 
       | inr not_canS   => inr _ (bop_product_not_right_cancellative_left not_canS)
       end.

Definition bop_product_is_left_decide : 
     bop_is_left_decidable S rS bS  → bop_is_left_decidable T rT bT  → bop_is_left_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl leftS => 
         match dT with 
         | inl leftT     => inl _ (bop_product_is_left leftS leftT)
         | inr not_leftT => inr _ (bop_product_not_is_left_right not_leftT)
         end 
       | inr not_leftS   => inr _ (bop_product_not_is_left_left not_leftS)
       end. 

Definition bop_product_is_right_decide : 
     bop_is_right_decidable S rS bS  → bop_is_right_decidable T rT bT  → bop_is_right_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl rightS => 
         match dT with 
         | inl rightT     => inl _ (bop_product_is_right rightS rightT)
         | inr not_rightT => inr _ (bop_product_not_is_right_right not_rightT)
         end 
       | inr not_rightS   => inr _ (bop_product_not_is_right_left not_rightS)
       end . 

Definition bop_product_exists_id_decide : 
     bop_exists_id_decidable S rS bS -> bop_exists_id_decidable T rT bT -> bop_exists_id_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_product_exists_id eS eT)
         | inr neT => inr _ (bop_product_not_exists_id (inr _ neT))
         end 
       | inr neS   => inr _ (bop_product_not_exists_id (inl _ neS))
       end. 

Definition bop_product_exists_ann_decide : 
     bop_exists_ann_decidable S rS bS -> bop_exists_ann_decidable T rT bT -> bop_exists_ann_decidable (S * T) (rS <*> rT) (bS [*] bT) 
:= λ dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_product_exists_ann eS eT)
         | inr neT => inr _ (bop_product_not_exists_ann (inr _ neT))
         end 
       | inr neS   => inr _ (bop_product_not_exists_ann (inl _ neS))
      end. 

Definition bop_product_left_constant_decide : 
     bop_left_constant_decidable S rS bS -> bop_left_constant_decidable T rT bT -> bop_left_constant_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl PS => 
         match dT with 
         | inl PT     => inl _ (bop_product_left_constant PS PT)
         | inr nPT => inr _ (bop_product_not_left_constant_right nPT)
         end 
       | inr nPS   => inr _ (bop_product_not_left_constant_left nPS)
       end.


Definition bop_product_right_constant_decide : 
     bop_right_constant_decidable S rS bS -> bop_right_constant_decidable T rT bT ->      
         bop_right_constant_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl PS => 
         match dT with 
         | inl PT  => inl _ (bop_product_right_constant PS PT)
         | inr nPT => inr _ (bop_product_not_right_constant_right nPT)
         end 
       | inr nPS   => inr _ (bop_product_not_right_constant_left nPS)
       end.

Definition bop_product_anti_left_decide : 
     bop_anti_left_decidable S rS bS -> bop_anti_left_decidable T rT bT -> 
        bop_anti_left_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
   match dS with 
   | inl PS => inl _ (bop_product_anti_left (inl _ PS))
   | inr nPS   => 
     match dT with 
     | inl PT     => inl _ (bop_product_anti_left (inr _ PT))
     | inr nPT => inr _ (bop_product_not_anti_left nPS nPT)
     end 
   end. 

Definition bop_product_anti_right_decide : 
     bop_anti_right_decidable S rS bS -> bop_anti_right_decidable T rT bT -> 
        bop_anti_right_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
   match dS with 
   | inl PS => inl _ (bop_product_anti_right (inl _ PS))
   | inr nPS   => 
     match dT with 
     | inl PT     => inl _ (bop_product_anti_right (inr _ PT))
     | inr nPT => inr _ (bop_product_not_anti_right nPS nPT)
     end 
   end.


Lemma bop_not_left_or_not_right : ∀ (U : Type) (r : brel U) (b : binary_op U) (u : U) (h : U -> U),
    brel_not_trivial U r h -> brel_symmetric U r -> brel_transitive U r ->     
    bop_is_left U r b -> bop_is_right U r b -> False. 
Proof. intros U r b u h Ph symU transU ilS irS.
       destruct (Ph u) as [L _].
       assert (H1 := ilS u (h u)).
       assert (H2 := irS u (h u)).
       apply symU in H1.
       assert (H3 := transU _ _ _ H1 H2).
       rewrite L in H3. 
       discriminate H3. 
Qed. 

Definition bop_product_selective_decide : 
     bop_is_left_decidable S rS bS  → 
     bop_is_left_decidable T rT bT  → 
     bop_is_right_decidable S rS bS  → 
     bop_is_right_decidable T rT bT  → 
        bop_selective_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dlS dlT drS drT,  
       match dlS, dlT, drS, drT with 
       |                 _,                  _,    inl is_right_S,      inl is_right_T => 
          inl _ (bop_product_selective (inr _ (is_right_S, is_right_T)))

       |     inl is_left_S,      inl is_left_T,                 _,                   _ => 
          inl _ (bop_product_selective (inl _ (is_left_S, is_left_T)))

       | inr not_is_left_S,                  _,                 _,  inr not_is_right_T => 
          inr _ (bop_product_not_selective (inl _ not_is_left_S) 
                                           (inr _ not_is_right_T) 
                                           (inl _ not_is_left_S, inr _ not_is_right_T))

       |                 _,  inr not_is_left_T, inr not_is_right_S,                  _ => 
          inr _ (bop_product_not_selective (inr _ not_is_right_S) 
                                           (inl _ not_is_left_T) 
                                           (inr _ not_is_left_T, inl _ not_is_right_S))
       (* NB : use of abort *) 
       |     inl is_left_S,                  _,    inl is_right_S,                   _ => 
          abort _ (bop_not_left_or_not_right _ _ _ wS f Pf symS transS is_left_S is_right_S)

       |                 _,      inl is_left_T,                 _,      inl is_right_T => 
          abort _ (bop_not_left_or_not_right _ _ _ wT g Pg symT transT is_left_T is_right_T)
       end. 


Definition bop_product_selective_decide_commutative_case : 
     bop_commutative S rS bS  → 
     bop_commutative T rT bT  → 
         bop_selective_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ commS commT,  
   bop_product_selective_decide 
      (inr _ (bop_commutative_implies_not_is_left _ _ _ wS f Pf symS transS commS))
      (inr _ (bop_commutative_implies_not_is_left _ _ _ wT g Pg symT transT commT))
      (inr _ (bop_commutative_implies_not_is_right _ _ _ wS f Pf symS transS commS))
      (inr _ (bop_commutative_implies_not_is_right _ _ _ wT g Pg symT transT commT)). 

End Product. 