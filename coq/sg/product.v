Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.product. 
Require Import CAS.coq.theory.facts. 

Section Theory.

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
Proof. intros L R (s1, t1) (s2, t2). simpl. compute in *. rewrite L, R. simpl. reflexivity. Defined. 

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
End Theory.

Section ACAS.

Definition sg_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_proofs S rS bS -> sg_proofs T rT bT -> 
        sg_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in  
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in   
{|
  A_sg_associative   := bop_product_associative S T rS rT bS bT (A_sg_associative _ _ _ sgS) (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_congruence _ _ _ sgS) (A_sg_congruence _ _ _ sgT) 
; A_sg_commutative_d := bop_product_commutative_decide S T rS rT bS bT s t (A_sg_commutative_d _ _ _ sgS) (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_product_selective_decide S T rS rT bS bT s f Pf symS transS t g Pg symT transT
                         (A_sg_is_left_d _ _ _ sgS) 
                         (A_sg_is_left_d _ _ _ sgT) 
                         (A_sg_is_right_d _ _ _ sgS) 
                         (A_sg_is_right_d _ _ _ sgT) 
; A_sg_is_left_d     := bop_product_is_left_decide S T rS rT bS bT s t (A_sg_is_left_d _ _ _ sgS) (A_sg_is_left_d _ _ _ sgT) 
; A_sg_is_right_d    := bop_product_is_right_decide S T rS rT bS bT s t (A_sg_is_right_d _ _ _ sgS) (A_sg_is_right_d _ _ _ sgT) 
; A_sg_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT s t (A_sg_idempotent_d _ _ _ sgS) (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_exists_id_d   := bop_product_exists_id_decide S T rS rT bS bT (A_sg_exists_id_d _ _ _ sgS) (A_sg_exists_id_d _ _ _ sgT) 
; A_sg_exists_ann_d  :=  bop_product_exists_ann_decide S T rS rT bS bT (A_sg_exists_ann_d _ _ _ sgS) (A_sg_exists_ann_d _ _ _ sgT) 
; A_sg_left_cancel_d    := bop_product_left_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_left_cancel_d _ _ _ sgS) 
                            (A_sg_left_cancel_d _ _ _ sgT) 
; A_sg_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_right_cancel_d _ _ _ sgS) 
                            (A_sg_right_cancel_d _ _ _ sgT) 
; A_sg_left_constant_d  := bop_product_left_constant_decide S T rS rT bS bT s t 
                            (A_sg_left_constant_d _ _ _ sgS) 
                            (A_sg_left_constant_d _ _ _ sgT) 
; A_sg_right_constant_d := bop_product_right_constant_decide S T rS rT bS bT s t 
                            (A_sg_right_constant_d _ _ _ sgS) 
                            (A_sg_right_constant_d _ _ _ sgT) 
; A_sg_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT (A_sg_anti_left_d _ _ _ sgS) (A_sg_anti_left_d _ _ _ sgT) 
; A_sg_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT (A_sg_anti_right_d _ _ _ sgS) (A_sg_anti_right_d _ _ _ sgT) 
|}.

Definition sg_C_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_C_proofs S rS bS -> sg_C_proofs T rT bT -> 
        sg_C_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in   
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in
let commS := A_sg_C_commutative _ _ _ sgS in
let commT := A_sg_C_commutative _ _ _ sgT in 
{|
  A_sg_C_associative   := bop_product_associative S T rS rT bS bT (A_sg_C_associative _ _ _ sgS) (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_C_congruence _ _ _ sgS) (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative   := bop_product_commutative S T rS rT bS bT commS commT 
; A_sg_C_selective_d   := inr _ (bop_product_not_selective S T rS rT bS bT 
                                   (inl _ (bop_commutative_implies_not_is_left _ _ _ s f Pf symS transS commS))
                                   (inl _ (bop_commutative_implies_not_is_left _ _ _ t g Pg symT transT commT))             
                                   (inl _ (bop_commutative_implies_not_is_left _ _ _ s f Pf symS transS commS),  
                                    inl _ (bop_commutative_implies_not_is_right _ _ _ s f Pf symS transS commS)))
; A_sg_C_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT s t (A_sg_C_idempotent_d _ _ _ sgS) (A_sg_C_idempotent_d _ _ _ sgT) 
; A_sg_C_exists_id_d   := bop_product_exists_id_decide S T rS rT bS bT (A_sg_C_exists_id_d _ _ _ sgS) (A_sg_C_exists_id_d _ _ _ sgT) 
; A_sg_C_exists_ann_d  := bop_product_exists_ann_decide S T rS rT bS bT (A_sg_C_exists_ann_d _ _ _ sgS) (A_sg_C_exists_ann_d _ _ _ sgT) 
; A_sg_C_left_cancel_d := bop_product_left_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_C_left_cancel_d _ _ _ sgS) 
                            (A_sg_C_left_cancel_d _ _ _ sgT) 
; A_sg_C_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_C_right_cancel_d _ _ _ sgS) 
                            (A_sg_C_right_cancel_d _ _ _ sgT) 
; A_sg_C_left_constant_d  := bop_product_left_constant_decide S T rS rT bS bT s t 
                            (A_sg_C_left_constant_d _ _ _ sgS) 
                            (A_sg_C_left_constant_d _ _ _ sgT) 
; A_sg_C_right_constant_d := bop_product_right_constant_decide S T rS rT bS bT s t
                            (A_sg_C_right_constant_d _ _ _ sgS) 
                            (A_sg_C_right_constant_d _ _ _ sgT) 
; A_sg_C_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT (A_sg_C_anti_left_d _ _ _ sgS) (A_sg_C_anti_left_d _ _ _ sgT) 
; A_sg_C_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT (A_sg_C_anti_right_d _ _ _ sgS) (A_sg_C_anti_right_d _ _ _ sgT) 
|}. 

Definition sg_CI_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CI_proofs S rS bS -> sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in   
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in
let commS := A_sg_CI_commutative _ _ _ sgS in
let commT := A_sg_CI_commutative _ _ _ sgT in 
{|
  A_sg_CI_associative   := bop_product_associative S T rS rT bS bT (A_sg_CI_associative _ _ _ sgS) (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_CI_congruence _ _ _ sgS) (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative   := bop_product_commutative S T rS rT bS bT (A_sg_CI_commutative _ _ _ sgS) (A_sg_CI_commutative _ _ _ sgT) 
; A_sg_CI_idempotent    := bop_product_idempotent S T rS rT bS bT (A_sg_CI_idempotent _ _ _ sgS) (A_sg_CI_idempotent _ _ _ sgT) 
; A_sg_CI_selective_d   := inr _ (bop_product_not_selective S T rS rT bS bT 
                                   (inl _ (bop_commutative_implies_not_is_left _ _ _ s f Pf symS transS commS))
                                   (inl _ (bop_commutative_implies_not_is_left _ _ _ t g Pg symT transT commT))             
                                   (inl _ (bop_commutative_implies_not_is_left _ _ _ s f Pf symS transS commS),  
                                    inl _ (bop_commutative_implies_not_is_right _ _ _ s f Pf symS transS commS)))
; A_sg_CI_exists_id_d   := bop_product_exists_id_decide S T rS rT bS bT (A_sg_CI_exists_id_d _ _ _ sgS) (A_sg_CI_exists_id_d _ _ _ sgT) 
; A_sg_CI_exists_ann_d  := bop_product_exists_ann_decide S T rS rT bS bT (A_sg_CI_exists_ann_d _ _ _ sgS) (A_sg_CI_exists_ann_d _ _ _ sgT) 
|}. 


Definition sg_CK_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CK_proofs S rS bS -> sg_CK_proofs T rT bT -> 
        sg_CK_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CK_associative        := bop_product_associative S T rS rT bS bT (A_sg_CK_associative _ _ _ sgS) (A_sg_CK_associative _ _ _ sgT) 
; A_sg_CK_congruence         := bop_product_congruence S T rS rT bS bT (A_sg_CK_congruence _ _ _ sgS) (A_sg_CK_congruence _ _ _ sgT) 
; A_sg_CK_commutative        := bop_product_commutative S T rS rT bS bT (A_sg_CK_commutative _ _ _ sgS) (A_sg_CK_commutative _ _ _ sgT) 
; A_sg_CK_left_cancel        := bop_product_left_cancellative S T rS rT bS bT (A_sg_CK_left_cancel _ _ _ sgS) (A_sg_CK_left_cancel _ _ _ sgT) 

; A_sg_CK_exists_id_d        := bop_product_exists_id_decide S T rS rT bS bT (A_sg_CK_exists_id_d _ _ _ sgS) (A_sg_CK_exists_id_d _ _ _ sgT) 
; A_sg_CK_anti_left_d        := bop_product_anti_left_decide S T rS rT bS bT (A_sg_CK_anti_left_d _ _ _ sgS) (A_sg_CK_anti_left_d _ _ _ sgT) 
; A_sg_CK_anti_right_d       := bop_product_anti_right_decide S T rS rT bS bT (A_sg_CK_anti_right_d _ _ _ sgS) (A_sg_CK_anti_right_d _ _ _ sgT) 
|}. 



Definition A_sg_product : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_eq S sgS in
let eqvT := A_sg_eq T sgT in
let bS   := A_sg_bop S sgS in
let bT   := A_sg_bop T sgT in 
{| 
     A_sg_eq        := A_eqv_product S T eqvS eqvT
   ; A_sg_bop       := bop_product bS bT
   ; A_sg_proofs := sg_proofs_product S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT)
   ; A_sg_bop_ast   := Ast_bop_product (A_sg_bop_ast S sgS, A_sg_bop_ast T sgT)                                                                 
   ; A_sg_ast       := Ast_sg_product (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 


Definition A_sg_C_product : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_C_eqv S sgS in
let eqvT := A_sg_C_eqv T sgT in
let bS   := A_sg_C_bop S sgS in
let bT   := A_sg_C_bop T sgT in 
{| 
     A_sg_C_eqv    := A_eqv_product S T eqvS eqvT  
   ; A_sg_C_bop    := bop_product bS bT
   ; A_sg_C_proofs := sg_C_proofs_product S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)                            
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_bop_ast   := Ast_bop_product (A_sg_C_bop_ast S sgS, A_sg_C_bop_ast T sgT)                            
   ; A_sg_C_ast       := Ast_sg_C_product (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 

Definition A_sg_CI_product : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_CI_eqv S sgS in
let eqvT := A_sg_CI_eqv T sgT in
let bS   := A_sg_CI_bop S sgS in
let bT   := A_sg_CI_bop T sgT in 
{| 
     A_sg_CI_eqv    := A_eqv_product S T eqvS eqvT 
   ; A_sg_CI_bop    := bop_product bS bT 
   ; A_sg_CI_proofs := sg_CI_proofs_product S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT)
   ; A_sg_CI_bop_ast   := Ast_bop_product (A_sg_CI_bop_ast S sgS, A_sg_CI_bop_ast T sgT)                                                       
   ; A_sg_CI_ast       := Ast_sg_CI_product (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CK_product : ∀ (S T : Type),  A_sg_CK S -> A_sg_CK T -> A_sg_CK (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_CK_eqv S sgS in
let eqvT := A_sg_CK_eqv T sgT in
let bS   := A_sg_CK_bop S sgS in
let bT   := A_sg_CK_bop T sgT in 
{| 
     A_sg_CK_eqv    := A_eqv_product S T eqvS eqvT 
   ; A_sg_CK_bop    := bop_product bS bT 
   ; A_sg_CK_proofs := sg_CK_proofs_product S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)
                           (A_sg_CK_proofs S sgS) 
                           (A_sg_CK_proofs T sgT)
   ; A_sg_CK_bop_ast   := Ast_bop_product (A_sg_CK_bop_ast S sgS, A_sg_CK_bop_ast T sgT)                             
   ; A_sg_CK_ast       := Ast_sg_CK_product (A_sg_CK_ast S sgS, A_sg_CK_ast T sgT)
   |}. 



  
End ACAS.

Section CAS.

Definition check_commutative_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_commutative (S := S)) -> 
             (check_commutative (S := T)) -> 
                (check_commutative (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative 
      | Certify_Not_Commutative (s1, s2), _      => Certify_Not_Commutative ((s1, t), (s2, t))
      | _, Certify_Not_Commutative (t1, t2)      => Certify_Not_Commutative ((s, t1), (s, t2))
      end.


Definition check_left_cancellative_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_left_cancellative (S := S)) -> 
             (check_left_cancellative (S := T)) -> 
                (check_left_cancellative (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Left_Cancellative, Certify_Left_Cancellative => Certify_Left_Cancellative
      | Certify_Not_Left_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Left_Cancellative ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Left_Cancellative ((s, t1), ((s, t2), (s, t3)))
      end. 


Definition check_right_cancellative_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_right_cancellative (S := S)) -> 
             (check_right_cancellative (S := T)) -> 
                (check_right_cancellative (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Right_Cancellative , Certify_Right_Cancellative => Certify_Right_Cancellative
      | Certify_Not_Right_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Right_Cancellative ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Right_Cancellative ((s, t1), ((s, t2), (s, t3)))
      end .

Definition check_left_constant_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_left_constant (S := S)) -> 
             (check_left_constant (S := T)) -> 
                (check_left_constant (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Left_Constant, Certify_Left_Constant => Certify_Left_Constant
      | Certify_Not_Left_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Left_Constant ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Constant (t1, (t2, t3))  => 
           Certify_Not_Left_Constant ((s, t1), ((s, t2), (s, t3)))
      end .



Definition check_right_constant_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_right_constant (S := S)) -> 
             (check_right_constant (S := T)) -> 
                (check_right_constant (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Right_Constant, Certify_Right_Constant => Certify_Right_Constant
      | Certify_Not_Right_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Right_Constant ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Constant (t1, (t2, t3))  => 
           Certify_Not_Right_Constant ((s, t1), ((s, t2), (s, t3)))
      end .


Definition check_anti_left_product : 
   ∀ {S T : Type},  check_anti_left (S := S) -> check_anti_left (S := T) -> check_anti_left (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Anti_Left => Certify_Anti_Left 
   | Certify_Not_Anti_Left (s1, s2)  => 
     match dT with 
     | Certify_Anti_Left => Certify_Anti_Left 
     | Certify_Not_Anti_Left (t1, t2)  => Certify_Not_Anti_Left ((s1, t1), (s2, t2))
     end 
   end. 

Definition check_anti_right_product : 
   ∀ {S T : Type},  check_anti_right (S := S) -> check_anti_right (S := T) -> check_anti_right (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Anti_Right  => Certify_Anti_Right 
   | Certify_Not_Anti_Right (s1, s2)  => 
     match dT with 
     | Certify_Anti_Right => Certify_Anti_Right 
     | Certify_Not_Anti_Right (t1, t2)  => Certify_Not_Anti_Right ((s1, t1), (s2, t2))
     end 
   end. 

Definition check_idempotent_product : ∀ {S T : Type}
             (s : S) 
             (t : T), 
             (check_idempotent (S := S)) -> 
             (check_idempotent (S := T)) -> 
                (check_idempotent (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent (s1, t) 
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent (s, t1) 
      end.

Definition check_is_left_product : ∀ {S T : Type}
             (s : S) 
             (t : T), 
             (check_is_left (S := S)) -> 
             (check_is_left (S := T)) -> 
                (check_is_left (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Is_Left, Certify_Is_Left => Certify_Is_Left 
      | Certify_Not_Is_Left (s1, s2), _  => Certify_Not_Is_Left ((s1, t), (s2, t))
      | _, Certify_Not_Is_Left (t1, t2)  => Certify_Not_Is_Left ((s, t1), (s, t2))
      end.  


Definition check_is_right_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_is_right (S := S)) -> 
             (check_is_right (S := T)) -> 
                (check_is_right (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Is_Right, Certify_Is_Right => Certify_Is_Right 
      | Certify_Not_Is_Right (s1, s2), _   => Certify_Not_Is_Right ((s1, t), (s2, t))
      | _, Certify_Not_Is_Right (t1, t2)   => Certify_Not_Is_Right ((s, t1), (s, t2))
      end.


Definition check_not_selective_product : ∀ {S T : Type},
             (assert_not_is_left (S := S)) -> 
             (assert_not_is_right (S := T)) -> (check_selective (S := (S * T)))
:= λ {S T} nlS nrT,  
     match nlS, nrT with 
     | Assert_Not_Is_Left (s1, s2), Assert_Not_Is_Right (t1, t2) => 
          Certify_Not_Selective ((s1, t1), (s2, t2))  
     end. 


Definition check_selective_product : ∀ {S T : Type}
             (s : S) 
             (t : T), 
             (check_is_left (S := S)) -> 
             (check_is_left (S := T)) -> 
             (check_is_right (S := S)) -> 
             (check_is_right (S := T)) -> 
                (check_selective (S := (S * T)))
:= λ {S T} s t clS clT crS crT,  
     match clS with 
     | Certify_Not_Is_Left (s1, s2) => 
       (* NOT LEFT S *) 
       match crS with 
       | Certify_Is_Right =>  
         (* RIGHT S *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *)   Certify_Selective 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *) Certify_Not_Selective ((s1, t1), (s2, t2)) 
           end 
       | Certify_Not_Is_Right (s3, s4) =>  
          (* NOT RIGHT S *)   (* extra case *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) (* MUST BE NOT LEFT T *) 
              match clT with 
              | Certify_Is_Left => (* NOT POSSIBLE *) Certify_Selective 
              | Certify_Not_Is_Left (t1, t2) => Certify_Not_Selective ((s3, t1), (s4, t2))
              end 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *)  
             match clT with  (* why needed ??  to match proof!  clean up! *) 
             | Certify_Is_Left => Certify_Not_Selective ((s1, t1), (s2, t2))  
             | Certify_Not_Is_Left (t3, t4) => Certify_Not_Selective ((s1, t1), (s2, t2))
             end 
           end 
       end 
     | Certify_Is_Left => 
       (* LEFT S *) 
       match clT with 
       | Certify_Is_Left =>  
         (* LEFT T *) Certify_Selective
       | Certify_Not_Is_Left (t1, t2) =>  
         (* NOT LEFT T *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) 
                match crS with 
                | Certify_Is_Right =>   (* CAN'T HAPPEN with not-trivial S *) 
                  (* RIGHT S *)  Certify_Selective 
                | Certify_Not_Is_Right (s1, s2) => 
                  (* NOT RIGHT S *) Certify_Not_Selective ((s1, t1), (s2, t2))  
                end 
           | Certify_Not_Is_Right (t3, t4) => 
             (* NOT RIGHT T *) (* extra case *) 
             match crS with 
             | Certify_Is_Right => 
               (* RIGHT S *) (* MUST BE NOT LEFT S *) 
                match clS with 
                | Certify_Is_Left  => (* NOT POSSIBLE *) Certify_Selective 
                | Certify_Not_Is_Left  (s1, s2) => Certify_Not_Selective ((s1, t3), (s2, t4))
                end 
             | Certify_Not_Is_Right (s1, s2) => 
               (* NOT RIGHT S *)  Certify_Not_Selective ((s1, t1), (s2, t2))  
             end 
          end 
       end 
     end.



Definition check_selective_product_commutative_case : ∀ {S T : Type}
             (rS : brel S) 
             (rT : brel T) 
             (bS : binary_op S) 
             (bT : binary_op T) 
             (s : S) (f : S -> S)
             (t : T) (g : T -> T), 
                (check_selective (S := (S * T)))
:= λ {S T} rS rT bS bT s f t g,  
     check_selective_product s t 
        (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS s f))
        (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT t g))
        (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS s f))
        (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT t g)). 

Definition check_exists_id_product : ∀ {S T : Type}, 
             (check_exists_id (S := S)) -> (check_exists_id (S := T)) -> (check_exists_id (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t  => Certify_Exists_Id (s, t) 
      | Certify_Not_Exists_Id , _                 => Certify_Not_Exists_Id
      | _, Certify_Not_Exists_Id                  => Certify_Not_Exists_Id
      end. 

Definition check_exists_ann_product : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := T)) -> (check_exists_ann (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann 
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann 
      end. 

Definition sg_certs_product : ∀ {S T : Type},  S -> T -> sg_certificates (S := S) -> sg_certificates (S := T) -> sg_certificates (S := (S * T)) 
:= λ {S T} wS wT cS cT,  
{|
  sg_associative   := Assert_Associative   
; sg_congruence    := Assert_Bop_Congruence   
; sg_commutative_d := check_commutative_product wS wT 
                         (sg_commutative_d cS) 
                         (sg_commutative_d cT)
; sg_selective_d   := check_selective_product wS wT 
                         (sg_is_left_d cS) 
                         (sg_is_left_d cT)
                         (sg_is_right_d cS) 
                         (sg_is_right_d cT)
; sg_is_left_d     := check_is_left_product wS wT 
                         (sg_is_left_d cS) 
                         (sg_is_left_d cT)
; sg_is_right_d    := check_is_right_product wS wT 
                         (sg_is_right_d cS) 
                         (sg_is_right_d cT)
; sg_idempotent_d  := check_idempotent_product wS wT 
                         (sg_idempotent_d cS) 
                         (sg_idempotent_d cT)
; sg_exists_id_d   := check_exists_id_product 
                         (sg_exists_id_d cS) 
                         (sg_exists_id_d cT)
; sg_exists_ann_d  := check_exists_ann_product 
                         (sg_exists_ann_d cS) 
                         (sg_exists_ann_d cT)
; sg_left_cancel_d    := check_left_cancellative_product wS wT 
                          (sg_left_cancel_d cS)
                          (sg_left_cancel_d cT)
; sg_right_cancel_d   := check_right_cancellative_product wS wT 
                          (sg_right_cancel_d cS)
                          (sg_right_cancel_d cT)
; sg_left_constant_d  := check_left_constant_product wS wT 
                          (sg_left_constant_d cS)
                          (sg_left_constant_d cT)
; sg_right_constant_d := check_right_constant_product wS wT 
                          (sg_right_constant_d cS)
                          (sg_right_constant_d cT)
; sg_anti_left_d      := check_anti_left_product 
                         (sg_anti_left_d cS) 
                         (sg_anti_left_d cT)
; sg_anti_right_d     := check_anti_right_product 
                         (sg_anti_right_d cS) 
                         (sg_anti_right_d cT)
|}.


Definition sg_CK_certs_product : ∀ {S T : Type},  sg_CK_certificates (S := S) -> sg_CK_certificates (S := T) -> sg_CK_certificates (S := (S * T)) 
:= λ {S T} cS cT,  
{|
  sg_CK_associative   := Assert_Associative   
; sg_CK_congruence    := Assert_Bop_Congruence   
; sg_CK_commutative   := Assert_Commutative   
; sg_CK_left_cancel   := Assert_Left_Cancellative   
; sg_CK_exists_id_d   := check_exists_id_product 
                         (sg_CK_exists_id_d cS) 
                         (sg_CK_exists_id_d cT)
; sg_CK_anti_left_d   := check_anti_left_product 
                         (sg_CK_anti_left_d cS) 
                         (sg_CK_anti_left_d cT)
; sg_CK_anti_right_d  := check_anti_right_product 
                         (sg_CK_anti_right_d cS) 
                         (sg_CK_anti_right_d cT)


|}.

Definition sg_C_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) ->
                                                  S -> (S -> S) -> T ->(T -> T) -> 
                                                 sg_C_certificates (S := S) -> sg_C_certificates (S := T) -> sg_C_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT s f t g cS cT,  
{|
  sg_C_associative   := Assert_Associative   
; sg_C_congruence    := Assert_Bop_Congruence   
; sg_C_commutative   := Assert_Commutative   
; sg_C_selective_d   := check_selective_product s t
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS s f))
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT t g))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS s f))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT t g))
; sg_C_idempotent_d  := check_idempotent_product s t
                         (sg_C_idempotent_d cS) 
                         (sg_C_idempotent_d cT)
; sg_C_exists_id_d   := check_exists_id_product 
                         (sg_C_exists_id_d cS) 
                         (sg_C_exists_id_d cT)
; sg_C_exists_ann_d  := check_exists_ann_product 
                         (sg_C_exists_ann_d cS) 
                         (sg_C_exists_ann_d cT)
; sg_C_left_cancel_d    := check_left_cancellative_product s t
                          (sg_C_left_cancel_d cS)
                          (sg_C_left_cancel_d cT)
; sg_C_right_cancel_d   := check_right_cancellative_product s t
                          (sg_C_right_cancel_d cS)
                          (sg_C_right_cancel_d cT)
; sg_C_left_constant_d  := check_left_constant_product s t
                          (sg_C_left_constant_d cS)
                          (sg_C_left_constant_d cT)
; sg_C_right_constant_d := check_right_constant_product s t
                          (sg_C_right_constant_d cS)
                          (sg_C_right_constant_d cT)
; sg_C_anti_left_d      := check_anti_left_product 
                         (sg_C_anti_left_d cS) 
                         (sg_C_anti_left_d cT)
; sg_C_anti_right_d     := check_anti_right_product 
                         (sg_C_anti_right_d cS) 
                         (sg_C_anti_right_d cT)

|}.

Definition sg_CI_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) ->
                                                  S -> (S -> S) -> T -> (T -> T) -> 
                                                  sg_CI_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT s f t g cS cT,  
{|
  sg_CI_associative   := Assert_Associative   
; sg_CI_congruence    := Assert_Bop_Congruence   
; sg_CI_commutative   := Assert_Commutative   
; sg_CI_idempotent  := Assert_Idempotent   
; sg_CI_selective_d   := check_selective_product s t
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS s f))
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT t g))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS s f))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT t g))
; sg_CI_exists_id_d   := check_exists_id_product (sg_CI_exists_id_d cS) (sg_CI_exists_id_d cT)
; sg_CI_exists_ann_d  := check_exists_ann_product (sg_CI_exists_ann_d cS) (sg_CI_exists_ann_d cT)
|}.


Definition sg_product : ∀ {S T : Type},  @sg S -> @sg T -> @sg (S * T)
:= λ {S T} sgS sgT, 
   {| 
     sg_eq     := eqv_product (sg_eq sgS) (sg_eq sgT) 
   ; sg_bop    := bop_product (sg_bop sgS) (sg_bop sgT) 
   ; sg_certs := sg_certs_product 
                    (eqv_witness (sg_eq sgS)) 
                    (eqv_witness (sg_eq sgT)) 
                    (sg_certs sgS) 
                    (sg_certs sgT)
   ; sg_bop_ast := Ast_bop_product (sg_bop_ast sgS, sg_bop_ast sgT)                        
   ; sg_ast    := Ast_sg_product (sg_ast sgS, sg_ast sgT)
   |}. 


Definition sg_CK_product : ∀ {S T : Type},  @sg_CK S -> @sg_CK T -> @sg_CK (S * T)
:= λ {S T} sgS sgT, 
   {| 
     sg_CK_eqv     := eqv_product (sg_CK_eqv sgS) (sg_CK_eqv sgT) 
   ; sg_CK_bop     := bop_product (sg_CK_bop sgS) (sg_CK_bop sgT) 
   ; sg_CK_certs   := sg_CK_certs_product (sg_CK_certs sgS) (sg_CK_certs sgT)
   ; sg_CK_bop_ast := Ast_bop_product (sg_CK_bop_ast sgS, sg_CK_bop_ast sgT)                             
   ; sg_CK_ast     := Ast_sg_CK_product (sg_CK_ast sgS, sg_CK_ast sgT)
   |}.

Definition sg_C_product : ∀ {S T : Type},  @sg_C S  -> @sg_C T -> @sg_C (S * T)
:= λ {S T} sgS sgT, 
   {| 
     sg_C_eqv    := eqv_product  (sg_C_eqv sgS) (sg_C_eqv sgT) 
   ; sg_C_bop    := bop_product (sg_C_bop sgS) (sg_C_bop sgT)                            
   ; sg_C_certs := sg_C_certs_product (eqv_eq (sg_C_eqv sgS)) (eqv_eq (sg_C_eqv sgT))
                                      (sg_C_bop sgS) (sg_C_bop sgT) 
                                      (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS))
                                      (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT)) 
                                      (sg_C_certs sgS) (sg_C_certs sgT)
   ; sg_C_bop_ast := Ast_bop_product (sg_C_bop_ast sgS, sg_C_bop_ast sgT)                                                                   
   ; sg_C_ast       := Ast_sg_C_product (sg_C_ast sgS, sg_C_ast sgT)
   |}. 


Definition sg_CI_product : ∀ {S T : Type},  sg_CI (S := S) -> sg_CI (S := T) -> sg_CI (S := (S * T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CI_eqv    := eqv_product (sg_CI_eqv sgS) (sg_CI_eqv sgT) 
   ; sg_CI_bop       := bop_product (sg_CI_bop sgS) (sg_CI_bop sgT) 
   ; sg_CI_certs := sg_CI_certs_product (eqv_eq (sg_CI_eqv sgS)) (eqv_eq (sg_CI_eqv sgT))
                                        (sg_CI_bop sgS) (sg_CI_bop sgT)
                                        (eqv_witness (sg_CI_eqv sgS))
                                        (eqv_new (sg_CI_eqv sgS))                                         
                                        (eqv_witness (sg_CI_eqv sgT))
                                        (eqv_new (sg_CI_eqv sgT))                                         
                                        (sg_CI_certs sgS) 
                                        (sg_CI_certs sgT)
   ; sg_CI_bop_ast := Ast_bop_product (sg_CI_bop_ast sgS, sg_CI_bop_ast sgT)                                                                     
   ; sg_CI_ast       := Ast_sg_CI_product (sg_CI_ast sgS, sg_CI_ast sgT)
   |}. 






End CAS.

Section Verify.

Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_check_commutative_product : 
      ∀ (dS : bop_commutative_decidable S rS bS) (dT : bop_commutative_decidable T rT bT),
        
         check_commutative_product wS wT 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_commutative_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined. 

Lemma correct_check_is_left_product : 
      ∀ (dS : bop_is_left_decidable S rS bS) (dT : bop_is_left_decidable T rT bT),
         
         check_is_left_product wS wT 
            (p2c_is_left_check S rS bS dS)
            (p2c_is_left_check T rT bT dT)
         = 
         p2c_is_left_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_is_left_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS ] ] [cT | [ [t3 t4] ncT ]]; compute; reflexivity. Defined. 

Lemma correct_check_is_right_product : 
      ∀ (dS : bop_is_right_decidable S rS bS) (dT : bop_is_right_decidable T rT bT),
         
         check_is_right_product wS wT
            (p2c_is_right_check S rS bS dS)
            (p2c_is_right_check T rT bT dT)
         = 
         p2c_is_right_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_is_right_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_product : 
      ∀ (dS : bop_idempotent_decidable S rS bS)  (dT : bop_idempotent_decidable T rT bT),
        
         check_idempotent_product wS wT 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_idempotent_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [s3 niS]] [cT | [t3 niT]]; compute; reflexivity. Defined. 


Lemma correct_check_exists_id_product : 
      ∀ (dS : bop_exists_id_decidable S rS bS) (dT : bop_exists_id_decidable T rT bT),
         
         check_exists_id_product 
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_id_decide S T rS rT bS bT dS dT).
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_exists_ann_product : 
      ∀ (dS : bop_exists_ann_decidable S rS bS) (dT : bop_exists_ann_decidable T rT bT),
         
         check_exists_ann_product 
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT)
         =
         p2c_exists_ann_check (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_ann_decide S T rS rT bS bT dS dT).
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_selective_product : 
      ∀ (dlS : bop_is_left_decidable S rS bS)
         (dlT : bop_is_left_decidable T rT bT)
         (drS : bop_is_right_decidable S rS bS)
         (drT : bop_is_right_decidable T rT bT),
         p2c_selective_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_selective_decide S T rS rT bS bT wS f Pf symS transS wT g Pg symT transT dlS dlT drS drT)
         = 
         check_selective_product wS wT 
            (p2c_is_left_check S rS bS dlS)
            (p2c_is_left_check T rT bT dlT)
            (p2c_is_right_check S rS bS drS)
            (p2c_is_right_check T rT bT drT). 
Proof. 
       intros [ilS | [ [s3 s4] nilS]] [ilT | [ [t3 t4] nilT]]
              [irS | [ [s5 s6] nirS]] [irT | [ [t5 t6] nirT]]; 
          compute; auto. 
          assert (F := bop_not_left_or_not_right S rS bS wS f Pf symS transS ilS irS). 
             elim F. 
          assert (F := bop_not_left_or_not_right T rT bT wT g Pg symT transT ilT irT). 
             elim F. 
Defined. 



(* what abstractions where broken here? *) 
Lemma correct_check_selective_commutative_product : 
   ∀ (syS : brel_symmetric S rS) (syT : brel_symmetric T rT) (trnS : brel_transitive S rS) (trnT : brel_transitive T rT) 
     (pS : bop_commutative S rS bS) (pT : bop_commutative T rT bT), 
     
   check_selective_product wS wT (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS wS f))
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT wT g))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS wS f))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT wT g))
  = 
  p2c_selective_check (S * T) (brel_product rS rT) (bop_product bS bT)
                         (inr
                         (bop_product_not_selective S T rS rT bS bT
                              (inl (facts.bop_commutative_implies_not_is_left S rS bS wS f Pf syS trnS pS))
                              (inl (facts.bop_commutative_implies_not_is_left T rT bT wT g Pg syT trnT pT))
                              (inl (facts.bop_commutative_implies_not_is_left S rS bS wS f Pf syS trnS pS), 
                               inl (facts.bop_commutative_implies_not_is_right S rS bS wS f Pf syS trnS pS)))).
Admitted.
(*
Proof. intros syS syT trnS trnT pS pT. unfold p2c_selective_check.
       unfold check_selective_product.
       unfold cef_commutative_implies_not_is_left, cef_commutative_implies_not_is_right.
       case_eq(rS (bS (f wS) wS) wS); intro J1; case_eq(rT (bT (g wT) wT) wT); intro J2.
       unfold bop_commutative_implies_not_is_left.
       unfold cef_commutative_implies_not_is_left, cef_commutative_implies_not_is_right.
       unfold bop_product_not_selective. simpl.
*)        

Lemma correct_check_left_cancel_product : 
      ∀ (dS : bop_left_cancellative_decidable S rS bS) (dT : bop_left_cancellative_decidable T rT bT),
         
         p2c_left_cancel_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_left_cancellative_decide S T rS rT bS bT wS refS wT refT dS dT)
         = 
         check_left_cancellative_product  wS wT 
            (p2c_left_cancel_check S rS bS dS)
            (p2c_left_cancel_check T rT bT dT). 
Proof. intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; compute; reflexivity. Defined. 

Lemma correct_check_right_cancel_product : 
      ∀ (dS : bop_right_cancellative_decidable S rS bS) (dT : bop_right_cancellative_decidable T rT bT),
         
         p2c_right_cancel_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_right_cancellative_decide S T rS rT bS bT wS refS wT refT dS dT)
         = 
         check_right_cancellative_product wS wT 
            (p2c_right_cancel_check S rS bS dS)
            (p2c_right_cancel_check T rT bT dT). 
Proof. intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; compute; reflexivity. Defined. 

Lemma correct_check_left_constant_product : 
      ∀ (dS : bop_left_constant_decidable S rS bS) (dT : bop_left_constant_decidable T rT bT),
         
         p2c_left_constant_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_left_constant_decide S T rS rT bS bT wS wT dS dT)
         = 
         check_left_constant_product wS wT 
            (p2c_left_constant_check S rS bS dS)
            (p2c_left_constant_check T rT bT dT).
Proof. intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_right_constant_product : 
      ∀ (dS : bop_right_constant_decidable S rS bS) (dT : bop_right_constant_decidable T rT bT),
         
         p2c_right_constant_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_right_constant_decide S T rS rT bS bT wS wT dS dT)
         = 
         check_right_constant_product wS wT 
            (p2c_right_constant_check S rS bS dS)
            (p2c_right_constant_check T rT bT dT).
Proof. intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_anti_left_product : 
      ∀ (dS : bop_anti_left_decidable S rS bS) (dT : bop_anti_left_decidable T rT bT),
         
         p2c_anti_left_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_anti_left_decide S T rS rT bS bT dS dT)
         = 
         check_anti_left_product 
            (p2c_anti_left_check S rS bS dS)
            (p2c_anti_left_check T rT bT dT).
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_anti_right_product : 
      ∀ (dS : bop_anti_right_decidable S rS bS)
         (dT : bop_anti_right_decidable T rT bT),
         p2c_anti_right_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_anti_right_decide S T rS rT bS bT dS dT)
         = 
         check_anti_right_product 
            (p2c_anti_right_check S rS bS dS)
            (p2c_anti_right_check T rT bT dT).
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined.


End ChecksCorrect. 

Section ProofsCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable eS : eqv_proofs S rS.
  Variable eT : eqv_proofs T rT. 


Lemma correct_sg_certs_product : 
      ∀ (pS : sg_proofs S rS bS) (pT : sg_proofs T rT bT),
        
      sg_certs_product wS wT (P2C_sg S rS bS pS) (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S * T) (brel_product rS rT) 
                     (bop_product bS bT) 
                     (sg_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_proofs_product, sg_certs_product, P2C_sg; simpl. 
       rewrite correct_check_idempotent_product.
       rewrite correct_check_selective_product.              
       rewrite correct_check_is_right_product. 
       rewrite correct_check_is_left_product. 
       rewrite correct_check_commutative_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product. 
       rewrite <- correct_check_anti_left_product. 
       rewrite <- correct_check_anti_right_product.
       rewrite <- correct_check_left_constant_product.       
       rewrite <- correct_check_right_constant_product.        
       rewrite correct_check_left_cancel_product. 
       rewrite correct_check_right_cancel_product. 
       reflexivity. 
Defined.

Lemma correct_sg_CI_certs_product : 
      ∀ (pS : sg_CI_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
        
      sg_CI_certs_product rS rT bS bT wS f wT g (P2C_sg_CI S rS bS pS) (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S * T) (brel_product rS rT) 
                        (bop_product bS bT) 
                       (sg_CI_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CI_proofs_product, sg_CI_certs_product, P2C_sg_CI.
       unfold A_sg_CI_selective_d. (* broken abstraction *) 
       destruct eS. destruct eT. 
       rewrite <- correct_check_selective_commutative_product; auto. 
       simpl. 
       rewrite correct_check_exists_id_product; auto. 
       rewrite correct_check_exists_ann_product; auto.
Defined. 


Lemma correct_sg_C_certs_product : 
      ∀ (pS : sg_C_proofs S rS bS) (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_product rS rT bS bT wS f wT g (P2C_sg_C S rS bS pS) (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S * T) (brel_product rS rT) 
                       (bop_product bS bT) 
                       (sg_C_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_product, sg_C_certs_product, P2C_sg_C.
       unfold A_sg_C_selective_d. (* broken abstraction *)
       destruct eS. destruct eT.        
       rewrite <- correct_check_selective_commutative_product; auto. 
       simpl. 
       rewrite correct_check_idempotent_product; auto.
       rewrite correct_check_exists_ann_product; auto.
       rewrite correct_check_exists_id_product; auto.  
       rewrite <- correct_check_anti_left_product; auto. 
       rewrite <- correct_check_anti_right_product; auto.
       rewrite <- correct_check_left_constant_product; auto.       
       rewrite <- correct_check_right_constant_product; auto.        
       rewrite correct_check_left_cancel_product; auto. 
       rewrite correct_check_right_cancel_product; auto. 
Defined. 


Lemma  correct_sg_CK_certs_product : 
      ∀ (pS : sg_CK_proofs S rS bS) (pT : sg_CK_proofs T rT bT),
        
      sg_CK_certs_product (P2C_sg_CK S rS bS pS) (P2C_sg_CK T rT bT pT) 
      = 
      P2C_sg_CK (S * T) 
         (brel_product rS rT) 
         (bop_product bS bT) 
         (sg_CK_proofs_product S T rS rT bS bT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CK_proofs_product, sg_CK_certs_product, P2C_sg_CK; simpl. 
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_anti_left_product. 
       rewrite correct_check_anti_right_product. 
       reflexivity. 
Defined.

End ProofsCorrect. 

Theorem correct_sg_product :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_product (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_product, A2C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_CK_product :
      ∀ (S T : Type) (sgS : A_sg_CK S) (sgT : A_sg_CK T), 
         sg_CK_product (A2C_sg_CK S sgS) (A2C_sg_CK T sgT) 
         = 
         A2C_sg_CK (S * T) (A_sg_CK_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CK_product, A2C_sg_CK; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CK_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_CI_product :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_product (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_product, A2C_sg_CI; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CI_certs_product. 
       reflexivity. 
Qed. 

Theorem correct_sg_C_product :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_product (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_product, A2C_sg_C; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_C_certs_product. 
       reflexivity. 
Qed. 

 
End Verify.   
  