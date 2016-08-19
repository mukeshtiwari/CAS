Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts.


(* note similarity in this and next lemma .... 

   ∀ (s : finite_set S) (t1 t2 : S),
   r t1 t2 = true → in_set S r s t1 = true → in_set S r s t2 = true
*) 
Lemma in_set_right_congruence : 
       ∀ (S : Type) (r : brel S), 
       brel_symmetric S r -> brel_transitive S r -> 
          brel2_right_congruence (finite_set S) S r (in_set S r). 
Proof. intros S r symS transS. unfold brel2_right_congruence. 
       induction s; intros t1 t2 H1 H2. 
       unfold in_set in H2. discriminate.        
       unfold in_set. fold in_set. 
       unfold in_set in H2. fold in_set in H2. 
       apply orb_is_true_left in H2. destruct H2 as [H2|H2]. 
       apply symS in H1. rewrite (transS t2 t1 a H1 H2). simpl. reflexivity. 
       rewrite (IHs _ _ H1 H2). rewrite orb_comm. simpl. reflexivity. 
Defined. 

(* 
   ∀ (X : finite_set S) (s t : S),
   r s t = true → in_set S r X s = in_set S r X t
*) 
Lemma in_set_bProp_congruence : 
       ∀ (S : Type) (r : brel S),  
       brel_symmetric S r -> brel_transitive S r -> 
          ∀ (X : finite_set S), bProp_congruence S r (in_set S r X). 
Proof. intros S r symS transS. unfold bProp_congruence. 
       induction X. auto. 
       intros s t H. 
       unfold in_set. fold in_set. 
       rewrite (IHX s t H). 
       case_eq(r s a); intro J. 
          simpl. apply symS in H. rewrite (transS _ _ _ H J). auto. 
          simpl. assert (fact : r t a = false). 
             case_eq(r t a); intro F. rewrite (transS _ _ _ H F) in J. assumption. 
             reflexivity.            
          rewrite fact. simpl. reflexivity. 
Defined. 



Lemma in_set_cons_intro : 
   ∀ (S : Type) (eq : brel S) (a b : S) (X : finite_set S),
      (eq a b = true) + (in_set S eq X a = true) → in_set S eq (b :: X) a = true. 
Proof. intros S eq a b X. destruct X; intros [L | R]. 
          compute. rewrite L. reflexivity. 
          compute in R. discriminate. 
          compute. rewrite L. reflexivity. 
          unfold in_set. fold in_set. 
          case_eq(eq a s); intro H. 
             simpl. rewrite orb_comm. simpl. reflexivity. 
             unfold in_set in R. fold in_set in R. rewrite H in R. simpl in R. 
             rewrite R. simpl. rewrite orb_comm. simpl. reflexivity. 
Defined. 

Lemma in_set_cons_elim : 
   ∀ (S : Type) (eq : brel S) (a b : S) (X : finite_set S),
       (in_set S eq (b :: X) a = true) →  (eq a b = true) + (in_set S eq X a = true). 
Proof. intros S eq a b X H. destruct X. 
          case_eq(eq a b); intro J. 
             left. reflexivity. 
             compute in H. rewrite J in H. discriminate. 
          case_eq(eq a b); intro J. 
             left. reflexivity. 
             right. unfold in_set in H. fold in_set in H. rewrite J in H. simpl in H. 
             unfold in_set. fold in_set. assumption. 
Defined. 

Lemma in_set_test_intro : 
   ∀ (S : Type) (eq : brel S) (a : S) (X Y : finite_set S) (b : bool),
      ((b = true) * (in_set S eq X a = true)) + ((b = false) * (in_set S eq Y a = true)) 
          → in_set S eq (if b then X else Y) a = true. 
Proof. intros S eq a X Y b [[A B] | [A B]]. 
       rewrite A. assumption. rewrite A. assumption. 
Defined. 

Lemma in_set_test_elim : 
   ∀ (S : Type) (eq : brel S) (a : S) (X Y : finite_set S) (b : bool),
     in_set S eq (if b then X else Y) a = true -> 
      ((b = true) * (in_set S eq X a = true)) + ((b = false) * (in_set S eq Y a = true)). 
Proof. intros S eq a X Y. induction b; intro H. left; auto. right; auto. Defined. 


Lemma in_set_concat_intro : 
   ∀ (S : Type) (eq : brel S) (X Y : finite_set S) (a : S),
     (in_set S eq X a = true) + (in_set S eq Y a = true) →
         in_set S eq (X ++ Y) a = true. 
Proof. intros S eq. induction X. 
          intros Y a [L | R]. 
             compute in L. discriminate. 
             rewrite List.app_nil_l. assumption. 
          intros Y a0 [L | R]. 
             rewrite <- List.app_comm_cons. 
             unfold in_set. fold in_set. unfold in_set in L. fold in_set in L. 
             apply orb_is_true_left in L. destruct L as [L | L]. 
                rewrite L. simpl. reflexivity. 
                apply orb_is_true_right. right. apply IHX. left. assumption. 

             rewrite <- List.app_comm_cons. 
             unfold in_set. fold in_set. 
             apply orb_is_true_right. right. apply IHX. right. assumption. 
Defined. 

Lemma in_set_concat_elim : 
   ∀ (S : Type) (eq : brel S) (X Y : finite_set S) (a : S),
      in_set S eq (X ++ Y) a = true →
         (in_set S eq X a = true) + (in_set S eq Y a = true). 
Proof. intros S eq. induction X. 
          intros U a H. rewrite List.app_nil_l in H. right. assumption. 
          intros U b H. rewrite <- List.app_comm_cons in H. 
          unfold in_set in H. fold in_set in H. 
          apply orb_is_true_left in H.  destruct H as [L | R]. 
             left. unfold in_set. fold in_set. rewrite L. simpl. reflexivity. 
             assert (K := IHX U b R). destruct K as [KL | KR].
                left. apply in_set_cons_intro. right. assumption. 
                right. assumption.              
Defined. 


Lemma in_set_filter_elim : 
   ∀ (S : Type) (r : brel S) (f : bProp S),  
      (bProp_congruence S r f) -> 
      ∀ (a : S) (X : finite_set S),
         in_set S r (filter f X) a = true -> (f a = true) * (in_set S r X a = true).
Proof. intros S r f cong a. induction X; intro H. 
       compute in H.  discriminate. 
       unfold in_set. fold in_set.  simpl in H. 
       case_eq(f a); case_eq(f a0); case_eq(r a a0); intros J K M; simpl; auto. 
          split. reflexivity. rewrite K in H. 
          apply in_set_cons_elim in H. destruct H as [L | R]. 
             rewrite L in J. discriminate. 
             apply IHX;auto. 
          rewrite K in H. split. reflexivity. apply IHX;auto. 
          assert (A := cong _ _ J). rewrite K, M in A. discriminate. 
          rewrite K in H. unfold in_set in H. fold in_set in H. rewrite J in H. simpl in H. 
          destruct (IHX H) as [L R]. rewrite L in M. discriminate. 
          rewrite K in H. destruct (IHX H) as [L R]. rewrite L in M. discriminate. 
          rewrite K in H. destruct (IHX H) as [L R]. rewrite L in M. discriminate. 
Defined. 

Lemma in_set_filter_intro : 
   ∀ (S : Type) (r : brel S) (f : bProp S), 
     (bProp_congruence S r f) -> 
         ∀  (a : S) (X : finite_set S),
          (f a = true) * (in_set S r X a = true) -> in_set S r (filter f X) a = true. 
Proof. intros S r f cong a. induction X; intros [L R]. 
       compute in R. discriminate. 
       simpl. case_eq(f a0); case_eq(r a a0); intros K M; simpl; auto. 
          rewrite K. simpl. reflexivity. 
          rewrite K. simpl. apply in_set_cons_elim in R. destruct R as [RL | RR]. 
             rewrite K in RL. discriminate. 
             apply IHX. split; assumption.         
          assert (A := cong _ _ K). rewrite M, L in A. discriminate. 
          apply in_set_cons_elim in R. destruct R as [RL | RR]. 
             rewrite K in RL. discriminate. 
             apply IHX. split; assumption.         
Defined. 


Lemma in_set_uop_filter_elim : 
   ∀ (S : Type) (r : brel S) (f : bProp S),  
     (bProp_congruence S r f) -> 
        ∀ (a : S) (X : finite_set S),
           in_set S r (uop_filter S f X) a = true -> (f a = true) * (in_set S r X a = true).
Proof. unfold uop_filter. apply in_set_filter_elim. Defined. 

Lemma in_set_uop_filter_intro : 
   ∀ (S : Type) (r : brel S) (f : bProp S), 
     (bProp_congruence S r f) -> 
       ∀  (a : S) (X : finite_set S),
          (f a = true) * (in_set S r X a = true) -> in_set S r (uop_filter S f X) a = true. 
Proof. unfold uop_filter. apply in_set_filter_intro. Defined. 


Hypothesis in_set_duplicate_elim : ∀ (S : Type) (r : brel S) (s : S) (X : finite_set S),
    in_set S r (uop_duplicate_elim S r X) s = in_set S r X s. 
(* 
Proof. intros S r s. induction X. 
       compute. reflexivity. 
       unfold in_set. fold in_set. 
       unfold uop_duplicate_elim. 
Defined. 
*) 



