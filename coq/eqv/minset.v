Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce. 


Section Operations.

(* not_below eq lte a y   <-->   not(y < a)   *) 
Definition not_below {S : Type} (eq lte : brel S) : brel S := λ a y, bop_or (uop_not (lte y a)) (eq y a).

Definition is_minimal_wrt {S : Type} (eq lte : brel S)  : brel2 S (finite_set S)
:= λ a X, bProp_forall S (not_below eq lte a) X. 

Definition uop_minset {S : Type} (eq lte : brel S) : unary_op (finite_set S) 
:= λ X, uop_filter (λ a, is_minimal_wrt eq lte a X) X. 

Definition brel_minset {S : Type} (eq lte : brel S)  : brel (finite_set S) 
  := brel_reduce (brel_set eq) (uop_minset eq lte).

End Operations.  

Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable fS : S -> S.                
Variable Pf : brel_not_trivial S rS fS. 

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S. 
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 


Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a !=S b" := (rS a b = false) (at level 15).
Notation "a <<= b" := (lteS a b = true) (at level 15).
Notation "a <<!= b" := (lteS a b = false) (at level 15).


(* Move these ... ? *)

Lemma in_set_nil (s : S) : in_set rS nil s = false.
Proof. compute. reflexivity. Qed.

Lemma brel_set_nil_nil : brel_set rS nil nil = true.
Proof. compute. reflexivity.   Qed.

Lemma brel_set_nil_notnil : ∀ (s : S) (X : finite_set S), brel_set rS nil (s :: X) = false.
Proof. intros s X. compute. reflexivity.   Qed.

Lemma brel_set_notnil_nil : ∀ (s : S) (X : finite_set S), brel_set rS  (s :: X) nil = false.
Proof. intros s X. apply (brel_symmetric_implies_dual _ _ (brel_set_symmetric S rS) nil (s :: X) (brel_set_nil_notnil s X)). Qed. 

(* depends on CAS.coq.eqv.set.brel_set_elim_prop *) 
Lemma in_set_left_congruence : ∀ (a : S) (X Y : finite_set S),
    brel_set rS X Y = true -> in_set rS X a = true -> in_set rS Y a = true.
Proof. intros a X Y H1 H2.
       apply brel_set_elim_prop in H1; auto. destruct H1 as [L R].
       apply L; auto. 
Qed.

Lemma bProp_forall_cons_true_intro (a : S) (f : S -> bool) (X : finite_set S) :
   ((f a) = true) * (bProp_forall S f X = true) -> bProp_forall S f (a :: X) = true. 
Proof. intros [L R].
       unfold bProp_forall. unfold List.forallb.
       apply andb_is_true_right. split; auto. 
Qed.

Lemma bProp_forall_cons_true_elim (a : S) (f : S -> bool) (X : finite_set S) :
   bProp_forall S f (a :: X) = true -> ((f a) = true) * (bProp_forall S f X = true).
Proof. intro H.
       unfold bProp_forall in H. unfold List.forallb in H.
       apply andb_is_true_left in H. destruct H as [ L R ]; auto. 
Qed.

Lemma bProp_forall_cons_false_elim (a : S) (f : S -> bool) (X : finite_set S) :
   bProp_forall S f (a :: X) = false -> ((f a) = false) + (bProp_forall S f X = false).
Proof. intro H.
       unfold bProp_forall in H. unfold List.forallb in H.
       apply andb_is_false_left in H. destruct H as [ H | H ]; auto. 
Qed.

Lemma bProp_forall_true_elim (f : S -> bool) (cong : ∀ (s s' : S), rS s s' = true -> f s = f s') (X : finite_set S) :
        bProp_forall S f X = true -> ∀ (s : S),  in_set rS X s = true -> (f s) = true.
Proof. intros H s I. induction X. compute in I. discriminate I.
       apply bProp_forall_cons_true_elim in H. destruct H as [L R].
       apply in_set_cons_elim in I; auto.
       destruct I as [ I | I]. 
       rewrite <- (cong a s I). exact L. 
       apply IHX; auto.     
Qed.

Lemma bProp_forall_true_intro (f : S -> bool) (cong : ∀ (s s' : S), rS s s' = true -> f s = f s') (X : finite_set S) :
        (∀ (s : S),  in_set rS X s = true -> (f s) = true) -> bProp_forall S f X = true. 
Proof. intros H . induction X. compute. reflexivity. 
       apply bProp_forall_cons_true_intro.
       assert (J : in_set rS (a :: X) a = true). compute. rewrite refS; auto. 
       rewrite (H a J). rewrite IHX. auto.
       intros s K. apply H. apply in_set_cons_intro; auto. 
Qed.

Lemma bProp_forall_false_intro (f : S -> bool) (cong : ∀ (s s' : S), rS s s' = true -> f s = f s') (X : finite_set S) :
        {s : S & (in_set rS X s = true) * ((f s) = false)} -> bProp_forall S f X = false. 
Proof. intros [s [P Q]].
       case_eq(bProp_forall S f X); intro J; auto.
          assert (K := bProp_forall_true_elim f cong X J s P). 
          rewrite K in Q. exact Q. 
Qed. 

Lemma bProp_forall_false_elim (f : S -> bool) (X : finite_set S): bProp_forall S f X = false -> {s : S &  (in_set rS X s = true)  * ((f s) = false)}.
Proof. intro H. induction X. compute in H. discriminate H. 
       apply bProp_forall_cons_false_elim in H.
       destruct H as [H | H]. exists a. 
       split; auto. apply in_set_cons_intro; auto. 
       destruct (IHX H) as [s [L R]].
       exists s; split; auto.
       apply in_set_cons_intro; auto. 
Qed.



Lemma bProp_forall_congruence (f g : S -> bool)
      (f_cong : ∀ s s' : S, s =S s' → f s = f s')
      (g_cong : ∀ s s' : S, s =S s' → g s = g s')      
      (fg_cong : ∀ (s s' : S), rS s s' = true -> f s = g s')
      (X Y : finite_set S) : 
                brel_set rS X Y = true -> bProp_forall S f X = bProp_forall S g Y. 
Proof. intro H.
       apply brel_set_elim_prop in H; auto. destruct H as [L R].
       case_eq(bProp_forall S f X); intro J1; case_eq(bProp_forall S g Y); intro J2; auto.
       assert (K1 := bProp_forall_true_elim f f_cong X J1).
       destruct (bProp_forall_false_elim g Y J2) as [s [E G]]. 
       assert (F := K1 s (R s E)).
       assert (C := fg_cong s s (refS s)). rewrite F, G in C. discriminate C. 
       destruct (bProp_forall_false_elim f X J1) as [s [E F]].        
       assert (K1 := bProp_forall_true_elim g g_cong Y J2).
       assert (G := K1 s (L s E)).
       assert (C := fg_cong s s (refS s)). rewrite F, G in C. discriminate C. 
Qed.        


(********** lemmas for not_below ***********)

Lemma brel_not_below_congruence : brel_congruence S rS (not_below rS lteS). 
Proof. unfold brel_congruence, not_below. intros s t u v E1 E2.
       assert (LC := lteCong _ _ _ _ E2 E1).
       assert (EC := congS _ _ _ _ E2 E1).
       rewrite LC, EC. reflexivity. 
Qed.        

(********** lemmas for is_minimal_wrt ***********)

Lemma brel2_is_minimal_wrt_congruence : brel2_congruence S (finite_set S) rS (brel_set rS) (is_minimal_wrt rS lteS).
Proof. unfold brel2_congruence.
       intros a b X Y E1 E2. 
       unfold is_minimal_wrt.
       apply bProp_forall_congruence; auto. 
       intros s s' H. apply brel_not_below_congruence; auto. 
       intros s s' H. apply brel_not_below_congruence; auto. 
       intros s s' H. apply brel_not_below_congruence; auto. 
Qed. 


Lemma bProp_is_minimal_wrt_congruence (Y : finite_set S) : bProp_congruence S rS (λ a : S, is_minimal_wrt rS lteS a Y).
Proof. unfold bProp_congruence.
       intros a b E.
       apply brel2_is_minimal_wrt_congruence; auto.
       apply brel_set_reflexive; auto.
Qed.

Lemma is_minial_in_singleton : ∀ (s : S), is_minimal_wrt rS lteS s (s :: nil) = true.
Proof. intro s. unfold is_minimal_wrt. unfold bProp_forall.
       compute. rewrite refS. rewrite lteRefl. reflexivity. 
Qed.

Lemma is_minimal_wrt_elim (a : S) (X : finite_set S)  :
      is_minimal_wrt rS lteS a X = true -> ∀ (s : S), in_set rS X s = true -> (rS a s = true) + (lteS s a = false). 
Proof. intro H. unfold is_minimal_wrt in H. 
       intros s J. assert (M := bProp_forall_true_elim _ (λ u v, brel_not_below_congruence a u a v (refS a)) X H s J).
       compute in M. case_eq(lteS s a); intro N; auto. rewrite N in M. left. apply symS. exact M. 
Qed.

Lemma is_minimal_wrt_fasle_elim (a : S) (X : finite_set S)  :
      is_minimal_wrt rS lteS a X = false -> ∀ (s : S), in_set rS X s = true -> (rS a s = false) * (lteS s a = true). 
Admitted. 

Lemma is_minimal_wrt_intro (a : S) (X : finite_set S) :
   (∀ (s : S), in_set rS X s = true -> (rS a s = true) + (lteS s a = false)) -> is_minimal_wrt rS lteS a X = true.
Proof. intros R. unfold is_minimal_wrt. 
       apply bProp_forall_true_intro. intros s s' E. apply (brel_not_below_congruence _ _ _ _ (refS a) E). 
       intros s H. destruct (R s H) as [J | K]. compute. apply symS in J. rewrite J.
       rewrite (lteCong _ _ _ _ J (refS a)). rewrite lteRefl; auto. 
       compute. rewrite K; auto. 
Qed. 


 (********** lemmas for uop_minset ***********)

Lemma uop_minset_congruence : uop_congruence (finite_set S) (brel_set rS) (uop_minset rS lteS).
Proof. unfold uop_congruence. intros X Y H.
       unfold uop_minset. unfold uop_filter.
       apply brel_set_intro_prop; auto. split.
       intros a J. apply in_set_filter_intro; auto. 
       apply bProp_is_minimal_wrt_congruence. 
       apply in_set_filter_elim in J; auto. destruct J as [L R]. split; auto.
       rewrite <- (brel2_is_minimal_wrt_congruence _ _ _ _ (refS a) H). exact L. 
       apply (in_set_left_congruence a X Y H R). 
       apply bProp_is_minimal_wrt_congruence. 
       intros a J. apply in_set_filter_intro; auto.
       apply bProp_is_minimal_wrt_congruence.        
       apply in_set_filter_elim in J; auto. destruct J as [L R]. split; auto.
       apply brel_set_symmetric in H; auto. 
       rewrite <- (brel2_is_minimal_wrt_congruence _ _ _ _ (refS a) H). exact L.
       apply brel_set_symmetric in H; auto.        
       apply (in_set_left_congruence a Y X H R). 
       apply bProp_is_minimal_wrt_congruence.        
Qed. 


Lemma uop_minset_singleton (s : S) : uop_minset rS lteS (s :: nil) = s :: nil.
Proof. compute. rewrite lteRefl. rewrite refS. reflexivity. Qed.

Lemma uop_minset_nil : uop_minset rS lteS nil = nil.
Proof. compute. reflexivity. Qed.

Lemma in_set_true_implies_not_nil (X : finite_set S) : ∀ s : S, in_set rS X s = true -> brel_set rS nil X = false. 
Proof. intros s H. induction X. compute in H. discriminate H.  apply in_set_cons_elim in H; auto.  Qed. 


Lemma in_set_minset_intro (a : S) (X : finite_set S) :
  (in_set rS X a = true) * (∀ (s : S), in_set rS X s = true -> (rS a s = true) + (lteS s a = false))
              -> in_set rS (uop_minset rS lteS X) a = true. 
Proof. intros [L R].
       unfold uop_minset. unfold uop_filter. apply in_set_filter_intro; auto. 
       apply bProp_is_minimal_wrt_congruence. split; auto. 
       apply is_minimal_wrt_intro; auto. 
Qed.

Lemma in_set_minset_elim (a : S) (X : finite_set S) :
  in_set rS (uop_minset rS lteS X) a = true ->
         (in_set rS X a = true) * (∀ (s : S), in_set rS X s = true -> (rS a s = true) + (lteS s a = false)). 
Proof. intro H. 
       unfold uop_minset in H. unfold uop_filter in H. 
       apply in_set_filter_elim in H.
       destruct H as [L R]. split; auto. 
          intros s K. case_eq(rS a s); intro J; auto. 
          right. destruct (is_minimal_wrt_elim a X L s K) as [M | M].
          rewrite M in J. discriminate J. exact M.          
       apply bProp_is_minimal_wrt_congruence. 
Qed.

Lemma in_set_minset_singleton_intro (a s : S) : (rS a s = true) -> in_set rS (uop_minset rS lteS (s :: nil)) a = true. 
Proof. intro H. apply in_set_minset_intro. split. 
       apply in_set_singleton_intro; auto. 
       intros s0 H1. apply in_set_singleton_elim in H1; auto. 
       left. exact (tranS _ _ _ H H1). 
Qed.

Lemma in_set_minset_singleton_elim (a s : S) : in_set rS (uop_minset rS lteS (s :: nil)) a = true -> (rS a s = true). 
Proof. intro H. apply in_set_minset_elim in H. destruct H as [H _]. 
       apply in_set_singleton_elim in H; auto. 
Qed.


(* MOVE *) 
Lemma in_set_filter_false_elim (g : bProp S) (cong : bProp_congruence S rS g) (X : finite_set S) (a : S) : 
    in_set rS (filter g X) a = false -> (g a = false) + (in_set rS X a = false).
Proof. intro H. induction X. right. compute; auto.
       unfold filter in H. fold @filter in H.
       case_eq(rS a a0); intro J1; case_eq(g a0); intro J2; rewrite J2 in H. 
          unfold in_set in H. fold @in_set in H. apply orb_is_false_left in H. destruct H as [L R]. rewrite J1 in L; discriminate L. 
          apply symS in J1. rewrite <- (cong a0 a J1). left. exact J2. 
          unfold in_set in H. fold @in_set in H. apply orb_is_false_left in H. destruct H as [L R].
          destruct (IHX R) as [ L1 | R1 ]; auto. right. unfold in_set; fold @in_set. rewrite J1, R1. compute; auto. 
          destruct (IHX H) as [ L | R ]; auto.
             right. case_eq(in_set rS (a0 :: X) a); intro K; auto. 
             apply in_set_cons_elim in K; auto. destruct K as [K | K].
             apply symS in K. rewrite K in J1. exact J1. 
             rewrite K in R. exact R. 
Qed.


(* USED in minset_union !!!! REPLACE *) 
Lemma in_set_uop_minset_false_elim (a : S) (X : finite_set S) :
  in_set rS X a = true -> in_set rS (uop_minset rS lteS X) a = false ->
  {s : S & (in_set rS (uop_minset rS lteS X) s = true) * (lteS s a = true) * (rS s a = false)}.  
Admitted. 


Lemma uop_minset_idempotent : uop_idempotent (finite_set S) (brel_set rS) (uop_minset rS lteS). 
Proof. unfold uop_idempotent.
       intro X. apply brel_set_intro_prop; auto; split; intros s H.
       apply in_set_minset_elim in H. destruct H as [H _]. exact H. 
       apply in_set_minset_intro. split; auto. 
       apply in_set_minset_elim in H. destruct H as [_ H].
       intros s' H'. apply H. 
       apply in_set_minset_elim in H'. destruct H' as [H' _]. exact H'.        
Qed.

Lemma in_set_minset_minset (s : S) (X : finite_set S) :
  in_set rS (uop_minset rS lteS (uop_minset rS lteS X)) s = in_set rS (uop_minset rS lteS X) s.
Proof. apply in_set_congruence; auto.
       apply uop_minset_idempotent. 
Qed.

Lemma brel_set_minset_minset (X Y : finite_set S) :
  brel_set rS (uop_minset rS lteS (uop_minset rS lteS X)) (uop_minset rS lteS (uop_minset rS lteS Y))
  =
  brel_set rS (uop_minset rS lteS X) (uop_minset rS lteS Y).
Proof. apply brel_set_congruence; auto.
       apply uop_minset_idempotent.
       apply uop_minset_idempotent.        
Qed.


(********** lemmas for brel_minset ***********) 

Lemma brel_minset_congruence : brel_congruence (finite_set S) (brel_minset rS lteS) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_congruence.
       apply brel_set_congruence; auto.
Qed.

Lemma brel_minset_reflexive : brel_reflexive (finite_set S) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_reflexive.
       apply brel_set_reflexive; auto.
Qed.
  
Lemma brel_minset_symmetric : brel_symmetric (finite_set S) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_symmetric.
       apply brel_set_symmetric; auto.
Qed.


Lemma brel_minset_transitive : brel_transitive (finite_set S) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_transitive.
       apply brel_set_transitive; auto.
Qed.


Definition brel_minset_new : unary_op (finite_set S)
  := λ X, if brel_set rS nil X then wS :: nil else nil.

Lemma brel_minset_nil_singleton (s : S) : brel_minset rS lteS nil (s :: nil) = false.
Proof. unfold brel_minset. unfold brel_reduce. rewrite uop_minset_nil. rewrite uop_minset_singleton. apply brel_set_nil_notnil. Qed. 

Lemma brel_minset_singleton_nil (s : S) : brel_minset rS lteS (s :: nil) nil = false.
Proof. apply (brel_symmetric_implies_dual _ _ brel_minset_symmetric nil (s :: nil) (brel_minset_nil_singleton s)). Qed.   


Lemma uop_minset_swap (a s : S) (X : finite_set S) : 
  (∀ a0 : S, in_set rS (uop_minset rS lteS (a :: s :: X)) a0 = true → in_set rS (uop_minset rS lteS (s :: a :: X)) a0 = true). 
Proof.  intros s0 H.
          apply in_set_minset_elim in H. destruct H as [H1 H2]. 
          apply in_set_minset_intro. split. 
             apply in_set_cons_intro; auto.
             apply in_set_cons_elim in H1; auto. 
             destruct H1 as [H1 | H1]. 
                right. apply in_set_cons_intro; auto.
                apply in_set_cons_elim in H1; auto. 
                destruct H1 as [H1 | H1]. 
                   left; auto.
                   right. apply in_set_cons_intro; auto.

             intros s1 H3.
             apply H2. 
             apply in_set_cons_elim in H3; auto.              
             apply in_set_cons_intro; auto.
             destruct H3 as [H3 | H3].
                right. apply in_set_cons_intro; auto.
                apply in_set_cons_elim in H3; auto.              
                destruct H3 as [H3 | H3].
                   left. auto. 
                   right. apply in_set_cons_intro; auto.
Qed.                    

Lemma brel_uop_minset_swap (a s : S) (X : finite_set S) : brel_set rS (uop_minset rS lteS (a :: s :: X)) (uop_minset rS lteS (s :: a :: X)) = true.
Proof. apply brel_set_intro_prop; auto. split.
       apply uop_minset_swap.
       apply uop_minset_swap.
Qed.        
          
Lemma brel_minset_cons_minimal (s : S) (X : finite_set S) :
  is_minimal_wrt rS lteS s X = true -> brel_set rS (uop_minset rS lteS (s :: X)) (uop_minset rS lteS (s :: (uop_minset rS lteS X))) = true.
Admitted.
(*
Proof. intro H.
       apply brel_set_intro_prop; auto. split; intros a aIn. 
          apply in_set_cons_intro; auto.        
          case_eq(rS s a); intro N; auto. 
             right.  apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal].
             apply in_set_cons_elim in aIn; auto. 
             destruct aIn as [E | aIn]. 
                rewrite E in N. discriminate N. 
                apply in_set_minset_intro. split; auto. 
                intros s0 s0In. 
                apply aMinimal.
                apply in_set_cons_intro; auto.

          apply in_set_minset_intro.        
          apply in_set_cons_elim in aIn; auto.           
          destruct aIn as [E | aIn]. 
             split. 
                apply in_set_cons_intro; auto. 
                intros s0 s0In. 
                apply in_set_cons_elim in s0In; auto.
                destruct s0In as [E' | s0In].
                   apply symS in E. left. exact (tranS _ _ _ E E').
                   assert (K := is_minimal_wrt_elim _ _ H s0 s0In). 
                   apply symS in E. rewrite (congS _ _ _ _ E (refS s0)).
                   rewrite (lteCong _ _ _ _ (refS s0) E). 
                   exact K. 

                split. 
                   apply in_set_cons_intro; auto. 
                   right. apply in_set_minset_elim in aIn. 
                   destruct aIn as [aIn _]; auto. 





                   intros s0 s0In. 
                   apply in_set_cons_elim in s0In; auto.
                   apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal].
                   destruct s0In as [E' | s0In].
                      apply symS in E'. rewrite (congS _ _ _ _ (refS a) E').
                      rewrite (lteCong _ _ _ _ E' (refS a)).                   
                      assert (K := is_minimal_wrt_elim _ _ H a aIn).
                      destruct K as [K | K].
                         left. apply symS; auto.
                         case_eq(rS a s); intro F1; case_eq(lteS s a); intro F2; auto.
                         admit.  (* OUCH *) 
                      apply (aMinimal s0 s0In). 
Admitted.
 *)

(* move *) 
Lemma set_is_empty (X : finite_set S) : (∀ s : S, in_set rS X s = false) -> X = nil.
Proof. induction X; intro H.
       reflexivity. 
       assert (K := H a). unfold in_set in K. rewrite refS in K. simpl in K. 
       discriminate K. 
Qed. 

Lemma brel_minset_drop_not_minimal (lteAntiSym : brel_antisymmetric S rS lteS) (s : S) (X : finite_set S) :
    is_minimal_wrt rS lteS s X = false -> brel_set rS (uop_minset rS lteS (s :: X)) (uop_minset rS lteS X) = true.
Proof. intro H. 
       apply brel_set_intro_prop; auto. split; intros a aIn. 
          apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal]. 
          apply in_set_minset_intro. split. 
             apply in_set_cons_elim in aIn; auto. destruct aIn as [E | aIn]; auto. 
                assert (aMinimal' : ∀ s0 : S, in_set rS X s0 = true → a =S s0 + s0 <<!= a). 
                   intros s0 s0In. apply aMinimal.
                   apply in_set_cons_intro; auto. 
                assert (K := is_minimal_wrt_fasle_elim s X H). 
                assert (J : ∀ s0 : S, in_set rS X s0 = false).
                   intro s0. case_eq(in_set rS X s0); intro J; auto. 
                   assert (J1 := aMinimal' s0 J).
                   assert (J2 := K s0 J).
                   destruct J2 as [L R].
                   rewrite (congS _ _ _ _ E (refS s0)) in L. rewrite (lteCong _ _ _ _ (refS s0) E) in R. 
                   rewrite L in J1. rewrite R in J1. destruct J1 as [F | F]; discriminate F. 
                   assert (L : X = nil). apply set_is_empty; auto. 
                rewrite L in H. compute in H. discriminate H. 
 
          intros s0 s0In. 
          apply aMinimal. 
          apply in_set_cons_intro; auto.

          apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal]. 
          apply in_set_minset_intro. split. 
             apply in_set_cons_intro; auto. 
             intros s0 s0In. 
             apply in_set_cons_elim in s0In; auto.
             destruct s0In as [E | s0In].
                case_eq(rS a s0); intro F1; case_eq(lteS s0 a); intro F2; auto.
                assert (K := is_minimal_wrt_fasle_elim s X H). 
                assert (J := K a aIn). destruct J as [L R]. 
                apply symS in E. rewrite (lteCong _ _ _ _ E (refS a)) in F2.
                assert (E' := lteAntiSym _ _ F2 R). rewrite E' in L. discriminate L. 
                apply aMinimal; auto. 
Qed. 
          
Lemma tttt (s : S) (X : finite_set S) : brel_set rS nil (uop_minset rS lteS (s :: X)) = false.
Proof. induction X.
       rewrite uop_minset_singleton. compute; auto. 

       case_eq(brel_set rS nil (uop_minset rS lteS (s :: a :: X))); intro H; auto. 
       assert (K := brel_uop_minset_swap s a X).
       assert (J := brel_set_transitive S rS refS symS tranS _ _ _ H K).
          case_eq(is_minimal_wrt rS lteS a (s :: X)); intro F.
             assert (L := brel_minset_cons_minimal _ _ F).
             assert (M := brel_set_transitive S rS refS symS tranS _ _ _ J L).
             assert (N := brel_set_nil S rS _ M).
             admit.  (* OUCH discriminate N. *) 
(*
             assert (L := brel_minset_drop_not_minimal _ _ F).
             assert (M := brel_set_transitive S rS refS symS tranS _ _ _ J L).
             rewrite M in IHX. 
             exact IHX. 
*) 
Admitted. 
                                 
       
Lemma brel_minset_nil_notnil (s : S) (X : finite_set S) : brel_minset rS lteS nil (s :: X) = false.
Proof. unfold brel_minset. unfold brel_reduce. rewrite uop_minset_nil.
       assert (K : brel_set rS nil (s :: X) = false). apply brel_set_nil_notnil.
       apply tttt.
Qed.

Lemma brel_minset_notnil_nil (s : S) (X : finite_set S) : brel_minset rS lteS (s :: X) nil = false.
Proof. apply (brel_symmetric_implies_dual _ _ brel_minset_symmetric nil (s :: X) (brel_minset_nil_notnil s X)). Qed. 

Lemma brel_minset_not_trivial : brel_not_trivial (finite_set S) (brel_minset rS lteS) brel_minset_new.
Proof. unfold brel_not_trivial. intro X. 
       destruct X. 
       unfold brel_minset_new. rewrite brel_set_nil_nil. 
       rewrite brel_minset_nil_singleton. rewrite brel_minset_singleton_nil. auto. 
       unfold brel_minset_new. rewrite brel_set_nil_notnil.        
       rewrite brel_minset_nil_notnil. rewrite brel_minset_notnil_nil. auto. 
Qed. 


Lemma brel_minset_elim (X Y : finite_set S) : brel_minset rS lteS X Y = true ->
       (∀ (s : S),  (in_set rS (uop_minset rS lteS X) s = true) <-> (in_set rS (uop_minset rS lteS Y) s = true)). 
Proof. intro H. unfold brel_minset in H.  unfold brel_reduce in H. apply brel_set_elim_prop in H; auto.
       destruct H as [L R]. intro s. 
       assert (J := L s); assert (K := R s). split; auto. 
Qed. 

Lemma brel_minset_intro (X Y : finite_set S) : 
       (∀ (s : S),  (in_set rS (uop_minset rS lteS X) s = true) <-> (in_set rS (uop_minset rS lteS Y) s = true))
       -> brel_minset rS lteS X Y = true.
Proof. intro H. unfold brel_minset. unfold brel_reduce. 
       apply brel_set_intro_prop; auto; split; intros s J.
          destruct (H s) as [K _]. apply K; auto.
          destruct (H s) as [_ K]. apply K; auto.        
Qed. 


Lemma brel_minset_singleton_elim (a : S) (X : finite_set S) :
      brel_minset rS lteS (a :: nil) X = true -> (in_set rS X a = true) * (is_minimal_wrt rS lteS a X = true). 
Proof.  intro H. 
        destruct (brel_minset_elim _ _ H a) as [L R].
        assert (K : in_set rS (uop_minset rS lteS X) a = true).
           apply L. rewrite uop_minset_singleton. compute. rewrite refS; auto. 
        apply in_set_minset_elim in K.
        destruct K as [K1 K2]. split; auto.
        apply is_minimal_wrt_intro; auto. 
Qed.

Definition minset_negate ( X Y : finite_set S) :=
   match uop_minset rS lteS X, uop_minset rS lteS Y with 
   | nil, nil => wS :: nil
   | nil, t::_ => (fS t) :: nil 
   | t::_, nil => (fS t) :: nil      
   | t :: _, u :: _ => nil 
  end. 


Lemma brel_minset_negate_left (X Y : finite_set S) : brel_minset rS lteS X (minset_negate X Y) = false.
Proof. unfold brel_minset.
       unfold brel_reduce. 
       destruct X; destruct Y; unfold minset_negate; simpl.
          rewrite uop_minset_nil. rewrite uop_minset_singleton. apply brel_set_nil_notnil.
          rewrite uop_minset_nil.
             destruct (uop_minset rS lteS (s :: Y)).
                rewrite uop_minset_singleton. apply brel_set_nil_notnil.
                rewrite uop_minset_singleton. apply brel_set_nil_notnil.             
          destruct (uop_minset rS lteS (s :: X)).
             rewrite uop_minset_singleton. apply brel_set_nil_notnil.
             rewrite uop_minset_singleton. destruct f.
                compute. destruct (Pf s0) as [L R]. rewrite L. reflexivity. 
                unfold brel_set. unfold brel_and_sym. 
                apply andb_is_false_right. left. unfold brel_subset. fold (@brel_subset).
                apply andb_is_false_right. left. compute. destruct (Pf s0) as [L R]. rewrite L. reflexivity. 
          destruct (uop_minset rS lteS (s :: X)); destruct (uop_minset rS lteS (s0 :: Y)).
             rewrite uop_minset_singleton. apply brel_set_nil_notnil.
             rewrite uop_minset_singleton. apply brel_set_nil_notnil.
             rewrite uop_minset_singleton. destruct f.
                compute. destruct (Pf s1) as [L R]. rewrite L. reflexivity. 
                unfold brel_set. unfold brel_and_sym. 
                apply andb_is_false_right. left. unfold brel_subset. fold (@brel_subset).
                apply andb_is_false_right. left. compute. destruct (Pf s1) as [L R]. rewrite L. reflexivity. 
             rewrite uop_minset_nil. apply brel_set_notnil_nil. 
Qed.

Lemma brel_minset_negate_comm (X Y : finite_set S) : minset_negate X Y = minset_negate Y X.
Proof. destruct X; destruct Y; unfold minset_negate; simpl; auto.
       destruct(uop_minset rS lteS (s :: X)); destruct (uop_minset rS lteS (s0 :: Y)); auto. 
Qed.

Lemma brel_minset_negate_right (X Y : finite_set S) : brel_minset rS lteS Y (minset_negate X Y) = false.
Proof. rewrite brel_minset_negate_comm. apply brel_minset_negate_left. Qed. 

Lemma brel_minset_not_exactly_two : brel_not_exactly_two (finite_set S) (brel_minset rS lteS). 
Proof. unfold brel_not_exactly_two. exists minset_negate. 
       intros X Y. right. split.
       apply brel_minset_negate_left.
       apply brel_minset_negate_right.
Defined. 

Definition squash : list (finite_set S) -> list S
  := fix f l :=
       match l with
       | nil => nil
       | X :: rest => X ++ (f rest)
       end.


Lemma minset_lemma1 (s : S) :  brel_minset rS lteS nil (s :: nil) = false. 
Proof. unfold brel_minset. unfold brel_reduce.
       case_eq(brel_set rS (uop_minset rS lteS nil) (uop_minset rS lteS (s :: nil))); intro J; auto.
       apply brel_set_elim_prop in J; auto. destruct J as [L R].
       assert (K := R s). rewrite uop_minset_singleton  in K.
       assert (T : in_set rS (s :: nil) s = true). compute. rewrite refS; auto. 
       assert (J := K T).  compute in J. discriminate J. 
Qed. 

                                              
Lemma minset_lemma2 (s : S) (X : finite_set S) (H : brel_minset rS lteS X (s :: nil) = true) : in_set rS X s = true.
Proof. induction X. rewrite minset_lemma1 in H. discriminate H. 
       apply in_set_cons_intro; auto.
       apply brel_minset_symmetric in H; auto.
       apply brel_minset_singleton_elim in H. destruct H as [H _]. 
       apply in_set_cons_elim in H; auto. 
Qed. 

Lemma squash_lemma (s : S) (X : list (finite_set S)) (H : in_set (brel_minset rS lteS) X (s :: nil) = true) : in_set rS (squash X) s = true. 
Proof. induction X. compute in H. discriminate H.
       apply in_set_cons_elim in H.
       unfold squash; fold squash.
       apply in_set_concat_intro.
       destruct H as [H | H].       
          left. apply minset_lemma2; auto. 
          right. apply IHX; auto. 
       apply brel_minset_symmetric; auto.
Qed.        

Definition brel_minset_is_not_finite : carrier_is_not_finite S rS -> carrier_is_not_finite (finite_set S) (brel_minset rS lteS).
Proof. unfold carrier_is_not_finite.   
       intros H f.
       destruct (H (λ _, squash (f tt))) as [s Ps].
       exists (s :: nil). 
       case_eq(in_set (brel_minset rS lteS) (f tt) (s :: nil)); intro J; auto.
       apply squash_lemma in J. rewrite J in Ps. exact Ps. 
Defined.

Definition minset_enum (fS : unit -> list S) (x : unit) :=  List.map (uop_minset rS lteS) (power_set S (fS x)).

Lemma empty_set_in_minset_enum (f : unit -> list S) : in_set (brel_minset rS lteS) (minset_enum f tt) nil = true.
Admitted. 

Lemma min_set_enum_cons (f : unit -> list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (a : S) (X : finite_set S) : 
        in_set rS (f tt) a = true -> 
        in_set (brel_minset rS lteS) (minset_enum f tt) X = true -> 
        in_set (brel_minset rS lteS) (minset_enum f tt) (a :: X) = true. 
Admitted. 

Lemma minset_enum_lemma (f : unit → list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (X : finite_set S) : 
  in_set (brel_minset rS lteS) (minset_enum f tt) X = true.
Proof.  induction X. 
        apply empty_set_in_minset_enum. 
        assert (aIn := pf a). 
        apply min_set_enum_cons; auto. 
Qed. 

Definition brel_minset_is_finite : carrier_is_finite S rS -> carrier_is_finite (finite_set S) (brel_minset rS lteS).
Proof. unfold carrier_is_finite.   intros [f pf].
       exists (minset_enum f). intro X. 
       apply minset_enum_lemma; auto.
Defined. 

Definition brel_minset_finite_decidable (d : carrier_is_finite_decidable S rS) : carrier_is_finite_decidable (finite_set S) (brel_minset rS lteS)
  := match d with
     | inl fS  => inl (brel_minset_is_finite fS)
     | inr nfS => inr (brel_minset_is_not_finite nfS)                       
     end.




(*********************************************************************************************************

0) ms and upper are congruent 
1)  x in upper(ms(X)) <-> x in upper(X) 
2)  x in ms(X) <-> x in ms(upper(X))
3)  (x in upper(X) <-> x in upper(Y)) <-> ms(X) = ms(Y) 
*)

Definition in_upper_set (S : Type) (eq : brel S) (lte : brel S) (X : finite_set S) (a : S) :=
   { b : S & (in_set eq X b = true) * (lte b a = true) }. 

Definition in_up := in_upper_set S rS lteS.

Definition ms := uop_minset rS lteS.

Lemma p1_left : ∀ (X : finite_set S) (x : S),  in_up (ms X) x → in_up X x.
Proof.  intros X x [b [H Q]]. 
        unfold in_up. unfold in_upper_set.
        apply in_set_minset_elim in H. 
        destruct H as [H1 H2]. 
        exists b. 
        split; auto. 
Qed. 


Lemma p1_right : ∀ (X : finite_set S) (x : S),  in_up X x → in_up (ms X) x.
Proof.  intros X x [b [H Q]]. 
        unfold in_up. unfold in_upper_set.
        case_eq (in_set rS (ms X) b); intro P.
           exists b. split; auto.
           apply in_set_uop_minset_false_elim in P; auto.
           destruct P as [s [[P1 P2] P3]]. 
           exists s. split; auto.
           apply (lteTrans _ _ _ P2 Q). 
Qed. 


Notation "a == b"  := (brel_set rS a b = true) (at level 15).

Lemma minset_subset : ∀ (X : finite_set S) (x: S),  in_set rS (ms X) x = true -> in_set rS X x = true.
Admitted.


Lemma p3_right1 : ∀ (X Y : finite_set S),  (ms X) == (ms Y) -> ∀ (x: S), in_up X x -> in_up Y x. 
Proof. intros X Y H1 x H2.
       unfold in_up. unfold in_upper_set.
       apply brel_set_elim_prop in H1; auto. 
       destruct H1 as [H1 _].       
       destruct H2 as [s [H3 H4]].
       case_eq (in_set rS Y s); intro P.
          exists s. split; auto. 
          case_eq (in_set rS (ms X) s); intro Q.
             exists s. split; auto.
             assert (H2 := H1 s Q).
             apply minset_subset. exact H2.
             assert (H2 := in_set_uop_minset_false_elim s X H3 Q).
             destruct H2 as [b [[A B]] _]. 
             exists b. split; auto.
                assert (H2 := H1 b A).
                apply minset_subset. exact H2.
                exact (lteTrans _ _ _ B H4). 
Defined. 


Lemma p3_left : ∀ (X Y : finite_set S),  (∀  (x : S), in_up X x -> in_up Y x) -> (∀  (y : S), in_up Y y -> in_up X y) -> (ms X) == (ms Y).
Proof. intros X Y H1 H2.
       apply brel_minset_intro.
       intro s. split. intro H3.
       apply in_set_minset_intro.
       apply in_set_minset_elim in H3.
       destruct H3 as [H3 H4].
       split.
          admit.           
          intros b H5.
          case_eq(rS s b); intro H6; auto.
          right.
          case_eq(lteS b s); intro H7; auto. 
          assert (H8 : in_up Y b).
             exists b; auto.
          case_eq(in_set rS X b); intro H9. 
             destruct (H4 b H9) as [H10 | H10].
                rewrite H10 in H6. exact H6.
                rewrite H7 in H10. exact H10.
             
          apply H2 in H8.
          destruct H8 as [c [H8 H10]]. 
          destruct (H4 c H8) as [H11 | H11].
             assert (H12 := lteCong _ _ _ _ H11 (refS b)).
             rewrite <- H12 in H10.
             (* Note : suppose b ~ s, b<>s. 
                then up{b} = up{s}, but up{b} <> up{s}, 
                so need antisymmetry here. 
             *) 
             admit.                    
             assert (H12 := lteTrans _ _ _ H10 H7). 
             rewrite H12 in H11. exact H11.
Admitted. 

End Theory.



Section ACAS.

Definition eqv_proofs_brel_minset : ∀ (S : Type) (r : brel S) (lteS : brel S), eqv_proofs S r → eqv_proofs (finite_set S) (brel_minset r lteS)
:= λ S r lteS eqv, 
   {| 
     A_eqv_congruence  := brel_minset_congruence S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) lteS
   ; A_eqv_reflexive   := brel_minset_reflexive S r  (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) lteS 
   ; A_eqv_transitive  := brel_minset_transitive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) lteS
   ; A_eqv_symmetric   := brel_minset_symmetric S r lteS
   ; A_eqv_type_ast    := Ast_type_set (A_eqv_type_ast S r eqv)                                                           
   ; A_eqv_brel_ast    := Ast_brel_eq_minset (A_eqv_brel_ast S r eqv)                                                
   |}.

Definition A_eqv_minset : ∀ (S : Type),  A_po S -> A_eqv (finite_set S) 
  := λ S poS,
  let eqvS  := A_po_eqv S poS in 
  let rS    := A_eqv_eq S eqvS in
  let wS    := A_eqv_witness S eqvS in
  let fS    := A_eqv_new S eqvS in
  let nt    := A_eqv_not_trivial S eqvS in
  let eqP   := A_eqv_proofs S eqvS in
  let congS := A_eqv_congruence S rS eqP in 
  let refS  := A_eqv_reflexive S rS eqP in  
  let symS  := A_eqv_symmetric S rS eqP in
  let trnS  := A_eqv_transitive S rS eqP in
  let lteS  := A_po_lte S poS in
  let lteP  := A_po_proofs S poS in 
  let lte_congS := A_po_congruence S rS lteS lteP in 
  let lte_refS  := A_po_reflexive S rS lteS lteP in  
(*  let lte_asymS := A_po_antisymmetric S rS lteS lteP in *) 
  let lte_trnS  := A_po_transitive S rS lteS lteP in  
   {| 
      A_eqv_eq            := brel_minset rS lteS 
    ; A_eqv_proofs        := eqv_proofs_brel_minset S rS lteS eqP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (* lte_asymS *) 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS lteS lte_refS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS lteS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS lteS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (* lte_asymS *) (A_eqv_finite_d S eqvS)
    ; A_eqv_ast           := Ast_eqv_minset (A_po_ast S poS)
   |}. 

End ACAS.


Section CAS.

Definition check_brel_minset_finite {S : Type} (rS : brel S) (lteS : brel S) (d : @check_is_finite S) : @check_is_finite (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Is_Finite (minset_enum S rS lteS fS) 
     | Certify_Is_Not_Finite => Certify_Is_Not_Finite 
     end.


Definition eqv_minset : ∀ {S : Type},  @po S -> @eqv (finite_set S)
:= λ {S} poS,
  let eqvS := po_eqv poS in  
  let rS   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in
  let fS   := eqv_new eqvS in  
  let lteS := po_lte poS in 
   {| 
      eqv_eq            := brel_minset rS lteS 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     ; eqv_type_ast       := Ast_type_set (eqv_type_ast (eqv_certs eqvS)) 
     ; eqv_brel_ast       := Ast_brel_eq_minset (eqv_brel_ast (eqv_certs eqvS)) 
     |}  
    ; eqv_witness       := nil 
    ; eqv_new           := brel_minset_new S rS wS 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (minset_negate S rS wS fS lteS) 
    ; eqv_data          := λ l, DATA_list (List.map (eqv_data eqvS) (uop_minset rS lteS l))   
    ; eqv_rep           := λ l, List.map (eqv_rep eqvS) (uop_minset rS lteS l)
    ; eqv_finite_d      := check_brel_minset_finite rS lteS (eqv_finite_d eqvS)  
    ; eqv_ast           := Ast_eqv_minset (po_ast poS)
   |}. 
  
End CAS.

Section Verify.

Theorem correct_eqv_minset : ∀ (S : Type) (P : A_po S),  
    eqv_minset (A2C_po S P) = A2C_eqv (finite_set S) (A_eqv_minset S P).
Proof. intros S P. 
       unfold eqv_minset, A_eqv_minset, A2C_eqv; simpl. 
       destruct P; simpl.
       destruct A_po_proofs; destruct A_po_eqv; simpl.
       destruct A_eqv_finite_d as [ [fS FS] | NFS ]; simpl; auto. 
Qed.        
  
 
End Verify.   
