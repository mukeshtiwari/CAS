Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.


Lemma brel_set_nil : ∀ (X : finite_set S), brel_set eq nil X = true -> X = nil. 
Proof. induction X; intro H. reflexivity. compute in H. discriminate. Defined. 


Lemma brel_set_intro : ∀ (X Y : finite_set S), (brel_subset eq X Y = true) * (brel_subset eq Y X = true)  → brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. unfold brel_set. unfold brel_and_sym. apply andb_is_true_right; auto. Defined. 

Lemma brel_set_elim : ∀ (X Y : finite_set S), 
     brel_set eq X Y = true -> (brel_subset eq X Y = true) * (brel_subset eq Y X = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]; auto. 
Defined. 

Lemma brel_set_intro_prop : ∀ (X Y : finite_set S), 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true)  → 
             brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. apply brel_set_intro. split. 
          apply brel_subset_intro in H1; auto. 
          apply brel_subset_intro in H2; auto. 
Defined. 

Lemma brel_set_elim_prop : ∀ (X Y : finite_set S),
     brel_set eq X Y = true -> 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       assert (A1 := brel_subset_elim S eq symS tranS _ _ H1). 
       assert (A2 := brel_subset_elim S eq symS tranS _ _ H2); auto. 
Defined. 


(* 
   ∀ (t : S) (s1 s2 : finite_set S),
   brel_set X s1 s2 = true → in_set X s1 t = in_set X s2 t
*) 
Lemma in_set_left_congruence : brel2_left_congruence (finite_set S) S (brel_set eq) (in_set eq). 
Proof. unfold brel2_left_congruence.
       intros t s1 s2 H. 
       apply brel_set_elim_prop in H; auto. destruct H as [L R]. 
       case_eq(in_set eq s1 t); intro J; 
       case_eq(in_set eq s2 t); intro K; auto.  
          rewrite (L t J) in K. assumption. 
          rewrite (R t K) in J. discriminate. 
Defined.

Lemma in_set_left_congruence_v3 : ∀ (a : S) (X Y : finite_set S),
    brel_set eq X Y = true -> in_set eq X a = true -> in_set eq Y a = true.
Proof. intros a X Y H1 H2. 
       apply brel_set_elim in H1.
       destruct H1 as [H1 _]. 
       assert (K := brel_subset_elim _ _ symS tranS X Y H1). 
       apply K; auto. 
Qed.



(***     brel_set eqv properties   ****)

(* move and_sym lemmas? *)
Lemma brel_and_sym_relexive (T : Type) (r : brel T) (refr : brel_reflexive T r) : brel_reflexive T (brel_and_sym r). 
Proof. unfold brel_reflexive, brel_and_sym. intros s. 
       rewrite (refr s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_transitive (T : Type) (r : brel T) (tranr : brel_transitive T r) : brel_transitive T (brel_and_sym r). 
Proof. unfold brel_transitive, brel_and_sym. intros s t u H1 H2. 
       apply andb_is_true_left in H1. destruct H1 as [H1_l H1_r].        
       apply andb_is_true_left in H2. destruct H2 as [H2_l H2_r].        
       rewrite (tranr _ _ _ H1_l H2_l).
       rewrite (tranr _ _ _ H2_r H1_r ). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_symmetric (T : Type) (r : brel T) : brel_symmetric T (brel_and_sym r). 
Proof. unfold brel_symmetric, brel_and_sym. intros s t H. 
       apply andb_is_true_left in H. destruct H as [H_l H_r].        
       rewrite H_l. rewrite H_r. simpl. reflexivity. 
Defined. 



Lemma in_set_left_congruence_v2 : ∀ (X Y : finite_set S),
    brel_set eq X Y = true -> ∀ (a : S), in_set eq X a = in_set eq Y a.
Proof. intros X Y H a. 
       apply brel_set_elim in H.
       destruct H as [H1 H2]. 
       assert (K1 := brel_subset_elim _ _ symS tranS X Y H1).
       assert (K2 := brel_subset_elim _ _ symS tranS Y X H2).        
       case_eq(in_set eq X a); intro J1; case_eq(in_set eq Y a); intro J2; auto.
       apply K1 in J1. rewrite J1 in J2. exact J2.
       apply K2 in J2. rewrite J1 in J2. exact J2.       
Qed.



Lemma in_set_congruence : ∀ (a b : S) (X Y : finite_set S),
    brel_set eq X Y = true -> eq a b = true -> in_set eq X a = in_set eq Y b.
Proof. intros a b X Y H1 H2.
       assert (J1 := in_set_right_congruence S eq symS tranS _ _ X H2).
       apply symS in H2. assert (J2 := in_set_right_congruence S eq symS tranS _ _ Y H2).        
       assert (Ma := in_set_left_congruence_v2 X Y H1 a).       
       assert (Mb := in_set_left_congruence_v2 X Y H1 b).
       case_eq(in_set eq X a); intro K1; case_eq(in_set eq Y b); intro K2; auto.
       rewrite (J1 K1) in Mb. rewrite <- Mb in K2. exact K2.
       rewrite (J2 K2) in Ma. rewrite K1 in Ma. exact Ma.
Qed. 


(***)


Lemma brel_set_reflexive : brel_reflexive (finite_set S) (brel_set eq). 
Proof. unfold brel_set. 
       apply brel_and_sym_relexive. 
       apply brel_subset_reflexive; auto. 
Defined.

Lemma brel_set_transitive : brel_transitive (finite_set S) (brel_set eq). 
Proof. unfold brel_set.
       apply brel_and_sym_transitive. 
       apply brel_subset_transitive; auto. 
Defined.

Lemma brel_set_symmetric : brel_symmetric (list S) (brel_set eq). 
Proof. unfold brel_set. apply brel_and_sym_symmetric. Defined. 

Lemma brel_set_congruence : brel_congruence (finite_set S) (brel_set eq) (brel_set eq). 
Proof. apply brel_congruence_self. 
       apply brel_set_symmetric; auto.  
       apply brel_set_transitive; auto.  
Defined. 

Lemma brel_set_not_trivial (s : S) : 
   brel_not_trivial (finite_set S) (brel_set eq) (λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil). 
Proof. intro X. destruct X; compute; auto. Qed. 

(* 
Lemma brel_set_rep_correct : ∀ (rep : unary_op S), 
          brel_rep_correct S eq rep →
              brel_rep_correct (finite_set S) (brel_set S eq) (uop_set_rep S eq rep). 
Proof. intros rep P l. 
       apply brel_set_intro. split. 
          apply brel_subset_intro;auto. intros s H. 
          apply brel_subset_intro;auto. admit.  
Defined. 

Lemma brel_set_rep_idempotent : ∀ (rep : unary_op S), 
          brel_rep_idempotent S eq rep →
              brel_rep_idempotent (finite_set S) (brel_set S eq) (uop_set_rep S eq rep). 
Proof. intros rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 
 *)

End Theory.

Section ACAS.


Definition eqv_proofs_set : ∀ (S : Type) (r : brel S),
    eqv_proofs S r → eqv_proofs (finite_set S) (brel_set r) 
:= λ S r eqv, 
   {| 
     A_eqv_congruence  := brel_set_congruence S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) 
   ; A_eqv_reflexive   := brel_set_reflexive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) 
   ; A_eqv_transitive  := brel_set_transitive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_set_symmetric S r 
   |}. 


Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S)
:= λ S eqvS,
  let eq := A_eqv_eq S eqvS in
  let s := A_eqv_witness S eqvS in 
   {| 
      A_eqv_eq     := brel_set eq 
    ; A_eqv_proofs := eqv_proofs_set S eq (A_eqv_proofs S eqvS)
    ; A_eqv_witness := s :: nil 
    ; A_eqv_new     := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil
    ; A_eqv_not_trivial := brel_set_not_trivial S eq s 

    ; A_eqv_data   := λ d, DATA_list (List.map (A_eqv_data S eqvS) d)  (* need DATA_set *) 
    ; A_eqv_rep    := λ d, d  (* fix this? *) 

    ; A_eqv_ast    := Ast_eqv_set (A_eqv_ast S eqvS)
   |}. 

End ACAS.

Section CAS.

Definition eqv_set : ∀ {S : Type},  @eqv S -> @eqv (finite_set S)
:= λ {S} eqvS,
  let eq := eqv_eq eqvS in
  let s := eqv_witness eqvS in 
 {| 
     eqv_eq       := brel_set eq 
    ; eqv_witness := s :: nil 
    ; eqv_new     := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil
    ; eqv_data    := λ d, DATA_list (List.map (eqv_data eqvS) d)  (* need DATA_set *) 
    ; eqv_rep     := λ d, d  (* fix this? *) 
    ; eqv_ast     := Ast_eqv_set (eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.


Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S),  
    eqv_set (A2C_eqv S E) = A2C_eqv (finite_set S) (A_eqv_set S E).
Proof. intros S E. destruct E, A_eqv_proofs. compute. reflexivity. Qed. 
  
 
End Verify.   
  