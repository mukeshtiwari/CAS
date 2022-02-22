
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import Lia.
Local Open Scope bool_scope.
Local Open Scope nat_scope.

Section Computation.

(* define type matrix 
   define = for matricies 
*)

Record square_matrix {S: Type} := 
{
  sm_size   : nat 
; sm_matrix : nat -> nat -> S
}.



Fixpoint square_matrix_eq_row {S: Type} (eq : brel S) 
  (col : nat) (row : nat) : brel (nat -> nat -> S) :=
  fun f => fun h =>
  match col with
  | 0 => eq (f row col) (h row col) 
  | S col' =>
       (eq (f row col) (h row col)) && 
       (square_matrix_eq_row eq col' row f h)
  end. 
  
Fixpoint square_matrix_eq_all_rows {S: Type} (eq : brel S)
  (row : nat) (n : nat) : brel (nat -> nat -> S) :=
  fun f => fun h =>
  match row with
  | 0 => square_matrix_eq_row eq n 0 f h
  | S row' =>
       (square_matrix_eq_row eq n row f h) && 
       (square_matrix_eq_all_rows eq row' n f h)
  end . 
  
Definition square_matrix_eq_aux {S: Type} (eq : brel S)
  (n : nat) : brel (nat -> nat -> S) :=
  fun f => fun h =>
  match n with
  | 0 => true
  | S n' => square_matrix_eq_all_rows eq n' n' f h
  end.                                          



Definition square_matrix_eq {S: Type} (eq : brel S) 
  : brel (@square_matrix S) :=
  fun a => fun b =>
   if Nat.eqb (sm_size a) (sm_size b)
   then square_matrix_eq_aux eq (sm_size a) (sm_matrix a) (sm_matrix b)
   else false.

  
End Computation. 


Section Theory.

Variables 
  (S : Type)
  (eq : brel S)
  (ref : brel_reflexive S eq)
  (sym : brel_symmetric S eq)
  (trn : brel_transitive S eq). 



Lemma brel_square_matrix_eq_row_reflexive : forall (n m : nat), 
  brel_reflexive (nat → nat → S) (square_matrix_eq_row eq n m). 
Proof. unfold brel_reflexive. induction n. 
       + intros m s. simpl. apply ref. 
       + intros m s. simpl. rewrite (ref (s m (Datatypes.S n))).
         rewrite IHn. auto. 
Qed. 

Lemma brel_square_matrix_eq_all_rows_reflexive : forall (n m : nat),
  brel_reflexive (nat → nat → S) (square_matrix_eq_all_rows eq n m). 
Proof. unfold brel_reflexive. induction n. 
       + intros m s. simpl.  apply brel_square_matrix_eq_row_reflexive. 
       + intros m s. simpl. rewrite IHn.
         assert (A := brel_square_matrix_eq_row_reflexive m (Datatypes.S n) s).
         rewrite A. auto. 
Qed.  


Lemma brel_square_matrix_eq_aux_reflexive (n : nat) : 
  brel_reflexive (nat → nat → S) (square_matrix_eq_aux eq n). 
Proof. unfold brel_reflexive.
       intro s. destruct n. 
       + compute; auto. 
       + simpl. apply brel_square_matrix_eq_all_rows_reflexive. 
Qed.          


Lemma brel_square_matrix_eq_reflexive : 
  brel_reflexive (@square_matrix S) (square_matrix_eq eq). 
Proof. unfold brel_reflexive.
       intro s. destruct s. unfold square_matrix_eq. simpl. 
       rewrite PeanoNat.Nat.eqb_refl.
       apply brel_square_matrix_eq_aux_reflexive. 
Qed. 



Lemma brel_square_matrix_eq_row_symmetric :
  forall (n m : nat), 
  brel_symmetric _ (square_matrix_eq_row eq n m).
Proof.
  unfold brel_symmetric.
  induction n; simpl.
  + intros * Heq.
    apply sym;
    assumption.
  + intros * Heq.
    apply Bool.andb_true_iff in Heq.
    destruct Heq as [Heql Heqr].
    rewrite (IHn _ _ _ Heqr). 
    apply sym in Heql. 
    rewrite Heql.
    reflexivity.
Qed.





Lemma brel_square_matrix_eq_all_rows_symmetric : 
  forall (n m : nat),
  brel_symmetric _ (square_matrix_eq_all_rows eq n m).
Proof.
  unfold brel_symmetric.
  induction n; simpl.
  + intros ? ? ? Hsq.
    eapply brel_square_matrix_eq_row_symmetric;
    assumption.
  + intros * Hsq.
    apply Bool.andb_true_iff in Hsq.
    destruct Hsq as [Hsql Hsqr].
    rewrite (IHn _ _ _ Hsqr).
    rewrite brel_square_matrix_eq_row_symmetric.
    reflexivity.
    exact Hsql.
Qed.  




Lemma brel_square_matrix_eq_aux_symmetric :  
  forall n, brel_symmetric _ (square_matrix_eq_aux eq n).
Proof.
  unfold brel_symmetric.
  destruct n; simpl.
  + intros ? ? ?.
    reflexivity.
  + intros ? ? Hsq.
    eapply brel_square_matrix_eq_all_rows_symmetric;
    assumption.
Qed.



Lemma brel_square_matrix_eq_symmetric : 
  brel_symmetric (@square_matrix S) (square_matrix_eq eq).
Proof.
  unfold brel_symmetric;
  intros * Hsq.
  unfold square_matrix_eq in *.
  case (Nat.eqb (sm_size s) (sm_size t)) eqn:Ht.
  +
  apply PeanoNat.Nat.eqb_eq in Ht.
  rewrite Ht, PeanoNat.Nat.eqb_refl.
  eapply brel_square_matrix_eq_aux_symmetric.
  rewrite Ht in Hsq.
  exact Hsq.
  +
  congruence.
Qed.
  

Lemma brel_square_matrix_eq_row_transitive :
  forall (n m : nat), 
  brel_transitive _ (square_matrix_eq_row eq n m).
Proof.
  unfold brel_transitive.
  induction n; simpl.
  + intros * Heq.
    apply trn;
    assumption.
  + intros * Ha Hb.
    apply Bool.andb_true_iff in Ha, Hb.
    destruct Ha as [Hal Har].
    destruct Hb as [Hbl Hbr].
    erewrite IHn, trn.
    reflexivity.
    exact Hal.
    exact Hbl.
    exact Har.
    exact Hbr.
Qed.  


Lemma brel_square_matrix_eq_all_rows_transitive : 
  forall (n m : nat),
  brel_transitive _ (square_matrix_eq_all_rows eq n m).
Proof.
  unfold brel_transitive.
  induction n; simpl.
  + intros ? ? ? Ha Hb.
    eapply brel_square_matrix_eq_row_transitive;
    assumption.
  + intros * Ha Hb.
    apply Bool.andb_true_iff in Ha, Hb.
    destruct Ha as [Hal Har].
    destruct Hb as [Hbl Hbr].
    erewrite IHn,
    brel_square_matrix_eq_row_transitive;
    try reflexivity.
    exact Hal.
    exact Hbl.
    exact Har.
    exact Hbr.
Qed.
      

Lemma brel_square_matrix_eq_aux_transitive :  
  forall n, brel_transitive _ (square_matrix_eq_aux eq n).
Proof.
  unfold brel_transitive.
  destruct n; simpl.
  + intros ? ? ? ? ?.
    reflexivity.
  + intros ? ? ? Ha Hb.
    eapply brel_square_matrix_eq_all_rows_transitive;
    [exact Ha | exact Hb].
Qed.

Lemma brel_square_matrix_eq_transitive : 
  brel_transitive _ (square_matrix_eq eq).
Proof.
  unfold brel_transitive;
  intros * Ha Hb.
  unfold square_matrix_eq in *.
  case (Nat.eqb (sm_size s) (sm_size t)) eqn:Hat;
  case (Nat.eqb (sm_size t) (sm_size u)) eqn:Hbt.
  assert (Hn : Nat.eqb (sm_size s) (sm_size u) = true).
  rewrite PeanoNat.Nat.eqb_eq in Hat. 
  rewrite Hat.
  exact Hbt.
  rewrite Hn; clear Hn.
  eapply brel_square_matrix_eq_aux_transitive.
  exact Ha.
  rewrite PeanoNat.Nat.eqb_eq in Hat. 
  rewrite Hat.
  exact Hb.
  all: congruence.
Qed.
  


End Theory.   

Section ACAS.

End ACAS. 


Section CAS.

End CAS. 


Section Verify.


End Verify. 
