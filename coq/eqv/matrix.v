Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
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
  
Lemma brel_square_matrix_eq_row_congruence :
  forall (n m : nat), 
  brel_congruence _ (square_matrix_eq_row eq n m)
  (square_matrix_eq_row eq n m).
Proof.
  unfold brel_congruence.
  induction n; simpl.
  + intros * Ha Hb.
    case (eq (s m 0) (t m 0)) eqn:Hsm;
    case (eq (u m 0) (v m 0)) eqn:Hum.
    reflexivity.
    apply sym in Ha.
    assert (Hut := trn _ _ _ Ha Hsm).
    assert (A := trn _ _ _ Hut Hb).
    rewrite A in Hum.
    congruence.
    apply sym in Hb.
    assert (A := trn _ _ _ Ha Hum).
    assert (B := trn _ _ _ A Hb).
    rewrite B in Hsm.
    congruence.
    reflexivity.
  + intros * Ha Hb.
    apply Bool.andb_true_iff in Ha, Hb.
    destruct Ha as [Hal Har].
    destruct Hb as [Hbl Hbr].
    f_equal.
    case (eq (s m (Datatypes.S n)) (t m (Datatypes.S n))) eqn:Ha;
    case (eq (u m (Datatypes.S n)) (v m (Datatypes.S n))) eqn:Hb.
    reflexivity.
    apply sym in Hal.
    assert (A := trn _ _ _ Hal Ha).
    assert (B := trn _ _ _ A Hbl).
    rewrite B in Hb.
    congruence.
    apply sym in Hbl.
    assert (A := trn _ _ _ Hal Hb).
    assert (B := trn _ _ _ A Hbl).
    rewrite B in Ha.
    congruence.
    reflexivity.
    eapply IHn; try assumption.
Qed.

  

Lemma brel_square_matrix_eq_all_rows_congruence : 
  forall (n m : nat),
  brel_congruence _ (square_matrix_eq_all_rows eq n m)
  (square_matrix_eq_all_rows eq n m).
Proof.
  unfold brel_congruence.
  induction n; simpl. 
  + intros * Ha Hb.
    eapply brel_square_matrix_eq_row_congruence;
    try assumption.
  + intros * Ha Hb.
    apply Bool.andb_true_iff in Ha, Hb.
    destruct Ha as [Hal Har].
    destruct Hb as [Hbl Hbr].
    f_equal.
    eapply brel_square_matrix_eq_row_congruence;
    try assumption.
    eapply IHn;
    try assumption.
Qed.


Lemma brel_square_matrix_eq_aux_congruence :  
  forall n, 
  brel_congruence _ (square_matrix_eq_aux eq n)
  (square_matrix_eq_aux eq n).
Proof.
  unfold brel_congruence.
  destruct n; simpl.
  + intros ? ? ? ? ? ?.
    reflexivity.
  + intros ? ? ? ? Ha Hb.
    eapply brel_square_matrix_eq_all_rows_congruence;
    [exact Ha | exact Hb].
Qed.





Lemma brel_square_matrix_eq_congruence : 
  brel_congruence _ (square_matrix_eq eq)
  (square_matrix_eq eq).
Proof.
  unfold brel_congruence;
  intros * Ha Hb.
  unfold square_matrix_eq in *.
  case (Nat.eqb (sm_size s) (sm_size u)) eqn:Hsu;
  case (Nat.eqb (sm_size t) (sm_size v)) eqn:Htv;
  case (Nat.eqb (sm_size s) (sm_size t)) eqn:Hst; 
  case (Nat.eqb (sm_size u) (sm_size v)) eqn:Huv;
  try congruence.
  rewrite PeanoNat.Nat.eqb_eq in Hsu, Htv, Hst, Huv.
  rewrite Hsu.
  eapply brel_square_matrix_eq_aux_congruence;
  try assumption.
  rewrite <-Hsu; exact Ha.
  assert (Ht : (sm_size u) = (sm_size t)).
  nia. rewrite Ht; clear Ht.
  exact Hb.
  rewrite PeanoNat.Nat.eqb_eq in Hsu, Htv, Hst.
  rewrite PeanoNat.Nat.eqb_neq in Huv.
  congruence.
  rewrite PeanoNat.Nat.eqb_eq in Hsu, Htv, Huv.
  rewrite PeanoNat.Nat.eqb_neq in Hst.
  congruence.
Qed.


(* We need a witness on S *)
Variables 
  (s : S). 
  
Definition unit_matrix : @square_matrix S := 
    {|
      sm_size := 1;
      sm_matrix := fun _ _ => s
    |}.

Definition two_by_two_matrix : @square_matrix S :=
    {|
      sm_size := 2;
      sm_matrix := fun _ _ => s
    |}.

Definition three_by_three_matrix : @square_matrix S :=
    {|
      sm_size := 3;
      sm_matrix := fun _ _ => s
    |}.


    
    
Definition brel_square_matrix_new : @square_matrix S -> @square_matrix S :=
  fun mt => 
    if @square_matrix_eq S eq mt unit_matrix then two_by_two_matrix 
    else unit_matrix.
    
  
Lemma brel_square_matrix_eq_not_trivial : 
  brel_not_trivial 
    (@square_matrix S)  (* Type *)
    (@square_matrix_eq S eq) (* binary relation *)
    brel_square_matrix_new. (*fun square matris -> square matrix *)
Proof.
  unfold brel_not_trivial; intros u.
  unfold brel_square_matrix_new.
  case (square_matrix_eq eq u unit_matrix) eqn:Hes.
  split.
  case (square_matrix_eq eq u two_by_two_matrix) eqn:Heu.
  rewrite <-Heu in Hes.
  unfold square_matrix_eq in * |-.
  simpl in *.
  case (Nat.eqb (sm_size u) 1) eqn:Hsuo;
  case (Nat.eqb (sm_size u) 2) eqn:Hsut.
  rewrite PeanoNat.Nat.eqb_eq in Hsuo, Hsut.
  try nia.
  congruence.
  rewrite PeanoNat.Nat.eqb_neq in Hsuo.
  rewrite PeanoNat.Nat.eqb_eq in Hsut.
  unfold square_matrix_eq_aux in * |-.
  rewrite Hsut in Hes, Heu.
  simpl in *.
  rewrite <-Hes in Heu.
  congruence.
  congruence.
  reflexivity.

  case (square_matrix_eq eq two_by_two_matrix u) eqn:Heu.
  rewrite <-Heu in Hes. 
  unfold square_matrix_eq in * |-.
  assert (Ht : (sm_size unit_matrix) = 1).
  reflexivity.
  rewrite Ht in Hes; clear Ht.
  assert (Ht : (sm_size two_by_two_matrix) = 2).
  reflexivity.
  rewrite Ht in Hes; clear Ht.
  case (Nat.eqb (sm_size u) 1) eqn:Hsuo;
  case (Nat.eqb 2 (sm_size u)) eqn:Hsut.
  rewrite PeanoNat.Nat.eqb_eq in Hsuo, Hsut.
  try nia.
  rewrite PeanoNat.Nat.eqb_eq in Hsuo.
  rewrite PeanoNat.Nat.eqb_neq in Hsut.
  unfold square_matrix_eq_aux in * |-.
  rewrite Hsuo in Hes, Heu.
  simpl in *.
  congruence.
  assert (Ht : (sm_size two_by_two_matrix) = 2).
  reflexivity.
  rewrite Ht in Heu; clear Ht.
  rewrite Hsut in Heu.
  rewrite <-Hes in Heu.
  congruence.
  assert (Ht : (sm_size two_by_two_matrix) = 2).
  reflexivity.
  rewrite Ht in Heu.
  rewrite Hsut in Heu.
  congruence.
  reflexivity.
  
  split.
  exact Hes.
  unfold square_matrix_eq in *.
  assert (Ht : (sm_size unit_matrix) = 1).
  reflexivity.
  rewrite Ht in Hes.
  rewrite Ht.
  case (Nat.eqb (sm_size u) 1) eqn:Hsuo.
  rewrite PeanoNat.Nat.eqb_eq in Hsuo.
  rewrite Hsuo in Hes.
  rewrite Hsuo.
  simpl in *. 
  case (eq s (sm_matrix u 0 0)) eqn:Hsm.
  apply sym in Hsm.
  rewrite Hes in Hsm.
  congruence.
  reflexivity.
  rewrite PeanoNat.Nat.eqb_neq in Hsuo.
  case (Nat.eqb 1 (sm_size u)) eqn:Hst.
  rewrite PeanoNat.Nat.eqb_eq in Hst.
  nia.
  reflexivity.
Qed.




Lemma brel_square_matrix_eq_not_exactly_two :  
  brel_not_exactly_two 
    (@square_matrix S) 
    (@square_matrix_eq _ eq).
Proof.
  unfold brel_not_exactly_two.
  apply brel_at_least_thee_implies_not_exactly_two.
  apply brel_square_matrix_eq_symmetric.
  apply brel_square_matrix_eq_transitive.
  unfold brel_at_least_three.
  exists (unit_matrix, (two_by_two_matrix, three_by_three_matrix)).
  unfold square_matrix_eq; simpl;
  repeat (split; try reflexivity).
Qed.





(*
How to prove this?
*)
Lemma brel_square_matrix_is_not_finite : 
  carrier_is_not_finite 
    (@square_matrix S) 
    (@square_matrix_eq S eq).
Proof.
  unfold carrier_is_not_finite.
  intros ?.
Admitted.





End Theory.   

Section ACAS.


Definition eqv_proofs_square_matrix_eq : forall (S : Type) 
  (r : brel S), eqv_proofs S r -> eqv_proofs _ (square_matrix_eq r) 
  := λ (S : Type) (r : brel S) (H : eqv_proofs S r),
    match H with
    | {|
        A_eqv_congruence := _;
        A_eqv_reflexive  := Hrefl;
        A_eqv_transitive := Htrn;
        A_eqv_symmetric  := Hsym
      |} =>
            {|
              A_eqv_congruence := brel_square_matrix_eq_congruence S r Hsym Htrn;
              A_eqv_reflexive  := brel_square_matrix_eq_reflexive S r Hrefl;
              A_eqv_transitive := brel_square_matrix_eq_transitive S r Htrn;
              A_eqv_symmetric  := brel_square_matrix_eq_symmetric S r Hsym
            |}
    end.


Definition A_eqv_square_matrix_eq : forall (S : Type),
  A_eqv S -> A_eqv (@square_matrix S).
Proof.
  intros ? H.
  destruct H.
  econstructor.
  +
  eapply eqv_proofs_square_matrix_eq;
  exact A_eqv_proofs.
  +
  exact (@unit_matrix _ A_eqv_witness).
  +
  eapply brel_square_matrix_eq_not_trivial;
  destruct A_eqv_proofs; try assumption.
  +
  destruct A_eqv_proofs;
  exact (inr (brel_square_matrix_eq_not_exactly_two S A_eqv_eq 
    A_eqv_symmetric
    A_eqv_transitive
    A_eqv_witness)).
  + destruct A_eqv_proofs;
    exact (inr (brel_square_matrix_is_not_finite S A_eqv_eq
      A_eqv_reflexive
      A_eqv_symmetric
      A_eqv_transitive
      A_eqv_witness)).
  + (* circular dependency? *) admit.
  + exact (brel_square_matrix_new S A_eqv_eq A_eqv_witness).
  + exact A_eqv_ast.
  
Admitted.



 
End ACAS. 


Section CAS.

Definition eqv_square_matrix_eq : forall {S : Type},
  @eqv S -> @eqv (@square_matrix S).
Proof.
  intros ? H.
  destruct H.
  econstructor.
  + exact (@square_matrix_eq S eqv_eq).
  + econstructor.
    ++ exact (@Assert_Brel_Congruence (@square_matrix S)).
    ++ exact (@Assert_Reflexive (@square_matrix S)).
    ++ exact ((@Assert_Transitive (@square_matrix S))).
    ++ exact ((@Assert_Symmetric (@square_matrix S))).
  + exact (@unit_matrix _ eqv_witness).
  + exact (@brel_square_matrix_new _ eqv_eq eqv_witness).
  + exact (Certify_Not_Exactly_Two
    (not_ex2 (@square_matrix_eq _ eqv_eq) (@unit_matrix _ eqv_witness) 
      (@two_by_two_matrix _ eqv_witness)
      (@three_by_three_matrix _ eqv_witness))).
  + exact Certify_Is_Not_Finite.
  + admit.
  + exact (@brel_square_matrix_new _ eqv_eq eqv_witness).  
  + admit.
Admitted.
  
  
End CAS. 


Section Verify.


End Verify. 
