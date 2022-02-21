
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.


Section Computation.

(* define type matrix 
   define = for matricies 
*)

Record square_matrix {S: Type} := 
{
  sm_size   : nat 
; sm_matrix : nat -> nat -> S
}.

Local Open Scope bool_scope.

Fixpoint square_matrix_eq_row {S: Type} (eq : brel S) (col : nat) (row : nat) : brel (nat -> nat -> S) :=
  fun f => fun h =>
  match col with
  | 0 => eq (f row col) (h row col) 
  | S col' =>
       (eq (f row col) (h row col)) && 
       (square_matrix_eq_row eq col' row f h)
  end. 
  
Fixpoint square_matrix_eq_all_rows {S: Type} (eq : brel S) (row : nat) (n : nat) : brel (nat -> nat -> S) :=
  fun f => fun h =>
  match row with
  | 0 => square_matrix_eq_row eq n 0 f h
  | S row' =>
       (square_matrix_eq_row eq n row f h) && 
       (square_matrix_eq_all_rows eq row' n f h)
  end . 
  
Definition square_matrix_eq_aux {S: Type} (eq : brel S) (n : nat) : brel (nat -> nat -> S) :=
     fun f => fun h =>
     match n with
     | 0 => true
     | S n' => square_matrix_eq_all_rows eq n' n' f h
     end.                                          
  
Local Open Scope nat_scope.

Definition square_matrix_eq {S: Type} (eq : brel S) : brel (@square_matrix S) :=
  fun a => fun b =>
   if Nat.eqb (sm_size a) (sm_size b)
   then square_matrix_eq_aux eq (sm_size a) (sm_matrix a) (sm_matrix b)
   else false .

  
End Computation. 


Section Theory.

Variables (S : Type)
          (eq : brel S)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (trn : brel_transitive S eq). 



Lemma brel_square_matrix_eq_row_reflexive : forall (n m : nat), brel_reflexive (nat → nat → S) (square_matrix_eq_row eq n m). 
Proof. unfold brel_reflexive. induction n. 
       + intros m s. simpl. apply ref. 
       + intros m s. simpl. rewrite (ref (s m (Datatypes.S n))).
         rewrite IHn. auto. 
Qed. 

Lemma brel_square_matrix_eq_all_rows_reflexive : forall (n m : nat), brel_reflexive (nat → nat → S) (square_matrix_eq_all_rows eq n m). 
Proof. unfold brel_reflexive. induction n. 
       + intros m s. simpl.  apply brel_square_matrix_eq_row_reflexive. 
       + intros m s. simpl. rewrite IHn.
         assert (A := brel_square_matrix_eq_row_reflexive m (Datatypes.S n) s).
         rewrite A. auto. 
Qed.        
Lemma brel_square_matrix_eq_aux_reflexive (n : nat) : brel_reflexive (nat → nat → S) (square_matrix_eq_aux eq n). 
Proof. unfold brel_reflexive.
       intro s. destruct n. 
       + compute; auto. 
       + simpl. apply brel_square_matrix_eq_all_rows_reflexive. 
Qed.          

Lemma brel_square_matrix_eq_reflexive : brel_reflexive (@square_matrix S) (square_matrix_eq eq). 
Proof. unfold brel_reflexive.
       intro s. destruct s. unfold square_matrix_eq. simpl. 
       rewrite PeanoNat.Nat.eqb_refl.
       apply brel_square_matrix_eq_aux_reflexive. 
Qed. 


End Theory.   

Section ACAS.

End ACAS. 


Section CAS.

End CAS. 


Section Verify.


End Verify. 
