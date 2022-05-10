From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.eqv.nat. 

Section Computation.
  
Definition functional_matrix (S : Type) := nat -> nat -> S.

Record square_matrix {S: Type} :=
{
  sqm_size   : nat 
; sqm_functional_matrix : nat -> nat -> S
}.

Fixpoint list_enum (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: list_enum n' 
  end.


Definition eq_functional_matrix {S: Type} (eq : brel S) (n : nat) (m : nat): brel (functional_matrix S) :=
  fun m1 => fun m2 =>
  let dim1 := list_enum n in
  let dim2 := list_enum m in                  
  forallb (fun i => forallb (fun j => eq (m1 i j) (m2 i j)) dim2) dim1. 


Definition eq_square_matrix {S: Type} (eq : brel S) : brel (@square_matrix S) :=
  fun m1 => fun m2 =>
    if brel_eq_nat (sqm_size m1) (sqm_size m2)
    then eq_functional_matrix eq
                       (sqm_size m1)
                       (sqm_size m2)
                       (sqm_functional_matrix m1)
                       (sqm_functional_matrix m2)                           
    else false.
                
End Computation. 

Section Matrix_Equality.

  Variables
    (R : Type)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).


  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
  

   Definition functional_matrix_congruence (m : functional_matrix R) :=
         ∀ i j i' j', i =n= i' -> j =n= j' -> (m i j) =r= (m i' j'). 

  Definition eq_functional_matrix_prop (m₁ m₂ : functional_matrix R) : Prop :=
    ∀ c d, m₁ c d =r= m₂ c d.

  Local Infix "=M=" := (eq_functional_matrix_prop) (at level 70).

  Lemma eq_functional_matrix_prop_reflexive : ∀ m, m =M= m .
  Proof. intros i j d. apply refR. Qed.

  Lemma eq_functional_matrix_prop_symmetric : ∀ m₁ m₂, m₁ =M= m₂ -> m₂ =M= m₁.
  Proof. intros m₁ m₂ A i j. exact (symR _ _ (A i j)). Qed.
  
  Lemma eq_functional_matrix_prop_transitive : 
    ∀ m m' m'', m =M= m' -> m' =M= m'' -> m =M= m''. 
  Proof. intros m m' m'' A B i j. exact (trnR _ _ _ (A i j) (B i j)). Qed.

  (* what exactly do we require? *) 
  Lemma eq_square_matrix_is_sound (m₁ m₂ : @square_matrix R) : 
    eq_functional_matrix_prop (sqm_functional_matrix m₁) (sqm_functional_matrix m₂) -> eq_square_matrix eqR m₁ m₂ = true. 
  Proof. intro A. destruct m₁, m₂. 
         induction sqm_size0; induction sqm_size1. 
         + compute; auto. 
         + admit. 
         + admit. 
         + unfold eq_square_matrix. admit.
Admitted. 

  
End Matrix_Equality.   
