From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.sg.properties
     coq.algorithms.matrix_definition
     coq.algorithms.matrix_algorithms. 

Section Matrix_Addition.

  Variables
    (R : Type)
    (eqR  : brel R)    
    (zeroR : R)
    (plusR : binary_op R)
    .

  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Notation "a +M b" := (matrix_add plusR a b) (at level 70).  
  Local Notation "a =M= b" := (eq_functional_matrix_prop R eqR a b) (at level 70).
  Local Notation "~M m" := (functional_matrix_congruence _ eqR m) (at level 70).

  Lemma matrix_add_congruence (congrP : bop_congruence R eqR plusR) :
      ∀ m₁ m₂ m₃ m₄, (m₁ =M= m₃) -> (m₂ =M= m₄) -> (m₁ +M m₂) =M= (m₃ +M m₄). 
  Proof. intros m₁ m₂ m₃ m₄ H₁ H₂. unfold matrix_add.
         intros a b.
         apply congrP.
         apply H₁; intros *; apply refN.
         apply H₂; intros *; apply refN.
  Qed.

  Lemma matrix_add_preserves_congruence (congrP : bop_congruence R eqR plusR) :
      ∀ m₁ m₂, ~M m₁ -> ~M m₂ -> ~M (m₁ +M m₂). 
  Proof. intros m₁ m₂ A B i j i' j' C D. 
         unfold matrix_add.
         apply congrP.
         + apply A; auto.
         + apply B; auto.          
  Qed.

  Lemma matrix_add_assoc (plus_associative : bop_associative R eqR plusR) :
      ∀ m₁ m₂ m₃, ((m₁ +M m₂) +M m₃) =M= (m₁ +M (m₂ +M m₃)). 
  Proof. unfold matrix_add; intros m₁ m₂ m₃ a b. 
         rewrite plus_associative.
         reflexivity. 
  Qed.
  
  Lemma matrix_add_comm (plus_commutative  : bop_commutative R eqR plusR): 
      ∀ m₁ m₂, (m₁ +M m₂) =M= (m₂ +M m₁). 
  Proof. intros m₁ m₂ a b; unfold matrix_add.
         rewrite plus_commutative.
         reflexivity.
  Qed.
  
  Lemma matrix_add_idempotence (plus_idempotence : bop_idempotent R eqR plusR):
    ∀ m, (m +M m) =M= m .
  Proof. unfold matrix_add; intros m a b. apply plus_idempotence. Qed.
  
    
End Matrix_Addition.   

