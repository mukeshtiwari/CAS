From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.sg.properties
     coq.algorithm.matrix_definition
     coq.algorithm.matrix_equality. 

Section Matrix_Addition.
  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (finN : list Node)
    (refN : brel_reflexive Node eqN). 

  Variables
    (R : Type)
    (eqR  : brel R)    
    (zeroR : R)
    (plusR : binary_op R) 
    .

  (* pointwise addition to two matrices *)
  Definition matrix_add (m₁ m₂ : Matrix Node R) : Matrix Node R :=
    fun c d => plusR (m₁ c d) (m₂ c d).

  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Notation "a +M b" := (matrix_add a b) (at level 70).  
  Local Notation "a =M= b" := (matrix_equality Node R eqR a b) (at level 70).

  (*
   Lemma mat_add_cong_gen : 
      forall m₁ m₂ m₃ m₄ c d, 
      two_mat_congr Node R eqR m₁ m₃ -> 
      two_mat_congr Node R eqR m₂ m₄ -> 
      matrix_add Node R plusR m₁ m₂ c d =r= 
      matrix_add Node R plusR m₃ m₄ c d = true.
   *) 
  Lemma mat_add_cong_gen (congrP : bop_congruence R eqR plusR) : 
      ∀ m₁ m₂ m₃ m₄ c d, (m₁ =M= m₃) -> (m₂ =M= m₄) -> (m₁ +M m₂) c d =r= (m₃ +M m₄) c d.
  Proof. intros * H₁ H₂. unfold matrix_add.
         apply congrP.
         apply H₁; intros *; apply refN.
         apply H₂; intros *; apply refN.
  Qed.

  (* NEW NAME?  matrix_add_congruence!  *) 
  Lemma mat_add_cong_gen_CLEANER (congrP : bop_congruence R eqR plusR) :
      ∀ m₁ m₂ m₃ m₄, (m₁ =M= m₃) -> (m₂ =M= m₄) -> (m₁ +M m₂) =M= (m₃ +M m₄). 
  Proof. intros m₁ m₂ m₃ m₄ H₁ H₂. unfold matrix_add.
         intros a b.
         apply congrP.
         apply H₁; intros *; apply refN.
         apply H₂; intros *; apply refN.
  Qed.

  (*
      Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add _ _ plusR m₁ (matrix_add _ _ plusR m₂ m₃) c d =r= 
      matrix_add _ _ plusR (matrix_add Node R plusR m₁ m₂) m₃ c d = true.
  *) 
  Lemma matrix_add_assoc (plus_associative : bop_associative R eqR plusR) :
      ∀ m₁ m₂ m₃ c d, ((m₁ +M m₂) +M m₃) c d =r= (m₁ +M (m₂ +M m₃)) c d. 
  Proof. unfold matrix_add; intros.
         rewrite plus_associative.
         reflexivity. 
  Qed.

  Lemma matrix_add_assoc_CLEANER (plus_associative : bop_associative R eqR plusR) :
      ∀ m₁ m₂ m₃, ((m₁ +M m₂) +M m₃) =M= (m₁ +M (m₂ +M m₃)). 
  Proof. unfold matrix_add; intros m₁ m₂ m₃ a b. 
         rewrite plus_associative.
         reflexivity. 
  Qed.
  
  Lemma matrix_add_comm (plus_commutative  : bop_commutative R eqR plusR): 
      ∀ m₁ m₂ c d, (m₁ +M m₂) c d =r= (m₂ +M m₁) c d. 
  Proof. intros; unfold matrix_add.
         rewrite plus_commutative.
         reflexivity.
  Qed.

  Lemma matrix_add_comm_CLEANER (plus_commutative  : bop_commutative R eqR plusR): 
      ∀ m₁ m₂, (m₁ +M m₂) =M= (m₂ +M m₁). 
  Proof. intros m₁ m₂ a b; unfold matrix_add.
         rewrite plus_commutative.
         reflexivity.
  Qed.
  
  Lemma matrix_add_idempotence (plus_idempotence : bop_idempotent R eqR plusR):
    ∀ m c d, (m +M m) c d =r= m c d.
  Proof. unfold matrix_add; intros *. apply plus_idempotence. Qed.

  Lemma matrix_add_idempotence_CLEANER (plus_idempotence : bop_idempotent R eqR plusR):
    ∀ m, (m +M m) =M= m .
  Proof. unfold matrix_add; intros m a b. apply plus_idempotence. Qed.
  
    
End Matrix_Addition.   

