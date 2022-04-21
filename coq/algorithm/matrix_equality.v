From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.algorithm.matrix_definition. 

Section Matrix_Equality.


  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (finN : list Node).
  Variables
    (R : Type)
    (eqR  : brel R)
    (trnR : brel_transitive R eqR).
  
  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Notation "a =n= b" := (eqN a b = true) (at level 70).

  (* congruence relation on matrix 

  call this matrix_congruence? 
  *)
  Definition mat_cong (m : Matrix Node R) : Prop :=
    ∀ a b c d, a =n= c -> b =n= d -> m a b =r= m c d.

(* two matrices are equal only if they are equal every point 
  Definition two_mat_congr (m₁ m₂ : Matrix Node R) : Prop :=
    ∀ c d, m₁ c d =r= m₂ c d.
*)
  Definition matrix_equality (m₁ m₂ : Matrix Node R) : Prop :=
    ∀ c d, m₁ c d =r= m₂ c d.
  
(* more general version 
  Definition two_mat_congr_gen (m₁ m₂ : Matrix Node R) : Prop :=
    ∀ a b c d, a =n= c -> b =n= d -> m₁ a b =r= m₂ c d. 
 
   Is this really needed?  two_mat_congr_gen is never used. 
*)
Lemma matrix_equality_gen (m₁ m₂ : Matrix Node R) (cong2 : mat_cong m₂) (eq : matrix_equality m₁ m₂) :
    ∀ a b c d, a =n= c -> b =n= d -> m₁ a b =r= m₂ c d.
Proof. intros a b c d A B.
         assert (C := eq a b). 
         assert (D := cong2 _ _ _ _ A B). 
         exact (trnR _ _ _ C D). 
Qed.
  
End Matrix_Equality.   
