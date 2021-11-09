From Coq Require Import List Utf8
  FunctionalExtensionality.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory.
Import ListNotations.

(* See if it can be proved using coq/eqv/properties *)
Definition eq_congruent (R : Type) (eqR : brel R) : Prop  := 
  forall a b : R, eqR a b = true -> a = b.

Section Matrix.
  Variables 
    (Node : Type)
    (finN : finite_set Node)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN)
    (memN : forall x : Node, in_list eqN finN x = true)

    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : R -> R -> R)
    (* Semiring Axiom on R *)
    (zero_left_identity_plus  : forall r : R, plusR zeroR r = r)
    (zero_right_identity_plus : forall r : R, plusR r zeroR = r)
    (plus_associative : forall a b c : R, plusR a (plusR b c) = 
      plusR (plusR a b) c)
    (plus_commutative : forall a b : R, plusR a b = plusR b a)
    (one_left_identity_mul    : forall r : R, mulR oneR r = r)
    (one_right_identity_mul   : forall r : R, mulR r oneR = r)
    (mult_associative : forall a b c : R, mulR a (mulR b c) = 
      mulR (mulR a b) c)
    (left_distributive_mul_over_plus : 
      forall a b c : R, mulR a (plusR b c) = plusR (mulR a b) (mulR a c))
    (right_distributive_mul_over_plus :
      forall a b c : R, mulR (plusR a b) c = plusR (mulR a c) (mulR b c))
    (zero_left_anhilator_mul  : forall a : R, mulR zeroR a = zeroR)
    (zero_right_anhilator_mul : forall a : R, mulR a zeroR = zeroR)
    (* end of axioms *)
    (* equivalence relation on R *)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (conR : eq_congruent R eqR).
    (* end of equivalence relation *)
    
    
    Declare Scope Mat_scope.
    Delimit Scope Mat_scope with R.
    Bind Scope Mat_scope with R.
    Local Open Scope Mat_scope.
  

    Local Notation "0" := zeroR : Mat_scope.
    Local Notation "1" := oneR : Mat_scope.
    Local Infix "+" := plusR : Mat_scope.
    Local Infix "*" := mulR : Mat_scope.
    Local Infix "=r=" := eqR (at level 70) : Mat_scope.
    Local Infix "=n=" := eqN (at level 70) : Mat_scope.

    
    Theorem eqr_eq : forall a b : R, eqR a b = true <-> @eq R a b.
    Proof.
      intros a b; split; 
      intro Hab.
      + apply conR; exact Hab.
      + subst; apply refR.
    Qed. (* Qed or Defined, *)

    (* (square) matrix is a function. It's easy to prove various 
      properties of matrix with this representation. However, 
      it's not very efficient, at least in my experience, 
      so later we will replace it by another similar more 
      efficient structure for computation *) 
    
    Definition Matrix : Type := Node -> Node -> R.



    (* returns the cth row of m *)
    Definition get_row (m : Matrix) (c : Node) : Node -> R := 
      fun d => m c d.

    (* returns the cth column of m *)
    Definition get_col (m : Matrix) (c : Node) : Node -> R :=
      fun d => m d c.

    (* zero matrix, additive identity of plus *)
    Definition zero_matrix : Node -> Node -> R := 
      fun _ _ => 0.
    


    (* identity matrix, mulitplicative identity of mul *)
    (* Idenitity Matrix *)
    Definition I : Matrix := fun (c d : Node) =>
      match c =n= d with 
      | true => 1
      | false => 0 
      end.
    
    
    (* transpose the matrix m *)
    Definition transpose (m : Matrix) : Matrix := 
      fun (c d : Node) => m d c.

    Definition transpose_transpose_id : ∀ (m : Matrix) (c d : Node), 
      (((transpose (transpose m)) c d) =r= (m c d)) = true.
    Proof. 
      intros ? ? ?; unfold transpose; 
      simpl. 
      apply refR.
    Defined.

    (* pointwise addition to two matrices *)
    Definition matrix_add (m₁ m₂ : Matrix) : Matrix :=
      fun c d => (m₁ c d + m₂ c d).

    Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
      match l with 
      | [] => 0
      | h :: t => f h + sum_fn f t
      end.

    Lemma sum_fn_add : forall (f g : Node -> R) (l : list Node), 
      (sum_fn (fun x => f x + g x) l) =r= (sum_fn f l +  sum_fn g l) = true.
    Proof.
      intros ? ?.
      induction l; simpl.
      + rewrite zero_left_identity_plus.
        apply refR.
      + rewrite eqr_eq in IHl; rewrite IHl.
        apply eqr_eq.
        assert (Ht: f a + sum_fn f l + (g a + sum_fn g l) = 
          f a + g a + (sum_fn f l + sum_fn g l)).
        {
          replace (g a + sum_fn g l) with (sum_fn g l + g a).
          rewrite plus_associative, plus_commutative.
          replace (f a + sum_fn f l + sum_fn g l) with 
            (f a + (sum_fn f l + sum_fn g l)).
          rewrite plus_associative with (c := sum_fn f l + sum_fn g l).
          replace (f a + g a) with (g a + f a).
          exact eq_refl.
          apply plus_commutative.
          apply plus_associative.
          apply plus_commutative.
        }
        rewrite Ht. exact eq_refl.
    Qed.

    
    Lemma mul_constant_left : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => c * f x) l =r= (c * sum_fn f l) = true.
    Proof.
      intros ? ?. 
      induction l.
      + simpl. (* (0 =r= c * 0) =n= true
          we need 0 is anhilator for multiplication *)
        admit.
      + simpl. 
        (* Left distributive: 
          mulitplication distributes over plus,
          c * (a + b) = c * a + c * b *)
        admit.
    Admitted.

  Lemma mul_constant_right : forall (f : Node -> R) (c : R) (l : list Node), 
    sum_fn (fun x => (f x * c)) l =r= (sum_fn f l * c) = true.
  Proof.
    intros ? ?.
    induction l.
    + simpl. (* 0 is anhilator *) admit.
    + simpl.
      (* Right distributive: (a + b) * c = a * c + b * c *)
  Admitted.

  

  (* generalised matrix multiplication *)
  Definition matrix_mul_gen (m₁ m₂ : Matrix) (l : list Node) : Matrix :=
    fun (c d : Node) => sum_fn (fun y => (m₁ c y * m₂ y d)) l.

  (* This need right distributive (a + b) * c = a * c + b * c*)  
  Lemma push_mul_right_sum_fn : forall (l₂ l₁ : list Node) (m₁ m₂ m₃ : Matrix) a x x0,
    sum_fn (λ y : Node,
      ((m₁ x a * m₂ a y + 
        sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁) * m₃ y x0)) l₂ =r= 
    sum_fn (λ y : Node, 
      (m₁ x a * m₂ a y * m₃ y x0 + 
        sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁ * m₃ y x0)) l₂ = true.
  Proof.
  Admitted.


  Lemma matrix_mul_gen_assoc : forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
    (matrix_mul_gen m₁ (matrix_mul_gen m₂ m₃ l₂) l₁ c d) =r= 
    (matrix_mul_gen (matrix_mul_gen m₁ m₂ l₁) m₃ l₂ c d) = true.
  Proof.
    unfold matrix_mul_gen.
    induction l₁; simpl; intros.
    + induction l₂.
      ++ simpl. apply refR.
      ++ simpl. (* 0 is anhilator. *) 
      admit.
    + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
  Admitted.







    
    




