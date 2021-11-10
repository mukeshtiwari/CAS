From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties.
Import ListNotations.


Section Matrix.
  Variables 
    (Node : Type)
    (finN : finite_set Node)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN)
    (memN : forall x : Node, in_list eqN finN x = true)

    (* carrier set and the operators *)
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)

    (* equivalence relation on R *)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (* end of equivalence relation *)

    (* Semiring Axiom on R *)
    (zero_left_identity_plus  : forall r : R, eqR (plusR zeroR r) r = true)
    (zero_right_identity_plus : forall r : R, eqR (plusR r zeroR) r = true)
    (plus_associative : forall a b c : R, eqR (plusR a (plusR b c)) 
      (plusR (plusR a b) c) = true)
    (plus_commutative  : forall a b : R, eqR (plusR a b) (plusR b a) = true)
    (one_left_identity_mul  : forall r : R, eqR (mulR oneR r) r = true)
    (one_right_identity_mul : forall r : R, eqR (mulR r oneR) r = true)
    (mul_associative : forall a b c : R, eqR (mulR a (mulR b c)) 
      (mulR (mulR a b) c) = true)
    (left_distributive_mul_over_plus : forall a b c : R, eqR (mulR a (plusR b c)) 
      (plusR (mulR a b) (mulR a c)) = true)
    (right_distributive_mul_over_plus : forall a b c : R, eqR (mulR (plusR a b) c) 
      (plusR (mulR a c) (mulR b c)) = true)
    (zero_left_anhilator_mul  : forall a : R, eqR (mulR zeroR a) zeroR = true)
    (zero_right_anhilator_mul : forall a : R, eqR (mulR a zeroR) zeroR = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR).
    (* end of congruence *)
    

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


    Lemma zero_add_left : forall c d m, 
      eqR (matrix_add zero_matrix m c d) (m c d) = true.
    Proof.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_left_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma zero_add_right : forall c d m, 
      eqR (matrix_add m zero_matrix c d) (m c d) = true.
    Proof.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_right_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add m₁ (matrix_add m₂ m₃) c d =r= 
      matrix_add (matrix_add m₁ m₂) m₃ c d = true.
    Proof.
      unfold matrix_add; intros.
      rewrite plus_associative;
      exact eq_refl.
    Qed.

    
    Lemma matrix_add_comm : forall m₁ m₂ c d, 
      matrix_add m₁ m₂ c d =r= matrix_add m₂ m₁ c d = true.
    Proof.
      intros; unfold matrix_add.
      rewrite plus_commutative.
      reflexivity.
    Qed.


    Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
      match l with 
      | [] => 0
      | h :: t => f h + sum_fn f t
      end.


    Theorem sum_fn_congr : forall (f g : Node -> R) (a : Node) (l : list Node),
      (sum_fn (λ x : Node, f x + g x) l =r= sum_fn f l + sum_fn g l) = true ->
      (f a + g a + sum_fn (λ x : Node, f x + g x) l =r= 
      f a + sum_fn f l + (g a + sum_fn g l)) = true.
    Proof.
    Admitted.

  

    (* I need to prove that sum_fn is congruent by 
    showing its arguments are congruent.

    Look into the minset.v coq/eqv/minset.v *)
    Lemma sum_fn_add : forall (f g : Node -> R) (l : list Node), 
      (sum_fn (fun x => f x + g x) l) =r= (sum_fn f l +  sum_fn g l) = true.
    Proof.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_identity_plus.
      + apply sum_fn_congr. exact IHl.
    Qed.

    (* so far upto this point, everything is okay *)

    Lemma sum_fn_add_eq : forall (f g : Node -> R) (l : list Node), 
      (sum_fn (fun x => f x + g x) l) = (sum_fn f l +  sum_fn g l).
    Proof.
      intros;
      apply eqr_eq, sum_fn_add.
    Qed.

    Lemma mul_constant_left : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => c * f x) l =r= (c * sum_fn f l) = true.
    Proof.
      intros ? ?. 
      induction l; simpl.
      + rewrite zero_right_anhilator_mul;
        apply refR.
      + apply eqr_eq in IHl; rewrite IHl.
        rewrite left_distributive_mul_over_plus.
        apply refR.
    Qed.

    Lemma mul_constant_left_eq : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => c * f x) l = (c * sum_fn f l).
    Proof.
      intros;
      apply eqr_eq, mul_constant_left.
    Qed.

    Lemma mul_constant_right : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => (f x * c)) l =r= (sum_fn f l * c) = true.
    Proof.
      intros ? ?.
      induction l; simpl.
      + rewrite zero_left_anhilator_mul;
        apply refR.
      + apply eqr_eq in IHl; rewrite IHl.
        rewrite right_distributive_mul_over_plus.
        apply refR.
    Qed.

    Lemma mul_constant_right_eq : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => (f x * c)) l = (sum_fn f l * c).
    Proof.
      intros; 
      apply eqr_eq, mul_constant_right.
    Qed.


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
      intros; apply eqr_eq.
      revert l₁ m₁ m₂ m₃ a x x0.
      induction l₂; simpl; intros ? ? ? ? ? ? ?.
      + apply eq_refl.
      + rewrite IHl₂, right_distributive_mul_over_plus;
        reflexivity.  
    Qed.

    Lemma push_mul_right_sum_fn_eq : forall (l₂ l₁ : list Node) (m₁ m₂ m₃ : Matrix) a x x0,
      sum_fn (λ y : Node,
        ((m₁ x a * m₂ a y + 
          sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁) * m₃ y x0)) l₂ = 
      sum_fn (λ y : Node, 
        (m₁ x a * m₂ a y * m₃ y x0 + 
          sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁ * m₃ y x0)) l₂.
    Proof.
      intros;
      apply eqr_eq, push_mul_right_sum_fn.
    Qed.
      

  
  Lemma matrix_mul_gen_assoc : forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
    (matrix_mul_gen m₁ (matrix_mul_gen m₂ m₃ l₂) l₁ c d) =r= 
    (matrix_mul_gen (matrix_mul_gen m₁ m₂ l₁) m₃ l₂ c d) = true.
  Proof.
    intros; rewrite eqr_eq;
      revert l₁ l₂ m₁ m₂ m₃ c d.
    unfold matrix_mul_gen; induction l₁; simpl;
    intros ? ? ? ? ? ?. 
    +
      induction l₂; simpl.
      ++ reflexivity. 
      ++ rewrite <-IHl₂,
        zero_left_anhilator_mul, zero_left_identity_plus.
        exact eq_refl. 
    + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
      rewrite IHl₁.
      rewrite <-mul_constant_left_eq.
      rewrite <-sum_fn_add_eq.
      rewrite push_mul_right_sum_fn_eq.
      clear IHl₁.
      induction l₂; simpl.
      ++ reflexivity.
      ++ rewrite IHl₂, mul_associative;
        reflexivity.
  Qed.

  Lemma matrix_mul_gen_assoc_eq : forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
    (matrix_mul_gen m₁ (matrix_mul_gen m₂ m₃ l₂) l₁ c d) =
    (matrix_mul_gen (matrix_mul_gen m₁ m₂ l₁) m₃ l₂ c d).
  Proof.
    intros; 
    apply eqr_eq, matrix_mul_gen_assoc.
  Qed.


  Definition matrix_mul (m₁ m₂ : Matrix) := 
    matrix_mul_gen m₁ m₂ finN.

  
  Lemma matrix_mul_assoc : forall m₁ m₂ m₃ (c d : Node),
    matrix_mul m₁ (matrix_mul m₂ m₃) c d =r= 
    matrix_mul (matrix_mul m₁ m₂) m₃ c d = true.
  Proof.
    unfold matrix_mul.
    apply matrix_mul_gen_assoc.
  Qed.


  Lemma matrix_mul_assoc_eq : forall m₁ m₂ m₃ (c d : Node),
    matrix_mul m₁ (matrix_mul m₂ m₃) c d =  
    matrix_mul (matrix_mul m₁ m₂) m₃ c d.
  Proof.
    intros;
    apply eqr_eq, matrix_mul_assoc.
  Qed.


  (* Now I need Matrix exponentiation *)
  (* write a slow one, nat, and fast one, Binary nat and 
    prove that they are equal. 
    For nat, 
    proofs will be easy, but slow computation. For Binary nat, 
    proofs be difficult but computation will be fast. 

    Then show that 0-stable, then it reaches a fixpoint
    *)
  Fixpoint matrix_exp_unary (m : Matrix) (n : nat) : Matrix :=
    match n with 
    | 0%nat => I 
    | S n' => matrix_mul m (matrix_exp_unary m n')
    end.
  
    
  Fixpoint repeat_op_ntimes_rec (e : Matrix) (n : positive) : Matrix :=
    match n with
    | xH => e
    | xO p => let ret := repeat_op_ntimes_rec e p in matrix_mul ret ret
    | xI p => let ret := repeat_op_ntimes_rec e p in matrix_mul e (matrix_mul ret ret)
    end.

  Definition matrix_exp_binary (e : Matrix) (n : N) :=
    match n with
    | N0 => I
    | Npos p => repeat_op_ntimes_rec e p 
    end.

  
  (* now prove that slow and fast computes the same value. *)

  Lemma binnat_zero : forall (n : nat), 0%N = N.of_nat n -> n = 0%nat.
  Proof.
    induction n; try lia.
  Qed.

 
  Lemma binnat_odd : forall (p : positive) (n : nat), N.pos (xI p) = N.of_nat n -> 
    exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
  Proof.
    intros p n Hp.
    destruct (Even.even_or_odd n) as [H | H].
    apply Even.even_equiv in H. destruct H as [k Hk].
    (* Even (impossible) Case *)
    rewrite Hk in Hp; lia.
    (* Odd (possible) case *)
    apply Even.odd_equiv in H. destruct H as [k Hk].
    rewrite Hk in Hp. exists k.
    split. exact Hk. lia.
  Qed.



  Lemma binnat_even : forall (p : positive) (n : nat), N.pos (xO p) = N.of_nat n :> N -> 
    exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
  Proof.
    intros p n Hp.
    destruct (Even.even_or_odd n) as [H | H].
    apply Even.even_equiv in H. destruct H as [k Hk].
    (* Even (possible) case*)
    rewrite Hk in Hp. exists k.
    split. exact Hk. lia.
    (* Odd (impossible) case *)
    apply Even.odd_equiv in H. 
    destruct H as [k Hk].
    rewrite Hk in Hp. lia.
  Qed. 

  (* 
  Lemma push_out_e_unary_nat_gen : forall k1 k2 e c d , matrix_exp e (k1 + k2)  c d = 
    matrix_mul (matrix_exp e k1)  (matrix_exp e k2) c d.
  Proof.
    induction k1.
    + intros ? ?; simpl. 
      (* requires I * m = m *)
      admit.
    + admit.
  Admitted. *)









    
    




