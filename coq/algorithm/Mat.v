From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties
  coq.algorithm.Listprop
  coq.algorithm.Orel
  coq.algorithm.Path.
Import ListNotations.


Section Matrix_def.

  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (finN : list Node).

  (* carrier set and the operators *)
  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R).
    

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

  (* returns the cth row of m *)
  Definition get_row (m : Matrix Node R) (c : Node) : Node -> R := 
    fun d => m c d.

  (* returns the cth column of m *)
  Definition get_col (m : Matrix Node R) (c : Node) : Node -> R :=
    fun d => m d c.

  (* zero matrix, additive identity of plus *)
  Definition zero_matrix : Matrix Node R := 
    fun _ _ => 0.
  


  (* identity matrix, mulitplicative identity of mul *)
  (* Idenitity Matrix *)
  Definition I : Matrix Node R := 
    fun (c d : Node) =>
    match c =n= d with 
    | true => 1
    | false => 0 
    end.
  
  
  (* transpose the matrix m *)
  Definition transpose (m : Matrix Node R) : Matrix Node R := 
    fun (c d : Node) => m d c.

  

  (* pointwise addition to two matrices *)
  Definition matrix_add (m₁ m₂ : Matrix Node R) : Matrix Node R :=
    fun c d => (m₁ c d + m₂ c d).

  
  Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
    match l with 
    | [] => 0
    | h :: t => f h + sum_fn f t
    end.


  (* generalised matrix multiplication *)
  Definition matrix_mul_gen (m₁ m₂ : Matrix Node R) 
    (l : list Node) : Matrix Node R :=
    fun (c d : Node) => 
      sum_fn (fun y => (m₁ c y * m₂ y d)) l.


  (* f is congruent wrt =n= *)
  Definition fncong (f : Node -> R) : Prop :=
    forall a b : Node, a =n= b = true -> 
    f a =r= f b = true.

  (* congruence relation on matrix *)
  Definition mat_cong (m : Matrix Node R) : Prop :=
    forall a b c d, a =n= c = true -> 
    b =n= d = true -> m a b =r= m c d = true.

  
  (* Specialised form of general multiplicaiton *)
  Definition matrix_mul  
    (m₁ m₂ : Matrix Node R) := 
    matrix_mul_gen m₁ m₂ finN.

  
  Fixpoint matrix_exp_unary (m : Matrix Node R) (n : nat) : Matrix Node R :=
    match n with 
    | 0%nat => I 
    | S n' => matrix_mul m (matrix_exp_unary m n')
    end.
  
  
    
  Fixpoint repeat_op_ntimes_rec (e : Matrix Node R) (n : positive) : Matrix Node R :=
    match n with
    | xH => e
    | xO p => let ret := repeat_op_ntimes_rec e p in matrix_mul ret ret
    | xI p => let ret := repeat_op_ntimes_rec e p in 
      matrix_mul e (matrix_mul ret ret)
    end.

  Definition matrix_exp_binary (e : Matrix Node R) (n : N) :=
    match n with
    | N0 => I
    | Npos p => repeat_op_ntimes_rec e p 
    end.


  
  (* more general version *)
  Definition two_mat_congr_gen (m₁ m₂ : Matrix Node R) : Prop :=
    forall a b c d, a =n= c = true -> b =n= d = true -> 
    m₁ a b =r= m₂ c d = true. 


  Fixpoint exp_r (a : R) (n : nat) : R :=
    match n with 
    | O => 1
    | S n' => a * exp_r a n'
    end.


  Fixpoint partial_sum_r (a : R) (n : nat) : R :=
    match n with
    | O => 1
    | S n' => (partial_sum_r a n') + exp_r a n
    end.


  (* Print Grammar constr. *)
  Local Infix "+M" := matrix_add (at level 50) : Mat_scope.
  Local Infix "*M" := matrix_mul (at level 40) : Mat_scope.

  Fixpoint partial_sum_mat (m : Matrix Node R) (n : nat) : Matrix Node R :=
    match n with
    | O => I 
    | S n' => (partial_sum_mat m n') +M (matrix_exp_unary m n)
    end.

  
End Matrix_def.


Section Matrix_proofs.


  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN).

  (* Assumption of number of nodes *)
  Variables 
    (finN : list Node)
    (dupN : no_dup Node eqN finN = true) (* finN is duplicate free *)
    (lenN : (2 <= List.length finN)%nat)
    (memN : ∀ x : Node, in_list eqN finN x = true).

  (* carrier set and the operators *)
  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).

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



  Variables 
    (* Semiring Axiom on R *)
    (zero_left_identity_plus  : forall r : R, 0 + r =r= r = true)
    (zero_right_identity_plus : forall r : R, r + 0 =r= r = true)
    (plus_associative : forall a b c : R, a + (b + c) =r= 
      (a + b) + c = true)
    (plus_commutative  : forall a b : R, a + b =r= b + a = true)
    (plus_idempotence : forall a : R, a + a =r= a = true)
    (zero_stable : forall a : R, 1 + a =r= 1 = true)
    (one_left_identity_mul  : forall r : R, 1 * r =r= r = true)
    (one_right_identity_mul : forall r : R, r * 1 =r= r = true)
    (mul_associative : forall a b c : R, a * (b * c) =r= 
      (a * b) * c = true)
    (left_distributive_mul_over_plus : forall a b c : R, 
      a * (b + c) =r= a * b + a * c = true)
    (right_distributive_mul_over_plus : forall a b c : R, 
      (a + b) * c =r= a * c + b * c = true)
    (zero_left_anhilator_mul  : forall a : R, 0 * a =r= 0 = true)
    (zero_right_anhilator_mul : forall a : R, a * 0 =r= 0 = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)

    
    Lemma zero_add_left : forall c d m,
      matrix_add Node R plusR (zero_matrix Node R zeroR) m c d =r= 
      m c d = true.
    Proof using Node R eqR plusR zeroR 
    zero_left_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_left_identity_plus.
      exact eq_refl.
    Qed.
    
    Lemma zero_add_right : forall c d m, 
      matrix_add Node R plusR m 
      (zero_matrix Node R zeroR) c d =r= 
      m c d = true.
    Proof using Node R eqR plusR zeroR 
    zero_right_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_right_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add _ _ plusR m₁ (matrix_add _ _ plusR m₂ m₃) c d =r= 
      matrix_add _ _ plusR (matrix_add Node R plusR m₁ m₂) m₃ c d = true.
    Proof using Node R eqR plusR plus_associative.
      unfold matrix_add; intros.
      rewrite plus_associative;
      exact eq_refl.
    Qed.

    
    Lemma matrix_add_comm : forall m₁ m₂ c d, 
      matrix_add Node R plusR m₁ m₂ c d =r= 
      matrix_add Node R plusR m₂ m₁ c d = true.
    Proof using Node R eqR plusR plus_commutative.
      intros; unfold matrix_add.
      rewrite plus_commutative.
      reflexivity.
    Qed.


    Lemma sum_with_two_var : forall fn ga u v, 
      fn =r= u + v= true -> ga + fn =r= u + (ga + v) = true.
    Proof using R congrP congrR eqR plusR plus_associative 
    plus_commutative refR symR.
      intros.
      unfold bop_congruence in congrP.
      assert (Ht: ga + fn =r= ga + (u + v) = true).
      apply congrP; [apply refR | exact H].
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : u + (ga + v) =r= u + (v + ga) = true).
      apply congrP. apply refR.
      apply plus_commutative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (u + v) + ga =r= u + (v + ga) = true).
      apply symR, plus_associative.
      rewrite <-Ht. apply congrR.
      apply plus_commutative. 
      apply refR.
    Qed.


    Lemma sum_first_congr : forall fa ga u v fn, 
      fn =r= u + v = true -> 
      fa + ga + fn =r= fa + u + (ga + v) = true.
    Proof using R congrP congrR eqR plusR refR symR
    plus_associative plus_commutative.
      intros.
      pose proof (congrP fa (ga + fn) fa (u + (ga + v)) (refR fa)
        (sum_with_two_var _ _ _ _ H)) as Href.
      rewrite <-Href.
      apply congrR, symR, plus_associative.
      apply symR, plus_associative.
    Qed.
    
    
    Lemma sum_fn_congr : 
      forall (f g : Node -> R) (a : Node) (l : list Node),
      sum_fn Node R zeroR plusR (λ x : Node, f x + g x) l =r= 
      sum_fn Node R zeroR plusR f l + 
      sum_fn Node R zeroR plusR g l = true ->
      f a + g a + sum_fn Node R zeroR plusR (λ x : Node, f x + g x) l =r= 
      f a + sum_fn Node R zeroR plusR f l + 
      (g a + sum_fn Node R zeroR plusR g l) = true.
    Proof using Node R congrP congrR eqR plusR 
    plus_associative plus_commutative refR symR zeroR.
      intros. 
      apply sum_first_congr.
      exact H.
    Qed.
  

    Lemma sum_fn_add : 
      forall (f g : Node -> R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => f x + g x) l =r= 
      sum_fn Node R zeroR plusR f l + 
      sum_fn Node R zeroR plusR g l = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    plus_commutative refR symR zeroR zero_left_identity_plus.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_identity_plus.
      + apply sum_fn_congr. 
        exact IHl.
    Qed.


    Lemma mul_gen_left_distr : 
      forall c fa fn gn, 
      fn =r= c * gn = true -> c * fa + fn =r= c * (fa + gn) = true.
    Proof using R congrP congrR eqR left_distributive_mul_over_plus 
    mulR plusR refR.
      intros ? ? ? ? H.
      assert (Ht : c * fa + fn =r= c * fa + c * gn = true).
      apply congrP. 
      apply refR. 
      exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : c * (fa + gn) =r= c * fa + c * gn = true).
      apply left_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP; 
      apply refR.
    Qed.
    


    Lemma mul_constant_left : 
      forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => c * f x) l =r= 
      (c * sum_fn Node R zeroR plusR f l) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus 
    mulR plusR refR symR zeroR zero_right_anhilator_mul.
      intros ? ?. 
      induction l; simpl.
      + apply symR,
        zero_right_anhilator_mul.
      + apply mul_gen_left_distr; 
        exact IHl.
    Qed.


    Lemma mul_gen_right_distr : 
      forall c fa fn gn, 
      fn =r= gn * c = true -> fa * c + fn =r= (fa + gn) * c = true.
    Proof using R congrP congrR eqR mulR plusR refR
    right_distributive_mul_over_plus.
      intros.
      assert (Ht : fa * c + fn =r= fa * c + gn * c = true).
      apply congrP. 
      apply refR. 
      exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (fa + gn) * c =r= fa * c + gn * c = true).
      apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP; 
      apply refR.
    Qed.


    Lemma mul_constant_right : 
      forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn Node R zeroR plusR (fun x => (f x * c)) l =r= 
      sum_fn Node R zeroR plusR f l * c = true.
    Proof using Node R congrP congrR eqR mulR plusR refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_anhilator_mul.
      + apply mul_gen_right_distr; exact IHl.
    Qed.


    Lemma push_mul_right_gen : forall a b c d fn gn, 
      fn =r= gn = true -> 
      (a * b + c) * d + fn =r= a * b * d + c * d + gn = true.
    Proof using R congrP eqR mulR plusR 
    right_distributive_mul_over_plus.
      intros. apply congrP.
      apply right_distributive_mul_over_plus.
      exact H.
    Qed.

    (* This need right distributive (a + b) * c = a * c + b * c*)  
    Lemma push_mul_right_sum_fn : 
      forall (l₂ l₁ : list Node) 
      (m₁ m₂ m₃ : Matrix Node R) a x x0,
      sum_fn Node R zeroR plusR (λ y : Node,
        ((m₁ x a * m₂ a y + sum_fn Node R zeroR plusR 
          (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁) * m₃ y x0)) l₂ =r= 
      sum_fn Node R zeroR plusR (λ y : Node, 
        (m₁ x a * m₂ a y * m₃ y x0 + sum_fn Node R zeroR plusR 
          (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁ * m₃ y x0)) l₂ = true.
    Proof using Node R congrP eqR mulR plusR refR
    right_distributive_mul_over_plus zeroR.
      intros.
      revert l₁ m₁ m₂ m₃ a x x0.
      induction l₂; simpl; intros ? ? ? ? ? ? ?.
      + apply refR.
      + apply push_mul_right_gen, IHl₂.
    Qed.



    Local Lemma rewrite_gen_ind : 
      forall a b c d e f g, 
      a * d + f =r= g = true -> 
      a * (b * c + d) + (e * c + f) =r= 
      (a * b + e) * c + g = true.
    Proof using R congrP congrR eqR left_distributive_mul_over_plus mulR
    mul_associative plusR plus_associative plus_commutative refR
    right_distributive_mul_over_plus symR.
      intros.
      assert (Ht : a * (b * c + d) + (e * c + f) =r= 
        a * b * c + a * d + (e * c + f) = true).
      apply congrP.
      assert (Hw : a * b * c + a * d =r= a * (b * c) + a * d = true).
      apply congrP. apply symR. apply mul_associative.
      apply refR. apply symR.
      rewrite <-Hw; clear Hw. 
      apply congrR. apply refR.
      apply left_distributive_mul_over_plus.
      apply refR.
      rewrite <-Ht; clear Ht. 
      apply congrR. 
      apply refR. apply symR.
      assert (Ht : a * b * c + a * d + (e * c + f) =r= 
        a * b * c + (a * d + (e * c + f)) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : a * b * c + (a * d + (e * c + f)) =r= 
        a * b * c + (e * c + a * d + f) = true).
      apply congrP. apply refR.
      assert (Hw : a * d + (e * c + f) =r= 
        a * d + e * c + f = true).
      apply plus_associative.
      rewrite <- Hw; clear Hw.
      apply congrR. apply refR.
      apply congrP. 
      apply plus_commutative.
      apply refR. 
      rewrite <- Ht; clear Ht.
      apply congrR.
      apply refR. apply symR.
      assert (Ht : (a * b + e) * c + g =r= 
        a * b * c + e * c + g = true).
      apply congrP.
      apply right_distributive_mul_over_plus.
      apply refR. apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      assert (Ht : a * b * c + e * c + g =r= 
        a * b * c + (e * c + g) = true).
      apply symR.
      apply plus_associative. 
      apply symR in Ht.
      rewrite <- Ht; clear Ht.
      apply congrR. apply congrP.
      apply refR.
      assert (Ht : e * c + g =r= e * c + (a * d + f) = true).
      apply congrP. apply refR.
      apply symR. exact H.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. apply symR.
      apply plus_associative.
      all: apply refR.
    Qed.

    
    Lemma matrix_mul_gen_assoc : 
      forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
      (matrix_mul_gen Node R zeroR plusR mulR m₁ 
        (matrix_mul_gen Node R zeroR plusR mulR m₂ m₃ l₂) l₁ c d) =r= 
      (matrix_mul_gen Node R zeroR plusR mulR 
        (matrix_mul_gen Node R zeroR plusR mulR  m₁ m₂ l₁) m₃ l₂ c d) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus mulR
    mul_associative plusR plus_associative plus_commutative refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul.
      intros.
        revert l₁ l₂ m₁ m₂ m₃ c d.
      unfold matrix_mul_gen; induction l₁; simpl;
      intros ? ? ? ? ? ?. 
      +
        induction l₂; simpl.
        ++ apply refR.
        ++ 
          apply symR.
          assert (Ht: 0 * m₃ a d + 
            sum_fn Node R 0 plusR (λ y : Node, 0 * m₃ y d) l₂ =r= 
            0 + sum_fn Node R 0 plusR  (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply congrP. 
          apply zero_left_anhilator_mul.
          apply refR. 
          rewrite <-Ht; clear Ht.
          apply congrR. 
          apply refR.
          assert (Ht : 0 + sum_fn Node R 0 plusR  (λ y : Node, 0 * m₃ y d) l₂ =r=
            sum_fn Node R 0 plusR (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply zero_left_identity_plus. 
          apply symR in Ht.
          rewrite <-Ht. 
          apply congrR.
          exact IHl₂. 
          apply refR.
      (* inductive case *)
      + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
        (* This one is going to be tricky *)
        assert (Ht: m₁ c a * sum_fn Node R 0 plusR  (λ y : Node, m₂ a y * m₃ y d) l₂ +
          sum_fn Node R 0 plusR 
            (λ y : Node, m₁ c y * 
              sum_fn Node R 0 plusR  (λ y0 : Node, m₂ y y0 * m₃ y0 d) l₂) l₁ =r=
          m₁ c a * sum_fn Node R 0 plusR (λ y : Node, m₂ a y * m₃ y d) l₂ + 
          sum_fn Node R 0 plusR 
            (λ y : Node,
              sum_fn Node R 0 plusR  (λ y0 : Node, m₁ c y0 * m₂ y0 y) l₁ * m₃ y d) l₂ = true).
        apply congrP.
        apply refR. 
        exact IHl₁.
        rewrite <-Ht.
        apply congrR. 
        apply refR.
        clear Ht; clear IHl₁.
        apply symR.
        induction l₂; simpl.
        ++ 
          assert (Ht : m₁ c a * 0 + 0 =r= 0 + 0 = true).
          apply congrP. 
          apply zero_right_anhilator_mul.
          apply refR.
          rewrite <-Ht. apply congrR.
          apply refR. apply symR.
          apply zero_left_identity_plus.
        ++ apply rewrite_gen_ind. exact IHl₂.
    Qed.

    Lemma sum_fn_list_app : 
      forall (l₁ l₂ : list Node) (f : Node -> R), 
      sum_fn Node R zeroR plusR f (l₁ ++ l₂) =r= 
      (sum_fn Node R zeroR plusR f l₁ + sum_fn Node R zeroR plusR f l₂) = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      induction l₁; simpl.
      intros ? ?.
      + apply symR, zero_left_identity_plus.
      + intros ? ?.
        specialize (IHl₁ l₂ f).
        assert (Ht : f a + sum_fn Node R zeroR plusR f l₁ + 
          sum_fn Node R zeroR plusR f l₂ =r= 
          f a + (sum_fn Node R zeroR plusR f l₁ + 
          sum_fn Node R zeroR plusR f l₂) = true).
        apply symR, plus_associative.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply congrP.
        apply refR. 
        exact IHl₁.
        apply refR.
    Qed.


    
    Lemma sum_fn_three_list_app : 
      forall (l₁ l₂ l₃ : list Node) 
      (f : Node -> R), 
      sum_fn Node R zeroR plusR f (l₁ ++ l₂ ++ l₃) =r= 
      sum_fn Node R zeroR plusR f l₁ + 
      sum_fn Node R zeroR plusR f l₂ + 
      sum_fn Node R zeroR plusR f l₃ = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      intros. 
      assert (Ht : sum_fn Node R zeroR plusR f (l₁ ++ l₂ ++ l₃) =r= 
        sum_fn Node R zeroR plusR f l₁ + sum_fn Node R zeroR plusR f (l₂ ++ l₃) = true).
      apply sum_fn_list_app. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      assert (Ht: sum_fn Node R zeroR plusR f l₁ + 
        sum_fn Node R zeroR plusR f l₂ + 
        sum_fn Node R zeroR plusR f l₃ =r= 
        sum_fn Node R zeroR plusR f l₁ + 
        (sum_fn Node R zeroR plusR f l₂ + 
        sum_fn Node R zeroR plusR f l₃) = true).
      apply symR. 
      apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply congrP. 
      apply refR.
      apply sum_fn_list_app.
    Qed.






    Lemma sum_fn_zero : 
      forall (l₁ l₂ : list Node) (f : Node -> R),
      sum_fn Node R zeroR plusR f l₁ =r= 0 = true ->  
      sum_fn Node R zeroR plusR f (l₁ ++ l₂) =r= 
      sum_fn Node R zeroR plusR f l₂ = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      intros ? ? ? Hf.
      assert (sum_fn Node R zeroR plusR f (l₁ ++ l₂) =r= 
      sum_fn Node R zeroR plusR f l₁ + sum_fn Node R zeroR plusR f l₂ = true).
      apply sum_fn_list_app.
      rewrite <-H; clear H.
      apply congrR. 
      apply refR.
      assert (Ht : sum_fn Node R zeroR plusR f l₁ + 
        sum_fn Node R zeroR plusR f l₂ =r= 
        0 + sum_fn Node R zeroR plusR f l₂ = true).
      apply congrP. 
      exact Hf.
      apply refR. 
      apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      apply zero_left_identity_plus.
    Qed.

    

   
    Lemma sum_fn_list_eqv_gen : forall (l la lb : list Node) 
      (f : Node -> R), 
      fncong Node eqN R eqR f -> list_eqv Node eqN l (la ++ lb) = true ->
      sum_fn Node R zeroR plusR f l =r= 
      sum_fn Node R zeroR plusR f (la ++ lb) = true.
    Proof using Node R congrP eqN eqR plusR refR zeroR.
      induction l.
      + simpl; intros ? ? ? Hc Hl.
        destruct (la ++ lb).
        simpl. 
        apply refR.
        inversion Hl.
      + intros ? ? ? Hc Hl. 
        destruct la; destruct lb.
        - inversion Hl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize (IHl [] lb f Hc Hlb).
          simpl in IHl. 
          apply congrP.
          apply Hc. 
          exact Hla.
          exact IHl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          apply congrP.
          apply Hc. 
          exact Hla.
          specialize (IHl la [] f Hc Hlb).
          exact IHl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize(IHl la (n0 :: lb) f Hc Hlb).
          apply congrP.
          apply Hc. 
          exact Hla.
          exact IHl.
    Qed.

    Lemma sum_fn_list_eqv : 
      forall (l la lb : list Node) 
      (c : Node) (f : Node -> R), 
      fncong Node eqN R eqR f ->
      list_eqv Node eqN l (la ++ [c] ++ lb) = true ->
      sum_fn Node R zeroR plusR f l =r= 
      sum_fn Node R zeroR plusR f (la ++ [c] ++ lb) = true.
    Proof using Node R congrP eqN eqR plusR refR zeroR.
      intros ? ? ? ? ? Hc Hl.
      exact (sum_fn_list_eqv_gen l la ([c] ++ lb) f Hc Hl).
    Qed. 


    Lemma sum_fn_not_mem : 
      forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), 
      in_list eqN l c = false ->
      sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
      0 = true.
    Proof using Node R congrP congrR eqN eqR mulR oneR plusR refR symR zeroR
    zero_left_anhilator_mul zero_left_identity_plus.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb]. 
        rewrite Ha.
        specialize (IHl c d m Hb).
        assert (Ht : 0 * m a d + 
          sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
          0 + sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) l 
          = true).
        apply congrP. 
        apply zero_left_anhilator_mul.
        apply refR. 
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR. 
        rewrite <-IHl. 
        apply congrR.
        apply zero_left_identity_plus.
        apply refR.
    Qed.

   
    Lemma matrix_mul_left_identity_gen : 
      forall (l : list Node),
      l <> [] -> 
      (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> 
      forall (m : Matrix Node R) (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_mul_gen Node R zeroR plusR mulR 
        (I Node eqN R 0 1) m l c d =r= m c d = true.
    Proof using Node R congrM congrP congrR eqN eqR mulR oneR
    one_left_identity_mul plusR plus_associative refN refR 
    symN symR trnN zeroR zero_left_anhilator_mul 
    zero_left_identity_plus zero_right_identity_plus.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l c Hl (Hx c) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn Node R zeroR plusR 
          (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
        sum_fn Node R zeroR plusR 
          (λ y : Node, (if c =n= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
        = true).
      apply sum_fn_list_eqv.
      unfold fncong.
      intros.
      destruct (c =n= a) eqn:Ht.
      pose proof (trnN _ _ _ Ht H) as Hcb.
      rewrite Hcb. 
      assert (Htt : 1 * m a d =r= m a d = true).
      apply one_left_identity_mul.
      rewrite <-Htt; clear Htt. 
      apply congrR.
      apply refR.
      assert (Htt : 1 * m b d =r= m b d = true).
      apply one_left_identity_mul.
      rewrite <-Htt; clear Htt.
      apply congrR. 
      apply refR.
      apply Hm. 
      exact H.
      apply refN.
      case_eq (c =n= b); intros Hf; auto.
      apply symN in H.
      assert (Htt := trnN _ _ _ Hf H).
      rewrite Ht in Htt.
      inversion Htt.

      exact Hleq. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      assert (Ht : 
        sum_fn Node R zeroR plusR
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
        =r= 
        sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) la + 
        sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) [c] + 
        sum_fn Node R zeroR plusR (λ y : Node, (if c =n= y then 1 else 0) * m y d) lb = true).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      simpl. 
      assert (Hc : c =n= c = true).
      apply refN. 
      rewrite Hc; clear Hc.
      apply symR.
      assert (Ht : 
        sum_fn Node R zeroR plusR
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) la + 
        (1 * m c d + 0) +
        sum_fn Node R zeroR plusR
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) lb =r= 
        0 + (1 * m c d + 0) + 0 = true).
      apply congrP. 
      apply congrP.
      apply sum_fn_not_mem. 
      exact Hina.
      apply refR.
      apply sum_fn_not_mem. 
      exact Hinb.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 0 + (1 * m c d + 0) + 0 =r= 
        0 + (1 * m c d + 0) = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR. 
      assert (Ht: 0 + (1 * m c d + 0) =r= (1 * m c d + 0) = true).
      apply zero_left_identity_plus.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : 1 * m c d + 0 =r= 1 * m c d = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; 
      clear Ht. 
      apply congrR.
      apply refR.
      apply symR. 
      apply one_left_identity_mul.
    Qed.

    

    Lemma sum_fn_not_mem_dnode : 
      forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), 
      in_list eqN l d = false ->
      sum_fn Node R zeroR plusR 
      (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 0 = true.
    Proof using Node R congrP congrR eqN eqR mulR oneR plusR refR 
    symN symR zeroR zero_right_anhilator_mul zero_right_identity_plus.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb].
        assert (a =n= d = false).
        case_eq (a =n= d); intro Hf; auto.
        apply symN in Hf.
        rewrite Hf in Ha.
        inversion Ha.
        rewrite H.
        assert (Ht : 
          m c a * 0 +
          sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
          m c a * 0 + 0 = true).
        apply congrP. 
        apply refR.
        specialize (IHl c d m Hb).
        exact IHl.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply congrP. 
        apply refR.
        apply refR.
        apply symR.
        assert (Ht : m c a * 0 + 0 =r= m c a * 0 = true).
        apply zero_right_identity_plus.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR.
        apply zero_right_anhilator_mul.
    Qed.

      

    Lemma matrix_mul_right_identity_gen : 
      forall (l : list Node),
      l <> [] -> 
      (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> 
      forall (m : Matrix Node R ) (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_mul_gen Node R zeroR plusR mulR 
        m (I Node eqN R 0 1) l c d =r= m c d = true.
    Proof using Node R congrM congrP congrR eqN eqR mulR oneR
    one_right_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l d Hl (Hx d) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn Node R zeroR plusR 
          (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
        sum_fn Node R zeroR plusR
          (λ y : Node, m c y * (if y =n= d then 1 else 0)) (la ++ [d] ++ lb)
        = true).
      apply sum_fn_list_eqv.
      unfold fncong.
      intros.
      destruct (a =n= d) eqn:Ht.
      apply symN in H.
      pose proof (trnN _ _ _ H Ht) as Hbd.
      rewrite Hbd.
      assert (Htt : m c a * 1 =r= m c a = true).
      apply one_right_identity_mul.
      rewrite <-Htt; clear Htt. 
      apply congrR.
      apply refR.
      assert (Htt : m c b * 1 =r= m c b = true).
      apply one_right_identity_mul.
      rewrite <-Htt; clear Htt.
      apply congrR. 
      apply refR.
      apply Hm. 
      apply refN. 
      apply symN in H. 
      exact H.
      case_eq (b =n= d); intros Hf; auto.
      assert (Htt := trnN _ _ _ H Hf).
      rewrite Ht in Htt.
      inversion Htt.
      exact Hleq. 
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) (la ++ [d] ++ lb)
        =r= 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) la + 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) [d] + 
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) lb = true).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      simpl. 
      assert (Hd : d =n= d = true).
      apply refN. 
      rewrite Hd; clear Hd.
      assert (Ht :
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) la +
        (m c d * 1 + 0) +
        sum_fn Node R zeroR plusR (λ y : Node, m c y * (if y =n= d then 1 else 0)) lb =r= 
        0 + (m c d * 1 + 0) + 0 = true).
      apply congrP. 
      apply congrP.
      apply sum_fn_not_mem_dnode. 
      exact Hina.
      apply refR.
      apply sum_fn_not_mem_dnode. 
      exact Hinb.
      apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht : 0 + (m c d * 1 + 0) + 0 =r= 
        0 + (m c d * 1 + 0)  = true).
      apply zero_right_identity_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      assert (Ht: 0 + (m c d * 1 + 0) =r= (m c d * 1 + 0) = true).
      apply zero_left_identity_plus.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : m c d * 1 + 0 =r= m c d * 1 = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; 
      clear Ht. 
      apply congrR. 
      apply refR.
      apply symR. 
      apply one_right_identity_mul.
    Qed.

    


    



    
    


  