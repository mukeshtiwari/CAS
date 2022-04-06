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

    Print zero_matrix.
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
    
    
    


  