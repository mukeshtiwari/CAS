From Coq Require Import List Utf8
  FunctionalExtensionality.
From CAS Require Import coq.common.compute.
Import ListNotations.

(* This code comes from eqv/properties.v and  
  will go away, once I reorganise the repo to 
  compile on my machine, in fact on any machine. 
  For the moment, I am not 
  able to import  coq.eqv.properties because 
  there is no .vo file because 'make' is not producing 
  object file. *)
Section Compuation.

  Fixpoint in_list {S : Type} (r : brel S) (l : list S) (s : S) : bool 
    := match l with 
      | nil => false 
      | a :: rest => orb (r s a) (in_list r rest s)
      end. 
End Compuation.

Section ACAS. 
  Close Scope nat. 

  Definition brel_not_trivial (S : Type) (r : brel S) (f : S -> S) 
      := ∀ s : S, (r s (f s) = false) * (r (f s) s = false). 

  Definition brel_congruence (S : Type) (eq : brel S) (r : brel S) := 
    ∀ s t u v : S, eq s u = true → eq t v = true → r s t = r u v. 

  Definition brel_reflexive (S : Type) (r : brel S) := 
      ∀ s : S, r s s = true. 

  Definition brel_not_reflexive (S : Type) (r : brel S) := 
      {s : S &  r s s = false}. 

  Definition brel_reflexive_decidable (S : Type) (r : brel S) := 
      (brel_reflexive S r) + (brel_not_reflexive S r). 

  Definition brel_transitive (S : Type) (r : brel S) := 
      ∀ s t u: S, (r s t = true) → (r t u = true) → (r s u = true). 

  Definition brel_not_transitive (S : Type) (r : brel S) 
    := { z : S * (S * S) & match z with (s, (t, u)) => (r s t = true) * (r t u = true) * (r s u = false)  end}. 

  Definition brel_transitive_decidable (S : Type) (r : brel S) := 
    (brel_transitive S r) + (brel_not_transitive S r). 

  Definition brel_symmetric (S : Type) (r : brel S) := 
      ∀ s t : S, (r s t = true) → (r t s = true). 

  Definition brel_not_symmetric (S : Type) (r : brel S) 
  (*    {s : S & {t : S & (r s t = true) * (r t s = false)}}. *) 
    := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = false) end}. 

  Definition brel_symmetric_decidable (S : Type) (r : brel S) := 
    (brel_symmetric S r) + (brel_not_symmetric S r).

End ACAS.



Section Matrix.
  Variables 
    (Node : Type)
    (finN : finite_set Node)
    (eqN   : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN)
    (decN : forall c d : Node, (eqN c d = true) + (eqN c d = false))
    (memN : forall x : Node, in_list eqN finN x = true)

    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : R -> R -> R)
    (eqR   : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnr : brel_transitive R eqR)
    (decR : forall c d : R, (eqR c d = true) + (eqR c d = false)).

    
    Declare Scope Mat_scope.
    Local Open Scope Mat_scope.
    Delimit Scope Mat_scope with R.
    


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
      match decN c d with 
      | inl _ => 1
      | inr _ => 0 
      end.
    
    
    (* transpose the matrix m *)
    Definition transpose (m : Matrix) : Matrix := 
      fun (c d : Node) => m d c.

    Definition transpose_transpose_id : ∀ (m : Matrix) (c d : Node), 
      (((transpose (transpose m)) c d) =r= (m c d)) = true.
    Proof. 
      intros ? ? ?; unfold transpose; 
      simpl.  
      (* Reflexivity *)
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
      + (* 0 =r= (0 + 0). 
        I need two proofs: 1) 0 + 0 = 0 because it's additive 
        identity and eqR 0 0 = true. *) admit. 
      + (* I definitely need associativity of plusR *) 
    Admitted.

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

  





    
    




