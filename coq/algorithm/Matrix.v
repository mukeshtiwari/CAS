From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties.
Import ListNotations.

Section Lfn.
  (* This is temporary section and the functions defined 
    here will move to another file.*)
  Variables (A : Type)
    (eqA : brel A)
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA).


  Fixpoint list_eqv (l₁ l₂ : list A) : bool := 
    match l₁ with 
    | [] => match l₂ with 
      | [] => true
      | _ => false
      end
    | h₁ :: t₁ => match l₂ with
      | [] => false 
      | h₂ :: t₂ => (eqA h₁ h₂) && (list_eqv t₁ t₂) 
      end
    end.   

  Lemma list_eqv_refl : forall l : list A, list_eqv l l = true.
  Proof using A eqA refA.
    induction l.
    + simpl; reflexivity.
    + simpl. apply Bool.andb_true_iff.
      split. apply refA. apply IHl.
  Qed.

  Lemma list_eqv_sym : forall l₁ l₂ : list A, 
    list_eqv l₁ l₂ = true -> list_eqv l₂ l₁ = true.
  Proof using A eqA symA.
    induction l₁; simpl.
    + intros ? Hl. destruct l₂.
      reflexivity. inversion Hl.
    + intros ? Hl. destruct l₂.
      inversion Hl.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Ha Hb].
      simpl. apply Bool.andb_true_iff.
      split. apply symA. exact Ha.
      apply IHl₁. exact Hb.
  Qed.

  
  Lemma list_mem_not : forall (l : list A) (c a : A), eqA c a = true ->
    in_list eqA l a = false -> in_list eqA l c = false.
  Proof using A eqA symA trnA.
    induction l; simpl; intros ? ? Heq Hf.
    + reflexivity.
    + apply Bool.orb_false_iff in Hf.
      destruct Hf as [Hfa Hfb].
      apply Bool.orb_false_iff.
      split.

      case_eq (eqA c a); intro Hf; auto.
      apply symA in Hf.
      assert (Ht := trnA a c a0 Hf Heq).
      apply symA in Ht. 
      rewrite Hfa in Ht.
      inversion Ht.

      apply IHl with (a := a0).
      exact Heq. exact Hfb.
  Qed.
  
  Lemma list_mem_true_false : forall (l : list A) (a c : A),
    in_list eqA l a = false -> in_list eqA l c = true -> eqA c a = false.
  Proof using A eqA symA trnA.
    induction l; simpl; intros ? ? Ha Hb.
    + inversion Hb.
    + apply Bool.orb_false_iff in Ha.
      apply Bool.orb_true_iff in Hb.
      destruct Ha as [Ha1 Ha2].
      destruct Hb as [Hb | Hb].
      apply symA in Hb.

      case_eq (eqA c a0); intros Hf; auto.
      pose proof (trnA _ _ _ Hb Hf) as Ht.
      apply symA in Ht. 
      rewrite Ha1 in Ht.
      inversion Ht.
      apply IHl; assumption.
  Qed.


  Fixpoint no_dup (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t => negb (in_list eqA t h) &&
        no_dup t
    end.
  
  Lemma list_split : forall (l : list A) (c : A),
    l <> [] -> in_list eqA l c = true -> 
    no_dup l = true -> exists l₁ l₂ : list A, 
    list_eqv l (l₁ ++ [c] ++ l₂) = true /\ 
    in_list eqA l₁ c = false /\ 
    in_list eqA l₂ c = false.
  Proof using  A eqA refA symA trnA.
    induction l; simpl.
    + intros ? H₁ H₂ H₃.
      inversion H₂.
    + intros c H₁ H₂ H₃.
      apply Bool.andb_true_iff in H₃.
      destruct H₃ as [Hl₃ Hr₃].
      apply Bool.orb_true_iff in H₂.
      destruct H₂ as [H₂ | H₂].
      exists [], l; simpl; subst.
      apply Bool.negb_true_iff in Hl₃.
      split. apply Bool.andb_true_iff.
      split. apply symA. apply H₂.
      apply list_eqv_refl.
      split. auto.
      apply list_mem_not with (a := a).
      exact H₂. exact Hl₃.
      (* l = [] \/ l <> []*)
      destruct l as [|b l].
      - inversion H₂.
      - assert (Ht : b :: l <> []).
        intro Hf. inversion Hf.
        destruct (IHl c Ht H₂ Hr₃) as 
         [la [lb [Ha [Hb Hc]]]].
        exists (a :: la), lb.
        assert (Hlf : (a :: la) ++ c :: lb = a :: la ++ c :: lb).
        simpl. reflexivity.
        rewrite Hlf. clear Hlf.
        apply Bool.negb_true_iff in Hl₃.
        split. apply Bool.andb_true_iff.
        split. apply refA.
        exact Ha.
        split. simpl.
        apply Bool.orb_false_iff.
        split. apply list_mem_true_false with (l := b :: l).
        exact Hl₃. exact H₂.
        exact Hb. exact Hc.
  Qed.
        
    
End Lfn.



Section Matrix.
  Variables 
    (Node : Type)
    (finN : finite_set Node)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN)
    (dupN : no_dup Node eqN finN = true) (* finN is duplicate free *)
    (empN : finN <> []) (* finN is non-empty *)
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
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
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

    
    (* 
      (square) matrix is a function. It's easy to prove various 
      properties of matrix with this representation. However, 
      it's not very efficient, at least in my experience, 
      so later we will replace it by another similar more 
      efficient structure for computation 
    *) 
    
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


    Lemma transpose_transpose_id : ∀ (m : Matrix) (c d : Node),
      (((transpose (transpose m)) c d) =r= (m c d)) = true.
    Proof using Node R eqR refR.
      intros ? ? ?; unfold transpose; 
      simpl. 
      apply refR.
    Qed.


    (* pointwise addition to two matrices *)
    Definition matrix_add (m₁ m₂ : Matrix) : Matrix :=
      fun c d => (m₁ c d + m₂ c d).


    Lemma zero_add_left : forall c d m,
      matrix_add zero_matrix m c d =r= (m c d) = true.
    Proof using Node R eqR plusR zeroR 
    zero_left_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_left_identity_plus.
      exact eq_refl.
    Qed. 


    Lemma zero_add_right : forall c d m, 
      (matrix_add m zero_matrix c d) =r= (m c d) = true.
    Proof using Node R eqR plusR zeroR 
    zero_right_identity_plus.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_right_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add m₁ (matrix_add m₂ m₃) c d =r= 
      matrix_add (matrix_add m₁ m₂) m₃ c d = true.
    Proof using Node R eqR plusR plus_associative.
      unfold matrix_add; intros.
      rewrite plus_associative;
      exact eq_refl.
    Qed.

    
    Lemma matrix_add_comm : forall m₁ m₂ c d, 
      matrix_add m₁ m₂ c d =r= matrix_add m₂ m₁ c d = true.
    Proof using Node R eqR plusR plus_commutative.
      intros; unfold matrix_add.
      rewrite plus_commutative.
      reflexivity.
    Qed.


    Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
      match l with 
      | [] => 0
      | h :: t => f h + sum_fn f t
      end.

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
  
    
    Lemma sum_fn_congr : forall (f g : Node -> R) (a : Node) (l : list Node),
      (sum_fn (λ x : Node, f x + g x) l =r= sum_fn f l + sum_fn g l) = true ->
      (f a + g a + sum_fn (λ x : Node, f x + g x) l =r= 
      f a + sum_fn f l + (g a + sum_fn g l)) = true.
    Proof using Node R congrP congrR eqR plusR 
    plus_associative plus_commutative refR symR zeroR.
      intros. 
      apply sum_first_congr.
      exact H.
    Qed.
  

    Lemma sum_fn_add : forall (f g : Node -> R) (l : list Node), 
      (sum_fn (fun x => f x + g x) l) =r= (sum_fn f l +  sum_fn g l) = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    plus_commutative refR symR zeroR zero_left_identity_plus.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_identity_plus.
      + apply sum_fn_congr. exact IHl.
    Qed.


    Lemma mul_gen_left_distr : forall c fa fn gn, 
      fn =r= c * gn = true -> c * fa + fn =r= c * (fa + gn) = true.
    Proof using R congrP congrR eqR left_distributive_mul_over_plus 
    mulR plusR refR.
      intros ? ? ? ? H.
      assert (Ht : c * fa + fn =r= c * fa + c * gn = true).
      apply congrP. apply refR. exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : c * (fa + gn) =r= c * fa + c * gn = true).
      apply left_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP; apply refR.
    Qed.
    


    Lemma mul_constant_left : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => c * f x) l =r= (c * sum_fn f l) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus 
    mulR plusR refR symR zeroR zero_right_anhilator_mul.
      intros ? ?. 
      induction l; simpl.
      + apply symR,
        zero_right_anhilator_mul.
      + apply mul_gen_left_distr; exact IHl.
    Qed.



    Lemma mul_gen_right_distr : forall c fa fn gn, 
      fn =r= gn * c = true -> fa * c + fn =r= (fa + gn) * c = true.
    Proof using R congrP congrR eqR mulR plusR refR
    right_distributive_mul_over_plus.
      intros.
      assert (Ht : fa * c + fn =r= fa * c + gn * c = true).
      apply congrP. apply refR. exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (fa + gn) * c =r= fa * c + gn * c = true).
      apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP; apply refR.
    Qed.


    Lemma mul_constant_right : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => (f x * c)) l =r= (sum_fn f l * c) = true.
    Proof using Node R congrP congrR eqR mulR plusR refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_anhilator_mul.
      + apply mul_gen_right_distr; exact IHl.
    Qed.



    (* generalised matrix multiplication *)
    Definition matrix_mul_gen (m₁ m₂ : Matrix) (l : list Node) : Matrix :=
      fun (c d : Node) => sum_fn (fun y => (m₁ c y * m₂ y d)) l.



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
    Lemma push_mul_right_sum_fn : forall (l₂ l₁ : list Node) 
      (m₁ m₂ m₃ : Matrix) a x x0,
      sum_fn (λ y : Node,
        ((m₁ x a * m₂ a y + 
          sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁) * m₃ y x0)) l₂ =r= 
      sum_fn (λ y : Node, 
        (m₁ x a * m₂ a y * m₃ y x0 + 
          sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁ * m₃ y x0)) l₂ = true.
    Proof using Node R congrP eqR mulR plusR refR
    right_distributive_mul_over_plus zeroR.
      intros.
      revert l₁ m₁ m₂ m₃ a x x0.
      induction l₂; simpl; intros ? ? ? ? ? ? ?.
      + apply refR.
      + apply push_mul_right_gen, IHl₂.
    Qed.
      

    Local Lemma rewrite_gen_ind : forall a b c d e f g, 
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


    Lemma matrix_mul_gen_assoc : forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
      (matrix_mul_gen m₁ (matrix_mul_gen m₂ m₃ l₂) l₁ c d) =r= 
      (matrix_mul_gen (matrix_mul_gen m₁ m₂ l₁) m₃ l₂ c d) = true.
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
        ++ apply symR.
          assert (Ht: 0 * m₃ a d + sum_fn (λ y : Node, 0 * m₃ y d) l₂ =r= 
            0 + sum_fn (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply congrP. apply zero_left_anhilator_mul.
          apply refR. rewrite <-Ht; clear Ht.
          apply congrR. apply refR.
          assert (Ht : 0 + sum_fn (λ y : Node, 0 * m₃ y d) l₂ =r=
            sum_fn (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply zero_left_identity_plus. apply symR in Ht.
          rewrite <-Ht. apply congrR.
          exact IHl₂. apply refR.
      (* inductive case *)
      + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
        (* This one is going to be tricky *)
        assert (Ht: m₁ c a * sum_fn (λ y : Node, m₂ a y * m₃ y d) l₂ +
          sum_fn 
            (λ y : Node, m₁ c y * 
              sum_fn (λ y0 : Node, m₂ y y0 * m₃ y0 d) l₂) l₁ =r=
          m₁ c a * sum_fn (λ y : Node, m₂ a y * m₃ y d) l₂ + 
          sum_fn
            (λ y : Node,
              sum_fn (λ y0 : Node, m₁ c y0 * m₂ y0 y) l₁ * m₃ y d) l₂ = true).
        apply congrP.
        apply refR. exact IHl₁.
        rewrite <-Ht.
        apply congrR. apply refR.
        clear Ht; clear IHl₁.
        apply symR.
        induction l₂; simpl.
        ++ assert (Ht : m₁ c a * 0 + 0 =r= 0 + 0 = true).
          apply congrP. apply zero_right_anhilator_mul.
          apply refR.
          rewrite <-Ht. apply congrR.
          apply refR. apply symR.
          apply zero_left_identity_plus.
        ++ apply rewrite_gen_ind. exact IHl₂.
    Qed.

    
    Lemma sum_fn_list_app : forall (l₁ l₂ : list Node) (f : Node -> R), 
      sum_fn f (l₁ ++ l₂) =r= (sum_fn f l₁ + sum_fn f l₂) = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      induction l₁; simpl.
      intros ? ?.
      + apply symR, zero_left_identity_plus.
      + intros ? ?.
        specialize (IHl₁ l₂ f).
        assert (Ht : f a + sum_fn f l₁ + sum_fn f l₂ =r= 
          f a + (sum_fn f l₁ + sum_fn f l₂) = true).
        apply symR, plus_associative.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply congrP.
        apply refR. exact IHl₁.
        apply refR.
    Qed.
  
    Lemma sum_fn_three_list_app : forall (l₁ l₂ l₃ : list Node) 
      (f : Node -> R), 
      sum_fn f (l₁ ++ l₂ ++ l₃) =r= (sum_fn f l₁ + sum_fn f l₂ + sum_fn f l₃) 
      = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      intros. 
      assert (Ht : sum_fn f (l₁ ++ l₂ ++ l₃) =r= 
        sum_fn f l₁ + sum_fn f (l₂ ++ l₃) = true).
      apply sum_fn_list_app. rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht: sum_fn f l₁ + sum_fn f l₂ + sum_fn f l₃ =r= 
        sum_fn f l₁ + (sum_fn f l₂ + sum_fn f l₃) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP. apply refR.
      apply sum_fn_list_app.
    Qed.




    Lemma sum_fn_zero : forall (l₁ l₂ : list Node) (f : Node -> R),
      sum_fn f l₁ =r= 0 = true ->  
      sum_fn f (l₁ ++ l₂) =r= sum_fn f l₂ = true.
    Proof using Node R congrP congrR eqR plusR plus_associative 
    refR symR zeroR zero_left_identity_plus.
      intros ? ? ? Hf.
      assert (sum_fn f (l₁ ++ l₂) =r= sum_fn f l₁ + sum_fn f l₂ = true).
      apply sum_fn_list_app.
      rewrite <-H; clear H.
      apply congrR. apply refR.
      assert (Ht : sum_fn f l₁ + sum_fn f l₂ =r= 0 + sum_fn f l₂ = true).
      apply congrP. exact Hf.
      apply refR. apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR. 
      apply zero_left_identity_plus.
    Qed.


    (* f is congruent wrt =n= *)
    Definition fncong (f : Node -> R) : Prop :=
      forall a b : Node, a =n= b = true -> 
        f a =r= f b = true.
    


    Lemma sum_fn_list_eqv_gen : forall (l la lb : list Node) 
      (f : Node -> R), 
      fncong f -> list_eqv Node eqN l (la ++ lb) = true ->
      sum_fn f l =r= sum_fn f (la ++ lb) = true.
    Proof using Node R congrP eqN eqR plusR refR zeroR.
      induction l.
      + simpl; intros ? ? ? Hc Hl.
        destruct (la ++ lb).
        simpl. apply refR.
        inversion Hl.
      + intros ? ? ? Hc Hl. 
        destruct la; destruct lb.
        - inversion Hl.
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hl.
          destruct Hl as [Hla Hlb].
          specialize (IHl [] lb f Hc Hlb).
          simpl in IHl. apply congrP.
          apply Hc. exact Hla.
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
          apply Hc. exact Hla.
          exact IHl.
    Qed.

    Lemma sum_fn_list_eqv : forall (l la lb : list Node) 
      (c : Node) (f : Node -> R), fncong f ->
      list_eqv Node eqN l (la ++ [c] ++ lb) = true ->
      sum_fn f l =r= sum_fn f (la ++ [c] ++ lb) = true.
    Proof using Node R congrP eqN eqR plusR refR zeroR.
      intros ? ? ? ? ? Hc Hl.
      exact (sum_fn_list_eqv_gen l la ([c] ++ lb) f Hc Hl).
    Qed. 


    Lemma sum_fn_not_mem : forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), in_list eqN l c = false ->
      sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
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
          sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
          0 + sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) l 
          = true).
        apply congrP. apply zero_left_anhilator_mul.
        apply refR. rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        apply symR. 
        rewrite <-IHl. apply congrR.
        apply zero_left_identity_plus.
        apply refR.
    Qed.
        
    (* congruence relation on matrix *)
    Definition mat_cong (m : Matrix) : Prop :=
      forall a b c d, a =n= c = true -> b =n= d = true ->
      m a b =r= m c d = true.

    Lemma matrix_mul_left_identity_gen : forall (l : list Node),
      l <> [] -> (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> forall (m : Matrix) (c d : Node),
      mat_cong m -> 
      matrix_mul_gen I m l c d =r= m c d = true.
    Proof using Node R congrM congrP congrR eqN eqR mulR oneR
    one_left_identity_mul plusR plus_associative refN refR 
    symN symR trnN zeroR zero_left_anhilator_mul 
    zero_left_identity_plus zero_right_identity_plus.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l c Hl (Hx c) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn 
          (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
        sum_fn 
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
      apply congrR. apply refR.
      apply Hm. exact H.
      apply refN.
      case_eq (c =n= b); intros Hf; auto.
      apply symN in H.
      assert (Htt := trnN _ _ _ Hf H).
      rewrite Ht in Htt.
      inversion Htt.

      exact Hleq. rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR. 
      assert (Ht : 
        sum_fn 
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) (la ++ [c] ++ lb)
        =r= 
        sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) la + 
        sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) [c] + 
        sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) lb = true).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. apply congrR.
      apply refR. simpl. 
      assert (Hc : c =n= c = true).
      apply refN. rewrite Hc; clear Hc.
      apply symR.
      assert (Ht : 
        sum_fn 
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) la + 
        (1 * m c d + 0) +
        sum_fn 
        (λ y : Node, (if c =n= y then 1 else 0) * m y d) lb =r= 
        0 + (1 * m c d + 0) + 0 = true).
      apply congrP. apply congrP.
      apply sum_fn_not_mem. exact Hina.
      apply refR.
      apply sum_fn_not_mem. exact Hinb.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      assert (Ht : 0 + (1 * m c d + 0) + 0 =r= 
        0 + (1 * m c d + 0) = true).
      apply zero_right_identity_plus. 
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR. 
      assert (Ht: 0 + (1 * m c d + 0) =r= (1 * m c d + 0) = true).
      apply zero_left_identity_plus.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. apply symR.
      assert (Ht : 1 * m c d + 0 =r= 1 * m c d = true).
      apply zero_right_identity_plus. rewrite <-Ht; 
      clear Ht. apply congrR. apply refR.
      apply symR. apply one_left_identity_mul.
    Qed.

    

    Lemma sum_fn_not_mem_dnode : forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), in_list eqN l d = false ->
      sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
      0 = true.
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
          sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
          m c a * 0 + 0 = true).
        apply congrP. apply refR.
        specialize (IHl c d m Hb).
        exact IHl.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply congrP. apply refR.
        apply refR.
        apply symR.
        assert (Ht : m c a * 0 + 0 =r= m c a * 0 = true).
        apply zero_right_identity_plus.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        apply symR.
        apply zero_right_anhilator_mul.
    Qed.

      

    Lemma matrix_mul_right_identity_gen : forall (l : list Node),
      l <> [] -> (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> forall (m : Matrix) (c d : Node),
      mat_cong m ->
      matrix_mul_gen m I l c d =r= m c d = true.
    Proof using Node R congrM congrP congrR eqN eqR mulR oneR
    one_right_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ? Hm.
      destruct (list_split _ eqN refN symN trnN l d Hl (Hx d) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      assert (Ht : 
        sum_fn 
          (λ y : Node, m c y * (if y =n= d then 1 else 0)) l =r= 
        sum_fn 
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
      apply congrR. apply refR.
      apply Hm. apply refN. 
      apply symN in H. exact H.
      case_eq (b =n= d); intros Hf; auto.
      assert (Htt := trnN _ _ _ H Hf).
      rewrite Ht in Htt.
      inversion Htt.

      exact Hleq. rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      assert (Ht : 
        sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) (la ++ [d] ++ lb)
        =r= 
        sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) la + 
        sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) [d] + 
        sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) lb = true).
      apply sum_fn_three_list_app.
      rewrite <-Ht; clear Ht. apply congrR.
      apply refR. simpl. 
      assert (Hd : d =n= d = true).
      apply refN. rewrite Hd; clear Hd.
      assert (Ht :
        sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) la +
        (m c d * 1 + 0) +
        sum_fn (λ y : Node, m c y * (if y =n= d then 1 else 0)) lb =r= 
        0 + (m c d * 1 + 0) + 0 = true).
      apply congrP. apply congrP.
      apply sum_fn_not_mem_dnode. exact Hina.
      apply refR.
      apply sum_fn_not_mem_dnode. exact Hinb.
      apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      assert (Ht : 0 + (m c d * 1 + 0) + 0 =r= 
        0 + (m c d * 1 + 0)  = true).
      apply zero_right_identity_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      assert (Ht: 0 + (m c d * 1 + 0) =r= (m c d * 1 + 0) = true).
      apply zero_left_identity_plus.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. apply symR.
      assert (Ht : m c d * 1 + 0 =r= m c d * 1 = true).
      apply zero_right_identity_plus. rewrite <-Ht; 
      clear Ht. apply congrR. apply refR.
      apply symR. apply one_right_identity_mul.
    Qed.


    Definition matrix_mul (m₁ m₂ : Matrix) := 
      matrix_mul_gen m₁ m₂ finN.

    
    Lemma matrix_mul_assoc : forall m₁ m₂ m₃ (c d : Node),
      matrix_mul m₁ (matrix_mul m₂ m₃) c d =r= 
      matrix_mul (matrix_mul m₁ m₂) m₃ c d = true.
    Proof using Node R congrP congrR eqR finN left_distributive_mul_over_plus
    mulR mul_associative plusR plus_associative plus_commutative refR
    right_distributive_mul_over_plus symR zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul.
      unfold matrix_mul.
      apply matrix_mul_gen_assoc.
    Qed.

    Lemma matrix_mul_left_identity : forall m (c d : Node), 
      mat_cong m -> 
      matrix_mul I m c d =r= m c d = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN memN mulR oneR
    one_left_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_anhilator_mul zero_left_identity_plus zero_right_identity_plus.
      unfold matrix_mul.
      apply matrix_mul_left_identity_gen.
      apply empN. apply memN.
      apply dupN.
    Qed.

    Lemma matrix_mul_right_identity : forall m (c d : Node),
      mat_cong m -> 
      matrix_mul m I c d =r= m c d = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN memN mulR oneR
    one_right_identity_mul plusR plus_associative refN refR symN symR trnN zeroR
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      unfold matrix_mul.
      apply matrix_mul_right_identity_gen.
      apply empN. apply memN.
      apply dupN.
    Qed.

    
    
    Fixpoint matrix_exp_unary (m : Matrix) (n : nat) : Matrix :=
      match n with 
      | 0%nat => I 
      | S n' => matrix_mul m (matrix_exp_unary m n')
      end.
    
    
      
    Fixpoint repeat_op_ntimes_rec (e : Matrix) (n : positive) : Matrix :=
      match n with
      | xH => e
      | xO p => let ret := repeat_op_ntimes_rec e p in matrix_mul ret ret
      | xI p => let ret := repeat_op_ntimes_rec e p in 
        matrix_mul e (matrix_mul ret ret)
      end.

    Definition matrix_exp_binary (e : Matrix) (n : N) :=
      match n with
      | N0 => I
      | Npos p => repeat_op_ntimes_rec e p 
      end.

    
    
    (* now prove that slow and fast computes the same value. *)
    (* This is generic and does not use Section Variable, so move it 
      to a new file/section. *)
    Lemma binnat_zero : forall (n : nat), 0%N = N.of_nat n -> n = 0%nat.
    Proof using -All.
      induction n; try lia.
    Qed.

  
    Lemma binnat_odd : forall (p : positive) (n : nat), 
      N.pos (xI p) = N.of_nat n -> 
      exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
    Proof using -All.
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

    


    Lemma binnat_even : forall (p : positive) (n : nat), 
      N.pos (xO p) = N.of_nat n :> N -> 
      exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
    Proof using -All.
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

    (* end of generic nat lemma *)


    Lemma add_r_cong : forall a b c d, a =r= c = true ->
      b =r= d = true -> a + b =r= c + d = true.
    Proof using R congrP eqR plusR.
      intros ? ? ? ? Hac Hbd.
      apply congrP.
      exact Hac.
      exact Hbd.
    Qed.

    Lemma mat_pointwise_cong : forall a b c d e f g h 
      (m₁ m₂ : Matrix), 
      a =n= c = true -> b =n= d = true ->
      e =n= g = true -> f =n= h = true ->
      mat_cong m₁ -> mat_cong m₂ -> 
      m₁ a b * m₂ e f =r=  m₁ c d * m₂ g h = true.
    Proof using Node R congrM eqN eqR mulR.
      intros ? ? ? ? ? ? ? ? ? ? Hac Hbd Heg Hfh
        Hm₁ Hm₂.
      apply congrM.
      apply Hm₁; assumption.
      apply Hm₂; assumption.
    Qed.

    Lemma sum_fn_mul_congr : forall l m₁ m₂ a b c d, 
      (a =n= c) = true  -> (b =n= d) = true ->
      mat_cong m₁ -> mat_cong m₂ ->
      sum_fn (λ y : Node, m₁ a y * m₂ y b) l =r= 
      sum_fn (λ y : Node, m₁ c y * m₂ y d) l = true.
    Proof using Node R congrM congrP eqN eqR mulR 
    plusR refN refR zeroR.
      induction l; simpl; 
      intros ? ? ? ? ? ? Hac Hbd Hm₁ Hm₂.
      + apply refR.
      + apply add_r_cong.
        apply mat_pointwise_cong;
        try assumption; try (apply refN).
        apply IHl; assumption.
    Qed.

  
    Lemma mat_mul_cong : forall m₁ m₂ a b c d, 
      a =n= c= true -> b =n= d = true -> 
      mat_cong m₁ -> mat_cong m₂ -> 
      matrix_mul m₁ m₂ a b =r= matrix_mul m₁ m₂ c d = true.
    Proof using Node R congrM congrP eqN eqR finN mulR 
    plusR refN refR zeroR.
      intros.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mul_congr; assumption.
    Qed.

    Lemma identity_cong : forall a b c d, 
      (a =n= c) = true -> (b =n= d) = true ->
      I a b =r= I c d = true.
    Proof using Node R eqN eqR oneR refR symN trnN zeroR.
      intros ? ? ? ? Hac Hbd.
      unfold I.
      case_eq (a =n= b); intros Hf; auto.
      assert (Ht1 := trnN _ _ _ Hf Hbd).
      apply symN in Hac.
      assert (Ht2 := trnN _ _ _ Hac Ht1).
      rewrite Ht2. apply refR.
      case_eq (c =n= d); intros Hcd; auto.
      assert (Had := trnN _ _ _ Hac Hcd).
      apply symN in Hbd.
      assert (Habt := trnN _ _ _ Had Hbd).
      rewrite Habt in Hf.
      inversion Hf.
    Qed.


    Lemma mat_exp_cong : ∀ k e (a b c d : Node),
      (a =n= c) = true → (b =n= d) = true →
      mat_cong e →
      matrix_exp_unary e k a b =r= 
      matrix_exp_unary e k c d = true.
    Proof using Node R congrM congrP eqN eqR finN 
    mulR oneR plusR refN refR symN trnN zeroR.
      induction k; simpl; 
      intros ? ? ? ? ? Hac Hbd Hme.
      + apply identity_cong; assumption.
      + apply mat_mul_cong. exact Hac.
        exact Hbd. exact Hme.
        unfold mat_cong; intros.
        apply IHk; assumption.
    Qed.

    (* two matrices are equal only if they are equal every point *)
    Definition two_mat_congr (m₁ m₂ : Matrix) : Prop :=
      forall c d, m₁ c d =r= m₂ c d = true.
    
    Lemma sum_fn_mul_congr_diff : forall l (e m₁ m₂ : Matrix) c d,
      two_mat_congr m₁ m₂ ->  
      sum_fn (λ y : Node, e c y * m₁ y d) l =r= 
      sum_fn (λ y : Node, e c y * m₂ y d) l = true.
    Proof using Node R congrM congrP eqR mulR plusR refR zeroR.
      induction l; simpl; 
      intros  ? ? ? ? ? Hm.
      + apply refR.
      + apply add_r_cong.
        apply congrM.
        apply refR.
        apply Hm.
        apply IHl; assumption.
    Qed.

    (* naming is very difficult. I can't come up meaningful names *)
    Lemma mat_mul_cong_diff : forall e m₁ m₂ c d,
      two_mat_congr m₁ m₂ ->
      matrix_mul e m₁ c d =r= matrix_mul e m₂ c d = true.
    Proof using Node R congrM congrP eqR finN mulR plusR refR zeroR.
      intros ? ? ? ? ? Hm.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mul_congr_diff.
      exact Hm.
    Qed.


    Lemma push_out_e_unary_nat_gen : forall k1 k2 e c d,
      mat_cong e -> 
      matrix_exp_unary e (k1 + k2)  c d =r= 
      matrix_mul (matrix_exp_unary e k1) (matrix_exp_unary e k2) c d = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul plusR plus_associative plus_commutative refN refR
    right_distributive_mul_over_plus symN symR trnN zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul zero_right_identity_plus.
      induction k1; simpl.
      + intros ? ? ? ? ?.
        apply symR, matrix_mul_left_identity.
        unfold mat_cong. intros.
        apply mat_exp_cong; assumption.
      + intros ? ? ? ? He.
        pose proof  (IHk1 k2 e c d He).
        assert (Ht : matrix_mul e (matrix_exp_unary e (k1 + k2)) c d =r=
          matrix_mul e (matrix_mul (matrix_exp_unary e k1) 
          (matrix_exp_unary e k2)) c d = true).
        apply mat_mul_cong_diff. 
        unfold two_mat_congr; intros.
        apply IHk1. exact He.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        apply symR.
        apply matrix_mul_assoc.
    Qed.

    (* more general version *)
    Definition two_mat_congr_gen (m₁ m₂ : Matrix) : Prop :=
      forall a b c d, a =n= c = true -> b =n= d = true -> 
      m₁ a b =r= m₂ c d = true. 

    Lemma sum_fn_congr_gen : forall l m₁ m₂ m₃ m₄ a b c d,
      a =n= c = true -> b =n= d = true ->
      two_mat_congr_gen m₁ m₃ -> two_mat_congr_gen m₂ m₄ -> 
      sum_fn (λ y : Node, m₁ a y * m₂ y b) l =r=
      sum_fn (λ y : Node, m₃ c y * m₄ y d) l = true.
    Proof using Node R congrM congrP eqN eqR mulR plusR refN refR zeroR.
      induction l; simpl; 
      intros ? ? ? ? ? ? ? ? Hac Hbd Hm₁ Hm₂.
      + apply refR.
      + apply congrP.
        apply congrM.
        apply Hm₁.
        exact Hac. apply refN.
        apply Hm₂.
        apply refN. exact Hbd.
        apply IHl; 
        (try assumption; try (apply refN)).
    Qed.

    Lemma mat_mul_cong_gen : forall m₁ m₂ m₃ m₄ a b c d,
      a =n= c = true -> b =n= d = true -> 
      two_mat_congr_gen m₁ m₃ -> two_mat_congr_gen m₂ m₄ -> 
      matrix_mul m₁ m₂ a b =r= matrix_mul m₃ m₄ c d = true.
    Proof using Node R congrM congrP eqN eqR finN mulR 
    plusR refN refR zeroR.
      intros ? ? ? ? ? ? ? ? Hac Hbd H₁ H₂.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_congr_gen; assumption.
    Qed.

    Lemma sum_fn_mat_ind : forall l m₁ m₂ u v, 
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      sum_fn (λ y : Node, m₁ u y * m₁ y v) l =r=
      sum_fn (λ y : Node, m₂ u y * m₂ y v) l = true.
    Proof using Node R congrM congrP eqR mulR plusR refR zeroR.
      induction l; simpl; 
      intros  ? ? ? ? Hm.
      + apply refR.
      +
        apply add_r_cong.
        apply congrM. apply Hm.
        apply Hm.
        apply IHl; assumption.
    Qed.


    Lemma mat_equal_ind : forall m₁ m₂ u v,
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      matrix_mul m₁ m₁ u v =r= matrix_mul m₂ m₂ u v = true.
    Proof using Node R congrM congrP eqR finN mulR 
    plusR refR zeroR.
      intros ? ? ? ? Hcd.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mat_ind.
      apply Hcd.
    Qed.


    Lemma matrix_exp_unary_binary_eqv : forall (n : N) (m : Matrix) c d,
      mat_cong m -> 
      matrix_exp_unary m (N.to_nat n) c d =r= matrix_exp_binary m n c d 
      = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative refN refR right_distributive_mul_over_plus symN symR trnN
    zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      destruct n;
      intros ? ? ? Hm.
      + apply refR.
      + 
        assert (Hw : forall w, matrix_exp_binary m (N.pos w) = 
          repeat_op_ntimes_rec m w).
        reflexivity.
        revert c d. induction p.
        rewrite Hw in IHp. rewrite Hw.
        - intros ? ?.
          assert (Ht : N.pos (xI p) = N.of_nat (N.to_nat (N.pos (xI p)))).
          rewrite Nnat.N2Nat.id; reflexivity.
          destruct (binnat_odd p (N.to_nat (N.pos (xI p))) Ht) as 
            [k [Ha Hb]].
          rewrite Ha. rewrite Hb in IHp.
          rewrite Nnat.Nat2N.id in IHp.
          assert (Hv : (2 * k + 1 = 1 + k + k)%nat).
          lia. rewrite Hv; clear Hv.
          simpl. apply mat_mul_cong_diff.
          unfold two_mat_congr; intros u v.
          pose proof push_out_e_unary_nat_gen k k m 
            u v Hm as Htt.
          rewrite <- Htt.
          apply congrR. apply refR.
          apply mat_equal_ind.
          intros. apply symR. 
          apply IHp.
        - intros ? ?. rewrite Hw in IHp. rewrite Hw.
          assert (Ht : N.pos (xO p) = N.of_nat (N.to_nat (N.pos (xO p)))).
          rewrite Nnat.N2Nat.id; reflexivity.
          destruct (binnat_even p (N.to_nat (N.pos (xO p))) Ht) as 
            [k [Ha Hb]].
          rewrite Ha. rewrite Hb in IHp.
          rewrite Nnat.Nat2N.id in IHp.
          assert (Hv : (2 * k = k + k)%nat).
          lia. rewrite Hv; clear Hv.
          simpl.
          pose proof push_out_e_unary_nat_gen k k m 
            c d Hm as Htt.
          rewrite <- Htt; clear Htt.
          apply congrR. apply refR.
          apply mat_equal_ind.
          intros. apply symR. simpl in IHp.
          apply IHp.
        - intros ? ?. simpl.
          apply matrix_mul_right_identity.
          exact Hm.
    Qed.


    (* a path is a triple *)
    Definition Path : Type := Node * Node * list (Node * Node * R). 


    Definition source (c : Node) (l : list (Node * Node * R)) : bool :=
      match l with 
      | [] => false
      | (x, _, _) :: _ => c =n= x 
      end.
    

    Definition target_alt (d : Node) (l : list (Node * Node * R)) := 
      match List.rev l with
      | [] => false
      | (x, y, r) :: t => d =n= y
      end. 


    (* generic lemma about list. It does not use any section assumption *)
    Lemma target_alt_end : forall (l : list (Node * Node * R))
      (x : Node * Node * R) (d : Node),
      target_alt d (l ++ [x]) = target_alt d [x].
    Proof using -All.
      intros ? ? ?.
      unfold target_alt.
      rewrite rev_unit.
      assert (Ht : rev [x] = [x]).
      reflexivity.
      rewrite Ht; clear Ht.
      reflexivity.
    Qed.


    Fixpoint target (d : Node) (l : list (Node * Node * R)) : bool :=
      match l with
      | [] => false
      | (x, y, r) :: t => match t with 
        | [] => d =n= y
        | hs :: ts => target d t
      end
      end.


    Lemma target_end : forall (l : list (Node * Node * R))
      (x : Node * Node * R) (d : Node),
      target d (l ++ [x]) = target d [x].
    Proof using -All.
      induction l.
      - simpl; intros ? ?. reflexivity.
      - intros ? ?.
        assert (Ht : target d ((a :: l) ++ [x]) = target d (l ++ [x])).
        simpl. destruct a. destruct p.
        destruct (l ++ [x]) eqn:Hv.
        pose proof app_eq_nil l [x] Hv as Hw.
        destruct Hw as [Hwl Hwr].
        congruence. reflexivity.
        rewrite Ht. apply IHl.
    Qed.


    Lemma target_target_alt_same : forall (l : list (Node * Node * R)) (d : Node), 
      target d l = target_alt d l.
    Proof using -All.
      induction l using rev_ind.
      - unfold target_alt; simpl; intros ?.
        reflexivity.
      - intros ?. rewrite target_alt_end, target_end.
        reflexivity.
    Qed.

    (* path strength between c and d *)
    Fixpoint measure_of_path (l : list (Node * Node * R)) : R :=
      match l with 
      | [] => 1
      | (_, _, v) :: t => v * measure_of_path t
      end.

    Fixpoint well_formed_path_aux (m : Matrix) (l : list (Node * Node * R)) : bool :=
      match l with 
      | [] => true
      | (c, x, v) :: tl => (m c x =r= v) && match tl with 
        | [] => true
        | (y, _, _) :: _ => (x =n= y) && well_formed_path_aux m tl
        end
      end.
  
  
    
    Definition well_formed_path (m : Matrix) (p : Path) : bool :=
      match p with 
      | (c, d, []) => c =n= d 
      | (c, d, l) => well_formed_path_aux m l && 
          source c l && target d l
      end.
      
      

    Definition fp (p : Path) : Node :=
      match p with
      |(a, _, _) => a
      end. 

    Definition sp (p : Path) : Node :=
      match p with
      |(_, b, _) => b
      end. 
    
    Definition tp (p : Path) : list (Node * Node * R):=
      match p with
      |(_, _, l) => l
      end.


    (* stick a node 'c' in all the paths, represented by l *)
    Fixpoint append_node_in_paths (m : Matrix) 
      (c : Node) (l : list (list (Node * Node * R))) : 
      list (list (Node * Node * R)) := 
    match l with 
    | [] => []
    | h :: t => match h with 
      | [] => append_node_in_paths m c t
      | (x, _, _) :: ht => 
        ((c, x, m c x) :: h) :: append_node_in_paths m c t
      end 
    end.


    (* list of all paths of lenghth k from c to d *)
    Fixpoint all_paths_klength (m : Matrix) (k : nat) 
      (c d : Node) : list (list (Node * Node * R)) :=
      match k with
      | O => if c =n= d then [[(c, d, 1)]] else []
      | S k' =>
          let lf := List.flat_map (fun x => all_paths_klength m k' x d) finN
          in append_node_in_paths m c lf
      end.

    
    Definition construct_all_paths (m : Matrix) (k : nat) 
      (c d : Node) : list Path :=
      let lp := all_paths_klength m k c d in 
      List.map (fun l => (c, d, l)) lp.

    (* get all the R values from path *)
    Definition get_all_rvalues (pl : list Path): list R :=
      List.map (fun '(_, _, l) => measure_of_path l) pl.

  
    Definition sum_all_rvalues (pl : list R) :=
      List.fold_right (fun b a => b + a) 0 pl.

    
    (* sum_fn using fold_right *)
    Definition sum_fn_fold (f : Node -> R) (l : list Node) : R :=
      List.fold_right (fun b a => f b + a) 0 l.

    
    Definition non_empty_list {A : Type} (l : list A) : bool :=
      match l with 
      | [] => false
      | _ => true
      end.


    Fixpoint all_elems_non_empty_list {A : Type} (l : list (list A)) : bool :=
      match l with 
      | [] => true
      | h :: t => match h with 
        | [] => false
        | _ => all_elems_non_empty_list t
      end 
      end.


    (* This function compares two lists for boolean equality *)
    Fixpoint triple_elem_list (l₁ l₂ : list (Node * Node * R)) :=
      match l₁ with 
      | [] => match l₂ with 
        | [] => true
        | _ => false
        end
      | (a, b, c) :: t₁ => match l₂ with 
        | [] => false
        | (d, e, f) :: t₂ => ((a =n= d) && (b =n= e) && (c =r= f) && 
          triple_elem_list t₁ t₂)%bool
        end
      end.
    

    Lemma triple_elem_eq_list : forall l, 
      triple_elem_list l l = true.
    Proof using -All.
      induction l.
      - simpl. reflexivity.
      - simpl. destruct a.
        destruct p.
        repeat (apply Bool.andb_true_iff; split;
          try (apply refN); try (apply IHl)).
        apply refR.
    Qed.
    

    (* This function tests if l₁ in l₂ or not *)
    Fixpoint In_eq_bool (l₁ : list (Node * Node * R))
      (l₂ : list (list (Node * Node * R))) : bool :=
      match l₂ with
      | [] => false
      | h :: t => ((triple_elem_list l₁ h) || (In_eq_bool l₁ t))%bool 
      end.

    

    
    Lemma append_node_in_paths_non_empty_list : 
      forall (l : list (list (Node * Node * R))) (m : Matrix) 
      (c : Node),  
      all_elems_non_empty_list (append_node_in_paths m c l) = true.
    Proof using -All.
      induction l.
      + simpl; intros ? ?. 
        reflexivity.
      + simpl.
        destruct a. apply IHl.
        intros. destruct p. 
        destruct p.
        simpl. apply IHl.
    Qed.


    Lemma append_node_in_paths_eq : 
      forall (l : list (list (Node * Node * R))) 
      (m : Matrix) (c : Node) (xs : list (Node * Node * R)), 
      In_eq_bool xs (append_node_in_paths m c l) = true -> 
      exists y ys, triple_elem_list xs ((c, y, m c y) :: ys) = true /\
      source c xs = true /\ source y ys = true /\ ys <> [].
    Proof using  Node R eqN eqR refN symN.
      induction l.
      - simpl; intros ? ? ? Hf.
        inversion Hf.
      - intros ? ? ? H.
        simpl in H.
        destruct a.
        apply IHl with (m := m) (c := c).
        exact H.
        repeat destruct p.
        simpl in H.
        apply Bool.orb_true_iff in H.
        destruct H.
        exists n, ((n, n0, r) :: a).
        split. exact H.
        destruct xs. simpl in H.
        congruence. 
        repeat destruct p.
        simpl in H. simpl.
        apply Bool.andb_true_iff in H.
        destruct H as [Hl Hr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hll Hlr].
        apply Bool.andb_true_iff in Hll.
        destruct Hll as [Hlll Hlllr].
        split. apply symN. 
        exact Hlll. 
        split. apply refN.
        intro Hf. inversion Hf.
        apply IHl with (m := m) (c := c).
        exact H.
    Qed.
   

    Lemma non_empty_paths_in_kpath : forall (n : nat) (m : Matrix) 
      (c d : Node) (xs : list (Node * Node * R)), 
      In_eq_bool xs (all_paths_klength m n c d) = true -> 
      xs <> [].
    Proof using Node R eqN eqR finN oneR refN symN.
      induction n.
      - simpl; intros ? ? ? ? Hin.
        case (c =n= d) eqn:Ht.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        intro Hf. rewrite Hf in Hin.
        simpl in Hin. congruence.
        congruence.
        intro Hf. rewrite Hf in Hin.
        simpl in Hin. congruence.
      - simpl; intros ? ? ? ? Hin.
        destruct (append_node_in_paths_eq
          (flat_map (λ x : Node, all_paths_klength m n x d) finN)
          m c xs Hin) as [y [ys [Hl Hr]]].
        intro Hf. rewrite Hf in Hl.
        simpl in Hl. congruence.
    Qed.


    Lemma source_in_kpath : forall (n : nat) (m : Matrix) 
      (c d : Node) (xs : list (Node * Node * R)), 
      In_eq_bool xs (all_paths_klength m n c d) = true -> 
      source c xs = true.
    Proof using Node R eqN eqR finN oneR refN symN.
      induction n.
      - simpl; intros ? ? ?? Hin.
        case (c =n= d) eqn:Ht.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        destruct xs.
        simpl in Hin. 
        congruence.
        simpl in Hin.
        simpl.
        repeat destruct p.
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hrr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hrrr].
        apply symN. exact Hin.
        congruence.
        simpl in Hin.
        congruence.
      - simpl; intros ? ? ? ? Hin.
        destruct (append_node_in_paths_eq 
          (flat_map (λ x : Node, all_paths_klength m n x d) finN)
          m c xs Hin) as [y [ys [Hl [Hr Hw]]]].
        assumption.
    Qed.



    Lemma source_and_non_empty_kpath : forall (n : nat) (m : Matrix) 
      (c d : Node) (xs : list (Node * Node * R)), 
      In_eq_bool xs (all_paths_klength m n c d) = true ->
      xs <> [] /\ source c xs = true.
    Proof using Node R eqN eqR finN oneR refN symN.
      intros ? ? ? ? ? Hin.
      split.
      apply non_empty_paths_in_kpath with (n := n) (m := m) (c := c) (d := d).
      exact Hin.
      apply source_in_kpath with (n := n) (m := m) (d := d).
      exact Hin.
    Qed.




    Lemma fold_map_pullout : forall l w,
      fold_right (fun a b => a + b) 0 
        (map (fun y => w * measure_of_path y) l) =r=
      w * fold_right (fun a b => a + b) 0 
        (map measure_of_path l) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus mulR
    oneR plusR refR symR zeroR zero_right_anhilator_mul.
      induction l.
      - simpl; intros ?.
        apply symR, zero_right_anhilator_mul.
      - simpl; intros ?.
        assert (Ht: w *
          (measure_of_path a +
          fold_right (λ a0 b : R, a0 + b) 0 (map measure_of_path l)) =r= 
         w * measure_of_path a + 
         w * fold_right (λ a0 b : R, a0 + b) 0 (map measure_of_path l) = true).
        apply left_distributive_mul_over_plus.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply congrP.
        apply refR.
        apply IHl.
        apply refR.
    Qed.


    Lemma map_measure_simp_gen :
      forall (l : list (list (Node * Node * R))) 
      (m : Matrix) (c a : Node),
      mat_cong m ->
      (forall xs, In_eq_bool xs l = true -> xs <> [] /\ source a xs = true) ->
      list_eqv _ eqR 
        (map measure_of_path (append_node_in_paths m c l))
        (map (fun y => m c a * measure_of_path y) l) = true.
    Proof using Node R congrM eqN eqR mulR oneR refN refR symN.
      induction l as [|ys yss IH].
      - simpl; intros ? ? ? Hm Hin.
        reflexivity.
      - simpl; intros ? ? ? Hm Hin.
        assert (Ht : (triple_elem_list ys ys || In_eq_bool ys yss)%bool = true).
        apply Bool.orb_true_iff.
        left. apply triple_elem_eq_list.
        pose proof (Hin ys Ht) as Ha.
        destruct Ha as [Ha Hs].
        destruct ys. 
        congruence. simpl.
        repeat destruct p.
        simpl. simpl in Hs.
        apply Bool.andb_true_iff.
        split.
        apply congrM.
        apply Hm. apply refN.
        apply symN. exact Hs.
        apply refR. 
        apply IH. exact Hm.
        intros ? Hxs.
        apply Hin.
        apply Bool.orb_true_iff.
        right. exact Hxs.
    Qed.

    
     
    Lemma map_measure_simp : forall m n c d a, 
      mat_cong m -> 
      list_eqv _ eqR 
      (map measure_of_path
        (append_node_in_paths m c (all_paths_klength m n a d)))
      (map (fun y => m c a * measure_of_path y) 
        (all_paths_klength m n a d)) = true.
    Proof using Node R congrM eqN eqR finN mulR oneR refN refR symN.
      intros ? ? ? ? ? Hm.
      apply map_measure_simp_gen.
      exact Hm.
      intros ? Hin.
      exact (source_and_non_empty_kpath n m a d xs Hin).
    Qed.



    Lemma fold_right_congr : forall l₁ l₂,
      list_eqv R eqR l₁ l₂ = true -> 
      fold_right (fun a b => a + b) 0 l₁ =r= 
      fold_right (fun a b => a + b) 0 l₂ = true.
    Proof using R congrP eqR plusR refR zeroR.
      induction l₁; destruct l₂; simpl; intro H.
      - apply refR.
      - inversion H.
      - inversion H.
      - apply Bool.andb_true_iff in H.
        destruct H as [Hl Hr].
        apply congrP.
        exact Hl.
        apply IHl₁.
        exact Hr.
    Qed.


    (* x * l1 + x * l2 + x * l3 = x * (l1 + l2 + l3) *)
    Lemma fold_right_measure : forall n m c a d,
      mat_cong m -> 
      (fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
      (map measure_of_path
        (append_node_in_paths m c (all_paths_klength m n a d))) =r=
      m c a *
      fold_right (λ b v : R, b + v) 0
        (map measure_of_path (all_paths_klength m n a d))) = true.
    Proof using Node R congrM congrP congrR eqN eqR finN
    left_distributive_mul_over_plus mulR oneR plusR refN refR symN symR zeroR
    zero_right_anhilator_mul.
      intros ? ? ? ? ? Hm.
      assert (Ht : 
      fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
      (map measure_of_path
        (append_node_in_paths m c (all_paths_klength m n a d))) =r= 
      fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
      (map (fun y => m c a * measure_of_path y) 
        (all_paths_klength m n a d)) = true).
      apply fold_right_congr.
      apply map_measure_simp.
      exact Hm.
      rewrite <-Ht; clear Ht.
      apply congrR.
      apply refR.
      apply symR.
      apply fold_map_pullout.
    Qed.


    
    Lemma sum_fn_sum_fn_fold : forall l f, 
      sum_fn f l =r= sum_fn_fold f l = true.
    Proof using Node R congrP eqR plusR refR zeroR.
      induction l.
      + simpl; intros ?.
        apply refR.
      + simpl; intros ?.
        apply congrP.
        apply refR.
        apply IHl.
    Qed. 


    Lemma append_node_app : forall (l₁ l₂ : list (list (Node * Node * R))) 
      (m : Matrix) (c : Node), 
      fold_right (λ u v : R, u + v) 0
        (map measure_of_path
          (append_node_in_paths m c
            (l₁ ++ l₂))) 
      =r=
      fold_right (λ u v : R, u + v) 0
        (map measure_of_path
          (append_node_in_paths m c l₁ ++ 
          append_node_in_paths m c l₂)) = true.
    Proof using Node R congrP eqR mulR oneR plusR refR zeroR.
      induction l₁ as [|a l₁ IHL₁].
      - simpl; intros ? ? ?.
        apply refR.
      - simpl; intros ? ? ?.
        destruct a.
        apply IHL₁.
        repeat destruct p.
        simpl. 
        apply congrP.
        apply refR.
        apply IHL₁.
    Qed.
        

    Local Lemma fold_right_dist_eqr_aide :
      forall a b c d e : R, b =r= d + e = true ->
      a + b =r= a + d + e = true.
    Proof using R congrP congrR eqR plusR plus_associative refR symR.
      intros ? ? ? ? ? H.
      assert (Ht : a + d + e =r= a + (d + e) = true).
      apply symR. apply plus_associative.
      apply symR. rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP. apply refR.
      exact H.
    Qed.

    Lemma fold_right_dist_eqr : forall l₁ l₂ : list R, 
      (fold_right (fun u v : R => u + v) 0 (l₁ ++ l₂))
      =r= 
      (fold_right (fun u₁ v₁ : R => u₁ + v₁) 0 l₁ + 
      fold_right (fun u₂ v₂ : R => u₂ + v₂) 0 l₂) = true.
    Proof using R congrP congrR eqR plusR plus_associative refR symR zeroR
    zero_left_identity_plus.
      induction l₁.
      - simpl; intros ?.
        apply symR.
        apply zero_left_identity_plus.
      - simpl; intros ?.
        apply fold_right_dist_eqr_aide. exact a.
        apply IHl₁.
    Qed.



    (* x * l1 + x * l2 + x * l3 = x * (l1 + l2 + l3) *)
    Lemma fold_map_rel : forall l m n c d,
      mat_cong m ->  
      fold_right (λ u v : R, u + v) 0
        (map measure_of_path
          (append_node_in_paths m c
            (flat_map (λ x : Node, all_paths_klength m n x d) l))) 
      =r= 
      fold_right (fun x t => m c x * 
        (fold_right (fun b v => b + v) 0 
          (map measure_of_path (all_paths_klength m n x d))) + t) 0 l 
      = true.
    Proof using Node R congrM congrP congrR eqN eqR finN
    left_distributive_mul_over_plus mulR oneR plusR plus_associative refN refR
    symN symR zeroR zero_left_identity_plus zero_right_anhilator_mul.
      induction l as [|a l IHL].
      - simpl; intros ? ? ? ? Hm.
        apply refR.
      - simpl; intros ? ? ? ? Hm.
        pose proof append_node_app (all_paths_klength m n a d)
          (flat_map (λ x : Node, all_paths_klength m n x d) l)
          m c as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        apply symR.
        rewrite map_app.
        pose proof fold_right_dist_eqr 
        (map measure_of_path
          (append_node_in_paths m c (all_paths_klength m n a d)))
        (map measure_of_path
        (append_node_in_paths m c
           (flat_map (λ x : Node, all_paths_klength m n x d) l))) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        apply symR.
        apply congrP. 
        apply fold_right_measure.
        exact Hm.
        apply IHL.
        exact Hm.
    Qed.
    

        
    Lemma fold_right_cong : forall l (g f: Node -> R -> R) a,
      (forall x u v, u =r= v = true -> f x u =r= g x v = true) -> 
      fold_right f a l =r= fold_right g a l = true.
    Proof using Node R eqR refR.
      induction l.
      - simpl; intros ? ? ? Hx.
        apply refR.
      - simpl; intros ? ? ? Hx.
        pose proof (IHl g f a0 Hx) as Hw.
        apply Hx. exact Hw.
    Qed.



    Lemma matrix_path_equation : forall n m c d,
      mat_cong m -> 
      matrix_exp_unary m n c d =r= 
      sum_all_rvalues (get_all_rvalues (construct_all_paths m n c d)) = true.
    Proof using Node R congrM congrP congrR eqN eqR finN
    left_distributive_mul_over_plus mulR oneR one_left_identity_mul plusR
    plus_associative refN refR symN symR zeroR zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros ? ? ? ? Hm.
      unfold sum_all_rvalues, get_all_rvalues, construct_all_paths;
      rewrite map_map.
      revert n c d.
      induction n.
      + simpl; intros ? ?; unfold I.
        destruct (c =n= d) eqn:Ht.
        - simpl. apply symR.
          assert (Htw: 1 * 1 + 0 =r= 1 + 0 = true).
          apply congrP.
          apply one_left_identity_mul.
          apply refR.
          rewrite <- Htw; clear Htw.
          apply congrR.
          apply refR.
          apply symR.
          apply zero_right_identity_plus.
        - simpl. apply refR.
      + simpl; intros ? ?.
        unfold matrix_mul, matrix_mul_gen.
        assert (Ht : 
        (sum_fn (λ y : Node, m c y * matrix_exp_unary m n y d) finN =r=
        fold_right (λ b a : R, b + a) 0
          (map (λ x : list (Node * Node * R), measure_of_path x)
             (append_node_in_paths m c
                (flat_map (λ x : Node, all_paths_klength m n x d) finN))))
        =
        (sum_fn_fold (λ y : Node, m c y * matrix_exp_unary m n y d) finN =r=
        fold_right (λ b a : R, b + a) 0
          (map (λ x : list (Node * Node * R), measure_of_path x)
             (append_node_in_paths m c
                (flat_map (λ x : Node, all_paths_klength m n x d) finN))))).
        apply congrR.
        apply sum_fn_sum_fn_fold.
        apply refR.
        rewrite Ht; clear Ht.
        unfold sum_fn_fold.
        apply symR.
        rewrite <-(fold_map_rel finN m n c d).
        apply congrR.
        apply refR.
        apply fold_right_cong.
        intros.
        apply congrP.
        apply congrM.
        apply refR.
        apply IHn.
        exact H.
        exact Hm.
    Qed.
      

    Lemma triple_trim_tail : forall (xs : list (Node * Node * R)) 
      (a b : Node * Node * R) (c : list (Node * Node * R)),
      triple_elem_list xs (a :: b :: c) = true ->
      triple_elem_list (List.tl xs) (b :: c) = true.
    Proof using -All.
      destruct xs.
      - simpl; intros ? ? ? He.
        congruence.
      - simpl; intros ? ? ? He.
        repeat destruct p in He.
        destruct a in He.
        destruct p in He.
        apply Bool.andb_true_iff in He.
        destruct He as [Hel Her].
        exact Her.
    Qed.



    Local Lemma append_node_rest : forall l m c xs,
      In_eq_bool xs (append_node_in_paths m c l) = true ->
      In_eq_bool (List.tl xs) l = true.
    Proof using -All.
      induction l.
      - simpl; intros ? ? ? Hin.
        inversion Hin.
      - simpl; intros ? ? ? Hin. 
        destruct a.
        eapply Bool.orb_true_iff.
        right. 
        apply IHl with (m := m) (c := c).
        exact Hin.
        repeat destruct p.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [H | H].
        apply Bool.orb_true_iff.
        left. apply triple_trim_tail with (a := (c, n, m c n)).
        exact H.
        apply Bool.orb_true_iff.
        right. 
        apply IHl with (m := m) (c := c).
        exact H.
    Qed.



    Lemma target_tail : forall (xs : list (Node * Node * R)) (d : Node), 
      target d (tl xs) = true -> target d xs = true.
    Proof using -All.
      destruct xs.
      - simpl; intros ? ?.
        exact H.
      - simpl; intros ? ?.
        repeat destruct p.
        destruct xs.
        simpl in H.
        congruence.
        exact H.
    Qed.



    Lemma in_eq_bool_mem_first : forall (l₁ l₂ : list (list (Node * Node * R)))
      (y : list (Node * Node * R)), 
      In_eq_bool y (l₁ ++ l₂) = true -> 
      In_eq_bool y l₁ = true \/ In_eq_bool y l₂ = true.
    Proof using -All.
      induction l₁.
      - simpl; intros ? ? Hin.
        right. exact Hin.
      - simpl; intros ? ? Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        left. 
        apply Bool.orb_true_iff.
        left. exact Hin.
        destruct (IHl₁ _ _ Hin) as [H | H].
        left. 
        apply Bool.orb_true_iff.
        right. exact H.
        right.
        exact H.
    Qed.



    Lemma in_eq_bool_mem_second : forall (l₁ l₂ : list (list (Node * Node * R)))
      (y : list (Node * Node * R)),  
      In_eq_bool y l₁ = true \/ In_eq_bool y l₂ = true -> 
      In_eq_bool y (l₁ ++ l₂) = true.
    Proof using -All.
      induction l₁.
      - simpl; intros ? ? [Hin | Hin]; 
        congruence.
      - simpl; intros ? ? [Hin | Hin].
        apply Bool.orb_true_iff in Hin.
        apply Bool.orb_true_iff.
        destruct Hin as [Hin | Hin].
        left. exact Hin.
        right. 
        exact (IHl₁ l₂ y (or_introl Hin)).
        apply Bool.orb_true_iff.
        right.
        exact (IHl₁ l₂ y (or_intror Hin)).
    Qed.

      

    Lemma in_flat_map_bool_first : forall (l : list Node) (y : list (Node * Node * R))
      (f : Node -> list (list (Node * Node * R))),
      In_eq_bool y (flat_map f l) = true -> 
      (exists x : Node, in_list eqN l x = true /\ 
      In_eq_bool y (f x) = true).
    Proof using Node R eqN eqR refN.
      induction l.
      - simpl; intros ? ? Hin.
        congruence.
      - simpl; intros ? ? Hin.
        apply in_eq_bool_mem_first in Hin.
        destruct Hin as [Hin | Hin].
        exists a. split.
        apply Bool.orb_true_iff.
        left. apply refN.
        exact Hin.
        destruct (IHl _ _ Hin) as [x [Hl Hr]].
        exists x. split.
        apply Bool.orb_true_iff.
        right. exact Hl.
        exact Hr.
    Qed.


    Definition in_eq_bool_cong (f : Node → list (list (Node * Node * R))) :=
      forall (x a : Node) (y : list (Node * Node * R)),  
       (x =n= a) = true -> In_eq_bool y (f a) = In_eq_bool y (f x). 


    Lemma in_flat_map_bool_second : forall (l : list Node) 
      (f : Node -> list (list (Node * Node * R)))
      (y : list (Node * Node * R)) (x : Node),
      in_eq_bool_cong f -> 
      in_list eqN l x = true -> In_eq_bool y (f x) = true ->
      In_eq_bool y (flat_map f l) = true.
    Proof using -All.
      induction l.
      - simpl; intros ? ? ? Hc Hin Hf.
        congruence.
      - simpl; intros ? ? ? Hc Hin Hf.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        apply in_eq_bool_mem_second.
        left. rewrite <-Hf.
        apply Hc. exact Hin.
        apply in_eq_bool_mem_second.
        right. apply IHl with (x := x).
        exact Hc.
        exact Hin.
        exact Hf.
    Qed.


      
    (* boolean equivalent of in_flat_map *)
    Lemma in_flat_map_bool : forall (l : list Node) (y : list (Node * Node * R))
      (f : Node -> list (list (Node * Node * R))),
      in_eq_bool_cong f -> 
      In_eq_bool y (flat_map f l) = true <-> 
      (exists x : Node, in_list eqN l x = true /\ 
      In_eq_bool y (f x) = true).
    Proof using Node R eqN eqR refN.
      intros ? ? ? Hc; split; intros H.
      apply in_flat_map_bool_first; exact H.
      destruct H as [x [Hl Hr]].
      apply in_flat_map_bool_second with (x := x).
      exact Hc. exact Hl. exact Hr.
    Qed.

    Lemma orb_eq : forall (a b c : bool), 
      a = c -> (a || b = c || b)%bool.
    Proof using -All.
      intros [|] [|] [|] H; simpl;
      try reflexivity; try congruence.
    Qed.

    Lemma andb_eq : forall (a b c d e f g: bool), 
      (a && b && c = e && f && g)%bool -> 
      (a && b && c && d = e && f && g && d)%bool.
    Proof using -All.
      intros [|] [|] [|] [|] [|] [|] [|] H; simpl in * |- *;
      try reflexivity; try congruence.
    Qed.

    Lemma triple_eq_cong : forall l v y a₁ a₂
      b₁ b₂ r₁ r₂,
      a₁ =n= a₂ = true -> b₁ =n= b₂ = true -> 
      r₁ =r= r₂ = true ->
      triple_elem_list y ((a₁, b₁, r₁) :: v :: l) =
      triple_elem_list y ((a₂, b₂, r₂) :: v :: l).
    Proof using Node R eqN eqR symN symR trnN trnR.
      intros ? ? ? ? ? ? ? ? ? H₁ H₂ H₃.
      destruct y; simpl. reflexivity.
      repeat destruct p. apply andb_eq.
      
      (* 
        God, give me strenght to prove
        this lemma! 
      *)
      case (n =n= a₁) eqn:Hn₁;
      case (n0 =n= b₁) eqn:Hn₂;
      case (r =r= r₁) eqn:Hr₁;
      case (n =n= a₂) eqn:Hn₃;
      case (n0 =n= b₂) eqn:Hn₄;
      case (r =r= r₂) eqn:Hr₂; simpl;
      auto.
      pose proof (trnR _ _ _ Hr₁ H₃) as Hf.
      rewrite Hf in Hr₂. congruence.
      pose proof (trnN _ _ _ Hn₂ H₂) as Hf.
      rewrite Hf in Hn₄. congruence.
      pose proof (trnR _ _ _ Hr₁ H₃) as Hf.
      rewrite Hf in Hr₂. congruence.
      pose proof (trnN _ _ _ Hn₁ H₁) as Hf.
      rewrite Hf in Hn₃. congruence.
      pose proof (trnR _ _ _ Hr₁ H₃) as Hf.
      rewrite Hf in Hr₂. congruence.
      pose proof (trnN _ _ _ Hn₁ H₁) as Hf.
      rewrite Hf in Hn₃. congruence.
      pose proof (trnN _ _ _ Hn₁ H₁) as Hf.
      rewrite Hf in Hn₃. congruence.
      apply symR in H₃.
      pose proof (trnR _ _ _ Hr₂ H₃) as Hf.
      rewrite Hf in Hr₁. congruence.
      apply symN in H₂.
      pose proof (trnN _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      apply symN in H₂.
      pose proof (trnN _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      apply symN in H₁.
      pose proof (trnN _ _ _ Hn₃ H₁) as Hf.
      rewrite Hf in Hn₁; congruence.
      apply symR in H₃.
      pose proof (trnR _ _ _ Hr₂ H₃) as Hf.
      rewrite Hf in Hr₁. congruence.
      apply symN in H₂.
      pose proof (trnN _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      apply symN in H₂.
      pose proof (trnN _ _ _ Hn₄ H₂) as Hf.
      rewrite Hf in Hn₂. congruence.
      (* Thank you, God! *)
    Qed.



    Lemma in_eq_append_cong : forall l m a x y,
      mat_cong m -> 
      a =n= x = true ->  
      In_eq_bool y (append_node_in_paths m a l) =
      In_eq_bool y (append_node_in_paths m x l).
    Proof using Node R eqN eqR refN symN symR trnN trnR.
      induction l.
      - simpl; intros ? ? ? ? Hm Hax;
        reflexivity.
      - simpl; intros ? ? ? ? Hm Hax.
        destruct a.
        + apply IHl. exact Hm. exact Hax.
        + repeat destruct p.
          simpl. 
          pose proof (IHl m a0 x y Hm Hax) as IH.
          rewrite IH.
          apply orb_eq.
          apply triple_eq_cong.
          exact Hax.
          apply refN.
          apply Hm. exact Hax.
          apply refN.
    Qed.
    
          


    

    Lemma all_paths_cong : forall n m d,
      mat_cong m -> 
      in_eq_bool_cong (λ x : Node, all_paths_klength m n x d).
    Proof using Node R eqN eqR finN oneR refN symN symR trnN trnR.
      unfold in_eq_bool_cong.
      induction n.
      - simpl; intros ? ? Hm ? ? ? Hxa.
        case_eq (a =n= d); intros Ht.
        assert(Hv : x =n= d = true).
        eapply trnN with a; assumption.
        rewrite Hv; clear Hv.
        destruct y; simpl.
        reflexivity.
        repeat destruct p.
        repeat rewrite Bool.orb_false_r.
        assert (Hv : (n =n= a) = (n =n= x)).
        case_eq (n =n= a); intros Hna;
        case_eq (n =n= x); intros Hnx; auto.
        apply symN in Hxa.
        pose proof (trnN _ _ _ Hna Hxa) as Hf.
        rewrite Hf in Hnx; congruence.
        pose proof (trnN _ _ _ Hnx Hxa) as Hf.
        rewrite Hf in Hna; congruence.
        rewrite Hv. reflexivity.
        simpl; case_eq (x =n= d); 
        intro Hx; auto.
        apply symN in Hxa.
        pose proof (trnN _ _ _ Hxa Hx) as Hw.
        rewrite Ht in Hw.
        congruence.    
      - simpl; intros ? ? Hm ? ? ? Hxa.
        remember (flat_map (λ x0 : Node, all_paths_klength m n x0 d) finN)
        as l.
        apply in_eq_append_cong.
        exact Hm.
        apply symN. exact Hxa.
    Qed.



    Lemma target_in_kpath : forall (n : nat) (m : Matrix) 
      (c d : Node) (xs : list (Node * Node * R)),
      mat_cong m ->
      In_eq_bool xs (all_paths_klength m n c d) = true -> 
      target d xs = true.
    Proof using Node R eqN eqR finN oneR refN symN symR trnN trnR.
      induction n.
      - simpl; intros ? ? ? ? Hm Hin.
        case (c =n= d) eqn:Ht.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        destruct xs.
        simpl in Hin. 
        congruence.
        simpl in Hin.
        simpl.
        repeat destruct p.
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hrr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hrrr].
        destruct xs.
        apply symN. exact Hrrr.
        simpl in Hr.
        repeat destruct p.
        congruence.
        congruence.
        simpl in Hin.
        congruence.
      - simpl; intros ? ? ? ? Hm Hin.
        pose proof append_node_rest
        (flat_map (λ x : Node, all_paths_klength m n x d) finN)
        m c xs Hin as Hv.
        destruct (proj1 (in_flat_map_bool finN (List.tl xs)
        (λ x : Node, all_paths_klength m n x d)
        (all_paths_cong _ _ _ Hm)) Hv) as [w [Ha Hb]].
        specialize (IHn m w d (List.tl xs) Hm Hb).
        apply target_tail.
        exact IHn.
    Qed.    
        
   
    Lemma well_formed_by_extending : 
      forall xs ys c y m, mat_cong m -> ys <> [] ->  
      triple_elem_list xs ((c, y, m c y) :: ys) = true -> 
      source c xs = true -> source y ys = true ->
      well_formed_path_aux m (tl xs) = true ->
      well_formed_path_aux m xs = true.
    Proof using Node R congrR eqN eqR refR symN symR trnN.
      destruct xs.
      - simpl; intros ? ? ? ? Hm Hys Ht Hs Hsy Hw.
        congruence.
      - intros ? ? ? ? Hm Hys Ht Hs Hsy Hw.
        destruct xs.
        + simpl in * |- *.
          repeat destruct p.
          apply Bool.andb_true_iff in Ht.
          destruct Ht as [Ht Htr].
          apply Bool.andb_true_iff in Ht.
          destruct Ht as [Ht Htrr].
          apply Bool.andb_true_iff in Ht.
          destruct Ht as [Ht Hrrr].
          apply Bool.andb_true_iff.
          split. apply symR in Htrr.
          rewrite <-Htrr.
          apply congrR. apply Hm.
          apply symN.
          apply symN. exact Ht.
          exact Hrrr.
          apply refR.
          reflexivity.
        +
          repeat destruct p. repeat destruct p0.
          repeat destruct p.
          assert (Hwt : well_formed_path_aux m (tl ((n, n0, r) :: (n1, n2, r0) :: xs)) =
          well_formed_path_aux m (((n1, n2, r0) :: xs))).
          reflexivity. rewrite Hwt in Hw; clear Hwt.
          assert (Hg : well_formed_path_aux m ((n, n0, r) :: (n1, n2, r0) :: xs) =
          ((m n n0 =r= r) &&
          ((n0 =n= n1) && well_formed_path_aux m ((n1, n2, r0) :: xs)))%bool).
          reflexivity. rewrite Hg; clear Hg.
          assert (Hvt : triple_elem_list ((n, n0, r) :: (n1, n2, r0) :: xs)
          ((c, y, m c y) :: ys) = 
          ((n =n= c) && (n0 =n= y) && (r =r= m c y) &&
          triple_elem_list ((n1, n2, r0) :: xs) ys)%bool).
          reflexivity.
          rewrite Hvt in Ht; clear Hvt.
          apply Bool.andb_true_iff in Ht.
          destruct Ht as [Ht Htr].
          apply Bool.andb_true_iff in Ht.
          destruct Ht as [Ht Htrr].
          apply Bool.andb_true_iff in Ht.
          destruct Ht as [Ht Hrrr].
          apply Bool.andb_true_iff.
          split.
          apply symR in Htrr.
          rewrite <-Htrr.
          apply congrR. apply Hm.
          apply symN.
          apply symN. exact Ht.
          exact Hrrr.
          apply refR.
          apply Bool.andb_true_iff.
          split.
          destruct ys.
          simpl in Htr. congruence.
          repeat destruct p.
          simpl in Htr.
          simpl in Hsy.
          apply Bool.andb_true_iff in Htr.
          destruct Htr as [Htr Htt].
          apply Bool.andb_true_iff in Htr.
          destruct Htr as [Htr Htrrt].
          apply Bool.andb_true_iff in Htr.
          destruct Htr as [Htr Hrrw].
          pose proof (trnN _ _ _ Hrrr Hsy) as Ha.
          apply symN in Htr.
          exact (trnN _ _ _ Ha Htr).
          exact Hw.
    Qed.


     


    (* paths generated by all_paths_klength function are well formed *)
    Lemma all_paths_well_formed_in_kpaths : forall (n : nat) (m : Matrix) 
      (c d : Node) (xs : list (Node * Node * R)),
      (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
      mat_cong m ->  
      In_eq_bool xs (all_paths_klength m n c d) = true ->
      well_formed_path_aux m xs = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative refN refR right_distributive_mul_over_plus symN symR trnN
    trnR zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      induction n.
      - simpl; intros ? ? ? ? Hcd Hm Hin.
        case (c =n= d) eqn:Ht.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        destruct xs.
        simpl in Hin. 
        congruence.
        simpl in Hin.
        simpl.
        repeat destruct p.
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hrr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hrrr].
        destruct xs.
        apply Bool.andb_true_iff.
        split. apply symN in Ht.
        pose proof (trnN _ _ _ Hrrr Ht) as Hv.
        pose proof (trnN _ _ _ Hv (symN  _ _ Hin)) as Hw.
        apply symN in Hw.
        pose proof (Hcd _ _ Hw) as Hwt.
        rewrite <-Hwt.
        apply congrR. apply refR.
        exact Hrr.
        reflexivity.
        simpl in Hr. 
        repeat destruct p.
        congruence.
        congruence.
        simpl in Hin.
        congruence.
    -   simpl; intros ? ? ? ? Hcd Hm Hin.
        pose proof append_node_rest
        (flat_map (λ x : Node, all_paths_klength m n x d) finN)
        m c xs Hin as Hv.
        destruct (proj1 (in_flat_map_bool finN (List.tl xs)
        (λ x : Node, all_paths_klength m n x d)
        (all_paths_cong _ _ _ Hm)) Hv) as [w [Ha Hb]].
        specialize (IHn m w d (List.tl xs) Hcd Hm Hb).
        destruct (append_node_in_paths_eq
        (flat_map (λ x : Node, all_paths_klength m n x d) finN)
        m c xs Hin) as [y [ys [Hu [Hvt [Hwl Hwr]]]]].
        apply well_formed_by_extending with (ys := ys) (c := c) (y := y);
        assumption.
    Qed.
  
    

    Lemma path_split_measure : forall l l₁ l₂, 
      triple_elem_list l (l₁ ++ l₂) = true  -> 
      measure_of_path l =r= 
      measure_of_path l₁ * measure_of_path l₂ = true.
    Proof using Node R congrM congrR eqN eqR mulR mul_associative oneR
    one_left_identity_mul refR symR.
      induction l.
      - simpl; intros ? ? Hl.
        destruct l₁; destruct l₂; simpl in * |- *.
        apply symR. apply one_left_identity_mul.
        all: congruence.
      - simpl; intros ? ? Hl.
        destruct a. destruct p.
        destruct l₁; destruct l₂; simpl in * |- *.
        congruence.
        repeat destruct p.
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlrr].
        assert (Ht : 1 * (r0 * measure_of_path l₂) =r= 
          (r0 * measure_of_path l₂) = true).
        apply one_left_identity_mul.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply congrM.
        exact Hlr.
        pose proof (IHl [] l₂) as IHs.
        simpl in IHs.
        specialize (IHs Hr).
        rewrite <-IHs.
        apply congrR. 
        apply refR.
        apply symR.
        apply one_left_identity_mul.
        apply refR.
        repeat destruct p.
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlrr].
        specialize (IHl l₁ [] Hr).
        simpl in IHl.
        assert (Ht : r0 * (measure_of_path l₁ * 1) =r= 
        r0 * measure_of_path l₁ * 1 = true).
        apply mul_associative.
        rewrite <-Ht; clear Ht.
        apply congrR. apply congrM.
        exact Hlr. exact IHl.
        apply refR.
        repeat destruct p.
        destruct p0.
        destruct p.
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlrr].
        specialize (IHl l₁ ((n3, n4, r1) :: l₂) Hr).
        simpl in IHl.
        assert (Ht : r0 * (measure_of_path l₁ * (r1 * measure_of_path l₂)) =r= 
        r0 * measure_of_path l₁ * (r1 * measure_of_path l₂) = true).
        apply mul_associative.
        rewrite <-Ht; clear Ht.
        apply congrR. apply congrM.
        exact Hlr.
        exact IHl.
        apply refR.
    Qed.



    Fixpoint all_distinct_node (l : list Node) : bool :=
      match l with 
      | [] => true
      | h :: t => negb (in_list eqN t h) && 
        all_distinct_node t
      end.


   
    Lemma in_list_mem_true : forall (l : list Node) (a : Node),
      in_list eqN l a = true -> 
      exists l₁ l₂ : list Node, list_eqv _ eqN l (l₁ ++ [a] ++ l₂) = true.
    Proof using Node eqN refN symN.
      induction l.
      - simpl; intros ? H; 
        congruence.
      - simpl; intros ? H.
        apply Bool.orb_true_iff in H.
        destruct H as [H | H].
        exists [], l; simpl.
        apply Bool.andb_true_iff.
        split. apply symN. exact H.
        apply list_eqv_refl; assumption.
        destruct (IHl a0 H) as [l₁ [l₂ Ht]].
        exists (a :: l₁), l₂.
        simpl. apply Bool.andb_true_iff.
        split. apply refN.
        exact Ht.
    Qed.



    Lemma duplicate_node : forall (l : list Node),
      all_distinct_node l = false -> 
      exists (c : Node) (l₁ l₂  l₃ : list Node), 
      list_eqv _ eqN l (l₁ ++ [c] ++ l₂ ++ [c] ++ l₃) = true. 
    Proof using Node eqN refN symN.
      induction l.
      - simpl; intros Hf;
        congruence.
      - simpl; intros Ha.
        apply Bool.andb_false_iff in Ha.
        destruct Ha as [Ha | Ha].
        apply Bool.negb_false_iff in Ha.
        destruct (in_list_mem_true l a Ha) as 
          [l₁ [l₂ Ht]].
        exists a, [], l₁, l₂.
        simpl. apply Bool.andb_true_iff.
        split. apply refN.
        exact Ht.
        destruct (IHl Ha) as [c [l₁ [l₂ [l₃ Ht]]]].
        exists c, (a :: l₁), l₂, l₃.
        simpl.
        apply Bool.andb_true_iff.
        split. apply refN.
        exact Ht.
    Qed.




    Definition cyclic_path (c : Node) (l : list (Node * Node * R)) :=
      source c l = target c l.

    

    Fixpoint elem_path (m : Matrix) 
      (l : list (Node * Node * R)) : bool  :=
      match l with
      | [] => true
      | (a, b, _) :: t => (negb (a =n= b)) && 
        elem_path m t
      end.

  



    (* If the path is not elementry, then it has a loop *)
    Lemma elem_path_dup_node : forall (l : list (Node * Node * R)) m,
      elem_path m l = false -> 
      exists (c : Node) (l₁ l₂  l₃ : list (Node * Node * R)), 
      triple_elem_list l (l₁ ++ l₂ ++ l₃) = true /\ 
      cyclic_path c l₂. 
    Proof using Node R eqN eqR refN refR.
      induction l.
      - cbn; intros ? Hw.
        congruence.
      - simpl; intros ? Hw.
        destruct a.
        destruct p.
        apply Bool.andb_false_iff in Hw.
        destruct Hw as [Hw | Hw].
        apply Bool.negb_false_iff in Hw.
        exists n, [], [(n, n0, r)], l.
        simpl. unfold cyclic_path.
        simpl. split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        all:(try (apply refN); try (apply refR)).
        apply triple_elem_eq_list.
        rewrite Hw. apply refN.
        destruct (IHl m Hw) as (c & l₁ & l₂ & l₃ & H₁ & H₂).
        exists c, ([(n, n0, r)] ++ l₁), l₂, l₃.
        simpl. split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        all:(try (apply refN); try (apply refR); assumption).
    Qed.




    (* Here onwards, I am going to use Idempotence and 0-stable *)

    Variable (plus_idempotence : forall a, a + a =r= a = true).
    Variable (zero_stable : forall a : R, 1 + a =r= 1 = true).


    (* From Tim's email: 

        Orel a b := a + b = a (Left Order)
        Orel a b := a + b = b (Right Order)
        Do we need both for this one? 
    *)


    Definition Orel (a b : R) : Prop := a + b =r= a = true.

    (* 
      preccurlyeq Unicode 
      Local Notation "⟨" := Rel : Mat_scope.
    *)

    (* Orel is a partial order *)

    Lemma orel_refl : forall a, Orel a a.
    Proof using R eqR plusR plus_idempotence.
      unfold Orel; intros ?.
      apply plus_idempotence.
    Qed.

    Lemma orel_anti_sym : forall a b, Orel a b -> Orel b a -> a =r= b = true.
    Proof using R congrR eqR plusR plus_commutative refR symR.
      unfold Orel; intros ? ? Hab Hba.
      assert (Ht : a =r= a + b = true).
      apply symR. exact Hab.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      rewrite <-Hba.
      apply congrR.
      apply plus_commutative.
      apply refR.
    Qed.

    Lemma orel_trans : forall a b c, Orel a b -> Orel b c -> Orel a c.
    Proof using R congrP congrR eqR plusR plus_associative refR symR.
      unfold Orel; intros ? ? ? Hab Hbc.
      assert (Ht : a + c =r= a + b + c = true).
      apply congrP. apply symR.
      exact Hab.
      apply refR.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      rewrite <-Hab.
      apply congrR.
      assert (Ht : a + b + c =r= a + (b + c) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP. apply refR.
      apply symR. exact Hbc.
      apply refR.
    Qed.

    (* end of Orel partial order proof *)
      


    Lemma neutral_abouve : forall (a : R), Orel a 0.
    Proof using R eqR plusR zeroR zero_right_identity_plus.
      intro a; unfold Orel.
      apply zero_right_identity_plus.
    Qed.

    Lemma a_b_a : forall a b, Orel (a + b) a.
    Proof using R congrP congrR eqR plusR plus_associative 
    plus_commutative plus_idempotence refR symR.
      unfold Orel; intros ? ?.
      assert (Ht : a + b + a =r= a + a + b = true).
      pose proof (plus_commutative (a + b) a) as Hw.
      rewrite <-Hw; clear Hw.
      apply congrR. apply refR.
      apply symR, plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP. apply symR.
      apply plus_idempotence.
      apply refR.
    Qed.


    Lemma a_b_b : forall a b, Orel (a + b) b.
    Proof using R congrP congrR eqR plusR 
    plus_associative plus_idempotence refR symR.
      unfold Orel; intros ? ?.
      assert (Ht : a + b + b =r= a + (b + b) = true).
      apply symR, plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP. apply refR.
      apply symR.
      rewrite plus_idempotence with (a :=b).
      reflexivity.
    Qed.


    Lemma plus_a_b_c : forall a b c, Orel a b -> Orel (a + c) (b + c).
    Proof using R congrP congrR eqR plusR plus_associative plus_commutative
    plus_idempotence refR symR.
      unfold Orel; intros ? ? ? Ho.
      assert (Ht : a + c + (b + c) =r= 
        a + (c + (b + c)) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR.
      apply refR.
      assert (Ht : a + c =r= a + b + c = true).
      apply congrP. apply symR. exact Ho.
      apply refR. rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      assert (Ht : a + b + c =r= a + b + (c + c) = true).
      apply congrP. apply refR. 
      apply symR. apply plus_idempotence.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR. 
      assert (Ht : a + b + (c + c) =r= a + (b + (c + c)) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP. apply refR.
      assert (Ht : c + (b + c) =r= b + c + c = true).
      apply plus_commutative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply plus_associative.
    Qed.      


    Lemma mul_a_b_c : forall a b c, Orel a b -> Orel (a * c) (b * c).
    Proof using R congrM congrR eqR mulR plusR refR
    right_distributive_mul_over_plus symR.
      unfold Orel; intros ? ? ? Ho.
      assert (Ht : a * c + b * c =r= (a + b) * c = true).
      apply symR.
      apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrM. apply symR.
      exact Ho.
      apply refR.
    Qed.

    (* Strict Order Relation *)
    Definition SOrel (a b : R) := Orel a b /\ 
      a =r= b = false.

    Variable (left_cancellative : forall a b c : R, 
      a =r= 0 = false -> a * b =r= a * c = true ->
      b =r= c = true).

    Variable (right_cancellative : forall a b c : R, 
      a =r= 0 = false -> b * a =r=  c * a = true ->
      b =r= c = true).
    (* This can't be proved with left_cancellative rule. 
      In Carre's paper, multiplication is commutative, 2.1;
      however, we don't have such assumption. *)  
    Lemma smult_a_b_c : forall a b c : R, c =r= 0 = false ->
      SOrel a b -> SOrel (a * c) (b * c).
    Proof using R congrM congrR eqR mulR plusR refR 
    right_cancellative right_distributive_mul_over_plus symR zeroR.
      unfold SOrel, Orel; intros ? ? ? Hc [H₁ H₂].
      split.
      assert (Ht : a * c + b * c =r= (a + b) * c = true).
      apply symR. apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR.
      apply refR.
      apply congrM.
      apply symR. exact H₁.
      apply refR.
      pose proof (right_cancellative c a b Hc) as Hl.
      destruct (a * c =r= b * c) eqn:Ht.
      specialize (Hl eq_refl).
      rewrite Hl in H₂.
      congruence.
      reflexivity.
    Qed.

    (* end of strict order proof *)

    Lemma path_weight_rel : forall a b c : R, 
      Orel (a * c) (a * b * c).
    Proof using R congrM congrP congrR eqR left_distributive_mul_over_plus mulR
    mul_associative oneR one_left_identity_mul plusR refR
    right_distributive_mul_over_plus symR zero_stable.
      unfold Orel; intros ? ? ?.
      assert (Ht : a * c + a * b * c =r= 
        a * c + a * (b * c) = true).
      apply congrP. apply refR.
      apply symR. apply mul_associative.
      rewrite <-Ht; clear Ht. apply congrR.
      apply refR.
      apply symR.
      assert (Ht : a * c + a * (b * c) =r= 
        a * (c + b * c) = true).
      apply symR.
      apply left_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR. apply congrM.
      apply refR.
      assert (Ht : (1 * c + b * c) =r= 
        (1 + b) * c = true).
      apply symR.
      apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      (* Now, I need 0-stable  *)
      apply symR.
      assert (Ht : (1 + b) * c =r= 
        1 * c = true).
      apply congrM. 
      apply zero_stable.
      apply refR.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      apply one_left_identity_mul.
    Qed.


    Lemma matrix_fixpoint : forall (n : nat) (m : Matrix) c d , 
      matrix_exp_unary m (List.length finN) c d =r= 
      matrix_exp_unary m (n + List.length finN) c d = true.
    Proof.
    Admitted.


    Fixpoint atmost_kpath (m : Matrix) (k : nat) (c d : Node) :=
      match k with 
      | 0%nat => if c =n= d then [[[(c, d, 1)]]] else []
      | S k' => (all_paths_klength m k c d) ::
         atmost_kpath m k' c d
      end.
    
      (* q-stable: 
        qth partial sum := x^0 + x^1 .....+ x^q
        q-stable := qth partial sum = (q + 1)th partial sum

        Matrices are v-1 stable. 

        If semi ring is idempotence and there are 1's along 
        the diagonal, 
        qth partial sum = x^q.
      *)

    Fixpoint exp_r (a : R) (n : nat) : R :=
      match n with 
      | O => 1
      | S n' => a * exp_r a n'
      end.


    Lemma exp_r_pow_add : forall (n m : nat) (a : R), 
      exp_r a (n + m) =r= exp_r a n * exp_r a m = true.
    Proof.
      induction n.
      - simpl; intros ? ?.
        apply symR. 
        apply one_left_identity_mul.
      - simpl; intros ? ?.
        apply symR.
        assert (Ht : (a * exp_r a n * exp_r a m =r= a * exp_r a (n + m)) =
          (a * (exp_r a n * exp_r a m) =r= a * exp_r a (n + m))).
        apply congrR. 
        apply symR.
        apply mul_associative.
        apply refR.
        rewrite Ht; clear Ht.
        apply congrM.
        apply refR.
        apply symR.
        apply IHn.
    Qed.




    Fixpoint partial_sum_r (a : R) (n : nat) : R :=
      match n with
      | O => 1
      | S n' => (partial_sum_r a n') + exp_r a n
      end.


    (* q-stable. 0-stable is special case when q = 0 *)
    Variable (q : nat)
      (q_stable : forall (a : R), 
      partial_sum_r a q =r= partial_sum_r a (S q) = true).


    
    Lemma astar_exists : forall (t : nat) (a : R), 
      partial_sum_r a (t + q) =r= partial_sum_r a q = true.
    Proof.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl. simpl in q_stable; intros ?.
        apply symR.
        rewrite <-(q_stable a).
        apply congrR. apply refR.
        apply congrP. apply IHt.
    Admitted.

       
        
        
  
    


    Fixpoint partial_sum (m : Matrix) (n : nat) : Matrix :=
      match n with
      | O => I 
      | S n' => matrix_add (partial_sum m n') (matrix_exp_unary m n)
      end.
    
    

    
    



     
    

    


   



      


      
  
      

       
    



    

    (* 
    Fixpoint atmost_kpath (m : Matrix) (k : nat) (c d : Node) :=
      match k with 
      | 0%nat => []
      | S k' => (kpath m (S k') c d) ::
         atmost_kpath m k' c d
      end.
    



    Lemma matrix_path_forward : forall n s m c d, 
      matrix_exp_unary m n c d =r= s = true -> 
      exists (p : Path), 
      fp p =n= c = true /\ 
      sp p =n= d = true /\ 
      (List.length (tp p) = n)%nat /\
      well_formed_path p = true /\ 
      measure_of_path (tp p) =r= s = true.
    Proof.
      induction n.
      + admit.
      + simpl; intros.
      unfold matrix_mul, 
          matrix_mul_gen in H.



      + simpl; intros ? ? ? ? Hm.
        exists []. split.
        - reflexivity.
        - exact Hm.
      + simpl; intros ? ? ? ? Hm.
        unfold matrix_mul, 
          matrix_mul_gen in Hm.
        (* destruct n = 1 or inductive case  *)
      
        
        
        (* I need some concrete property about + and * *)
        (* I have not assumed idempotence yet. Would it help? *)

        (* what can we infer from Hm? 
          Assume there is intermediate node x 
          from which the strenght is s to node d.
        *)
    Admitted.

    Lemma matrix_path_reverse : forall n s m c d (l : list (Node * Node * R)),
      (List.length l = n)%nat -> measure_of_path c l d = s -> 
      matrix_exp_unary m n c d = s.
    Proof.
      induction n.
      + intros ? ? ? ? ? Hl Hm.
        assert (Ht : l = []).
        destruct l. reflexivity.
        simpl in Hl. lia.
        rewrite Ht in Hm.
        simpl in * |- *.
        unfold I. exact Hm.
      + intros ? ? ? ? ? Hl Hm.
        simpl.

    Admitted.

    (* Equation 3.5 from Carre *)
    Lemma strenght_path_split_list : forall (c d : Node) 
      (l₁ l₂ : list (Node * Node * R)) (a b : Node) (w s : R) ,
      measure_of_path c (l₁ ++ (a, b, w) :: l₂) d =r= s = true <->
      (measure_of_path c l₁ a) * w * 
      (measure_of_path b l₂ d) =r= s = true.
    Proof.
    Admitted.
      
     
    Lemma matrix_fixpoint : forall (n : nat) (m : Matrix) c d , 
      matrix_exp_unary m (List.length finN) c d =r= 
      matrix_exp_unary m (n + List.length finN) c d = true.
    Proof.
      (* Proof idea: 
        Left hand side gives us a list of strenght s, say, of 
        length (List.length finN).
        We show that the right hand side also gives us a 
        longer list, containing loop of length  
        (n + List.length finN), whose strenght is s. 
      
      *)


    Admitted.




    (* Y := A * Y + B : Distributed Bellman ford *)
    Fixpoint mul_left (a y b : Matrix) (k : nat) : Matrix :=
      match k with
      | 0%nat => matrix_add (matrix_mul a y) b 
      | S k' => matrix_add (matrix_mul a (mul_left a y b k')) b
      end.
    
    
    (* Y := Y * A + B : Dijkstra *)
    (* I need a function to multiply vector by matrix *)
    (* Y : Node -> R, A : Matrix, B : Node -> R *)  



    
    (* Functions below are same as above, except they avoids idenity matrix *)

    Fixpoint matrix_exp_unary_pone (m : Matrix) (n : nat) : Matrix :=
      match n with 
      | 0%nat => m
      | S n' => matrix_mul m (matrix_exp_unary_pone m n')
      end.


    Definition matrix_exp_binary_pone (e : Matrix) (n : N) :=
      match n with
      | N0 => e
      | Npos p => matrix_mul e (repeat_op_ntimes_rec e p)
      end.

    Lemma connection_unary_pone : forall (n : nat) (m : Matrix)  (c d : Node),
      mat_cong m ->  
      matrix_exp_unary_pone m n c d =r= 
      matrix_mul m (matrix_exp_unary m n) c d = true.
    Proof.
      induction n.
      - simpl; intros ? ? ? Hm.
        apply symR.
        apply matrix_mul_right_identity.
        exact Hm.
      - simpl; intros ? ? ? Hm.
        apply mat_mul_cong_diff.
        unfold two_mat_congr; intros u v.
        apply IHn. exact Hm.
    Qed.
    
    Lemma connection_binary_pone : forall (n : N) (m : Matrix)  (c d : Node),
      mat_cong m ->  
      matrix_exp_binary_pone m n c d =r= 
      matrix_mul m (matrix_exp_binary m n) c d = true.
    Proof.
      destruct n.
      - simpl; intros ? ? ? H.
        apply symR.
        apply matrix_mul_right_identity.
        exact H.
      - simpl; intros ? ? ? H.
        apply refR.
    Qed.


    Lemma matrix_exp_unary_binary_eqv_pone : forall (n : N) (m : Matrix) c d,
      mat_cong m -> 
      matrix_exp_unary_pone m (N.to_nat n) c d =r= matrix_exp_binary_pone m n c d 
      = true.
    Proof.
      intros ? ? ? ? Hm.
      pose proof connection_unary_pone (N.to_nat n) m c d Hm as Ht.
      rewrite <-Ht; clear Ht.
      apply congrR.
      apply refR.
      pose proof connection_binary_pone n m c d Hm as Ht.
      rewrite <-Ht; clear Ht.
      apply congrR.
      apply refR.
      apply mat_mul_cong_diff.
      unfold two_mat_congr; intros u v.
      apply matrix_exp_unary_binary_eqv.
      exact Hm.
    Qed.

    Fixpoint measure_of_path_pone (c : Node) (l : list R)  (d : Node) 
      (m : Matrix) : R :=
      match l with 
      | [] => m c d
      | v :: t => v * measure_of_path c t d m
      end. *)
    (* end of functions and proofs that avoids Identity *)

    
      
    

    (* Now, let's focus on proving fixpoint *)
    (* Now, I want to prove that if I exponentiate |finN| - 1 I will 
      reach fixpoint *)
    (* I need 0-stable assumption *)


    (* Interesting, Carre paper assumes multiplication is commutative *)
    (* under what circumstances, matrix_exp_unary m n c d =r= 
      matrix_exp_unary m (n+1) c d ? *)
    (* Law of Idempotency a + a =r= a 

       Law of cancellation: forall a : R, 
       eqR a 0 = false -> a * b =r= a * c => b = c. 

       Order Relation: R a b := a + b =r= a

       Lemma Rzero : forall a, R a 0. 
       Proof by definition. 

       Lemma Rab : forall a b, R (a + b) a. 
       Proof. unfold R. 
        (a + b) + a =r= (a + b)
        LHS: (a + b) + a 
          =r= a + (a + b) by commutative
          =r= (a + a) + b by associativity
          =r= a + b by  idempotence.
          
    *)



End Matrix.

Require Import Psatz Utf8 ZArith.
Section Ins.

  Inductive node := A | B | C | D.

  Definition fin_node := [A; B; C; D].

  Lemma Hfin : forall x : node, In x fin_node.
  Proof.
    destruct x; unfold fin_node;
    simpl; auto.
  Qed.

  Definition Hdec : forall c d : node, {c = d} + {c <> d}.
  Proof.
    destruct c; destruct d; firstorder.
    all: right; intro; inversion H.
  Defined.
    

  Definition m (c d : node) := 
    match c, d with 
    | A, A => 1%Z
    | A, B => 0%Z 
    | A, C => 0%Z
    | A, D => 0%Z 
    | B, A => 0%Z 
    | B, B => 1%Z
    | B, C => 0%Z
    | B, D => 0%Z
    | C, A => 0%Z
    | C, B => 0%Z 
    | C, C => 1%Z
    | C, D => 0%Z 
    | D, A => 0%Z
    | D, B => 0%Z 
    | D, C => 0%Z
    | D, D => 1%Z 
    end.

  Definition eqN (c d : node) : bool :=
    match c, d with 
    | A, A => true
    | B, B => true 
    | C, C => true
    | D, D => true
    | _, _ => false
    end.


  Eval vm_compute in (all_paths_klength node fin_node eqN Z 2%Z m 3 A D).
  
End Ins. 


          














    
    




