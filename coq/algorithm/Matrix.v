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

  Lemma list_eqv_trans : forall l₁ l₂ l₃ : list A, 
    list_eqv l₁ l₂ = true -> list_eqv l₂ l₃ = true ->
    list_eqv l₁ l₃ = true.
  Proof.
    induction l₁ as [|a l₁];
    destruct l₂ as [|b l₂];
    destruct l₃ as [|c l₃];
    intros Ha Hb; simpl in Ha, 
    Hb; try congruence; try reflexivity.
    simpl.
    apply Bool.andb_true_iff in Ha, Hb.
    apply Bool.andb_true_iff; split.
    apply trnA with b; firstorder.
    eapply IHl₁ with l₂; firstorder.
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
      

  Lemma list_split_gen : forall (l : list A) (c : A),
    in_list eqA l c = true -> 
    exists l₁ l₂ : list A, 
    list_eqv l (l₁ ++ [c] ++ l₂) = true.
  Proof.
    induction l; simpl.
    + intros ? H₁.
      congruence.
    + intros c H₁.
      apply Bool.orb_true_iff in H₁.
      destruct H₁ as [H₁ | H₁].
      exists [], l.
      simpl.
      apply Bool.andb_true_iff.
      split. apply symA; assumption.
      apply list_eqv_refl.
      destruct (IHl c H₁) as [l₁ [l₂ Hl]].
      exists (a :: l₁), l₂.
      simpl.
      apply Bool.andb_true_iff; split.
      apply refA. exact Hl.
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
    

    (* triple_elem_list is equivalence relation *)
    Lemma triple_elem_eq_list_refl : forall l, 
      triple_elem_list l l = true.
    Proof using Node R eqN eqR refN refR.
      induction l.
      - simpl. reflexivity.
      - simpl. destruct a.
        destruct p.
        repeat (apply Bool.andb_true_iff; split;
          try (apply refN); try (apply IHl)).
        apply refR.
    Qed.

    Lemma triple_elem_eq_list_sym : forall xs ys, 
      triple_elem_list xs ys = true -> 
      triple_elem_list ys xs = true.
    Proof.
      induction xs.
      + intros * Ht.
        destruct ys.
        reflexivity.
        simpl in Ht.
        congruence.
      + intros * Ht.
        destruct ys.
        simpl in Ht.
        destruct a as ((u, v), w).
        congruence.
        destruct a as ((au, av), aw).
        destruct p as ((pu, pv), pw).
        simpl in * |- *.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply symN; assumption.
        apply symN; assumption.
        apply symR; assumption.
        apply IHxs; assumption.
    Qed.


    Lemma triple_elem_eq_list_trans : forall xs ys zs, 
      triple_elem_list xs ys = true -> 
      triple_elem_list ys zs = true ->
      triple_elem_list xs zs = true.
    Proof.
      induction xs.
      + intros * Hy Hz.
        destruct ys; 
        destruct zs;
        simpl in * |- *;
        try reflexivity; 
        try congruence.
      + intros * Hy Hz.
        destruct ys; 
        destruct zs;
        simpl in * |- *;
        destruct a as ((au, av), aw);
        try congruence.
        destruct p as ((pu, pv), pw);
        try congruence.
        destruct p as ((pu, pv), pw).
        destruct p0 as ((put, pvt), pwt).
        apply Bool.andb_true_iff in Hy.
        destruct Hy as [Hy Hyr].
        apply Bool.andb_true_iff in Hy.
        destruct Hy as [Hy Hyrr].
        apply Bool.andb_true_iff in Hy.
        destruct Hy as [Hy Hyrrr].
        apply Bool.andb_true_iff in Hz.
        destruct Hz as [Hz Hzr].
        apply Bool.andb_true_iff in Hz.
        destruct Hz as [Hz Hzrr].
        apply Bool.andb_true_iff in Hz.
        destruct Hz as [Hz Hzrrr].
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply trnN with pu; assumption.
        apply trnN with pv; assumption.
        apply trnR with pw; assumption.
        apply IHxs with ys; assumption.
    Qed.
        
     (* end of triple_elem_list equivalence relation *)



    Lemma length_rewrite : forall xs ys,
        triple_elem_list xs ys = true ->
        List.length xs = List.length ys.
    Proof.
      induction xs.
      + intros * Hin.
        destruct ys.
        reflexivity.
        simpl in Hin.
        congruence.
      + intros * Hin.
        destruct ys.
        simpl in Hin.
        destruct a as ((u, v), w).
        congruence.
        simpl in * |- *.
        destruct a as ((au, av), aw).
        destruct p as ((pu, pv), pw).
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [_ Hin].
        apply f_equal.
        apply IHxs; assumption.
    Qed.




    

    (* This function tests if l₁ in l₂ or not *)
    Fixpoint In_eq_bool (l₁ : list (Node * Node * R))
      (l₂ : list (list (Node * Node * R))) : bool :=
      match l₂ with
      | [] => false
      | h :: t => ((triple_elem_list l₁ h) || (In_eq_bool l₁ t))%bool 
      end.

    
    Lemma path_tl_rewrite : forall lss xs ys, 
      triple_elem_list xs ys = true ->
      In_eq_bool xs lss = true -> In_eq_bool ys lss = true.
    Proof.
      induction lss.
      + intros * Ht Hin.
        simpl in Hin.
        congruence.
      + intros * Ht Hin.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        simpl.
        apply Bool.orb_true_iff.
        left.
        apply triple_elem_eq_list_trans with xs.
        apply triple_elem_eq_list_sym; assumption.
        exact Hin.
        simpl. apply Bool.orb_true_iff. 
        right.
        apply IHlss with xs; assumption.
    Qed.
    

    
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
        left. apply triple_elem_eq_list_refl.
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



    





    (* Here onwards, I am going to use Idempotence *)

    Variable (plus_idempotence : forall a, a + a =r= a = true).
    

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

    Section StrictOrder.
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

    End StrictOrder.

    (* end of strict order proof *)


    (* Matrix addition is idempotence: Section 2.2 of Carre
    (i) Generalize Matrix Addition *)
    Lemma matrix_add_idempotence : forall m c d, 
      matrix_add m m c d =r= m c d = true.
    Proof using Node R eqR plusR plus_idempotence.
      unfold matrix_add; intros *.
      apply plus_idempotence.
    Qed.



    Lemma path_weight_rel : forall a b c : R, 
      (forall a : R, 1 + a =r= 1 = true) ->
      Orel (a * c) (a * b * c).
    Proof using R congrM congrP congrR eqR left_distributive_mul_over_plus mulR
    mul_associative oneR one_left_identity_mul plusR refR
    right_distributive_mul_over_plus symR.
      unfold Orel; intros ? ? ? zero_stable.
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
  

    Lemma exp_r_pow_add : forall (n m : nat) (a : R), 
      exp_r a (n + m) =r= exp_r a n * exp_r a m = true.
    Proof using R congrM congrR eqR mulR mul_associative oneR
    one_left_identity_mul refR symR.
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

  

        
    Lemma astar_aide_zero_stable : forall (t : nat) (a : R),
      (forall a : R, 1 + a =r= 1 = true) ->
      partial_sum_r a t + a * exp_r a t =r=
      partial_sum_r a t = true.
    Proof using R congrM congrP congrR eqR mulR oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative refR
    right_distributive_mul_over_plus symR.
      induction t.
      - simpl; intros ? zero_stable.
        rewrite <-(zero_stable a).
        apply congrR.
        apply congrP.
        apply refR.
        apply one_right_identity_mul.
        apply refR.
      - simpl; intros ? zero_stable.
      assert (Ht:
      (partial_sum_r a t + a * exp_r a t + a * (a * exp_r a t) =r=
      partial_sum_r a t + a * exp_r a t) =
      (partial_sum_r a t + (a * exp_r a t + a * (a * exp_r a t)) =r=
      partial_sum_r a t + a * exp_r a t)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Ht; clear Ht.
      apply congrP.
      apply refR.
      remember (a * exp_r a t) as aw.
      assert (Ht : (aw + a * aw =r= aw) =
        (1 * aw + a * aw =r= aw)).
      apply congrR.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      apply refR.
      rewrite Ht; clear Ht.
      assert (Ht : (1 * aw + a * aw =r= aw) =
        ((1 + a) * aw =r= aw)).
      apply congrR.
      apply symR.
      apply right_distributive_mul_over_plus.
      apply refR.
      rewrite Ht; clear Ht.
      assert (Ht : ((1 + a) * aw =r= aw) = 
        (((1 + a) * aw =r= 1 * aw))).
      apply congrR.
      apply refR.
      apply symR.
      apply one_left_identity_mul.
      rewrite Ht; clear Ht.
      apply congrM.
      apply zero_stable.
      apply refR.
    Qed.



    (* special case q := 0 *)
    Lemma astar_exists_zero_stable : forall (t : nat) (a : R),
      (forall a : R, 1 + a =r= 1 = true) -> 
      partial_sum_r a t =r= partial_sum_r a 0 = true.
    Proof using R congrM congrP congrR eqR mulR oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative refR
    right_distributive_mul_over_plus symR.
      induction t.
      - simpl; intros ? zero_stable.
        apply refR.
      - simpl; intros ? zero_stable.
        rewrite <-(astar_aide_zero_stable t a).
        apply congrR.
        apply refR.
        simpl in IHt.
        apply symR.
        exact (IHt a zero_stable).
        apply zero_stable.
    Qed.




    Lemma astar_aide_gen_q_stable :
      forall (t : nat) (a : R),
      (partial_sum_r a (S t)) =r= 
      (1 + a * partial_sum_r a t) = true.
    Proof using R congrP congrR eqR
    left_distributive_mul_over_plus mulR oneR plusR
    plus_associative refR symR.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        simpl in IHt.
        assert (Ht : 1 + a * (partial_sum_r a t + a * exp_r a t) =r=
          (1 + (a * partial_sum_r a t + a * (a * exp_r a t))) = true).
        apply congrP. apply refR.
        apply left_distributive_mul_over_plus.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        assert (Ht : partial_sum_r a t + a * exp_r a t + a * (a * exp_r a t) =r=
          1 + a * partial_sum_r a t + a * (a * exp_r a t) = true).
        apply congrP.
        apply IHt. apply refR.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        assert (Ht : 1 + a * partial_sum_r a t + a * (a * exp_r a t) =r= 
          1 +  (a * partial_sum_r a t + a * (a * exp_r a t)) = true).
        apply symR. apply plus_associative.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply refR.
    Qed.
        

    
    Lemma astar_exists_gen_q_stable : forall (q : nat),
      (forall w : R, partial_sum_r w q =r= partial_sum_r w (S q) = true) -> 
      forall (t : nat) (a : R), 
      partial_sum_r a (t + q) =r= partial_sum_r a q = true.
    Proof using R congrM congrP congrR eqR
    left_distributive_mul_over_plus mulR oneR plusR
    plus_associative refR symR.
      intros ? q_stable.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        pose proof (astar_aide_gen_q_stable (t + q) a) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        assert (Ht : 1 + a * partial_sum_r a (t + q) =r= 
          1 + a * partial_sum_r a q = true).
        apply congrP. apply refR. 
        apply congrM. apply refR.
        apply IHt.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        pose proof (astar_aide_gen_q_stable q a) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply q_stable.
        apply refR.
    Qed.
    
    (* Print Grammar constr. *)
    Local Infix "+M" := matrix_add (at level 50) : Mat_scope.
    Local Infix "*M" := matrix_mul (at level 40) : Mat_scope.

    Fixpoint partial_sum_mat (m : Matrix) (n : nat) : Matrix :=
      match n with
      | O => I 
      | S n' => (partial_sum_mat m n') +M (matrix_exp_unary m n)
      end.

    Lemma mat_add_cong_gen : forall m₁ m₂ m₃ m₄ c d, 
      two_mat_congr m₁ m₃ -> two_mat_congr m₂ m₄ -> 
      matrix_add m₁ m₂ c d =r= matrix_add m₃ m₄ c d = true.
    Proof using Node R congrP eqR plusR.
      intros * H₁ H₂.
      unfold matrix_add.
      apply congrP.
      apply H₁; intros *;
      apply refN.
      apply H₂; intros *;
      apply refN.
    Qed.

    Lemma sum_fn_mul_distribute_over_plus_left : 
      forall (l : list Node) (m₁ m₂ m₃ : Matrix) (c d : Node),
      (sum_fn (λ y : Node, m₁ c y * (m₂ y d + m₃ y d)) l =r=
      sum_fn (λ y : Node, m₁ c y * m₂ y d) l +
      sum_fn (λ y : Node, m₁ c y * m₃ y d) l) = true.
    Proof using Node R congrP congrR eqR left_distributive_mul_over_plus mulR
    plusR plus_associative plus_commutative refR symR zeroR
    zero_left_identity_plus.
      induction l.
      - simpl. intros ? ? ? ? ?.
        apply symR, zero_left_identity_plus.
      - simpl; intros ? ? ? ? ?.
        pose proof (IHl m₁ m₂ m₃ c d) as IHt.
        remember (sum_fn (λ y : Node, m₁ c y * (m₂ y d + m₃ y d)) l) as sfn₁.
        remember (sum_fn (λ y : Node, m₁ c y * m₂ y d) l) as sfn₂.
        remember (sum_fn (λ y : Node, m₁ c y * m₃ y d) l) as sfn₃.
        assert (Ht : (m₁ c a * (m₂ a d + m₃ a d) + sfn₁ =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        ((m₁ c a * m₂ a d + m₁ c a * m₃ a d) + (sfn₂ + sfn₃) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃))).
        apply congrR.
        apply congrP.
        apply left_distributive_mul_over_plus.
        apply IHt.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        (m₁ c a * m₂ a d + m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃))).
        apply congrR.
        apply symR. apply plus_associative.
        apply refR. 
        rewrite Ht; clear Ht.
        assert (Ht : 
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r=
        m₁ c a * m₂ a d + sfn₂ + (m₁ c a * m₃ a d + sfn₃)) =
        (m₁ c a * m₂ a d + (m₁ c a * m₃ a d + (sfn₂ + sfn₃)) =r=
        m₁ c a * m₂ a d + (sfn₂ + (m₁ c a * m₃ a d + sfn₃)))).
        apply congrR.
        apply refR.
        apply symR.
        apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        assert (Ht : 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= sfn₂ + (m₁ c a * m₃ a d + sfn₃)) = 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= (m₁ c a * m₃ a d + sfn₃) + sfn₂)).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= m₁ c a * m₃ a d + sfn₃ + sfn₂) =
        (m₁ c a * m₃ a d + (sfn₂ + sfn₃) =r= m₁ c a * m₃ a d + (sfn₃ + sfn₂))).
        apply congrR. apply refR.
        apply symR. apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        apply plus_commutative.
    Qed.

        

    Lemma left_distributive_mat_mul_over_plus : 
      forall (m₁ m₂ m₃ : Matrix) (c d : Node), 
      (m₁ *M (m₂ +M m₃)) c d =r= 
      (m₁ *M m₂ +M m₁ *M m₃) c d = true.
    Proof using Node R congrP congrR eqR finN left_distributive_mul_over_plus
    mulR plusR plus_associative plus_commutative refR symR zeroR
    zero_left_identity_plus.
      intros *.
      unfold matrix_mul, matrix_mul_gen,
      matrix_add.
      apply sum_fn_mul_distribute_over_plus_left.
    Qed.
      



    Lemma astar_aide_gen_q_stable_matrix :
      forall (t : nat) (m : Matrix) (c d : Node),
      (partial_sum_mat m (S t) c d) =r= 
      (I +M m *M partial_sum_mat m t) c d = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR
    finN left_distributive_mul_over_plus memN
    mulR mul_associative oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR
    right_distributive_mul_over_plus symN
    symR trnN trnR zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_anhilator_mul
    zero_right_identity_plus.
      induction t.
      - simpl; intros ? ? ?.
        apply refR.
      - simpl; intros ? ? ?.
        remember (partial_sum_mat m t) as pmt.
        remember (matrix_exp_unary m t) as umt.
        assert (Ht : ((pmt +M m *M umt) +M m *M (m *M umt)) c d =r=
          ((I +M m *M pmt) +M m *M (m *M umt)) c d = true).
        apply mat_add_cong_gen.
        unfold two_mat_congr;
        intros u v. 
        simpl in IHt.
        pose proof (IHt m u v) as IHs.
        rewrite <-Heqpmt in IHs.
        rewrite <-Hequmt in IHs.
        exact IHs.
        unfold two_mat_congr; intros a b.
        apply refR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply symR.
        assert (Ht : ((I +M m *M pmt) +M m *M (m *M umt)) c d =r= 
          (I +M (m *M pmt +M m *M (m *M umt))) c d = true).
        apply symR.
        apply matrix_add_assoc.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply symR.
        apply mat_add_cong_gen.
        unfold two_mat_congr; intros a b.
        apply refR.
        unfold two_mat_congr; intros a b.
        apply symR.
        apply left_distributive_mat_mul_over_plus.
    Qed.



    Lemma astar_exists_gen_q_stable_matrix : 
      forall (q : nat) (m : Matrix),
      (forall (c d : Node), 
        partial_sum_mat m q c d =r= partial_sum_mat m (S q) c d = true) -> 
      forall (t : nat)  (u v : Node), 
      partial_sum_mat m (t + q) u v  =r= partial_sum_mat m q u v = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR right_distributive_mul_over_plus
    symN symR trnN trnR zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros * q_stable.
      induction t.
      - simpl; intros *.
        apply refR.
      - simpl; intros *.
        pose proof (astar_aide_gen_q_stable_matrix (t + q) m u v) as IHs.
        simpl in IHs.
        rewrite <-IHs; clear IHs.
        apply congrR.
        apply refR.
        pose proof (astar_aide_gen_q_stable_matrix q m u v) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply q_stable.
        apply mat_add_cong_gen.
        unfold two_mat_congr; intros a b.
        apply refR.
        unfold two_mat_congr; intros a b.
        apply mat_mul_cong_diff.
        unfold two_mat_congr; intros ut vt.
        specialize (IHt ut vt).
        exact IHt.
    Qed.


    Lemma sum_fn_mul_distribute_over_plus_right : 
      forall (l : list Node) (m₁ m₂ m₃ : Matrix) (c d : Node),
      (sum_fn (λ y : Node, (m₂ c y + m₃ c y) * m₁ y d) l =r=
      sum_fn (λ y : Node, m₂ c y * m₁ y d) l +
      sum_fn (λ y : Node, m₃ c y * m₁ y d) l) = true.
    Proof using Node R congrP congrR eqR mulR plusR plus_associative
    plus_commutative refR right_distributive_mul_over_plus symR zeroR
    zero_left_identity_plus.
      induction l.
      - simpl. intros ? ? ? ? ?.
        apply symR, zero_left_identity_plus.
      - simpl; intros ? ? ? ? ?.
        pose proof (IHl m₁ m₂ m₃ c d) as IHt.
        remember (sum_fn (λ y : Node, (m₂ c y + m₃ c y) * m₁ y d) l) as sfn₁.
        remember (sum_fn (λ y : Node, m₂ c y * m₁ y d) l) as sfn₂.
        remember (sum_fn (λ y : Node, m₃ c y * m₁ y d) l) as sfn₃.
        assert (Ht: 
        ((m₂ c a + m₃ c a) * m₁ a d + sfn₁ =r=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃)) =
        ((m₂ c a * m₁ a d + m₃ c a * m₁ a d) + (sfn₂ + sfn₃) =r=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃))).
        apply congrR.
        apply congrP.
        apply right_distributive_mul_over_plus.
        exact IHt.
        apply refR.
        rewrite Ht; clear Ht.
        assert(Ht: 
        (m₂ c a * m₁ a d + m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r=
        m₂ c a * m₁ a d + sfn₂ + (m₃ c a * m₁ a d + sfn₃)) =
        (m₂ c a * m₁ a d + (m₃ c a * m₁ a d + (sfn₂ + sfn₃)) =r=
        m₂ c a * m₁ a d + (sfn₂ + (m₃ c a * m₁ a d + sfn₃)))).
        apply congrR.
        apply symR. apply plus_associative.
        apply symR. apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        assert (Ht : 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= sfn₂ + (m₃ c a * m₁ a d + sfn₃)) = 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= (m₃ c a * m₁ a d + sfn₃) + sfn₂)).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= m₃ c a * m₁ a d + sfn₃ + sfn₂) =
        (m₃ c a * m₁ a d + (sfn₂ + sfn₃) =r= m₃ c a * m₁ a d + (sfn₃ + sfn₂))).
        apply congrR. apply refR.
        apply symR. apply plus_associative.
        rewrite Ht; clear Ht.
        apply congrP.
        apply refR.
        apply plus_commutative.
    Qed.




    Lemma right_distributive_mat_mul_over_plus : 
      forall (m₁ m₂ m₃ : Matrix) (c d : Node), 
      ((m₂ +M m₃) *M m₁) c d =r= 
      (m₂ *M m₁ +M m₃ *M m₁) c d = true.
    Proof using Node R congrP congrR eqR finN mulR plusR plus_associative
    plus_commutative refR right_distributive_mul_over_plus symR zeroR
    zero_left_identity_plus.
      intros *.
      unfold matrix_mul, matrix_mul_gen,
      matrix_add.
      apply sum_fn_mul_distribute_over_plus_right.
    Qed.



    Lemma partial_sum_mat_cong : forall n m,
      mat_cong m ->  
      mat_cong (partial_sum_mat m n).
    Proof using Node R congrM congrP eqN eqR finN 
    mulR oneR plusR refN refR symN trnN zeroR.
      unfold mat_cong.
      induction n.
      - simpl; intros ? ? ? ? ? Hm Hac Hbd.
        apply identity_cong; assumption.
      - simpl; intros ? ? ? ? ? HM Hac Hbd.
        remember (partial_sum_mat m n) as pmn.
        remember (matrix_exp_unary m n) as men.
        unfold matrix_add, matrix_mul, 
        matrix_mul_gen.
        apply congrP.
        rewrite Heqpmn.
        apply IHn; assumption.
        apply sum_fn_mul_congr.
        assumption.
        assumption.
        assumption.
        unfold mat_cong.
        intros au av bu bv Hab Hcd.
        rewrite Heqmen.
        apply mat_exp_cong; assumption.
    Qed.

    
    Lemma mat_mul_idem_ind : forall n m c d,  
      (m *M partial_sum_mat m n +M partial_sum_mat m n) c d =r=
      (partial_sum_mat m (S n) c d) = true.
    Proof using Node R congrP congrR eqN eqR finN left_distributive_mul_over_plus
    mulR oneR plusR plus_associative plus_commutative plus_idempotence refR symR
    zeroR zero_left_identity_plus.
      induction n.
      - simpl; intros ? ? ?.
        apply matrix_add_comm.
      - simpl; intros ? ? ?.
        pose proof (IHn m c d) as IHs.
        simpl in IHs.
        remember (partial_sum_mat m n) as m₁.
        remember (matrix_exp_unary m n) as m₂.
        assert (Ht :
        ((m *M (m₁ +M m *M m₂) +M (m₁ +M m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) =
        (((m *M m₁ +M m *M (m *M m₂)) +M (m₁ +M m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        apply left_distributive_mat_mul_over_plus.
        apply refR.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht:
        (((m *M m₁ +M m *M (m *M m₂)) +M (m₁ +M m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) = 
        (((m *M m₁ +M m *M (m *M m₂)) +M (m *M m₁ +M m₁)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        apply congrP.
        apply refR.
        apply refR.
        apply symR.
        apply IHs.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht :
        (((m *M m₁ +M m *M (m *M m₂)) +M (m *M m₁ +M m₁)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) =
        (((m *M m₁ +M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply matrix_add_comm.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht:
        (((m *M m₁ +M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) = 
        (((m₁ +M m *M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        apply matrix_add_comm.
        apply refR.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht: 
        (((m₁ +M m *M m₁) +M (m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) = 
        (((m₁ +M m *M m₁ +M m *M m₁ +M m *M (m *M m₂))) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply matrix_add_assoc.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht:
        ((((m₁ +M m *M m₁) +M m *M m₁) +M m *M (m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d) =
        (((m₁ +M m *M m₁) +M m *M (m *M m₂)) c d =r=
        ((m₁ +M m *M m₂) +M m *M (m *M m₂)) c d)).
        apply congrR.
        apply congrP.
        assert (Htv: 
        (((m₁ +M m *M m₁) +M m *M m₁) c d =r= (m₁ +M m *M m₁) c d) =
        ((m₁ +M (m *M m₁ +M m *M m₁)) c d =r= (m₁ +M m *M m₁) c d)).
        apply congrR.
        apply symR. 
        apply matrix_add_assoc.
        apply symR.
        apply refR.
        rewrite Htv; clear Htv.
        apply congrP.
        apply refR.
        apply plus_idempotence.
        apply refR.
        apply refR.
        rewrite Ht; clear Ht.
        apply congrP.
        rewrite <-IHs.
        apply congrR.
        apply matrix_add_comm.
        apply refR.
        apply refR.
    Qed.

      
    
    Lemma matrix_pow_idempotence :
      forall (n : nat) (m : Matrix) (c d : Node),
      mat_cong m ->
      matrix_exp_unary (m +M I) n c d =r= 
      partial_sum_mat m n c d = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN
    left_distributive_mul_over_plus memN mulR oneR one_left_identity_mul plusR
    plus_associative plus_commutative plus_idempotence refN refR
    right_distributive_mul_over_plus symN symR trnN zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_identity_plus.
      induction n.
      - simpl; intros ? ? ? Hm.
        apply refR.
      - simpl; intros ? ? ? Hm.
        pose proof (IHn m c d) as IHs.
        assert (Ht : 
        (((m +M I) *M matrix_exp_unary (m +M I) n) c d =r=
        (partial_sum_mat m n +M m *M matrix_exp_unary m n) c d) =
        (((m +M I) *M partial_sum_mat m n) c d =r=
        (partial_sum_mat m n +M m *M matrix_exp_unary m n) c d)).
        apply congrR.
        apply mat_mul_cong_diff.
        unfold two_mat_congr; intros u v.
        exact (IHn m u v Hm).
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        (((m +M I) *M partial_sum_mat m n) c d =r=
        (partial_sum_mat m n +M m *M matrix_exp_unary m n) c d) =
        (((m *M partial_sum_mat m n +M I *M partial_sum_mat m n) c d =r=
        (partial_sum_mat m n +M m *M matrix_exp_unary m n) c d))).
        apply congrR.
        apply right_distributive_mat_mul_over_plus.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        ((m *M partial_sum_mat m n +M I *M partial_sum_mat m n) c d =r=
        (partial_sum_mat m n +M m *M matrix_exp_unary m n) c d) = 
        ((m *M partial_sum_mat m n +M partial_sum_mat m n) c d =r=
        (partial_sum_mat m n +M m *M matrix_exp_unary m n) c d)).
        apply congrR.
        apply mat_add_cong_gen.
        unfold two_mat_congr; intros u v.
        apply refR.
        unfold two_mat_congr; intros u v.
        apply matrix_mul_left_identity.
        apply partial_sum_mat_cong; exact Hm.
        apply refR.
        rewrite Ht; clear Ht.
        apply mat_mul_idem_ind.
    Qed.



    Definition cyclic_path (c : Node) (l : list (Node * Node * R)) :=
      l <> [] /\ source c l = true /\ target c l = true.

    
    
    (* assume that path is well_founded *)
    Fixpoint collect_nodes_from_a_path  
      (l : list (Node * Node * R)) : list Node :=
      match l with
      | [] => []
      | (a, b, _) :: t => match t with
        | [] => [a; b]
        | _ :: _ => a :: collect_nodes_from_a_path t
      end
      end.
    

    Lemma elem_path_aux_true : forall (l : list Node) (a : Node),
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

    
      
    (* Constructs well founded path *)  
    Fixpoint construct_path_from_nodes (l : list Node) (m : Matrix) : 
      list (Node * Node * R) :=
      match l with 
      | [] => []
      | u :: t => match t with
        | [] => []
        | v :: _ => (u, v, m u v) :: construct_path_from_nodes t m
      end
      end.

      
    Lemma path_reconstruction : forall (l : list (Node * Node * R)) m,
      mat_cong m ->
      well_formed_path_aux m l = true -> 
      triple_elem_list (construct_path_from_nodes (collect_nodes_from_a_path l) m) l = true.
    Proof.
      induction l.
      + intros * Hm Hw. simpl; reflexivity.
      + intros * Hm Hw. simpl.
        destruct a as ((au, av), aw).
        destruct l.
        simpl in * |- *.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw _].
        repeat (apply Bool.andb_true_iff; split;
        try (apply refN); try assumption).
        reflexivity.
        (* induction case *)
        destruct p as ((pu, pv), pw). 
        assert (Hwt: (well_formed_path_aux m ((au, av, aw) :: (pu, pv, pw) :: l) = 
          (m au av =r= aw) && ((av =n= pu) && well_formed_path_aux m ((pu, pv, pw) :: l)))%bool).
        simpl. reflexivity.
        rewrite Hwt in Hw; clear Hwt.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        specialize (IHl m Hm Hw).
        assert (Hwt: construct_path_from_nodes
          (au :: collect_nodes_from_a_path ((pu, pv, pw) :: l)) m =
          (au, pu, m au pu) :: 
          construct_path_from_nodes (collect_nodes_from_a_path ((pu, pv, pw) :: l)) m).
        simpl. destruct l.
        reflexivity. reflexivity.
        rewrite Hwt; clear Hwt.
        remember (construct_path_from_nodes
        (collect_nodes_from_a_path ((pu, pv, pw) :: l)) m) as ml.
        remember ((pu, pv, pw) :: l) as pl.
        simpl.
        repeat (apply Bool.andb_true_iff; split).
        apply refN. apply symN. exact Hwll.
        rewrite <-Hwl. apply congrR.
        apply Hm. apply refN.
        apply symN. exact Hwll.
        apply refR.
        exact IHl.
    Qed.
    

    
    Lemma source_list_consturction : forall l c m,
      mat_cong m -> 
      well_formed_path_aux m l = true -> source c l = true ->
      exists d lc, triple_elem_list l ((c, d, m c d) :: lc) = true.
    Proof.
      destruct l.
      + intros ? ? Hm Hw Hs.
        simpl in Hs. congruence.
      + intros ? ? Hm Hw Hs.
        destruct p as ((u, v), w).
        simpl in * |- *.
        exists v, l.
        repeat (apply Bool.andb_true_iff; split).
        apply symN; assumption.
        apply refN.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw _].
        apply symR. rewrite <-Hw.
        apply congrR.
        apply Hm. exact Hs.
        apply refN.
        apply refR.
        apply triple_elem_eq_list_refl.
    Qed.

    Lemma target_list_consturction : forall l c m,
      mat_cong m -> 
      well_formed_path_aux m l = true -> target c l = true ->
      exists d lc, triple_elem_list l (lc ++ [(d, c, m d c)]) = true.
    Proof.
      induction l.
      + intros ? ? Hm Hw Ht.
        simpl in Ht.
        congruence.
      + intros ? ? Hm Hw Ht.
        destruct l.
        destruct a as ((au, av), aw).
        simpl in * |-.
        exists au, [].
        simpl.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        all:(try (apply refN); try (apply refR)).
        apply symN; assumption.
        apply symR.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw _].
        rewrite <-Hw.
        apply congrR.
        apply Hm.
        apply refN.
        exact Ht.
        apply refR.
        reflexivity.
        destruct a as ((au, av), aw).
        destruct p as ((pu, pv), pw).
        assert (Hwt: (well_formed_path_aux m ((au, av, aw) :: (pu, pv, pw) :: l) = 
          (m au av =r= aw) && ((av =n= pu) && well_formed_path_aux m ((pu, pv, pw) :: l)))%bool).
        simpl. reflexivity.
        rewrite Hwt in Hw; clear Hwt.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        assert (Hwt : target c ((au, av, aw) :: (pu, pv, pw) :: l) = 
        target c ((pu, pv, pw) :: l)). simpl. reflexivity.
        rewrite Hwt in Ht; clear Hwt.
        destruct (IHl c m Hm Hw Ht) as [d [lc Hlc]].
        exists d, ((au, av, aw) :: lc).
        rewrite <-List.app_comm_cons.
        remember ((pu, pv, pw) :: l) as pl.
        remember (lc ++ [(d, c, m d c)]) as ld.
        simpl. 
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        apply Bool.andb_true_iff; split.
        all:(try (apply refN); try (apply refR)).
        exact Hlc.
    Qed.

   

         

    Lemma list_equality_cons_gen : forall l ld le c d mcd e f mef,
      l <> [] -> triple_elem_list l ((c, d, mcd) :: ld) = true ->
      triple_elem_list l (le ++ [(e, f, mef)]) = true ->
      (triple_elem_list l [(c, d, mcd)] = true ∧ triple_elem_list l [(e, f, mef)] = true) ∨ 
      (exists lm, 
      triple_elem_list l ((c, d, mcd) :: lm ++ [(e, f, mef)]) = true).
    Proof.
      induction l as [|((au, av), aw) l].
      + intros * H He Hf.
        congruence.
      + intros * H He Hf.
        destruct l as [|((bu, bv), bw) l].
        destruct ld as [|((ldu, ldv), ldw) ld].
        destruct le as [|((leu, lev), lew) le].
        left.
        simpl in * |-*.
        split. exact He.
        exact Hf.
        simpl in Hf.
        destruct le;
        simpl in Hf; lia.
        destruct ld;
        simpl in He; lia.
        destruct ld as [|((ldu, ldv), ldw) ld].
        simpl in He. 
        apply Bool.andb_true_iff in He.
        lia.
        destruct le as [|((leu, lev), lew) le].
        simpl in Hf.
        apply Bool.andb_true_iff in Hf.
        lia.
        remember ((bu, bv, bw) :: l) as bl.
        remember ((ldu, ldv, ldw) :: ld) as dl.
        assert (Hwt : (((leu, lev, lew) :: le) ++ [(e, f, mef)]) =
        ((leu, lev, lew) :: (le ++ [(e, f, mef)]))).
        simpl; reflexivity.
        rewrite Hwt in Hf; clear Hwt.
        simpl in He, Hf.
        apply Bool.andb_true_iff in He, Hf.
        destruct He as [He Her].
        destruct Hf as [Hf Hfr].
        subst.
        assert (Hwt : (bu, bv, bw) :: l ≠ []).
        intro Hff; congruence.
        specialize(IHl _ _ _ _ _ _ _ _ Hwt Her Hfr).
        destruct IHl as [[IHll IHlr] | [lm IHl]].
        right.
        exists [].
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        apply Bool.andb_true_iff; split.
        exact He. assumption.
        right.
        exists ((ldu, ldv, ldw) :: lm).
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        apply Bool.andb_true_iff; split.
        exact He.
        exact IHl.
    Qed.


    
    
    Lemma in_list_mem_collect : forall l c d mcd, 
      in_list eqN (collect_nodes_from_a_path (l ++ [(c, d, mcd)])) d = true.
    Proof.
      induction l.
      + intros ? ? ?.
        simpl.
        apply Bool.orb_true_iff.
        right. apply Bool.orb_true_iff.
        left. apply refN.
      + intros ? ? ?.
        destruct a as ((au, av), aw).
        rewrite <-List.app_comm_cons.
        remember (l ++ [(c, d, mcd)]) as lcd.
        simpl. 
        destruct lcd.
        assert (Hwt : exists w wl, l ++ [(c, d, mcd)] = w :: wl).
        destruct l. simpl.
        exists (c, d, mcd), [].
        reflexivity.
        simpl. exists p, (l ++ [(c, d, mcd)]).
        reflexivity.
        destruct Hwt as [w [wt Hwt]].
        rewrite Hwt in Heqlcd.
        congruence.
        rewrite Heqlcd.
        simpl.
        apply Bool.orb_true_iff.
        right.
        apply IHl.
    Qed.
  
       
         

   
          
    Lemma in_list_collect : forall pl plw a b, 
      (a =n= b = true) ->
      triple_elem_list pl plw = true ->
      in_list eqN (collect_nodes_from_a_path pl) a =
      in_list eqN (collect_nodes_from_a_path plw) b.
    Proof.
      induction pl as [|((au, av), aw) pl].
      + intros [|((bu, bv), bw) plw] ? ? Hab Ht.
        reflexivity.
        simpl in Ht; congruence.
      + intros [|((bu, bv), bw) plw] ? ? Hab Ht.
        simpl in Ht; congruence.
        simpl in Ht.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        specialize (IHpl plw a b Hab Htr).
        destruct pl as [|((cu, cv), cw) pl].
        destruct plw as [|((du, dv), dw) plw].
        simpl.
        f_equal.
        case (a =n= au) eqn:Hau;
        case (b =n= bu) eqn:Hbu.
        reflexivity.
        pose proof trnN _ _ _ Hau Ht as Hf.
        apply symN in Hab.
        pose proof trnN _ _ _ Hab Hf.
        rewrite H in Hbu.
        congruence.
        pose proof trnN _ _ _ Hab Hbu.
        pose proof trnN _ _ _ H (symN _ _ Ht) as Hf.
        rewrite Hf in Hau. congruence.
        reflexivity.
        f_equal.
        case (a =n= av) eqn:Hav;
        case (b =n= bv) eqn:Hbv.
        reflexivity.
        pose proof trnN _ _ _ (symN _ _ Hab) (trnN _ _ _ Hav Htrrr) as Hf.
        rewrite Hf in Hbv.
        congruence.
        pose proof trnN _ _ _ (trnN _ _ _ Hab Hbv) (symN _ _ Htrrr) as Hf.
        rewrite Hf in Hav.
        congruence.
        reflexivity.
        simpl in Htr.
        congruence.
        destruct plw as [|((du, dv), dw) plw].
        simpl in Htr.
        congruence.
        remember ((cu, cv, cw) :: pl) as cpl.
        remember ((du, dv, dw) :: plw) as dpl.
        simpl.
        rewrite Heqcpl, Heqdpl.
        rewrite <-Heqcpl, <-Heqdpl.
        simpl.
        f_equal.
        case (a =n= au) eqn:Hau;
        case (b =n= bu) eqn:Hbu.
        reflexivity.
        pose proof trnN _ _ _ Hau Ht as Hf.
        apply symN in Hab.
        pose proof trnN _ _ _ Hab Hf.
        rewrite H in Hbu.
        congruence.
        pose proof trnN _ _ _ Hab Hbu.
        pose proof trnN _ _ _ H (symN _ _ Ht) as Hf.
        rewrite Hf in Hau. congruence.
        reflexivity.
        exact IHpl.
    Qed.

  

    Lemma well_formed_path_rewrite : forall l lw m,
      mat_cong m -> 
      well_formed_path_aux m l = true ->
      triple_elem_list l lw = true ->
      well_formed_path_aux m lw = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros [|((bu, bv), bw) lw] ? Hm Hw Ht.
        reflexivity.
        simpl in Ht. lia.
      + intros ? ? Hm Hw Ht.
        destruct lw as [|((bu, bv), bw) lw].
        simpl in Ht. congruence.
        simpl in Ht.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        (* Now, I need to know if l is well formed or not *)
        destruct l as [|((cu, cv), cw) l].
        destruct lw as [|((du, dv), dw) lw].
        simpl. simpl in Hw.
        apply Bool.andb_true_iff.
        split. 
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw _].
        rewrite <-Hw.
        apply congrR.
        apply Hm.
        apply symN; assumption.
        apply symN; assumption.
        apply symR; assumption.
        reflexivity.
        simpl in Htr.
        congruence.
        assert (Hwt: (well_formed_path_aux m ((au, av, aw) :: (cu, cv, cw) :: l) = 
          (m au av =r= aw) && ((av =n= cu) && well_formed_path_aux m ((cu, cv, cw) :: l)))%bool).
        simpl. reflexivity.
        rewrite Hwt in Hw; clear Hwt.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        specialize (IHl lw m Hm Hw Htr).
        simpl. apply Bool.andb_true_iff.
        split. 
        rewrite <-Hwl.
        apply congrR.
        apply Hm.
        apply symN; assumption.
        apply symN; assumption.
        apply symR; assumption.
        destruct lw. 
        reflexivity.
        destruct p as ((pu, pv), pw).
        simpl in Htr.
        apply Bool.andb_true_iff.
        split.
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htrv].
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htrw].
        apply Bool.andb_true_iff in Htr.
        destruct Htr as [Htr Htwx].
        apply trnN with cu.
        apply symN in Htrrr.
        apply trnN with av; assumption.
        exact Htr.
        exact IHl. 
    Qed.       

        
      
    

    
    Lemma list_equiv_simp : forall lf lr pu pv au, 
      list_eqv Node eqN [pu; pv] (lf ++ [au] ++ lr) = true ->
      (list_eqv Node eqN lf [] = true /\ 
      pu =n= au = true /\ 
      list_eqv Node eqN lr [pv] = true) ∨
      (list_eqv Node eqN lf [pu] = true /\ 
      pv =n= au = true /\ 
      list_eqv Node eqN lr [] = true).
    Proof.
      intros [|u lf] [|v lr] ? ? ? Hle.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      lia.
      left.
      split. 
      reflexivity.
      split.
      simpl in Hle.
      destruct lr.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      exact Hle.
      apply Bool.andb_true_iff in Hle.
      lia.
      destruct lr.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      simpl.  apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      apply Bool.andb_true_iff; split.
      apply symN; assumption.
      reflexivity.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      congruence.
      rewrite List.app_nil_r in Hle.
      right. split.
      destruct lf.
      simpl in Hle.
      simpl.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      apply Bool.andb_true_iff; split.
      apply symN; assumption.
      reflexivity.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      destruct lf; simpl in Hle; 
      congruence.
      split.
      destruct lf.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [Hle _].
      exact Hle.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      destruct lf; simpl in Hle; 
      congruence.
      reflexivity.
      rewrite <-List.app_comm_cons in Hle.
      simpl in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      assert (Hwt : exists a b l, lf ++ au :: v :: lr = a :: b :: l).
      destruct lf.
      exists au, v, lr. reflexivity.
      destruct lf.
      exists n, au, (v :: lr).
      simpl. reflexivity.
      exists n, n0, (lf ++ [au] ++ v :: lr).
      reflexivity.
      destruct Hwt as (a & b & l & Hwt).
      rewrite Hwt in Hle.
      apply Bool.andb_true_iff in Hle.
      destruct Hle as [_ Hle].
      congruence.
    Qed.
      
    
    
    Lemma collect_nodes_from_a_path_app : forall l m a b mab,
      l <> [] ->  well_formed_path_aux m (l ++ [(a, b, mab)]) = true ->
      list_eqv _ eqN (collect_nodes_from_a_path (l ++ [(a, b, mab)]))
      (collect_nodes_from_a_path l ++ [b]) = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros ? ? ? ? Hf Hw.
        congruence.
      + intros ? ? ? ? Hf Hw.
        destruct l as [|((bu, bv), bw) l].
        - simpl in * |- *.
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hwl Hw].
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hwll Hw].
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hw _].
          repeat (apply Bool.andb_true_iff; split).
          apply refN.
          apply symN; assumption.
          apply refN.
          reflexivity.
        - (* induction case *)
          assert (Hwt: (bu, bv, bw) :: l ≠ []).
          intros H; congruence.
          rewrite <-List.app_comm_cons in Hw.
          remember (((bu, bv, bw) :: l) ++ [(a, b, mab)]) as blm.
          simpl in Hw. 
          rewrite <-List.app_comm_cons in Heqblm.
          rewrite Heqblm in Hw.
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hwl Hw].
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hwll Hw].
          specialize (IHl m a b mab Hwt Hw).
          simpl. 
          apply Bool.andb_true_iff; split.
          apply refN.
          exact IHl.
    Qed.


    Lemma well_formed_path_snoc : forall ll lr m,
      well_formed_path_aux m (ll ++ lr) = true ->
      well_formed_path_aux m ll = true /\ 
      well_formed_path_aux m lr = true.
    Proof.
      induction ll.
      + intros ? ? Hw.
        simpl in Hw.
        split.
        reflexivity.
        exact Hw.
      + intros ? ? Hw.
        destruct a as ((au, av), aw).
        simpl in Hw.
        destruct ll;
          destruct lr.
        simpl in Hw.
        simpl. split.
        exact Hw.
        reflexivity.
        rewrite List.app_nil_l in Hw.
        destruct p as ((pu, pv), pw).
        split.
        simpl.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        rewrite Hwl. reflexivity.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        exact Hw.
        rewrite List.app_nil_r in Hw.
        destruct p as ((pu, pv), pw).
        split.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        specialize (IHll [] m).
        rewrite List.app_nil_r in IHll.
        specialize (IHll Hw).
        remember ((pu, pv, pw) :: ll) as pl.
        simpl. 
        rewrite Heqpl.
        apply Bool.andb_true_iff; split.
        assumption.
        apply Bool.andb_true_iff; split.
        assumption.
        rewrite <-Heqpl.
        assumption.
        reflexivity.
        rewrite <-List.app_comm_cons in Hw.
        destruct p as ((pu, pv), pw).
        specialize (IHll (p0 :: lr) m).
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        rewrite <-List.app_comm_cons in IHll.
        specialize (IHll Hw).
        remember ((pu, pv, pw) :: ll) as pll.
        split. simpl.
        rewrite Heqpll.
        apply Bool.andb_true_iff; split.
        assumption.
        apply Bool.andb_true_iff; split.
        assumption.
        destruct IHll as [IHlll IHllr].
        rewrite <-Heqpll.
        assumption.
        destruct IHll as [IHlll IHllr].
        assumption.
    Qed.




    Lemma list_eqv_snoc : forall t pl xb,
      list_eqv Node eqN t (pl ++ [xb]) = true ->
      exists tp, list_eqv Node eqN t (tp ++ [xb]) = true /\ 
      list_eqv _ eqN tp pl = true.
    Proof.
      intros ? ? ? Hl.
      exists pl.
      split. exact Hl.
      apply list_eqv_refl; assumption.
    Qed.
      

   
    Lemma construct_path_from_nodes_app : forall ll lr a b m,
      triple_elem_list 
        (construct_path_from_nodes (a :: ll ++ [b]) m ++
        construct_path_from_nodes (b :: lr) m)
        (construct_path_from_nodes (a :: ll ++ b :: lr) m) = true.
    Proof.
      induction ll as [|u ll IHll];
        destruct lr as [|v lr].
      + intros ? ? ?; simpl.
        repeat (apply Bool.andb_true_iff; split);
        try (apply refN); try (apply refR);
        reflexivity.
      + intros ? ? ?.
        remember (v :: lr) as vlr.
        simpl.
        rewrite Heqvlr. 
        repeat (apply Bool.andb_true_iff; split);
        try (apply refN); try (apply refR);
        try (apply triple_elem_eq_list_refl).
      + intros ? ? ?.
        rewrite <-List.app_comm_cons.
        remember (ll ++ [b]) as llb.
        simpl.
        assert (Hwt : exists w wl, ll ++ [b] = w :: wl).
        destruct ll. simpl.
        exists b, [].
        reflexivity.
        simpl. exists n, (ll ++ [b]).
        reflexivity.
        destruct Hwt as [w [wt Hwt]].
        rewrite Hwt in Heqllb.
        rewrite Heqllb.
        rewrite List.app_nil_r.
        repeat (apply Bool.andb_true_iff; split);
        try (apply refN); try (apply refR);
        try (apply triple_elem_eq_list_refl).
      + intros ? ? ?. 
        specialize (IHll (v :: lr) u b m).
        simpl in * |- *.
        repeat (apply Bool.andb_true_iff; split);
        try (apply refN); try (apply refR);
        try (apply IHll).
    Qed. 
  
        
    


    (* Checks if au is second element of path or not  *)      
    Fixpoint elem_path_triple_tail (au : Node) (l : list (Node * Node * R)) : bool :=
      match l with
      | [] => false
      | (bu, bv, _) :: t => (au =n= bv) || elem_path_triple_tail au t
      end.


    
    Fixpoint keep_collecting (au : Node) (l : list (Node * Node * R)) :=
      match l with
      | [] => []
      | (bu, bv, bw) :: t => if (au =n= bv) then [(bu, bv, bw)] else 
          (bu, bv, bw) :: keep_collecting au t
      end.
      
    Fixpoint keep_dropping (au : Node) (l : list (Node * Node * R)) :=
      match l with
      | [] => []
      | (bu, bv, bw) :: t => if (au =n= bv) then t else 
        keep_dropping au t
      end.

    (* computes the loop in a path *)
    Fixpoint elem_path_triple_compute_loop (l : list (Node * Node * R)) := 
      match l with
      | [] => None
      | (au, av, aw) :: t => if au =n= av then Some [(au, av, aw)] (* loop at the head, 1 length *)
        else 
            if elem_path_triple_tail au t then Some ((au, av, aw) :: keep_collecting au t)
            else elem_path_triple_compute_loop t
      end.

    (* This function is very similar to the above one, except it returns the 
      left over from the front ++ loop ++ rest of the list *)  
    Fixpoint elem_path_triple_compute_loop_triple (l : list (Node * Node * R)) := 
      match l with
      | [] => ([], None, [])
      | (au, av, aw) :: t => if au =n= av then ([], Some [(au, av, aw)], t) 
        else 
            if elem_path_triple_tail au t then 
            ([], Some ((au, av, aw) :: keep_collecting au t), keep_dropping au t)
            else match elem_path_triple_compute_loop_triple t with 
              | (fp, sp, tp) => ((au, av, aw) :: fp, sp, tp)
            end
      end.
  
  

    Lemma keep_collecting_dropping_dual : forall l au, 
      triple_elem_list l (keep_collecting au l ++ keep_dropping au l) = true.
    Proof.
      induction l as [|((ah, bh), ch) l].
      + intros ?; simpl; reflexivity.
      + intros ?; simpl.
        case (au =n= bh) eqn:Ha.
        rewrite <-List.app_comm_cons.
        rewrite refN, refN, refR.
        simpl. 
        apply triple_elem_eq_list_refl.
        rewrite <-List.app_comm_cons.
        rewrite refN, refN, refR.
        simpl.
        apply IHl.
    Qed.
        
   
    
    Lemma elem_path_triple_tail_true : forall l av,
      elem_path_triple_tail av l = true ->
      exists ll au aw lr, 
        triple_elem_list l (ll ++ [(au, av, aw)] ++ lr) = true /\ 
        elem_path_triple_tail av ll = false /\ 
        triple_elem_list (ll ++ [(au, av, aw)]) (keep_collecting av l) = true.
    Proof.
      induction l as [|((ah, bh), ch) l].
      + intros ? He.
        simpl in He; congruence.
      + intros ? He.
        simpl in He.
        case (av =n= bh) eqn:Hb.
        exists [], ah, ch, l.
        split.
        rewrite List.app_nil_l.
        simpl. apply symN in Hb. 
        rewrite Hb.
        rewrite refN.
        rewrite refR.
        simpl.
        apply triple_elem_eq_list_refl.
        split.
        simpl. reflexivity.
        simpl. 
        rewrite Hb.
        rewrite Hb, refN, refR.
        reflexivity.
        (* induction case *)
        destruct (IHl av He) as [ll [au [aw [lr [Hlra [Hlrb Hlrc]]]]]].
        exists ((ah, bh, ch) :: ll), au, aw, lr.
        split.
        rewrite <-List.app_comm_cons.
        simpl.
        repeat (rewrite refN).
        rewrite refR.
        simpl. exact Hlra.
        split.
        simpl. rewrite Hb.
        exact Hlrb.
        simpl. 
        rewrite Hb, refN, refR, refN.
        exact Hlrc.
    Qed.
      

  

    Lemma elem_path_triple_tail_simp : forall l av, 
      elem_path_triple_tail av l = true ->
      exists ll au aw, triple_elem_list (ll ++ [(au, av, aw)]) 
        (keep_collecting av l) = true.
    Proof.
      induction l as [|((ah, bh), ch) l].
      + intros ? He.
        simpl in He; congruence.
      + intros ? He.
        simpl in He.
        case (av =n= bh) eqn:Hb.
        exists [], ah, ch.
        rewrite List.app_nil_l.
        simpl.  
        rewrite Hb.
        rewrite refN.
        rewrite refR.
        rewrite Hb.
        simpl. reflexivity.
    
        (* induction case *)
        simpl in He.
        destruct (IHl av He) as [ll [aut [awt Htr]]]. 
        exists ((ah, bh, ch) :: ll), aut, awt.
        rewrite <-List.app_comm_cons.
        simpl.
        rewrite Hb.
        repeat (rewrite refN).
        rewrite refR.
        simpl. exact Htr.
    Qed.



    Lemma keep_collecting_rewrite : forall ll lr au, 
      triple_elem_list ll lr = true ->
      target au ll = true -> target au lr = true.
    Proof.
      induction ll as [|((au, av), aw) ll].
      + intros ? ? He Ht.
        simpl in Ht. congruence. 
      + intros [|((bu, bv), bw) lr] ? He Ht.
        simpl in He.  congruence.
        simpl in He.
        apply Bool.andb_true_iff in He.
        destruct He as [He Her].
        apply Bool.andb_true_iff in He.
        destruct He as [He Herr].
        apply Bool.andb_true_iff in He.
        destruct He as [He Herrr].
        destruct ll; destruct lr.
        simpl. simpl in Ht.
        apply trnN with av;
        assumption.
        simpl in Her.
        congruence.
        simpl in Her.
        destruct p as ((pu, pv), pw).
        congruence.
        remember (p :: ll) as pll.
        simpl in Ht.
        rewrite Heqpll in Ht.
        subst.
        specialize (IHll _ _ Her Ht).
        remember (p0 :: lr) as plr.
        simpl. rewrite Heqplr.
        subst.
        exact IHll.
    Qed.
  
        

    Lemma compute_loop_cycle : forall l lc,
      Some lc = elem_path_triple_compute_loop l ->
      exists au av aw lcc, Some ((au, av, aw) :: lcc) = Some lc /\ 
      cyclic_path au lc.
    Proof.
      induction l.
      + intros ? Hl.
        simpl in Hl; congruence.
      + intros ? Hl.
        destruct a as ((au, av), aw).
        simpl in Hl.
        case (au =n= av) eqn:Hb.
        (* loop of 1 lenght *)
        exists au, av, aw, [].
        split. eauto.
        unfold cyclic_path.
        split. congruence.
        split. 
        inversion Hl; subst; clear Hl;
        simpl; apply refN.
        inversion Hl; subst; clear Hl.
        simpl. exact Hb.
        (* loop of 2 or more length *)
        case (elem_path_triple_tail au l) eqn:He.
        exists au, av, aw, (keep_collecting au l).
        split. symmetry.
        exact Hl.
        unfold cyclic_path.
        split.
        congruence.
        split. 
        inversion Hl; subst; 
        simpl; apply refN.
        destruct (elem_path_triple_tail_true l au He) as [ll [aut [awt [lr [Hlra [Hlrb Hlrc]]]]]].
        inversion Hl; subst; clear Hl.
        apply target_tail; simpl.
        eapply keep_collecting_rewrite with (ll ++ [(aut, au, awt)]).
        exact Hlrc.
        erewrite target_end.
        simpl; apply refN.
        destruct (IHl _ Hl) as [aut [avt [awt [lcc [Hsl Hcy]]]]].
        exists aut, avt, awt, lcc.
        split.
        exact Hsl.
        exact Hcy.
    Qed.


    Lemma compute_loop_cycle_tim : forall l lcc au av aw,
      Some ((au, av, aw) :: lcc) = elem_path_triple_compute_loop l ->
      cyclic_path au ((au, av, aw) :: lcc).
    Proof.
      intros * Hs.
      destruct (compute_loop_cycle l ((au, av, aw) :: lcc) Hs)  as 
      (aut & avt & awt & lcct & Hss & Hcc).
      inversion Hss; subst; clear Hss.
      exact Hcc.
    Qed.




    (* elem_path_triple l = true means l does not have any cycle *)     
    Fixpoint elem_path_triple (l : list (Node * Node * R)) : bool := 
      match l with
      | [] => true 
      | (au, av, _) :: t => 
          negb (au =n= av) && 
          negb (elem_path_triple_tail au t) && 
          elem_path_triple t 
      end.


    Lemma elim_path_triple_connect_compute_loop_true_first : forall l,
      elem_path_triple l = true -> elem_path_triple_compute_loop l = None.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros He; simpl in He.
        simpl. reflexivity.
      + intros He; simpl in * |- *.
        apply Bool.andb_true_iff in He.
        destruct He as [He Her].
        apply Bool.andb_true_iff in He.
        destruct He as [He Herr].
        apply Bool.negb_true_iff in Herr, He.
        rewrite He, Herr.
        apply IHl; assumption.
    Qed.

    Lemma elim_path_triple_connect_compute_loop_true_second : forall l,
      elem_path_triple_compute_loop l = None -> elem_path_triple l = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros He; simpl in He.
        simpl. reflexivity.
      + intros He; simpl in * |- *.
        case (au =n= av) eqn:Hb.
        congruence.
        simpl.
        case (elem_path_triple_tail au l) eqn:Hbe.
        congruence.
        simpl. 
        apply IHl; assumption.
    Qed.



    Lemma elim_path_triple_connect_compute_loop_true_none_eqv : forall l, 
      elem_path_triple_compute_loop l = None <-> elem_path_triple l = true.
    Proof.
      intros ?; split; intro H.
      apply elim_path_triple_connect_compute_loop_true_second; assumption.
      apply elim_path_triple_connect_compute_loop_true_first; assumption.
    Qed.



    Lemma elim_path_triple_connect_compute_loop_false_first : forall l,
      elem_path_triple l = false -> exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path au lc. 
    Proof.
      induction l as [|((au, av), aw) l].
      + intro H; simpl in H.
        congruence.
      + intros He; simpl in He.
        case (au =n= av) eqn:Ha.
        simpl in He.
        (* loop of lenght 1, at the head itself *)
        exists au, av, aw, [(au, av, aw)], [].
        split. simpl.
        rewrite Ha.
        f_equal.
        split. 
        f_equal.
        unfold cyclic_path.
        split.
        congruence.
        split; simpl.
        apply refN.
        exact Ha.
        simpl in He.
        (* loop starts here but of >= lenght 2 *)
        case (elem_path_triple_tail au l) eqn:Hb.
        simpl in He.
        repeat eexists.
        simpl. rewrite Ha, Hb.
        f_equal.
        congruence.
        simpl. 
        apply refN.
        apply target_tail; simpl.
        destruct (elem_path_triple_tail_simp _ _ Hb) as (ll & aut & awt & Ht).
        erewrite keep_collecting_rewrite.
        reflexivity.
        exact Ht.
        erewrite target_end.
        simpl. apply refN.
        simpl in He.
        destruct (IHl He) as (aut & avt & awt & lc & lcc & Hlc & Haut & Hc).
        repeat eexists.
        simpl. rewrite Ha, Hb.
        rewrite <-Haut in Hlc.
        exact Hlc.
        congruence.
        simpl. apply refN.
        unfold cyclic_path in Hc.
        rewrite Haut.
        firstorder.
    Qed.


    Lemma elim_path_triple_connect_compute_loop_false_second : 
      forall l lc, 
      Some lc = elem_path_triple_compute_loop l ->
      elem_path_triple l = false.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros ? Hs; simpl in Hs;
        congruence.
      + intros ? Hs; simpl in * |- *.
        case (au =n= av) eqn:Ha.
        simpl. reflexivity.
        case (elem_path_triple_tail au l) eqn:Hb.
        simpl. reflexivity.
        simpl.
        eapply IHl; exact Hs.
    Qed.



    Lemma elim_path_triple_connect_compute_loop_false_eqv : forall l,
      elem_path_triple l = false <-> exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path au lc.
    Proof.
      intros *; split; intros He.
      apply  elim_path_triple_connect_compute_loop_false_first; assumption.
      destruct He as (au & av & aw & lc & lcc & Hs & Hlcc & Hc).
      eapply elim_path_triple_connect_compute_loop_false_second; 
      exact Hs.
    Qed.


    Lemma elem_path_triple_compute_loop_triple_middle_element : forall l ll lm lr, 
      (ll, lm, lr) = elem_path_triple_compute_loop_triple l ->
      lm = elem_path_triple_compute_loop l.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros ? ? ? Hl; simpl in Hl; simpl;
        inversion Hl; subst; reflexivity.
      + intros ? ? ? Hl.
        simpl in * |- *.
        case (au =n= av) eqn:Ha.
        inversion Hl; subst; reflexivity.
        case (elem_path_triple_tail au l) eqn:Hb.
        inversion Hl; subst; reflexivity.
        destruct (elem_path_triple_compute_loop_triple l) as ((al, bl), cl).
        inversion Hl; subst; clear Hl.
        eapply IHl.
        reflexivity.
    Qed.


    Lemma elem_path_triple_compute_loop_triple_combined_list : forall l,
      match elem_path_triple_compute_loop_triple l with
      | (fp, None, tp) => triple_elem_list l (fp ++ tp) = true
      | (fp, Some sp, tp) => triple_elem_list l  (fp ++ sp ++ tp) = true
      end. 
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl; reflexivity.
      + simpl. destruct (elem_path_triple_compute_loop_triple l) as ((la, lb), lc).
        case (au =n= av) eqn:Ha.
        rewrite List.app_nil_l, 
        <-List.app_comm_cons.
        rewrite refN, refN, refR.
        simpl. 
        apply triple_elem_eq_list_refl.
        case (elem_path_triple_tail au l) eqn:Hb.
        simpl. 
        rewrite refN, refN, refR.
        simpl. 
        apply keep_collecting_dropping_dual.
        destruct lb eqn:Hc.
        rewrite <-List.app_comm_cons.
        rewrite refN, refN, refR.
        simpl.
        exact IHl.
        rewrite <-List.app_comm_cons.
        rewrite refN, refN, refR.
        simpl.
        exact IHl.
    Qed.



    Lemma elem_path_triple_tail_rewrite : forall l lr au, 
      triple_elem_list l lr = true ->
      elem_path_triple_tail au l = false ->
      elem_path_triple_tail au lr = false.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros [|((pur, pvr), pwr) lr] ? Ht He.
        simpl. reflexivity.
        simpl in Ht; congruence.
      + intros [|((pur, pvr), pwr) lr] ? Ht He.
        simpl in Ht; congruence.
        simpl in * |- *.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        apply Bool.orb_false_iff; split.
        case (au0 =n= pvr) eqn:Hau.
        apply symN in Htrrr.
        pose proof trnN _ _ _ Hau Htrrr as Hf.
        rewrite Hf in He. 
        simpl in He. congruence.
        reflexivity.
        case ((au0 =n= av)) eqn:Hau.
        simpl in He.
        congruence.
        simpl in He.
        eapply IHl.
        exact Htr.
        exact He.
    Qed.


    Lemma elem_path_triple_tail_false : forall l ll lr au, 
      elem_path_triple_tail au l = false ->
      triple_elem_list l (ll ++ lr) = true ->
      elem_path_triple_tail au ll = false /\
      elem_path_triple_tail au lr = false.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros ? ? ? He Ht.
        simpl in * |- *.
        destruct ll; destruct lr;
        simpl in * |- *; 
        split; try reflexivity;
        try congruence.
      + intros ? ? ? He Ht.
        destruct ll as [|((pu, pv), pw) ll].
        destruct lr as [|((pur, pvr), pwr) lr].
        simpl in Ht. congruence.
        rewrite List.app_nil_l in Ht.
        simpl.
        split. reflexivity.
        simpl in He, Ht.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        case (au0 =n= av) eqn:Ha.
        simpl in He.
        congruence.
        simpl in He.
        apply Bool.orb_false_iff.
        split.
        case (au0 =n= pvr) eqn:Hau.
        apply symN in Htrrr.
        pose proof trnN _ _ _ Hau Htrrr as Hf.
        rewrite Hf in Ha. congruence.
        reflexivity.
        eapply elem_path_triple_tail_rewrite.
        exact Htr.
        exact He.
        rewrite <-List.app_comm_cons in Ht.
        simpl in He, Ht.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        simpl.
        case (au0 =n= av) eqn:Ha.
        simpl in He. congruence.
        simpl in He.
        destruct (IHl _ _ _ He Htr) as [Hl Hr].
        split.
        apply Bool.orb_false_iff.
        split. 
        case (au0 =n= pv) eqn:Hau.
        apply symN in Htrrr.
        pose proof trnN _ _ _ Hau Htrrr as Hf.
        rewrite Hf in Ha. congruence.
        reflexivity.
        exact Hl.
        exact Hr.
    Qed.



    Lemma elem_path_triple_compute_loop_first_element_elementry : forall l ll lm lr ,
      (ll, lm, lr) = elem_path_triple_compute_loop_triple l ->
      elem_path_triple ll = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros ? ? ? Hl;
        simpl in Hl;
        inversion Hl; subst;
        reflexivity.
      + intros ? ? ? Hl.
        simpl in Hl.
        case (au =n= av) eqn:Ha.
        inversion Hl; subst;
        reflexivity.
        case (elem_path_triple_tail au l) eqn:Hb.
        inversion Hl; subst;
        reflexivity.
        remember (elem_path_triple_compute_loop_triple l) as elp.
        destruct elp as ((al, bl), cl).
        inversion Hl; subst; clear Hl.
        simpl.
        rewrite Ha; simpl.
        pose proof elem_path_triple_compute_loop_triple_combined_list l as Hep.
        destruct (elem_path_triple_compute_loop_triple l) as ((atl, btl), ctl).
        destruct btl.
        apply Bool.andb_true_iff; split.
        apply Bool.negb_true_iff.
        destruct (elem_path_triple_tail_false l atl (l0 ++ ctl) _ Hb Hep) as (Hept & _).
        inversion Heqelp.
        exact Hept.
        eapply IHl.
        reflexivity.
        apply Bool.andb_true_iff; split.
        apply Bool.negb_true_iff.
        destruct (elem_path_triple_tail_false l atl ctl _ Hb Hep) as (Hept & _).
        inversion Heqelp.
        exact Hept.
        eapply IHl.
        reflexivity.
    Qed.





    Lemma source_same_path : forall l₁ l₂ x y,
      triple_elem_list l₁ l₂ = true -> 
      source x l₁ = true -> source y l₂ = true ->
      x =n= y = true.
    Proof.
      induction l₁.
      + intros * Ht Hx Hy. 
        simpl in * |-. 
        congruence. 
      + intros * Ht Hx Hy.
        destruct l₂ as [|b l₂].
        simpl in Hy; congruence.
        destruct a as ((au, av), aw).
        destruct b as ((bu, bv), bw).
        simpl in * |-.
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrr].
        apply Bool.andb_true_iff in Ht.
        destruct Ht as [Ht Htrrr].
        apply symN in Hy.
        eapply trnN with au.
        exact Hx.
        apply trnN with bu; 
        assumption.
    Qed.



    Lemma list_tl_lia {A : Type} : forall (xs : list A) k, 
      List.tl xs <> [] -> (length (List.tl xs) = S k)%nat ->
      (length xs = S (S k))%nat.
    Proof.
      induction xs.
      + intros * Hf Hin.
        simpl in * |- *.
        congruence.
      + intros * Hf Hin.
        simpl in * |- *.
        lia.
    Qed.
    


    Lemma all_paths_in_klength : ∀ (k : nat)
      (m : Matrix) (c d : Node) xs,
      In_eq_bool xs (all_paths_klength m k c d) = true ->
      (List.length xs = S k).
    Proof.
      induction k.
      + simpl; intros ? ? ? ? Hin.
        case (c =n= d) eqn:Hcd.
        destruct xs. 
        simpl in Hin.
        congruence.
        simpl in Hin. destruct p as ((u, v), w).
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin _].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hl Hin].
        simpl. destruct xs.
        simpl. reflexivity.
        simpl in Hin. 
        destruct p as ((px, py), pw).
        congruence.
        simpl in Hin.
        congruence.
      + simpl; intros ? ? ? ? Hin.
        pose proof append_node_in_paths_eq _ m c _ Hin as Hp.
        destruct Hp as [y [ys [Hy [Hsc [Hsd Hyn]]]]].
        apply append_node_rest in Hin.
        apply in_flat_map_bool_first in Hin.
        destruct Hin as [x [Hl Hr]].
        pose proof IHk m x d (List.tl xs) Hr as Hind.
        pose proof source_and_non_empty_kpath _ _ _ _ _ Hr as [Htl Hxy].
        (* ys = List.tl xs that means y = x *)
        assert(Htt: triple_elem_list (List.tl xs) ys = true).
        destruct xs. simpl in Hsc; congruence.
        simpl in Hy. simpl. destruct p as ((u, v), w).
        apply Bool.andb_true_iff in Hy.
        destruct Hy as [Hyl Hy]. exact Hy.
        pose proof source_same_path _ _ _ _ Htt Hxy Hsd as Hp.
        apply list_tl_lia; assumption.
    Qed.


  


    Fixpoint partial_sum_paths (m : Matrix) (n : nat) (c d : Node) : R :=
      match n with
      | O => I c d
      | S n' =>  partial_sum_paths m n' c d + 
        sum_all_rvalues (get_all_rvalues (construct_all_paths m n c d))
      end.

    

    Lemma connect_partial_sum_mat_paths : forall n m c d,
      mat_cong m -> 
      partial_sum_mat m n c d =r= partial_sum_paths m n c d = true.
    Proof.
      induction n.
      + intros * Hm; simpl;
        apply refR.
      + intros * Hm; simpl.
        unfold matrix_mul, matrix_add.
        apply congrP.
        exact (IHn m c d Hm).
        pose proof matrix_path_equation (S n) m c d Hm as Hp.
        rewrite <-Hp.
        apply congrR.
        simpl. unfold matrix_mul, 
        matrix_add.
        apply refR.
        apply refR.
    Qed.



    Lemma connect_unary_matrix_exp_partial_sum_paths : forall n m c d,
      mat_cong m -> 
      matrix_exp_unary (m +M I) n c d =r= partial_sum_paths m n c d = true.
    Proof.
      intros * Hm.
      pose proof matrix_pow_idempotence n m c d Hm as Hp.
      pose proof connect_partial_sum_mat_paths n m c d Hm as Hpp.
      eapply trnR with (partial_sum_mat m n c d); assumption.
    Qed.

    
    (* c covers l, i.e., every element of l appears in c *)
    Definition covers (c l : list Node) : Prop :=
      forall x, in_list eqN l x = true ->  
        in_list eqN c x = true.


    Lemma covers_list_elem : 
      forall (c l : list Node), 
      (forall y : Node, in_list eqN c y = true) ->
      covers c l.
    Proof.
      unfold covers.
      destruct c as [|a c].
      + intros ? Hy ? Hl.
        specialize (Hy x).
        simpl in Hy.
        congruence.
      + intros ? Hy ? Hl.
        simpl in *.
        exact (Hy x). 
    Qed.
     


    Lemma list_eqv_in_list_rewrite :
      forall l c x, 
      list_eqv Node eqN c l = true ->
      in_list eqN c x = true ->
      in_list eqN l x = true.
    Proof.
      induction l; 
      destruct c; 
      simpl;
      intros ? Ha Hb.
      + congruence.
      + congruence.
      + congruence.
      + apply Bool.andb_true_iff in Ha.
        destruct Ha as [Hal Har].
        case (x =n= n) eqn:Hxn.
        rewrite (trnN _ _ _ Hxn Hal).
        reflexivity.
        simpl in Hb.
        erewrite IHl.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
        exact Har.
        exact Hb.
    Qed.


    Lemma in_list_mem_ex_one : 
      forall l₁ l₂ a x, 
      x =n= a = false -> 
      in_list eqN (l₁ ++ a :: l₂) x = true ->
      in_list eqN (l₁ ++ l₂) x = true.
    Proof.
      induction l₁;
      simpl; 
      intros ? ? ? Hxa Hlx.
      + rewrite Hxa in Hlx.
        simpl in Hlx.
        exact Hlx.
      + case (x =n= a) eqn:Ha.
        reflexivity.
        simpl.
        eapply IHl₁.
        exact Hxa.
        simpl in Hlx.
        exact Hlx.   
    Qed.

    Lemma length_le_Sn : 
      forall l c n, 
      (length c < n)%nat -> 
      list_eqv Node eqN c l = true ->
      (length l < n)%nat.
    Proof.
      induction l.
      + simpl;
        intros * Ha Hb.
        nia.
      + simpl; 
        intros * Ha Hb.
        simpl in *.
        destruct c.
        - simpl in Hb.
          congruence.
        - simpl in Ha, Hb.
          apply Bool.andb_true_iff in Hb.
          destruct Hb as [Hbl Hbr].
          destruct n.
          nia.
          assert (Hc: (length c < n)%nat).
          nia.
          specialize (IHl _ _ Hc Hbr).
          nia.
    Qed.
      

    Lemma covers_dup : 
      forall l (c : list Node), 
      covers c l ->  (length c < List.length l)%nat -> 
      exists a l₁ l₂ l₃, 
        list_eqv Node eqN l (l₁ ++ [a] ++ l₂ ++ [a] ++ l₃) = true.
    Proof.
      induction l. 
      + simpl.
        intros * Ha Hb.
        nia.
      +
        (* a can be repeated or not *)
        simpl.
        intros * Ha Hb.
        unfold covers in Ha.
        destruct (in_list eqN l a) eqn:Hal.
        (* a in in the list and we have loop *)
        destruct (list_split_gen Node eqN refN symN l a Hal) as 
          [l₁ [l₂ Hlt]].
        exists a, [], l₁, l₂.
        simpl in *.
        rewrite refN, Hlt.
        reflexivity.
        (* a is not in l *)
        pose proof (Ha a) as Hw.
        simpl in Hw.
        rewrite refN in Hw.
        simpl in Hw.
        specialize (Hw eq_refl).
        destruct (list_split_gen Node eqN refN symN c a Hw) as 
        [l₁ [l₂ Hlt]].
        specialize (IHl (l₁ ++ l₂)).
        assert (Hcov : covers (l₁ ++ l₂) l).
        unfold covers.
        intros ? Hin.
        (* from Hal and Hin, we know that x <> a *)
        pose proof list_mem_true_false _ eqN 
          symN trnN _ _ _ Hal Hin as Hax.
        (* get a concrete instance *)
        pose proof (Ha x) as Hx.
        simpl in Hx.
        rewrite Hax, Hin in Hx.
        specialize (Hx eq_refl).
        pose proof list_eqv_in_list_rewrite _ _ _ 
          Hlt Hx as Hinc.
        eapply in_list_mem_ex_one;
        [exact Hax|
        simpl in Hinc;
        exact Hinc].
        specialize (IHl Hcov).
        pose proof length_le_Sn  
          _ _ _ Hb Hlt as Hwt.
        simpl in Hwt.
        rewrite app_length in Hwt.
        simpl in Hwt.
        rewrite PeanoNat.Nat.add_succ_r in Hwt.
        rewrite <-app_length in Hwt.
        assert (Hvt : (length (l₁ ++ l₂) < length l)%nat).
        nia.
        destruct (IHl Hvt) as
          (av & lv₁ & lv₂ & lv₃ & Hlp).
        exists av, (a :: lv₁), lv₂, lv₃.
        simpl.
        rewrite refN.
        simpl in *.
        exact Hlp.
    Qed.

    
      
    
    Lemma length_leq_lt : ∀ (l : list (Node * Node * R)),
      l <> [] -> 
      ((List.length l) < 
        List.length (collect_nodes_from_a_path l))%nat.
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl.
        intro H.
        congruence.
      + simpl. 
        intro H.
        destruct l as [|((bu, bv), bw) l].
        simpl.
        nia.
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        assert (Hne: bl <> []).
        intro Hf.
        congruence.
        specialize (IHl Hne);
        try nia.
    Qed.

        



   
    Lemma length_collect_node_gen :
      forall (c : list Node) (l : list (Node * Node * R)),
      c <> [] ->  
      (List.length c <= List.length l)%nat ->
      (List.length c < 
      List.length (collect_nodes_from_a_path l))%nat.
    Proof.
      intros ? ? Hne Hfin.
      pose proof length_leq_lt l as IHl.
      assert (Hlne: l <> []).
      destruct l. 
      intros Hf.
      destruct c.
      congruence.
      simpl in Hfin.
      nia.
      intro Hf.
      congruence.
      specialize (IHl Hlne).
      nia.
    Qed.


    Lemma elem_path_triple_tail_in_list : 
      forall (l : list (Node * Node * R)) m a,
      well_formed_path_aux m l = true -> 
      elem_path_triple_tail a l = true ->
      in_list eqN (collect_nodes_from_a_path l) a = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl.
        intros ? ? Hw Hf.
        congruence.
      + simpl.
        intros ? ? Hw Hf.
        destruct l as [|((bu, bv), bw) l].
        simpl in Hf.
        simpl.
        case (a =n= av) eqn:Haav.
        simpl.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
        simpl in Hf.
        congruence.
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw Hwr].
        case (a =n= av) eqn:Haav.
        simpl in Hf.
        case (a =n= au) eqn:Haau.
        simpl.
        reflexivity.
        simpl.
        rewrite Heqbl.
        simpl.
        destruct l as [|((cu, cv), cw) l].
        simpl.
        rewrite (trnN _ _ _ Haav Hw).
        reflexivity.
        simpl.
        simpl.
        rewrite (trnN _ _ _ Haav Hw).
        reflexivity.
        simpl in Hf.
        apply Bool.orb_true_iff.
        right.
        eapply IHl.
        exact Hwr.
        exact Hf.
    Qed.






        




    Lemma elem_path_collect_node_from_path_first :
      ∀ (l : list (Node * Node * R)) (m : Matrix), 
        well_formed_path_aux m l = true -> 
        elem_path_triple l = false -> 
        no_dup Node eqN (collect_nodes_from_a_path l) = false.
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl.
        intros ? Ha Hb.
        congruence.
      + simpl.
        intros ? Ha Hb.
        destruct l as [|((bu, bv), bw) l].
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Ha _].
        simpl in Hb.
        simpl.
        case (au =n= av) eqn:Hauv.
        reflexivity.
        simpl in Hb.
        congruence.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Ha Har].
        apply Bool.andb_true_iff in Har.
        destruct Har as [Hal Har].
        case (au =n= av) eqn:Hauv.
        remember ((bu, bv, bw) :: l) as bl.
        simpl.
        simpl in Hb.
        apply Bool.andb_false_iff.
        left.
        apply Bool.negb_false_iff.
        rewrite Heqbl.
        simpl.
        destruct l.
        simpl.
        rewrite (trnN _ _ _ Hauv Hal).
        reflexivity.
        simpl. 
        rewrite (trnN _ _ _ Hauv Hal).
        reflexivity.
        remember ((bu, bv, bw) :: l) as bl.
        simpl in Hb.
        simpl.
        case (elem_path_triple_tail au bl) eqn:Hep.
        simpl in Hb.
        apply Bool.andb_false_iff.
        left.
        apply Bool.negb_false_iff.
        eapply elem_path_triple_tail_in_list.
        exact Har.
        exact Hep.
        simpl in Hb.
        apply Bool.andb_false_iff.
        right.
        eapply IHl;
        try assumption.
        exact Har.
    Qed.
  

    
    Lemma elem_path_false_rewrite : 
      forall bl l bu bv bw m au, 
      bl = (bu, bv, bw) :: l ->
      au =n= bu = false ->
      well_formed_path_aux m bl = true ->
      elem_path_triple_tail au bl = false ->
      in_list eqN (collect_nodes_from_a_path bl) au = false.
    Proof.
      induction bl as [|((blbu, blbv), blbw) bl].
      + intros * Ha Hb Hw He.
        congruence.
      + intros * Ha Hb Hw He.
        inversion Ha; subst;
        clear Ha.
        (* check if l is empty or not? *)
        destruct l as [|((lcu, lcv), lcw) l].
        simpl in *.
        rewrite Hb.
        apply Bool.orb_false_iff in He.
        destruct He as [He _].
        rewrite He.
        reflexivity.
        (* inductive case *)
        remember ((lcu, lcv, lcw) :: l) as lbl.
        simpl in *.
        rewrite Heqlbl.
        rewrite Heqlbl in Hw.
        rewrite <-Heqlbl in Hw.
        rewrite <-Heqlbl.
        simpl.
        rewrite Hb.
        simpl.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hw Hwr].
        apply Bool.orb_false_iff in He.
        destruct He as [Hel Her].
        eapply IHbl.
        exact Heqlbl.
        case (au =n= lcu) eqn: Haul.
        apply symN in Hw.
        rewrite (trnN _ _ _ Haul Hw) in Hel.
        congruence.
        reflexivity.
        exact Hwr.
        exact Her.
    Qed.



    Lemma elem_path_collect_node_from_path_second :
      ∀ (l : list (Node * Node * R)) (m : Matrix), 
        well_formed_path_aux m l = true ->
        no_dup Node eqN (collect_nodes_from_a_path l) = false -> 
        elem_path_triple l = false.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros ? Ha Hb.
        simpl in Hb.
        congruence.
      + simpl.
        intros ? Ha Hb.
        destruct l as [|((bu, bv), bw) l].
        simpl in Hb.
        case (au =n= av) eqn:Hauv.
        simpl.
        reflexivity.
        simpl in Hb.
        congruence.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Hal Ha].
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Har Ha].
        remember ((bu, bv, bw) :: l) as bl. 
        simpl in Hb.
        apply Bool.andb_false_iff in Hb.
        destruct Hb as [Hb | Hb].
        apply Bool.negb_false_iff in Hb.
        case (au =n= av) eqn:Hauv.
        reflexivity.
        simpl.
        case ((elem_path_triple_tail au bl)) eqn:Hep.
        reflexivity.
        simpl.

        assert (Ht: au =n= bu = false).
        case (au =n= bu) eqn:Ht.
        apply symN in Har.
        rewrite (trnN _ _ _ Ht Har) in Hauv.
        congruence.
        reflexivity.
        rewrite (elem_path_false_rewrite  bl l bu bv bw m au 
          Heqbl Ht Ha Hep) in Hb.
        congruence.
        apply Bool.andb_false_iff.
        right.
        eapply IHl.
        exact Ha.
        exact Hb.
    Qed.



    
    Lemma list_eqv_in_list_rewrite_gen :
      forall l₁ l₂ a n,
      a =n= n = true ->  
      list_eqv Node eqN l₁ l₂ = true ->
      in_list eqN l₂ n = true ->
      in_list eqN l₁ a = true.
    Proof.
      induction l₁ as [|a₁ l₁]; 
      destruct l₂ as [|b₂ l₂]; 
      simpl;
      intros ? ? Ha Hb Hc.
      + congruence.
      + congruence.
      + congruence.
      + apply Bool.andb_true_iff in Hb.
        destruct Hb as [Hbl Hbr].
        case (n =n= b₂) eqn:Hxn.
        pose proof (trnN _ _ _ Ha Hxn) as Han.
        apply symN in Hbl.
        rewrite (trnN _ _ _ Han Hbl).
        reflexivity.
        simpl in Hc.
        erewrite IHl₁.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
        exact Ha.
        exact Hbr.
        exact Hc.
    Qed.


    Lemma list_eqv_no_dup_rewrite :
      forall l₁ l₂, 
      list_eqv Node eqN l₁ l₂ = true ->
      no_dup Node eqN l₂ = false ->
      no_dup Node eqN l₁ = false.
    Proof.
      induction l₁.
      + simpl.
        intros ? Ha Hb.
        destruct l₂.
        ++ simpl in Hb.
           congruence.
        ++ congruence.
      + (* inductive case *)
        simpl.
        intros ? Ha Hb.
        destruct l₂.
        ++ simpl in Hb.
           congruence.
        ++ simpl in Hb.
           apply Bool.andb_true_iff in Ha.
           destruct Ha as [Hal Har].
           apply Bool.andb_false_iff in Hb.
           destruct Hb as [Hb | Hb].
           apply Bool.negb_false_iff in Hb.
           rewrite (list_eqv_in_list_rewrite_gen _ _ 
           _ _ Hal Har Hb).
           reflexivity.
           erewrite IHl₁.
           apply Bool.andb_false_iff.
           right.
           reflexivity.
           exact Har.
           exact Hb.
    Qed.

    

    Lemma in_list_true : 
      forall l₁ l₂ a, 
      in_list eqN (l₁ ++ a :: l₂) a = true.
    Proof.
      induction l₁.
      + simpl.
        intros ? ?.
        rewrite refN.
        reflexivity.
      + simpl.
        intros ? ?.
        rewrite IHl₁.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
    Qed.


    Lemma no_dup_false_one : 
      forall l₁ l₂ l₃ a, 
      no_dup Node eqN (l₁ ++ a :: l₂ ++ a :: l₃) = false.
    Proof.
      induction l₁.
      + simpl.
        intros *.
        rewrite in_list_true.
        simpl.
        reflexivity.
      + simpl.
        intros *.
        rewrite IHl₁.
        apply Bool.andb_false_iff.
        right.
        reflexivity.
    Qed.
    


    Lemma all_paths_in_klength_paths_cycle : 
      forall (c : list Node)
      (l : list (Node * Node * R)) m,
      well_formed_path_aux m l = true ->
      covers c (collect_nodes_from_a_path l) -> 
      (List.length c < List.length (collect_nodes_from_a_path l))%nat ->
      elem_path_triple l = false.
    Proof.
      intros * Hw Hc Hl.
      eapply elem_path_collect_node_from_path_second.
      exact Hw.
      destruct (covers_dup 
         _ _ Hc Hl) as 
      [a [l₁ [l₂ [l₃ Hll]]]].
      eapply list_eqv_no_dup_rewrite.
      exact Hll.
      simpl.
      apply no_dup_false_one.
    Qed.




    (* if you give me path of length >= finN then there is loop *)
    Lemma all_paths_in_klength_paths_cycle_finN : 
      forall (l : list (Node * Node * R)) m,
      (List.length finN <= List.length l)%nat ->
      well_formed_path_aux m l = true ->
      exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path au lc.
    Proof.
      intros ? ? Hfin Hw.
      pose proof length_collect_node_gen finN 
        l empN Hfin as Hf.
      pose proof covers_list_elem finN 
        (collect_nodes_from_a_path l) memN as Hcov.
      pose proof all_paths_in_klength_paths_cycle
        finN l m Hw Hcov Hf as Hwt.
      eapply elim_path_triple_connect_compute_loop_false_first;
      try assumption.
    Qed.
    

    
        



    Lemma triple_compute_connect_with_triple_elem_forward : 
      forall l, 
      elem_path_triple l = false ->
      exists ll lm lr, (ll, Some lm, lr) = 
      elem_path_triple_compute_loop_triple l.
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl;
        intros Ha.
        congruence.
      + simpl.
        intros Ha.
        case (au =n= av) eqn:Hauv.
        eauto.
        simpl in Ha.
        case (elem_path_triple_tail au l) eqn:Hel.
        eauto.
        simpl in Ha.
        destruct (IHl Ha) as 
        (ll & lm & lr & Hb).
        destruct (elem_path_triple_compute_loop_triple l) as 
        ((bu, bv), bw).
        exists ((au, av, aw) :: bu),
          lm, lr.
        f_equal.
        f_equal.
        inversion Hb; subst;
        reflexivity.
        inversion Hb; subst;
        reflexivity.
    Qed.




    Lemma triple_compute_connect_with_triple_elem_backward : 
      forall l ll lm lr, 
      (ll, Some lm, lr) = 
      elem_path_triple_compute_loop_triple l ->
      elem_path_triple l = false.
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl.
        intros * Ha.
        congruence.
      + simpl.
        intros * Ha.
        case (au =n= av) eqn:Hauv.
        reflexivity.
        case (elem_path_triple_tail au l) eqn:Hel.
        reflexivity.
        simpl.
        destruct (elem_path_triple_compute_loop_triple l) as 
        ((bu, bv), bw).
        inversion Ha;
        subst; clear Ha.
        exact (IHl bu lm bw eq_refl).
    Qed.
        

    Lemma triple_compute_connect_with_triple_elem : 
      forall l, 
      elem_path_triple l = false <->
      exists ll lm lr, (ll, Some lm, lr) = 
      elem_path_triple_compute_loop_triple l.
    Proof.
      intros ?; 
      split;
      intros He.
      eapply triple_compute_connect_with_triple_elem_forward;
      try assumption.
      destruct He as (ll & lm & lr & Hal).
      eapply triple_compute_connect_with_triple_elem_backward;
      try assumption.
      exact Hal.
    Qed.


    Lemma target_keep_collect_rewrite :
      forall lm ln a au av aw,  
      triple_elem_list lm ln = true ->
      target a ((au, av, aw) :: ln) = true ->
      target a ((au, av, aw) :: lm) = true.
    Proof.
      induction lm as [|((au, av), aw) lm].
      + destruct ln as [|((bu, bv), bw) ln];
        simpl;
        intros ? ? ? ? Ha Hb;
        congruence.      
      + destruct ln as [|((bu, bv), bw) ln]. 
        intros ? ? ? ? Ha Hb.
        simpl in Ha.
        congruence.
        intros ? ? ? ? Ha Hb.
        simpl in Ha.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Ha Har].
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Ha Harr].
        remember ((bu, bv, bw) :: ln) as cln.
        remember ((au, av, aw) :: lm) as alm.
        simpl in Hb.
        rewrite Heqcln in Hb.
        simpl.
        rewrite Heqalm.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [Halt Hart].
        eapply IHlm.
        exact Har.
        simpl in Hb.
        simpl.
        destruct ln. 
        eapply trnN.
        exact Hb.
        apply symN; 
        exact Hart.
        exact Hb.
    Qed.
    


    Lemma triple_compute_connect_with_triple_elem_stronger : 
      forall l, 
      elem_path_triple l = false ->
      exists ll au av aw lm lr, (ll, Some ((au, av, aw) :: lm), lr) = 
      elem_path_triple_compute_loop_triple l /\ 
      cyclic_path au ((au, av, aw) :: lm) /\ 
      elem_path_triple ll = true /\ 
      triple_elem_list l (ll ++  ((au, av, aw) :: lm) ++ lr) = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + simpl;
        intros Ha.
        congruence.
      + simpl.
        intros Ha.
        case (au =n= av) eqn:Hauv.
        exists [], au, av, aw, 
          [], l. 
        simpl.
        split.
        reflexivity.
        split.
        unfold cyclic_path; 
        simpl; split. 
        intro H; congruence.
        split. apply refN. 
        exact Hauv.
        split.
        reflexivity.
        repeat rewrite refN.
        rewrite refR.
        apply triple_elem_eq_list_refl.
        simpl in Ha.
        case (elem_path_triple_tail au l) eqn:Hel.
        simpl in Ha.
        exists [], au, av, aw,
        (keep_collecting au l),
        (keep_dropping au l).
        simpl.
        repeat split;
        try reflexivity.
        congruence.
        unfold source;
        apply refN.
        destruct (elem_path_triple_tail_true l au Hel) as 
        (ll & aut & awt & lrt & Hb & Hc & Hd).
        (* From Hd, 
          Hd: triple_elem_list (ll ++ [(aut, au, awt)]) (keep_collecting au l) = true,
          we can infer that target au (au, av, aw) :: keep_collecting au l) = true *)
        erewrite target_keep_collect_rewrite. 
        reflexivity.
        apply triple_elem_eq_list_sym.
        exact Hd.
        eapply target_tail.
        simpl.
        rewrite target_end.
        simpl. 
        apply refN.
        repeat rewrite refN.
        rewrite refR.
        rewrite keep_collecting_dropping_dual.
        reflexivity.
        (* Inductive case *)
        simpl in Ha.
        destruct (IHl Ha) as 
        (ll & aut & avt & awt & lmt & lrt & Hb & Hc & Hd & He).
        destruct (elem_path_triple_compute_loop_triple l) as 
        ((bu, bv), bw).
        exists ((au, av, aw) :: bu),
        aut, avt, awt, lmt, bw.
        split.
        f_equal.
        f_equal.
        inversion Hb;
        reflexivity.
        split.
        exact Hc.
        split.
        simpl.
        rewrite Hauv.
        simpl.
        (* This one is also tricky *)
        destruct(elem_path_triple_tail_false
         _ _ _ _ Hel He) as [Helt Hert].
        inversion Hb; subst.
        rewrite Helt, Hd.
        reflexivity.
        simpl.
        repeat (rewrite refN).
        rewrite refR.
        simpl.
        simpl in He.
        inversion Hb;
        subst.
        exact He.
    Qed.


    (* if you give me path of length >= finN then there is loop *)
    Lemma all_paths_in_klength_paths_cycle_finN_stronger : 
      forall (l : list (Node * Node * R)) m,
      (List.length finN <= List.length l)%nat ->
      well_formed_path_aux m l = true ->
      exists ll au av aw lm lr, 
      (ll, Some ((au, av, aw) :: lm), lr) = 
      elem_path_triple_compute_loop_triple l /\ 
      cyclic_path au ((au, av, aw) :: lm) /\  (* Loop so we can remove this *)
      elem_path_triple ll = true /\ (* Elementry Path *)
      triple_elem_list l (ll ++  ((au, av, aw) :: lm) ++ lr) = true. 
      (* lr is the rest of path *)
    Proof.
      intros ? ? Hfin Hw.
      pose proof length_collect_node_gen finN 
        l empN Hfin as Hf.
      pose proof covers_list_elem finN 
        (collect_nodes_from_a_path l) memN as Hcov.
      pose proof all_paths_in_klength_paths_cycle
        finN l m Hw Hcov Hf as Hwt.
      eapply triple_compute_connect_with_triple_elem_stronger.
      exact Hwt.
    Qed.
    

    Lemma cycle_path_dup_remove : 
      forall ll lm lr, 
      (forall a : R, 1 + a =r= 1 = true) ->
      Orel 
        (measure_of_path (ll ++ lr))
        (measure_of_path (ll ++ lm ++ lr)). 
    Proof.
      intros * zero_stable.
      unfold Orel.
      assert (Ht : (measure_of_path (ll ++ lr) + measure_of_path (ll ++ lm ++ lr) =r=
        measure_of_path (ll ++ lr)) = 
        ((measure_of_path ll * measure_of_path lr) + 
         (measure_of_path ll * (measure_of_path lm * measure_of_path lr)) =r= 
         (measure_of_path ll * measure_of_path lr))).
      apply congrR.
      apply congrP.
      apply path_split_measure;
      apply triple_elem_eq_list_refl.
      rewrite <- (path_split_measure (ll ++ lm ++ lr)
        ll (lm ++ lr) (triple_elem_eq_list_refl (ll ++ lm ++ lr))). 
      apply congrR.
      apply refR.
      apply congrM.
      apply refR.
      apply symR.
      apply path_split_measure;
      apply triple_elem_eq_list_refl.
      apply path_split_measure;
      apply triple_elem_eq_list_refl.
      rewrite Ht; clear Ht.
      remember (measure_of_path ll) as a.
      remember (measure_of_path lm) as b.
      remember (measure_of_path lr) as c.
      assert (Ht : (a * c + a * (b * c) =r= a * c) = 
        (a * c + a * b * c =r= a * c)).
      apply congrR.
      apply congrP.
      apply refR.
      apply mul_associative.
      apply refR.
      rewrite Ht; clear Ht.
      apply path_weight_rel.
      apply zero_stable.
    Qed.
      
    

   
    

    Definition zwf (x y : list (Node * Node * R)) := 
        (List.length x < List.length y)%nat.

    Lemma zwf_well_founded : well_founded zwf.
    Proof.
      exact (Wf_nat.well_founded_ltof _ 
        (fun x => List.length x)).
    Defined.
    

     

    (* easy proof List.length finN <= List.length l -> loop *)
    Lemma elem_path_length : 
      forall (l : list (Node * Node * R)) m, 
      elem_path_triple l = true ->
      well_formed_path_aux m l = true -> 
      (List.length l < List.length finN)%nat.
    Proof.
      intros l m He Hw.
      assert (Hwt : (length l < length finN)%nat \/ 
      (length finN <= length l)%nat).
      nia.
      destruct Hwt as [Hwt | Hwt].
      exact Hwt.
      pose proof length_collect_node_gen finN 
      l empN Hwt as Hf.
      pose proof covers_list_elem finN 
        (collect_nodes_from_a_path l) memN as Hcov.
      pose proof all_paths_in_klength_paths_cycle
        finN l m Hw Hcov Hf as Hat.
      rewrite Hat in He.
      congruence.
    Qed.

      

    Lemma triple_elem_eq : 
      forall bl lrt, 
      triple_elem_list bl lrt = true ->
      (length lrt < S (S (length bl)))%nat.
    Proof.
      (* proof by nia? *)
      induction bl as [|((bau, bav), baw) bl].
      + intros [|((aau, aav), aaw) lrt].
        intros Ha.
        simpl.
        nia.
        intros Ha.
        simpl in Ha.
        congruence.
      + intros [|((aau, aav), aaw) lrt].
        intros Ha.
        simpl.
        nia.
        intros Ha.
        simpl in Ha.
        simpl.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        specialize (IHbl _ Ha).
        nia.
    Qed.


    Lemma triple_elem_rewrite_le : 
      forall bl llt awt lrt, 
      triple_elem_list bl (llt ++ [awt] ++ lrt) = true ->
      (length lrt < S (length bl))%nat.
    Proof.
      induction bl as [|((bau, bav), baw) bl].
      + simpl.
        intros * Ha.
        assert (Hlt : exists avt llw, llt ++ awt :: lrt = avt :: llw).
        destruct llt.
        simpl.
        exists awt, lrt.
        reflexivity.
        simpl.
        exists p, (llt ++ awt :: lrt).
        reflexivity.
        destruct Hlt as [avt [llw Hlw]].
        rewrite Hlw in Ha.
        congruence.
      + 
        intros * Ha.
        simpl.
        destruct llt as [|((llta, lltb), lltc) llt].
        simpl in Ha.
        destruct awt as ((awta, awtb), awtc).
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        eapply triple_elem_eq.
        exact Ha.
        simpl in Ha.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        specialize (IHbl _ _ _ Ha).
        nia.
    Qed.

    

    (* I can take any path l and turn it into elementry path 
      by keep applying *)
    Lemma reduce_path_into_elem_path : 
      forall (l : list (Node * Node * R)) m,
      mat_cong m -> 
      well_formed_path_aux m l = true ->
      exists lm, 
        well_formed_path_aux m lm = true /\ 
        elem_path_triple lm = true.
    Proof.
      intros l.
      induction (zwf_well_founded l) as [l Hf IHl].
      unfold zwf in * |- *.
      intros ? Hm Hw.
      (* check if list is empty of not empty *)
      destruct l as [|((au, av), aw) l].
      + simpl.
        exists [].
        repeat split.
      + (*  *)
        destruct l as [|((bu, bv), bw) l].
        - simpl.
          case (au =n= av) eqn:Hauv.
          exists [].
          repeat split.
          simpl.
          exists [(au, av, aw)].
          simpl.
          repeat split.
          simpl in Hw.
          exact Hw.
          rewrite Hauv.
          reflexivity.
        - (* l is non-empty *)
          remember ((bu, bv, bw) :: l) as bl.
          simpl in Hw.
          rewrite Heqbl in Hw.
          rewrite <-Heqbl in Hw.
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hwl Hw].
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hw Hwr].
          case (au =n= av) eqn:Hauv.
          (* There is a loop of length 1 
          at the front. Discard it and call 
          the function/Induction hypothesis
          on the remaining list. *)
          assert (Hwt : (length bl < length ((au, av, aw) :: bl))%nat).
          simpl. nia.
          destruct (IHl bl Hwt m Hm Hwr) as 
          (lm & Hwe & He).
          exists lm.
          repeat split.
          exact Hwe.
          exact He.
          (* au <> av but au can appear inside bl *)
          case (elem_path_triple_tail au bl) eqn:Heab.
          destruct (elem_path_triple_tail_true bl _ Heab) as 
          (llt & aut & awt & lrt & Ha & Hb & Hc).
          (* discard (llt ++ [(aut, au, awt)]) and 
            call the recursive function on lrt *)
          assert (Hd : well_formed_path_aux m lrt = true).
          pose proof well_formed_path_rewrite _ _ m Hm 
            Hwr Ha as Hwf.
          rewrite List.app_assoc in Hwf.
          destruct (well_formed_path_snoc _ _ _ 
            Hwf) as [Hwfl Hwfr].
          exact Hwfr.
          assert(Hwt : (length lrt < length ((au, av, aw) :: bl))%nat).
          simpl.
          eapply triple_elem_rewrite_le.
          exact Ha.
          destruct (IHl lrt Hwt m Hm Hd) as 
          (lm & Hwe & He).
          exists lm. 
          split.
          exact Hwe.
          exact He.
          (* no loop at the head so continue *)
          assert (Hwt : (length bl < length ((au, av, aw) :: bl))%nat).
          simpl. nia.
          destruct (IHl bl Hwt m Hm Hwr) as 
          (lm & Hwe & He).
          exists lm. 
          split.
          exact Hwe.
          exact He.
    Qed.


    (* Section 3.2 Network Tracks 
      Every elementry path  
      measuare μ* <= measure μ  
    *)
    (* This is going to be tricky proof *)
    Lemma reduce_path_into_elem_path_orel : 
      forall (l : list (Node * Node * R)) m,
      (forall a : R, 1 + a =r= 1 = true) ->
      mat_cong m -> 
      well_formed_path_aux m l = true ->
      exists lm, 
        Orel (measure_of_path lm) (measure_of_path l).
    Proof.
      intro l. 
      induction (zwf_well_founded l) as [l Hf IHl].
      unfold zwf in * |- *.
      intros ? zero_stable Hm Hw.
      (* check if list is empty of not empty *)
      destruct l as [|((au, av), aw) l].
      + exists [].
        simpl.
        apply orel_refl.
      + destruct l as [|((bu, bv), bw) l].
        - simpl.
          case (au =n= av) eqn:Hauv.
          (* unit loop *)
          exists [].
          simpl.
          unfold Orel.
          apply zero_stable.
          (* no unit loop *)
          exists [(au, av, aw)].
          simpl.
          apply orel_refl.
        - (* l is non-empty *)
          remember ((bu, bv, bw) :: l) as bl.
          simpl in Hw.
          rewrite Heqbl in Hw.
          rewrite <-Heqbl in Hw.
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hwl Hw].
          apply Bool.andb_true_iff in Hw.
          destruct Hw as [Hw Hwr].
          case (au =n= av) eqn:Hauv.
          (* loop at the front sos discard it *)
          assert (Hwt : (length bl < length ((au, av, aw) :: bl))%nat).
          simpl. nia.
          destruct (IHl bl Hwt m zero_stable Hm Hwr) as 
          (lm & Ho).
          exists lm.
          simpl.
          unfold Orel.
          unfold Orel in Ho.
          pose proof path_weight_rel 
            1 (aw * measure_of_path bl) 
            (measure_of_path lm) zero_stable.
          unfold Orel in H.
          (* Appears true *)
          admit.
          (* au <> av but au can appear inside bl *)
          case (elem_path_triple_tail au bl) eqn:Heab.
          destruct (elem_path_triple_tail_true bl _ Heab) as 
          (llt & aut & awt & lrt & Ha & Hb & Hc).
          (* discard (llt ++ [(aut, au, awt)]) and 
            call the recursive function on lrt *)
          assert (Hd : well_formed_path_aux m lrt = true).
          pose proof well_formed_path_rewrite _ _ m Hm 
            Hwr Ha as Hwf.
          rewrite List.app_assoc in Hwf.
          destruct (well_formed_path_snoc _ _ _ 
            Hwf) as [Hwfl Hwfr].
          exact Hwfr.
          assert(Hwt : (length lrt < length ((au, av, aw) :: bl))%nat).
          simpl.
          eapply triple_elem_rewrite_le.
          exact Ha.
          destruct (IHl lrt Hwt m zero_stable Hm Hd) as 
          (lm & Ho).
          exists lm.
          unfold Orel in * |- *.
          admit.
          (* no loop at the head so continue *)
          assert (Hwt : (length bl < length ((au, av, aw) :: bl))%nat).
          simpl. nia.
          destruct (IHl bl Hwt m zero_stable Hm Hwr) as 
          (lm & Ho).
          exists lm.
          simpl.
          unfold Orel in * |- *.
          simpl.
    Admitted. 


          




    (* Every well formed path can be reduced into 
      an well formed elementry path, i.e., path 
      without loop and it's length < finN *)
    Lemma reduce_path_into_elem_path_gen : 
      forall (l : list (Node * Node * R)) m,
      mat_cong m -> 
      well_formed_path_aux m l = true ->
      exists lm, 
        well_formed_path_aux m lm = true /\ 
        elem_path_triple lm = true /\ 
        (List.length lm < List.length finN)%nat.
    Proof.
      intros ? ? Hm Hw.
      destruct (reduce_path_into_elem_path l m Hm Hw) 
      as (lm & Hwa & Hwe).
      pose proof (elem_path_length lm m Hwe Hwa) as Hp.
      exists lm.
      repeat split; try assumption.
    Qed.

    
    (* Now, we know that every path coming out of 
      all_paths_klenght has a loop in the end.  
    *)
    Lemma path_end_loop : 
      forall k l m c d, 
      In_eq_bool l (all_paths_klength m k c d) = true ->
      exists l', 
        triple_elem_list l (l' ++ [(d, d, 1)]) = true.   
    Proof.
      induction k.
      + simpl. 
        intros ? ? ? ? Hin.
        case (c =n= d) eqn:Hcd.
        exists [].
        simpl.
        destruct l as [|((au, av), aw) l].
        simpl in Hin;
        congruence.
        destruct l as [|((bu, bv), bw) l].
        simpl in * |- *.
        rewrite Bool.orb_false_r in Hin.
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin _].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hin Hinr].
        apply Bool.andb_true_iff in Hin.
        destruct Hin as [Hinl Hinrr].
        rewrite (trnN _ _ _ Hinl Hcd),
        Hinrr, Hinr; reflexivity.
        simpl in Hin.
        rewrite Bool.orb_false_r, 
          Bool.andb_false_r in Hin.
        congruence.
        simpl in Hin.
        congruence.
      + simpl. 
        intros ? ? ? ? Hin.
        destruct (append_node_in_paths_eq
          (flat_map (λ x : Node, all_paths_klength m k x d) finN)
          m c l Hin) as [y [ys [Hl Hr]]].
        pose proof append_node_rest _ _ _ _ 
          Hin as Hap.
        destruct (in_flat_map_bool_first _ _ _ 
          Hap) as (x & Hf & Heb).
        simpl in Heb.
        destruct (IHk _ _ _ _ Heb) as 
        (l' & Hte).
        exists ((c, y, m c y) :: l').
        simpl.
        destruct l as [|((au, av), aw) l].
        simpl in Hl;
        congruence.
        simpl in Hl, Hte.
        simpl.
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlrr].
        apply Bool.andb_true_iff in Hl.
        destruct Hl as [Hl Hlrrr].
        rewrite Hl, Hlrrr, Hlrr.
        simpl.
        exact Hte.
    Qed.
    
    




    (* What do we get from this? 
      Well, we can reduce every path of lenght >= finN 
      into a path of length < finN. 


     Fixpoint partial_sum_paths (m : Matrix) (n : nat) (c d : Node) : R :=
      match n with
      | O => I c d
      | S n' =>  partial_sum_paths m n' c d + 
        sum_all_rvalues (get_all_rvalues (construct_all_paths m n c d))
      end.
      
    For any n, >= finN > 0, we can write 
    partial_sum_paths (m : Matrix) (n : nat) (c d : Node) :=
    partial_sum_paths (m : Matrix) (n' : nat) (c d : Node) + 
    sum_all_rvalues (get_all_rvalues (construct_all_paths m n c d)).

    But we know that for any path of of length >= finN, 
    there is a loop and we can reduce this path to an
    elementry path < finN. It means we can reduce all the 
    paths in (construct_all_paths m n c d) to an elementry 
    path that would be the member of (construct_all_paths m k c d),
    for some k < finN. 
    Loop reduction : 1 + a = a 
    Plus idempotence : a + a = a 
    would lead to the proof of 

    Lemma zero_stable_partial_sum_path : forall k m,
      (forall a : R, 1 + a =r= 1 = true) ->
      mat_cong m -> 
      (forall (c d : Node), 
        partial_sum_paths m (length finN - 1) c d =r= 
        partial_sum_paths m (k + length finN - 1) c d = true).
    *)


    (* 
    
    The idea I have right now is:
    Take any arbitrary path xs, reduce it to ys and 
    add a unit loop [(d, d, 1)] in the end of ys,
    show that (ys ++ [(d, d, 1)]) is an element 
    of all_paths_klength m (length ys) c d).
    Also, we can say that 
    measure (ys ++ [(d, d, 1)]) =r=
    measure ys because 1 + a =r= 1. 
    *)
    

    Lemma elem_path_membership : 
      forall l l' m c d,
      (* all_paths_well_formed_in_kpaths 
      (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> *)
      mat_cong m -> 
      triple_elem_list l (l' ++ [(d, d, 1)]) = true ->
      source c l = true ->
      target d l = true ->
      well_formed_path_aux m l = true ->
      In_eq_bool l (all_paths_klength m (List.length l') c d) = true.
    Proof.
      induction l as [|((au, av), aw) l].
      + intros * Hm Hte Hs Ht Hw.
        simpl in *.
        congruence.
      + intros * Hm Hte Hs Ht Hw.
        destruct l as [|((bu, bv), bw) l].
        - (* l is one element list and it 
          implies that l' is empty *)
          assert (Hlt: l' = []).
          destruct l' as [|((cu, cv), cw) l'].
          reflexivity.
          simpl in Hte.
          admit.
          rewrite Hlt in Hte.
          simpl in Hte.
          rewrite Hlt.
          simpl.
          simpl in *.
          admit.
        - (* ls has more than one element and it implies that 
          l' is not empty *) 
          assert (Htw : exists lt, 
            triple_elem_list  (l' ++ [(d, d, 1)])
              ((au, av, aw) :: lt ++ [(d, d, 1)]) = true /\ 
            triple_elem_list (lt ++ [(d, d, 1)])
              ((bu, bv, bw) :: l) = true).
          admit.
          destruct Htw as (lt & Ha & Hb).
          assert (Hlt : length l' = S (length lt)).
          admit.
          rewrite Hlt.
          simpl.
          remember ((bu, bv, bw) :: l) as bl.
          simpl in Hs.
          simpl in Hw.
          rewrite Heqbl in Hw.
          rewrite <-Heqbl in Hw.
          (* 
            I need to infer that 
            In_eq_bool bl 
              (all_path_klength m (length lt) bu d)
          *)
          apply triple_elem_eq_list_sym in Hb.
          specialize (IHl lt m bu d Hm Hb).
          assert (Hst : source bu bl = true).
          rewrite Heqbl; simpl;
          rewrite refN; reflexivity.
          assert (Hdt : target d bl = true).
          admit.
          
    Admitted.








    Lemma reduce_path : 
      forall n m c d,
      (forall a : R, 1 + a =r= 1 = true) -> 
      (length finN <= n)%nat -> 
      forall xs, In_eq_bool xs (all_paths_klength m n c d) = true ->
      exists k ys, 
        (k < length finN)%nat /\ 
        In_eq_bool ys (all_paths_klength m k c d) = true.
    Proof.
    Admitted.



    



  
     

        


    
    
  
   
    (*
    I need something like this: 
    Lemma reverse_rewrite :
      forall n m c d,
      (forall a : R, 1 + a =r= 1 = true) ->
      (List.length finN <= n)%nat -> 
      exists (kl : list nat),
        sum_all_rvalues (get_all_rvalues (construct_all_paths m n c d)) =r= 
        sum_all_rvalues (List.map (fun k => get_all_rvalues (construct_all_paths m k c d)) kl) = true.
    Proof.
    Admitted.
    *)



    Lemma zero_stable_partial_sum_path : forall k m,
      (forall a : R, 1 + a =r= 1 = true) ->
      mat_cong m -> 
      (forall (c d : Node), 
        partial_sum_paths m (length finN - 1) c d =r= 
        partial_sum_paths m (k + length finN - 1) c d = true).
    Proof.

      induction k.
      + simpl.
        intros ? Ha Hm ? ?.
        apply refR.
      + simpl. 
        intros ? Ha Hm ? ?.
        specialize (IHk m Ha 
          Hm c d).
        rewrite PeanoNat.Nat.sub_0_r.

        rewrite <-IHk.
        apply congrR.
        apply refR.
        apply symR.
    Admitted.


  
    (* This can be proved using the 
       (i) connect_partial_sum_mat_paths and 
       (ii) zero_stable_partial_sum_path *)

    Lemma zero_stable_partial : forall m,
      (forall a : R, 1 + a =r= 1 = true) ->
      mat_cong m -> 
      (forall (c d : Node), 
        partial_sum_mat m (length finN - 1) c d =r= 
        partial_sum_mat m (length finN) c d = true).
    Proof.
      intros * zero_stable Hm ? ?.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN - 1) m c d Hm).
      apply congrR.
      apply refR.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN) m c d Hm).
      apply congrR.
      apply refR.
      pose proof zero_stable_partial_sum_path
        1 m zero_stable Hm c d as Ht.
      assert (Hwt: (1 + length finN - 1 = length finN)%nat).
      nia.
      rewrite Hwt in Ht;
      clear Hwt.
      exact Ht.
    Qed.
      




    Lemma matrix_fx : forall (m : Matrix) (s : R) (c d : Node),
      mat_cong m ->
      (forall a : R, 1 + a =r= 1 = true) -> 
      matrix_exp_unary (m +M I) (length finN) c d =r= s = true ->
      exists k, (k < length finN )%nat/\ 
      matrix_exp_unary (m +M I) k c d =r= s = true.
    Proof.
      intros * Hc Ha Hm.
      exists (length finN - 1)%nat.
      split.
      destruct finN.
      congruence.
      simpl; lia.
      assert (Hv : partial_sum_mat m (length finN) c d =r= s = true).
      rewrite <-Hm.
      apply congrR; apply symR.
      apply matrix_pow_idempotence.
      exact Hc.
      apply refR.
      pose proof (matrix_pow_idempotence (length finN - 1) m c d Hc) as Hr.
      rewrite <-Hr.
      apply congrR.
      apply refR.
      apply symR.
      rewrite <-Hv.
      apply congrR.
      eapply zero_stable_partial.
      exact Ha.
      exact Hc.
      apply refR.
    Qed.


      

   



    Lemma matrix_fixpoint : forall (n : nat) (m : Matrix) c d,
      mat_cong m ->
      (forall (c d : Node), 
        partial_sum_mat m (length finN) c d =r= 
        partial_sum_mat m (S (length finN)) c d = true) ->  
      matrix_exp_unary (m +M I) (List.length finN) c d =r= 
      matrix_exp_unary (m +M I) (n + List.length finN) c d = true.
    Proof using Node R congrM congrP congrR dupN empN eqN eqR finN
    left_distributive_mul_over_plus memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR right_distributive_mul_over_plus
    symN symR trnN trnR zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros ? ? ? ? Hm q_stable.
      apply symR.
      assert (Ht:
      (matrix_exp_unary (m +M I) (n + length finN) c d =r=
      matrix_exp_unary (m +M I) (length finN) c d) =
      (partial_sum_mat m (n + length finN) c d =r=
      partial_sum_mat m (length finN) c d)).
      apply congrR.
      apply matrix_pow_idempotence; exact Hm.
      apply matrix_pow_idempotence; exact Hm.
      rewrite Ht; clear Ht.
      apply astar_exists_gen_q_stable_matrix.
      intros ut vt.
      apply q_stable.
    Qed.



    Fixpoint atmost_kpath (m : Matrix) (k : nat) (c d : Node) :=
      match k with 
      | 0%nat => if c =n= d then [[[(c, d, 1)]]] else []
      | S k' => (all_paths_klength m k c d) ::
         atmost_kpath m k' c d
      end.



    (* Compute X := A * X + B. But it's 
       not constant space.

    *)
    Fixpoint left_matrix_iteration (n : nat) 
      (A : Matrix) : Matrix :=
      match n with
      | O => I
      | S n' => A *M (left_matrix_iteration n' A) +M I 
      end. 


    Fixpoint right_matrix_iteration (n : nat) 
      (A : Matrix)
      : Matrix :=
      match n with
      | O => I 
      | S n' => (right_matrix_iteration n' A) *M A +M I 
      end.

    









End Matrix.

(* 
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

  
  Eval compute in  elem_path node eqN Z [(A, B, 1%Z); (B, A, 2%Z)].
  Eval compute in elem_path_triple_compute_loop  node eqN Z [(A, C, 2%Z); (C, B, 1%Z); (B, C, 1%Z)].
  Eval compute in elem_path_triple_aux node eqN Z D [(C, B, 1%Z); 
  (B, B, 1%Z); (B, A, 2%Z); (A, C , 1%Z)].
  Eval compute in elem_path_triple_compute_loop  node eqN Z [(C, B, 1%Z); 
  (B, B, 1%Z); (B, A, 2%Z); (A, C , 1%Z)].
  Eval compute in elem_path_triple_tail node eqN Z C [ 
  (B, B, 1%Z); (B, A, 2%Z); (A, C , 1%Z)].
  Eval compute in keep_collecting node eqN Z C [ 
    (B, B, 1%Z); (B, A, 2%Z); (A, C , 1%Z); (C, D, 2%Z)].

  Eval compute in keep_collecting node eqN Z A [(B, A, 2%Z)].
  Eval compute in elem_path_triple node eqN Z [(A, B, 1%Z); (B, A, 2%Z)].
  Eval compute in collect_nodes_from_a_path _ Z [(A, B, 1%Z); (B, A, 2%Z); (A, D, 3%Z)].
  Eval compute in (construct_path_from_nodes _ Z [A; B; A] m ++ 
    construct_path_from_nodes _ Z [A; D] m).
  Eval compute in collect_nodes_from_a_path _ Z [(A, A, 1%Z)].

  
End Ins. 
*)

          














    
    




