


(* Print Grammar constr. *)
  Local Infix "+M" := matrix_add (at level 50) : Mat_scope.
  Local Infix "*M" := matrix_mul (at level 40) : Mat_scope.

  Fixpoint partial_sum_mat (m : Matrix Node R) (n : nat) : Matrix Node R :=
    match n with
    | O => I 
    | S n' => (partial_sum_mat m n') +M (matrix_exp_unary m n)
    end.

  
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


      Lemma exp_r_pow_add : 
      forall (n m : nat) (a : R), 
      exp_r _ 1 mulR a (n + m) =r= 
      exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m.
    Proof using R congrM congrR eqR mulR mul_associative oneR
    one_left_identity_mul refR symR.
      induction n.
      - simpl; intros ? ?.
        apply symR. 
        apply one_left_identity_mul.
      - simpl; intros ? ?.
        apply symR.
        assert (Ht : (a * exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m =r= 
          a * exp_r  _ 1 mulR a (n + m)) =
          (a * (exp_r  _ 1 mulR a n * exp_r  _ 1 mulR a m) =r= a * exp_r  _ 1 mulR a (n + m))).
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

    Lemma astar_aide_zero_stable : 
      forall (t : nat) (a : R),
      partial_sum_r R 1 plusR mulR a t + a * exp_r  _ 1 mulR a t =r=
      partial_sum_r R 1 plusR mulR a t.
    Proof using R congrM congrP congrR eqR mulR oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative refR
    right_distributive_mul_over_plus symR zero_stable.
      induction t.
      - simpl; intros ?. 
        rewrite <-(zero_stable a).
        apply congrR.
        apply congrP.
        apply refR.
        apply one_right_identity_mul.
        apply refR.
      - simpl; intros ?. 
      assert (Ht:
      (partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR a t + a * (a * exp_r R 1 mulR a t) =r=
      partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR a t) =
      (partial_sum_r R 1 plusR mulR a t + (a * exp_r R 1 mulR a t + a * (a * exp_r R 1 mulR a t)) =r=
      partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR a t)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Ht; clear Ht.
      apply congrP.
      apply refR.
      remember (a * exp_r R 1 mulR a t) as aw.
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
    Lemma astar_exists_zero_stable : 
      forall (t : nat) (a : R), 
      partial_sum_r R 1 plusR mulR a t =r= partial_sum_r R 1 plusR mulR a 0.
    Proof using R congrM congrP congrR eqR mulR oneR one_left_identity_mul
    one_right_identity_mul plusR plus_associative refR
    right_distributive_mul_over_plus symR zero_stable.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        rewrite <-(astar_aide_zero_stable t a).
        apply congrR.
        apply refR.
        simpl in IHt.
        apply symR.
        exact (IHt a).
    Qed.




    Lemma astar_aide_gen_q_stable :
      forall (t : nat) (a : R),
      (partial_sum_r R 1 plusR mulR a (S t)) =r= 
      (1 + a * partial_sum_r R 1 plusR mulR a t).
    Proof using R congrP congrR eqR
    left_distributive_mul_over_plus mulR oneR plusR
    plus_associative refR symR.
      induction t.
      - simpl; intros ?.
        apply refR.
      - simpl; intros ?.
        simpl in IHt.
        assert (Ht : 1 + a * (partial_sum_r R 1 plusR mulR a t + a * exp_r R 1 mulR  a t) =r=
          (1 + (a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR  a t)))).
        apply congrP. apply refR.
        apply left_distributive_mul_over_plus.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        assert (Ht : partial_sum_r R 1 plusR mulR a t + 
          a * exp_r R 1 mulR  a t + a * (a * exp_r R 1 mulR  a t) =r=
          1 + a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR  a t)).
        apply congrP.
        apply IHt. apply refR.
        rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        assert (Ht : 1 + a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR a t) =r= 
          1 +  (a * partial_sum_r R 1 plusR mulR a t + a * (a * exp_r R 1 mulR a t))).
        apply symR. apply plus_associative.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply refR.
    Qed.
        

    
    Lemma astar_exists_gen_q_stable : 
      forall (q : nat),
      (forall w : R, partial_sum_r R 1 plusR mulR w q =r= 
        partial_sum_r R 1 plusR mulR w (S q)) -> 
      forall (t : nat) (a : R), 
      partial_sum_r R 1 plusR mulR a (t + q) =r= 
      partial_sum_r R 1 plusR mulR a q.
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
        assert (Ht : 1 + a * partial_sum_r R 1 plusR mulR a (t + q) =r= 
          1 + a * partial_sum_r R 1 plusR mulR a q).
        apply congrP. apply refR. 
        apply congrM. apply refR.
        apply IHt.
        apply symR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        pose proof (astar_aide_gen_q_stable q a) as Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply q_stable.
        apply refR.
    Qed.

    

      



    Lemma astar_aide_gen_q_stable_matrix :
      forall (t : nat) (m : Matrix Node R) (c d : Node),
      (partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S t) c d) =r= 
      (I Node eqN R 0 1 +M 
      m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m t) c d.
    Proof using Node R congrM congrP congrR dupN eqN eqR
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
        remember (partial_sum_mat Node eqN finN R 0 1 plusR mulR m t) as pmt.
        remember (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m t) as umt.
        assert (Ht : ((pmt +M m *M umt) +M m *M (m *M umt)) c d =r=
          ((I Node eqN R 0 1 +M m *M pmt) +M m *M (m *M umt)) c d).
        apply mat_add_cong_gen.
        unfold matrix_equality;
        intros u v. 
        simpl in IHt.
        pose proof (IHt m u v) as IHs.
        rewrite <-Heqpmt in IHs.
        rewrite <-Hequmt in IHs.
        exact IHs.
        unfold matrix_equality; intros a b.
        apply refR.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply symR.
        assert (Ht : ((I Node eqN R 0 1 +M m *M pmt) +M m *M (m *M umt)) c d =r= 
          (I Node eqN R 0 1 +M (m *M pmt +M m *M (m *M umt))) c d).
        apply symR.
        apply matrix_add_assoc.
        rewrite <-Ht; clear Ht.
        apply congrR.
        apply refR.
        apply symR.
        apply mat_add_cong_gen.
        unfold matrix_equality; intros a b.
        apply refR.
        unfold matrix_equality; intros a b.
        apply symR.
        apply left_distributive_mat_mul_over_plus.
    Qed.



    Lemma astar_exists_gen_q_stable_matrix : 
      forall (q : nat) (m : Matrix Node R),
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m q c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S q) c d) -> 
      forall (t : nat)  (u v : Node), 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m (t + q) u v =r= 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m q u v.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
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
        unfold matrix_equality; intros a b.
        apply refR.
        unfold matrix_equality; intros a b.
        apply mat_mul_cong_diff.
        unfold matrix_equality; intros ut vt.
        specialize (IHt ut vt).
        exact IHt.
    Qed.



    Lemma partial_sum_mat_cong : forall n m,
      mat_cong Node eqN R eqR m ->  
      mat_cong Node eqN R eqR (partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m n).
    Proof using Node R congrM congrP eqN eqR finN 
    mulR oneR plusR refN refR symN trnN zeroR.
      unfold mat_cong.
      induction n.
      - simpl; intros ? ? ? ? ? Hm Hac Hbd.
        apply identity_cong; assumption.
      - simpl; intros ? ? ? ? ? HM Hac Hbd.
        remember (partial_sum_mat Node eqN finN 
        R zeroR oneR plusR mulR m n) as pmn.
        remember (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) as men.
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
    
    Lemma mat_mul_idem_ind : 
      forall n m c d,  
      (m *M partial_sum_mat Node eqN finN R zeroR oneR plusR mulR m n +M 
        partial_sum_mat Node eqN finN 
        R zeroR oneR plusR mulR m n) c d =r=
      (partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m (S n) c d).
    Proof using Node R congrP congrR eqN eqR finN left_distributive_mul_over_plus
    mulR oneR plusR plus_associative plus_commutative plus_idempotence refR symR
    zeroR zero_left_identity_plus.
      induction n.
      - simpl; intros ? ? ?.
        apply matrix_add_comm.
      - simpl; intros ? ? ?.
        pose proof (IHn m c d) as IHs.
        simpl in IHs.
        remember (partial_sum_mat Node eqN finN 
        R zeroR oneR plusR mulR m n) as m₁.
        remember (matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) as m₂.
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
      forall (n : nat) (m : Matrix Node R) 
      (c d : Node),
      mat_cong Node eqN R eqR m ->
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n c d =r= 
      partial_sum_mat Node eqN finN 
      R zeroR oneR plusR mulR m n c d.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus lenN memN mulR oneR one_left_identity_mul plusR
    plus_associative plus_commutative plus_idempotence refN refR
    right_distributive_mul_over_plus symN symR trnN zeroR zero_left_anhilator_mul
    zero_left_identity_plus zero_right_identity_plus.
      induction n.
      - simpl; intros ? ? ? Hm.
        apply refR.
      - simpl; intros ? ? ? Hm.
        pose proof (IHn m c d) as IHs.
        assert (Ht : 
        (((m +M I Node eqN R 0 1) *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          m *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d) =
        (((m +M I Node eqN R 0 1) *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          m *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d)).
        apply congrR.
        apply mat_mul_cong_diff.
        unfold matrix_equality; intros u v.
        exact (IHn m u v Hm).
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        (((m +M I Node eqN R 0 1) *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
          *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d) =
        (((m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          I Node eqN R 0 1 *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
        *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d))).
        apply congrR.
        apply right_distributive_mat_mul_over_plus.
        apply refR.
        rewrite Ht; clear Ht.
        assert (Ht : 
        ((m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M I Node eqN R 0 1 
          *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
          *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d) = 
        ((m *M partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M 
          partial_sum_mat Node eqN finN R 0 1 plusR mulR m n) c d =r=
        (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n +M m 
        *M matrix_exp_unary Node eqN finN R 0 1 plusR mulR m n) c d)).
        apply congrR.
        apply mat_add_cong_gen.
        unfold matrix_equality; intros u v.
        apply refR.
        unfold matrix_equality; intros u v.
        apply matrix_mul_left_identity.
        apply partial_sum_mat_cong; exact Hm.
        apply refR.
        rewrite Ht; clear Ht.
        apply mat_mul_idem_ind.
    Qed.

    
    Lemma connect_partial_sum_mat_paths : forall n m c d,
      mat_cong Node eqN R eqR m -> 
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d =r= 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d.
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
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR (m +M I Node eqN R 0 1) n c d =r= 
      partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d.
    Proof.
      intros * Hm.
      pose proof matrix_pow_idempotence n m c d Hm as Hp.
      pose proof connect_partial_sum_mat_paths n m c d Hm as Hpp.
      eapply trnR with (partial_sum_mat Node eqN finN R 0 1 plusR mulR m n c d); assumption.
    Qed.

    Lemma zero_stable_partial : forall m,
      mat_cong Node eqN R eqR m -> 
      (∀ u v : Node, (u =n= v) → (m u v =r= 1)) ->
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR  m (length finN - 1) c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR  m (length finN) c d).
    Proof.
      intros * Hm Huv ? ?.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN - 1) m c d Hm).
      apply congrR.
      apply refR.
      rewrite <-(connect_partial_sum_mat_paths
        (length finN) m c d Hm).
      apply congrR.
      apply refR.
      assert (Hwt: (1 + length finN - 1 = length finN)%nat).
      nia.
      rewrite <-Hwt at 2;
      clear Hwt.
      eapply zero_stable_partial_sum_path with (k := S O) (eqR := eqR)
        (Node := Node) (eqN := eqN) (R := R) (zeroR := 0)
        (oneR := 1) (plusR := plusR) (mulR := mulR)
        (finN := finN) (m := m) (c := c) (d := d);
      try assumption.
    Qed.

    Lemma matrix_fixpoint : forall (n : nat) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m ->
      (forall (c d : Node), 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (length finN) c d =r= 
        partial_sum_mat Node eqN finN R 0 1 plusR mulR m (S (length finN)) c d) ->  
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (List.length finN) c d =r= 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
      (m +M I Node eqN R 0 1) (n + List.length finN) c d.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus lenN memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative plus_idempotence refN refR right_distributive_mul_over_plus symN
    symR trnN trnR zeroR zero_left_anhilator_mul zero_left_identity_plus
    zero_right_anhilator_mul zero_right_identity_plus.
      intros ? ? ? ? Hm q_stable.
      apply symR.
      assert (Ht:
      (matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
        (m +M I Node eqN R 0 1) (n + length finN) c d =r=
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR 
        (m +M I Node eqN R 0 1) (length finN) c d) =
      (partial_sum_mat Node eqN finN R 0 1 plusR mulR m (n + length finN) c d =r=
      partial_sum_mat Node eqN finN R 0 1 plusR mulR m (length finN) c d)).
      apply congrR.
      apply matrix_pow_idempotence; exact Hm.
      apply matrix_pow_idempotence; exact Hm.
      rewrite Ht; clear Ht.
      apply astar_exists_gen_q_stable_matrix.
      intros ut vt.
      apply q_stable.
    Qed.

