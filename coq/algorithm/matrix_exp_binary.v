



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


    (* now prove that slow and fast computes the same value. *)
    Lemma binnat_zero : 
      forall (n : nat), 
      0%N = N.of_nat n -> 
      n = 0%nat.
    Proof.
      induction n; 
      try lia.
    Qed.

  
    Lemma binnat_odd : forall (p : positive) (n : nat), 
      N.pos (xI p) = N.of_nat n -> 
      exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. 
      destruct H as [k Hk].
      (* Even (impossible) Case *)
      rewrite Hk in Hp; lia.
      (* Odd (possible) case *)
      apply Even.odd_equiv in H. 
      destruct H as [k Hk].
      rewrite Hk in Hp. 
      exists k.
      split. 
      exact Hk. 
      lia.
    Qed.

    Lemma binnat_even : forall (p : positive) (n : nat), 
      N.pos (xO p) = N.of_nat n :> N -> 
      exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. 
      destruct H as [k Hk].
      (* Even (possible) case*)
      rewrite Hk in Hp. 
      exists k.
      split. 
      exact Hk. lia.
      (* Odd (impossible) case *)
      apply Even.odd_equiv in H. 
      destruct H as [k Hk].
      rewrite Hk in Hp. lia.
    Qed.

  

    Lemma push_out_e_unary_nat_gen : forall k1 k2 e c d,
      mat_cong Node eqN R eqR e -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR e (k1 + k2)  c d =r= 
      matrix_mul Node finN R 0 plusR mulR 
        (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k1) 
        (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k2) c d = true.
    Proof using Node R congrM congrP congrR dupN lenN eqN eqR finN
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
        assert (Ht : matrix_mul Node finN R 0 plusR mulR e 
            (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e (k1 + k2)) c d =r=
          matrix_mul  Node finN R 0 plusR mulR e 
            (matrix_mul Node finN R 0 plusR mulR
            (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k1) 
            (matrix_exp_unary Node eqN finN R 0 1 plusR mulR e k2)) c d = true).
        apply mat_mul_cong_diff. 
        unfold matrix_equality; intros.
        apply IHk1. 
        exact He.
        rewrite <-Ht; clear Ht.
        apply congrR. 
        apply refR.
        apply symR.
        apply matrix_mul_assoc.
    Qed.

  

   Lemma sum_fn_mat_ind : 
      forall l m₁ m₂ u v, 
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      sum_fn Node R 0 plusR (λ y : Node, m₁ u y * m₁ y v) l =r=
      sum_fn Node R 0 plusR (λ y : Node, m₂ u y * m₂ y v) l = true.
    Proof using Node R congrM congrP eqR mulR plusR refR zeroR.
      induction l; simpl; 
      intros  ? ? ? ? Hm.
      + apply refR.
      +
        apply add_r_cong.
        apply congrM. 
        apply Hm.
        apply Hm.
        apply IHl; assumption.
    Qed.


    Lemma mat_equal_ind : 
      forall m₁ m₂ u v,
      (forall c d, m₁ c d =r= m₂ c d = true) ->
      matrix_mul Node finN R 0 plusR mulR m₁ m₁ u v =r= 
      matrix_mul Node finN R 0 plusR mulR m₂ m₂ u v = true.
    Proof using Node R congrM congrP eqR finN mulR 
    plusR refR zeroR.
      intros ? ? ? ? Hcd.
      unfold matrix_mul, matrix_mul_gen.
      apply sum_fn_mat_ind.
      apply Hcd.
    Qed.


    Lemma matrix_exp_unary_binary_eqv : 
      forall (n : N) (m : Matrix Node R) c d,
      mat_cong Node eqN R eqR m -> 
      matrix_exp_unary Node eqN finN R 0 1 plusR mulR m (N.to_nat n) c d =r= 
      matrix_exp_binary Node eqN finN R 0 1 plusR mulR m n c d = true.
    Proof using Node R congrM congrP congrR dupN eqN eqR finN
    left_distributive_mul_over_plus lenN memN mulR mul_associative oneR
    one_left_identity_mul one_right_identity_mul plusR plus_associative
    plus_commutative refN refR right_distributive_mul_over_plus symN symR trnN zeroR
    zero_left_anhilator_mul zero_left_identity_plus zero_right_anhilator_mul
    zero_right_identity_plus.
      destruct n;
      intros ? ? ? Hm.
      + apply refR.
      + 
        assert (Hw : forall w, matrix_exp_binary Node eqN finN R 0 1 plusR mulR m (N.pos w) = 
          repeat_op_ntimes_rec Node finN R 0 plusR mulR m w).
        reflexivity.
        revert c d. 
        induction p.
        rewrite Hw in IHp. 
        rewrite Hw.
        - intros ? ?.
          assert (Ht : N.pos (xI p) = N.of_nat (N.to_nat (N.pos (xI p)))).
          rewrite Nnat.N2Nat.id; reflexivity.
          destruct (binnat_odd p (N.to_nat (N.pos (xI p))) Ht) as 
            [k [Ha Hb]].
          rewrite Ha. 
          rewrite Hb in IHp.
          rewrite Nnat.Nat2N.id in IHp.
          assert (Hv : (2 * k + 1 = 1 + k + k)%nat).
          lia. 
          rewrite Hv; clear Hv.
          simpl. 
          apply mat_mul_cong_diff.
          unfold matrix_equality; intros u v.
          pose proof push_out_e_unary_nat_gen k k m 
            u v Hm as Htt.
          rewrite <- Htt.
          apply congrR. 
          apply refR.
          apply mat_equal_ind.
          intros. 
          apply symR. 
          apply IHp.
        - intros ? ?. 
          rewrite Hw in IHp. 
          rewrite Hw.
          assert (Ht : N.pos (xO p) = N.of_nat (N.to_nat (N.pos (xO p)))).
          rewrite Nnat.N2Nat.id; reflexivity.
          destruct (binnat_even p (N.to_nat (N.pos (xO p))) Ht) as 
            [k [Ha Hb]].
          rewrite Ha. 
          rewrite Hb in IHp.
          rewrite Nnat.Nat2N.id in IHp.
          assert (Hv : (2 * k = k + k)%nat).
          lia. 
          rewrite Hv; clear Hv.
          simpl.
          pose proof push_out_e_unary_nat_gen k k m 
            c d Hm as Htt.
          rewrite <- Htt; clear Htt.
          apply congrR. 
          apply refR.
          apply mat_equal_ind.
          intros. 
          apply symR. 
          simpl in IHp.
          apply IHp.
        - intros ? ?. 
          simpl.
          apply matrix_mul_right_identity.
          exact Hm.
    Qed.
