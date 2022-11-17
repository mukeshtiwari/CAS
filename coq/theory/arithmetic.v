Require Import Coq.Init.Datatypes.
From CAS Require Import coq.common.compute. 
  



Section NatArithmetic.
  Open Scope nat_scope.
  
  Lemma brel_eq_nat_u_Su : ∀ u,  brel_eq_nat u (Datatypes.S u) = false.
  Proof. induction u. reflexivity. simpl. exact IHu.  Qed.

  Lemma brel_eq_nat_Su_u : ∀ u,  brel_eq_nat (Datatypes.S u) u = false.
  Proof. induction u. reflexivity. simpl. exact IHu.  Qed.

  Lemma ltb_to_lt : ∀ n m, Nat.ltb n m = true -> n < m.
  (* Note: PeanoNat.Nat.ltb_lt: ∀ n m : nat, PeanoNat.Nat.ltb n m = true ↔ n < m *)  
  Proof. apply PeanoNat.Nat.ltb_lt. Qed.

  Lemma lt_to_ltb : ∀ n m, n < m -> Nat.ltb n m = true.
  Proof. apply PeanoNat.Nat.ltb_lt. Qed.

  Lemma eqb_to_eq : ∀ n m, brel_eq_nat n m = true -> n = m.
  (* Note: PeanoNat.Nat.eqb_eq: ∀ n m : nat, PeanoNat.Nat.eqb n m = true ↔ n = m *)  
  Proof. apply PeanoNat.Nat.eqb_eq. Qed. 

  Lemma eq_to_eqb : ∀ n m, n = m -> brel_eq_nat n m = true. 
  Proof. apply PeanoNat.Nat.eqb_eq. Qed.

  (* a ltb version of 
     PeanoNat.Nat.nlt_succ_diag_l: ∀ n : nat, ¬ Datatypes.S n < n
 *) 
  Lemma nltb_succ_diag_l : ∀ n, Nat.ltb (Datatypes.S n) n = false.
  Proof. intro n.
         case_eq(Nat.ltb (Datatypes.S n) n); intro A; auto. 
         apply ltb_to_lt in A.
         apply PeanoNat.Nat.nlt_succ_diag_l in A.
         elim A. 
  Qed.
  
  (* a ltb version of 
     Lt.lt_S_n: ∀ n m : nat, Datatypes.S n < Datatypes.S m → n < m
   *)
  Lemma ltb_S_n : ∀ n m, Nat.ltb (Datatypes.S n) (Datatypes.S m) = true → Nat.ltb n m = true. 
  Proof. intros n m A. 
         apply ltb_to_lt in A.
         apply Lt.lt_S_n in A.
         apply lt_to_ltb in A.
         exact A.
  Qed.

  (* a ltb version of 
     Lt.lt_n_S: ∀ n m : nat, n < m → Datatypes.S n < Datatypes.S m
  *) 
  Lemma ltb_n_S : ∀ n m, Nat.ltb n m = true → Nat.ltb (Datatypes.S n) (Datatypes.S m) = true. 
  Proof. intros n m A. 
         apply ltb_to_lt in A.
         apply Lt.lt_n_S in A.
         apply lt_to_ltb in A.
         exact A.
  Qed.

   (* a ltb version of 
       PeanoNat.Nat.lt_lt_succ_r: ∀ n m : nat, n < m → n < Datatypes.S m
    *)
   Lemma ltb_ltb_succ_r : ∀ n m, Nat.ltb n m = true -> Nat.ltb n (Datatypes.S m) = true. 
   Proof. intros n m A.
         apply ltb_to_lt in A.
         apply PeanoNat.Nat.lt_lt_succ_r in A.
         apply lt_to_ltb in A.
         exact A.
   Qed.

   (* a ltb versions of 
      PeanoNat.Nat.lt_1_r: ∀ n : nat, n < 1 ↔ n = 0
   *)  
   Lemma ltb_n_1_l: ∀ n, Nat.ltb n 1 = true → brel_eq_nat n 0 = true.
   Proof. intros n A.
         apply ltb_to_lt in A.
         apply PeanoNat.Nat.lt_1_r in A.
         rewrite A. simpl. 
         reflexivity. 
   Qed.

  (* a ltb version of 
     Lt.le_lt_n_Sm: ∀ n m : nat, n ≤ m → n < Datatypes.S m
   Lemma leb_ltb_n_Sm : 
  *)       


  (* a ltb similar to 
     Lt.le_lt_n_Sm: ∀ n m : nat, n ≤ m → n < Datatypes.S m
  *)       
   Lemma eq_lt_n_Sm : ∀ u n, brel_eq_nat u n = true -> Nat.ltb u (Datatypes.S n) = true. 
   Proof. induction u; intros n A.
          - reflexivity. 
          - destruct n.
            + compute in A. discriminate A. 
            + simpl in A.
              apply IHu in A.
              apply ltb_n_S.
              exact A. 
   Qed.
  
  Lemma ltb_S_not_eqb : ∀ n u, 
      Nat.ltb u (Datatypes.S n) = true -> 
      brel_eq_nat u n = false -> 
      Nat.ltb u n = true. 
  Proof. intros n u A B.
           apply ltb_to_lt in A.
           (* Note: Lt.lt_n_Sm_le: ∀ n m : nat, n < Datatypes.S m → n ≤ m *)
           apply Lt.lt_n_Sm_le in A.
           (* Note: EqNat.beq_nat_false: ∀ n m : nat, PeanoNat.Nat.eqb n m = false → n ≠ m *)
           apply EqNat.beq_nat_false in B.
           apply lt_to_ltb. 
           (* Note: PeanoNat.Nat.le_neq: ∀ n m : nat, n < m ↔ n ≤ m ∧ n ≠ m *)
           apply PeanoNat.Nat.le_neq; auto. 
  Qed.

  Lemma ltb_not_eqb : ∀ n u, 
      Nat.ltb u n = true -> brel_eq_nat u n = false.
  Proof. intros n u A.
         apply ltb_to_lt in A.
         case_eq(brel_eq_nat u n); intro B; auto.
         apply eqb_to_eq in B. rewrite B in A.
         apply lt_to_ltb in A.
         (* Note: PeanoNat.Nat.ltb_irrefl : ∀ x : nat, PeanoNat.Nat.ltb x x = false *) 
         rewrite PeanoNat.Nat.ltb_irrefl in A.
         discriminate A. 
  Qed.
  
  Close Scope nat_scope.
End NatArithmetic.
