From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties
  coq.algorithm.Listprop.
Import ListNotations.


Section Pathdefs.
  Variables 
    (Node : Type)
    (eqN  : brel Node).

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


  Fixpoint target (d : Node) (l : list (Node * Node * R)) : bool :=
    match l with
    | [] => false
    | (x, y, r) :: t => match t with 
      | [] => d =n= y
      | hs :: ts => target d t
    end
    end.


  (* path strength between c and d *)
  Fixpoint measure_of_path (l : list (Node * Node * R)) : R :=
    match l with 
    | [] => 1
    | (_, _, v) :: t => v * measure_of_path t
    end.


  Definition Matrix := Node -> Node -> R.
  
  
  Fixpoint well_formed_path_aux (m : Matrix) 
    (l : list (Node * Node * R)) : bool :=
    match l with 
    | [] => true
    | (c, x, v) :: tl => (m c x =r= v) && match tl with 
      | [] => true
      | (y, _, _) :: _ => (x =n= y) && well_formed_path_aux m tl
      end
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


  (* list of all paths of lenghth k from c to d. 
    xs is list of all candidates *)
  Fixpoint all_paths_klength (xs : list Node) 
    (m : Matrix) (k : nat) 
    (c d : Node) : list (list (Node * Node * R)) :=
    match k with
    | O => if c =n= d then [[(c, d, 1)]] else []
    | S k' =>
        let lf := List.flat_map (fun x => all_paths_klength xs m k' x d) xs
        in append_node_in_paths m c lf
    end.

  
  Definition construct_all_paths (xs : list Node) 
    (m : Node -> Node -> R) (k : nat) 
    (c d : Node) : list Path :=
    let lp := all_paths_klength xs m k c d in 
    List.map (fun l => (c, d, l)) lp.

  (* get all the R values from path *)
  Definition get_all_rvalues (pl : list Path): list R :=
    List.map (fun '(_, _, l) => measure_of_path l) pl.


  Definition sum_all_rvalues (pl : list R) :=
    List.fold_right (fun b a => b + a) 0 pl.

  (* sum_fn using fold_right *)
  Definition sum_fn_fold (f : Node -> R) (l : list Node) : R :=
    List.fold_right (fun b a => f b + a) 0 l.


  (* congruence relation on matrix *)
  Definition mat_cong (m : Matrix) : Prop :=
    forall a b c d, a =n= c = true -> 
    b =n= d = true -> m a b =r= m c d = true.
  

  Definition in_eq_bool_cong 
    (f : Node → list (list (Node * Node * R))) :=
    forall (x a : Node) (y : list (Node * Node * R)),  
    (x =n= a) = true -> 
    In_eq_bool _ _ _ eqN eqN eqR y (f a) = 
    In_eq_bool _ _ _ eqN eqN eqR y (f x).
    
    
  Definition cyclic_path (c : Node) 
    (l : list (Node * Node * R)) :=
    l <> [] /\ source c l = true /\ 
    target c l = true.

  
  
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

  (* elem_path_triple l = true means l does not have any cycle *)     
  Fixpoint elem_path_triple (l : list (Node * Node * R)) : bool := 
    match l with
    | [] => true 
    | (au, av, _) :: t => 
        negb (au =n= av) && 
        negb (elem_path_triple_tail au t) && 
        elem_path_triple t 
    end.

End Pathdefs.

Section Pathprops.

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
    (plus_idempotence : forall a, a + a =r= a = true)
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


  (* append node path function contains only 
    non-empty list *)  
  Lemma append_node_in_paths_non_empty_list : 
    forall (l : list (list (Node * Node * R))) 
      (m : Matrix Node R) (c : Node),  
    all_elems_non_empty_list _ 
    (append_node_in_paths Node R m c l) = true.
  Proof using -All.
    induction l as [|a l IHl].
    + simpl; intros ? ?. 
      reflexivity.
    + simpl.
      destruct a. 
      apply IHl.
      intros. 
      destruct p. 
      destruct p.
      simpl. 
      apply IHl.
  Qed.

  
  Lemma append_node_in_paths_eq : 
    ∀ (l : list (list (Node * Node * R))) 
    (m : Matrix Node R) (c : Node) 
    (xs : list (Node * Node * R)), 
    In_eq_bool _ _ _  eqN eqN eqR xs 
      (append_node_in_paths Node R m c l) = true -> 
    ∃ (y : Node) (ys : list (Node * Node * R)), 
      triple_elem_list _ _ _ eqN eqN eqR 
        xs ((c, y, m c y) :: ys) = true /\
      source Node eqN R c xs = true /\ 
      source Node eqN R y ys = true /\ 
      ys <> [].
  Proof using Node R eqN eqR refN symN.
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
      split. 
      apply symN. 
      exact Hlll. 
      split. 
      apply refN.
      intro Hf. 
      inversion Hf.
      apply IHl with (m := m) (c := c).
      exact H.
  Qed.

  
  Lemma non_empty_paths_in_kpath : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ 
        oneR finN m n c d) = true -> xs <> [].
  Proof using Node R eqN eqR finN 
  oneR refN symN.
    induction n.
    - simpl; intros ? ? ? ? Hin.
      case (eqN c d) eqn:Ht.
      simpl in Hin.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      intro Hf. 
      rewrite Hf in Hin.
      simpl in Hin. 
      congruence.
      congruence.
      intro Hf. 
      rewrite Hf in Hin.
      simpl in Hin. 
      congruence.
    - simpl; intros ? ? ? ? Hin.
      destruct (append_node_in_paths_eq
        (flat_map (λ x : Node, 
          all_paths_klength _ eqN _ oneR finN m n x d) finN)
        m c xs Hin) as [y [ys [Hl Hr]]].
      intro Hf. 
      rewrite Hf in Hl.
      simpl in Hl. 
      congruence.
  Qed.


  Lemma source_in_kpath : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)), 
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ 
        oneR finN m n c d) = true -> 
    source Node eqN R c xs = true.
  Proof using Node R eqN eqR finN oneR refN symN.
    induction n.
    - simpl; intros ? ? ? ? Hin.
      case (eqN c d) eqn:Ht.
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
      apply symN. 
      exact Hin.
      congruence.
      simpl in Hin.
      congruence.
    - simpl; intros ? ? ? ? Hin.
      destruct (append_node_in_paths_eq 
        (flat_map (λ x : Node, 
          all_paths_klength _ eqN _ oneR finN m n x d) finN)
        m c xs Hin) as [y [ys [Hl [Hr Hw]]]].
      assumption.
  Qed.

  

  Lemma append_node_rest : 
    forall l m c xs,
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (append_node_in_paths Node R m c l) = true ->
    In_eq_bool _ _ _ eqN eqN eqR 
      (List.tl xs) l = true.
  Proof using -All.
    induction l.
    - simpl; 
      intros ? ? ? Hin.
      inversion Hin.
    - simpl; 
      intros ? ? ? Hin. 
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
      left. 
      apply triple_trim_tail 
        with (a := (c, n, m c n)).
      exact H.
      apply Bool.orb_true_iff.
      right. 
      apply IHl with (m := m) (c := c).
      exact H.
  Qed.


  
  Lemma target_tail_forward : 
    forall (xs : list (Node * Node * R)) (d : Node), 
    target Node eqN R d (List.tl xs) = true -> 
    target Node eqN R d xs = true.
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

  Lemma target_tail_backward : 
    forall (xs : list (Node * Node * R)) (d : Node),
    List.tl xs <> [] -> 
    target Node eqN R d xs = true -> 
    target Node eqN R d (List.tl xs) = true.
  Proof using -All.
    destruct xs.
    - simpl; intros ? ?.
      congruence.
    - intros ? ? Ht.
      simpl in H.
      simpl.
      destruct xs.
      congruence.
      remember (p0 :: xs) as pxs.
      repeat destruct p.
      simpl in Ht.
      rewrite Heqpxs in Ht.
      rewrite <-Heqpxs in Ht.
      exact Ht.
  Qed.


  Lemma in_eq_append_cong : 
    forall l m a x y,
    mat_cong Node eqN R eqR m -> 
    a =n= x = true ->  
    In_eq_bool _ _ _ eqN eqN eqR y 
      (append_node_in_paths _ _  m a l) =
    In_eq_bool _ _ _ eqN eqN eqR y 
    (append_node_in_paths _ _ m x l).
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
        apply triple_eq_cong;
        try assumption.
        apply refN.
        apply Hm.
        exact Hax.
        apply refN.
  Qed.
  


  Lemma all_paths_cong : 
    forall n m d,
    mat_cong Node eqN R eqR m -> 
    in_eq_bool_cong Node eqN R eqR (λ x : Node, 
        all_paths_klength  _ eqN _ oneR finN m n x d).
  Proof using Node R eqN eqR finN oneR 
  refN symN symR trnN trnR.
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
      remember (flat_map (λ x0 : Node, all_paths_klength _ eqN _ oneR 
      finN m n x0 d) finN)
      as l.
      apply in_eq_append_cong.
      exact Hm.
      apply symN. 
      exact Hxa.
  Qed.


 
  Lemma target_in_kpath : 
    forall (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    mat_cong Node eqN R eqR m ->
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ 
      oneR finN m n c d) = true -> 
    target Node eqN R d xs = true.
  Proof using Node R eqN eqR finN 
  oneR refN symN symR trnN trnR.
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
      apply symN. 
      exact Hrrr.
      simpl in Hr.
      repeat destruct p.
      congruence.
      congruence.
      simpl in Hin.
      congruence.
    - simpl; intros ? ? ? ? Hm Hin.
      pose proof append_node_rest
      (flat_map (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d) finN)
      m c xs Hin as Hv.
      destruct (proj1 (in_flat_map_bool _ _ _ 
        eqN eqN eqR refN finN (List.tl xs)
        (λ x : Node, all_paths_klength _ eqN _ 
        oneR finN m n x d)
        (all_paths_cong _ _ _ Hm)) Hv) as [w [Ha Hb]].
      specialize (IHn m w d (List.tl xs) Hm Hb).
      apply target_tail_forward.
      exact IHn.
  Qed.    
      

  
  
  Lemma source_target_and_non_empty_kpath : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR 
        finN m n c d) = true ->
    xs <> [] ∧
    source _ eqN _ c xs = true ∧
    target _ eqN _ d xs = true.
  Proof using Node R eqN eqR finN 
  oneR refN symN symR trnN trnR.
    intros ? ? ? ? ? Hm Hin.
    split.
    apply non_empty_paths_in_kpath with 
      (n := n) (m := m) (c := c) (d := d).
    exact Hin.
    split.
    apply source_in_kpath with 
      (n := n) (m := m) (d := d).
    exact Hin.
    eapply target_in_kpath with 
    (n := n) (m := m) (d := d).
    exact Hm.
    exact Hin.
  Qed.
    

  Lemma well_formed_by_extending : 
    forall xs ys c y m, 
    mat_cong Node eqN R eqR m -> 
    ys <> [] ->  
    triple_elem_list _ _ _ eqN eqN eqR 
      xs ((c, y, m c y) :: ys) = true -> 
    source Node eqN _ c xs = true -> 
    source _ eqN _ y ys = true ->
    well_formed_path_aux Node eqN R eqR m (List.tl xs) = true ->
    well_formed_path_aux Node eqN R eqR m xs = true.
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
        repeat destruct p. 
        repeat destruct p0.
        repeat destruct p.
        assert (Hwt : well_formed_path_aux Node eqN R eqR m (tl ((n, n0, r) :: (n1, n2, r0) :: xs)) =
        well_formed_path_aux Node eqN R eqR m (((n1, n2, r0) :: xs))).
        reflexivity. rewrite Hwt in Hw; clear Hwt.
        assert (Hg : well_formed_path_aux Node eqN R eqR m ((n, n0, r) :: (n1, n2, r0) :: xs) =
        ((m n n0 =r= r) &&
        ((n0 =n= n1) && well_formed_path_aux Node eqN R eqR m ((n1, n2, r0) :: xs)))%bool).
        reflexivity. rewrite Hg; clear Hg.
        assert (Hvt : triple_elem_list _ _ _ eqN eqN eqR ((n, n0, r) :: (n1, n2, r0) :: xs)
        ((c, y, m c y) :: ys) = 
        ((n =n= c) && (n0 =n= y) && (r =r= m c y) &&
        triple_elem_list _ _ _ eqN eqN eqR ((n1, n2, r0) :: xs) ys)%bool).
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
  Lemma all_paths_well_formed_in_kpaths : 
    forall (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs (all_paths_klength _ eqN _ 
    oneR finN m n c d) = true ->
    well_formed_path_aux Node eqN R eqR m xs = true.
  Proof using Node R congrR eqN eqR finN oneR refN 
  refR symN symR trnN trnR. 
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
      (flat_map (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d) finN)
      m c xs Hin as Hv.
      destruct (proj1 (in_flat_map_bool  _ _ _ 
      eqN eqN eqR refN finN (List.tl xs)
      (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d)
      (all_paths_cong _ _ _ Hm)) Hv) as [w [Ha Hb]].
      specialize (IHn m w d (List.tl xs) Hcd Hm Hb).
      destruct (append_node_in_paths_eq
      (flat_map (λ x : Node, all_paths_klength _ eqN _ 
      oneR finN m n x d) finN)
      m c xs Hin) as [y [ys [Hu [Hvt [Hwl Hwr]]]]].
      apply well_formed_by_extending with (ys := ys) (c := c) (y := y);
      assumption.
  Qed.


  Lemma path_end_unit_loop : 
    forall k l m c d, 
    In_eq_bool _ _ _ eqN eqN eqR l 
    (all_paths_klength _ eqN _ 
      oneR finN m k c d) = true ->
    exists l', 
      triple_elem_list _ _ _ eqN eqN eqR 
        l (l' ++ [(d, d, 1)]) = true.   
  Proof using Node R eqN eqR finN oneR refN symN trnN.
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
        (flat_map (λ x : Node, all_paths_klength _ eqN _ 
        oneR finN m k x d) finN)
        m c l Hin) as [y [ys [Hl Hr]]].
      pose proof append_node_rest _ _ _ _ 
        Hin as Hap.
      destruct (in_flat_map_bool_first _ _ _ 
        eqN eqN eqR refN finN _ _ Hap) as (x & Hf & Heb).
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



  Lemma source_same_path : 
    forall l₁ l₂ x y,
    triple_elem_list _ _ _ eqN eqN eqR l₁ l₂ = true -> 
    source _ eqN _ x l₁ = true -> 
    source _ eqN _ y l₂ = true ->
    x =n= y = true.
  Proof using Node R eqN eqR symN trnN.
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


  Lemma all_paths_in_klength : 
    ∀ (k : nat) (m : Matrix Node R) 
    (c d : Node) xs,
    mat_cong Node eqN R eqR m -> 
    In_eq_bool _ _ _ eqN eqN eqR 
      xs (all_paths_klength _ eqN _ 
      oneR finN m k c d) = true ->
    (List.length xs = S k).
  Proof using Node R eqN eqR finN 
    oneR refN symN symR trnN trnR.
    induction k.
    + simpl; intros ? ? ? ? Hm Hin.
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
    + simpl; intros ? ? ? ? Hm Hin.
      pose proof append_node_in_paths_eq _ m c _ Hin as Hp.
      destruct Hp as [y [ys [Hy [Hsc [Hsd Hyn]]]]].
      apply append_node_rest in Hin.
      apply in_flat_map_bool_first in Hin.
      destruct Hin as [x [Hl Hr]].
      pose proof IHk m x d (List.tl xs) Hm Hr as Hind.
      pose proof source_target_and_non_empty_kpath k m x d 
        (List.tl xs) Hm Hr as (Ha & Hb & Hc).
      (* ys = List.tl xs that means y = x *)
      assert(Htt: triple_elem_list _ _ _ eqN eqN eqR (List.tl xs) ys = true).
      destruct xs. simpl in Hsc; congruence.
      simpl in Hy. simpl. destruct p as ((u, v), w).
      apply Bool.andb_true_iff in Hy.
      destruct Hy as [Hyl Hy]. exact Hy.
      pose proof source_same_path _ _ _ _ Htt Hb Hsd as Hp.
      apply list_tl_lia; assumption.
      apply refN.
  Qed.

  Lemma source_target_non_empty_kpath_and_well_formed : 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR 
        finN m n c d) = true ->
    xs <> [] ∧
    source _ eqN _ c xs = true ∧
    target _ eqN _ d xs = true ∧
    well_formed_path_aux Node eqN R eqR m xs = true ∧
    (List.length xs = S n)%nat ∧
    exists xs', 
      triple_elem_list _ _ _ eqN eqN eqR 
        xs (xs' ++ [(d, d, 1)]) = true. 
  Proof using Node R congrR eqN eqR finN oneR 
    refN refR symN symR trnN trnR. 
    intros ? ? ? ? ? Hcd Hm Hin.
    split.
    apply non_empty_paths_in_kpath with 
      (n := n) (m := m) (c := c) (d := d).
    exact Hin.
    split.
    apply source_in_kpath with 
      (n := n) (m := m) (d := d).
    exact Hin.
    split.
    eapply target_in_kpath with 
    (n := n) (m := m) (d := d).
    exact Hm.
    exact Hin.
    split.
    eapply all_paths_well_formed_in_kpaths;
    try assumption.
    exact Hin.
    split.
    eapply all_paths_in_klength.
    exact Hm.
    exact Hin.
    eapply path_end_unit_loop.
    exact Hin.
  Qed.


  (* generic lemma about list. It does not use any section assumption *)
  Lemma target_alt_end : 
    forall (l : list (Node * Node * R))
    (x : Node * Node * R) (d : Node),
    target_alt _ eqN _ d (l ++ [x]) = 
    target_alt _ eqN _ d [x].
  Proof using -All.
    intros ? ? ?.
    unfold target_alt.
    rewrite rev_unit.
    assert (Ht : rev [x] = [x]).
    reflexivity.
    rewrite Ht; clear Ht.
    reflexivity.
  Qed.


  Lemma target_end : 
    forall (l : list (Node * Node * R))
    (x : Node * Node * R) (d : Node),
    target _ eqN _ d (l ++ [x]) = 
    target _ eqN _ d [x].
  Proof using -All.
    induction l.
    - simpl; intros ? ?. reflexivity.
    - intros ? ?.
      assert (Ht : target _ eqN _ d ((a :: l) ++ [x]) = 
        target _ eqN _ d (l ++ [x])).
      simpl. destruct a. destruct p.
      destruct (l ++ [x]) eqn:Hv.
      pose proof app_eq_nil l [x] Hv as Hw.
      destruct Hw as [Hwl Hwr].
      congruence. reflexivity.
      rewrite Ht. apply IHl.
  Qed.


  Lemma target_target_alt_same : 
    forall (l : list (Node * Node * R)) (d : Node), 
    target _ eqN _ d l = target_alt _ eqN _ d l.
  Proof using -All.
    induction l using rev_ind.
    - unfold target_alt; simpl; intros ?.
      reflexivity.
    - intros ?. rewrite target_alt_end, target_end.
      reflexivity.
  Qed.

  
  Lemma triple_elem_rewrite :
    forall xs ys m c au av aw,
    mat_cong Node eqN R eqR m ->
    tl xs ≠ [] ->  
    source Node eqN R c xs = true ->
    well_formed_path_aux Node eqN R eqR m xs = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      (List.tl xs) ((au, av, aw) :: ys) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      xs ((c, au, m c au) :: (au, av, aw) :: ys) = true.
  Proof using Node R congrR eqN eqR refR symN symR trnN.
    intros * Hm Ha Hs Hw Ht.
    destruct xs as [|((bbu, bbv), bbw) xs].
    simpl in Ha;
    congruence.
    destruct xs as [|((cbu, cbv), cbw) xs].
    simpl in Ha;
    congruence.
    simpl in Ha, Hs.
    remember ((cbu, cbv, cbw) :: xs) as cxs.
    simpl in Hw, Ht.
    simpl.
    rewrite Heqcxs in Hw.
    apply Bool.andb_true_iff in Hw.
    destruct Hw as [Hwl Hw].
    apply Bool.andb_true_iff in Hw.
    destruct Hw as [Hwll Hw].
    apply symN in Hs;
    rewrite Hs, Ht.
    simpl.
    rewrite Heqcxs in Ht.
    simpl in Ht.
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htr].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htll].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htlr].
    rewrite (trnN _ _ _ Hwll Ht).
    simpl.
    apply Bool.andb_true_iff.
    split.
    apply symR.
    rewrite <-Hwl.
    apply congrR.
    apply Hm.
    apply symN; 
    exact Hs.
    apply symN.
    apply trnN with cbu;
    try assumption.
    apply refR.
    reflexivity.
  Qed.


  
 
  Lemma append_node_rest_rev : 
    forall l m c xs,
    mat_cong Node eqN R eqR m -> 
    source _ eqN _ c xs = true -> 
    List.tl xs <> [] ->
    well_formed_path_aux Node eqN R eqR m xs = true ->
    In_eq_bool _ _ _ eqN eqN eqR (List.tl xs) l = true ->
    In_eq_bool _ _ _ eqN eqN eqR xs 
    (append_node_in_paths _ _ m c l) = true.
  Proof.
    induction l as [|al l IHl].
    + intros * Hm Hs Hl Hw Hin.
      simpl in *.
      congruence.
    + intros * Hm Hs Hl Hw Hin.
      simpl in Hin.
      simpl.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      assert (Hat : exists au av aw ys, 
        al = ((au, av), aw) :: ys).
      destruct xs as [|((bu, bv), bw) xs].
      simpl in Hl;
      congruence.
      simpl in Hl, Hin.
      destruct xs as [|((cu, cv), cw) xs].
      simpl in Hl; 
      congruence.
      destruct al as [|((alu, alv), alw) al].
      simpl in Hin;
      congruence.
      exists alu, alv, alw, al. 
      reflexivity.
      destruct Hat as (au & av & aw & ys & Hat).
      rewrite Hat.
      assert (Hst : triple_elem_list Node Node R 
        eqN eqN eqR xs ((c, au, m c au) :: al) = true).
      rewrite Hat.
      eapply triple_elem_rewrite; 
      try assumption.
      rewrite Hat in Hin.
      exact Hin.
      eapply path_tl_rewrite;
      try assumption.
      apply triple_elem_eq_list_sym;
      try assumption.
      exact Hst.
      simpl.
      apply Bool.orb_true_iff.
      left.
      repeat (rewrite refN).
      repeat rewrite refR.
      simpl.
      rewrite Hat.
      apply triple_elem_eq_list_refl;
      try assumption.
      (* inductive hypothesis *)
      destruct al as [|((alu, alv), alw) al].
      apply IHl; try
      assumption.
      destruct xs as [|((cu, cv), cw) xs].
      simpl in Hl;
      congruence.
      simpl in Hl.
      destruct xs as [|((du, dv), dw) xs].
      simpl in Hl; 
      congruence.
      simpl.
      apply Bool.orb_true_iff.
      right. 
      remember ((cu, cv, cw) :: (du, dv, dw) :: xs) as cxs.
      apply IHl;
      try assumption.
      intro Hf;
      rewrite Heqcxs in Hf;
      simpl in Hf;
      congruence.
  Qed.



    


  (* *)
  Lemma source_target_non_empty_kpath_and_well_formed_rev : 
    ∀ (xs : list (Node * Node * R)) 
    (m : Matrix Node R) (c d : Node) ,
    mat_cong Node eqN R eqR m ->
    source _ eqN _ c (xs ++ [(d, d, 1)]) = true ->
    target _ eqN _ d (xs ++ [(d, d, 1)]) = true ->
    well_formed_path_aux Node eqN R eqR m (xs ++ [(d, d, 1)]) = true ->
    In_eq_bool _ _ _ eqN eqN eqR (xs ++ [(d, d, 1)])  
      (all_paths_klength _ eqN _ oneR 
        finN m (List.length xs) c d) = true.
  Proof.
    induction xs as [|((au, av), aw) xs].
    + intros * Hm Hs Ht Hw.
      simpl in *.
      rewrite Hs.
      simpl.
      apply symN in Hs.
      rewrite Hs, refN, refR.
      reflexivity.
    + intros * Hm Hs Ht Hw.
      simpl in Hs, Hw.
      assert (Hwt: exists bu bv bw ys, 
        xs ++ [(d, d, 1)] = (bu, bv, bw) :: ys).
      destruct xs as [|((cu, cv), cw) xs].
      exists d, d, 1, [].
      reflexivity.
      simpl.
      exists cu, cv, cw, (xs ++ [(d, d, 1)]).
      reflexivity.
      destruct Hwt as (bu & bv & bw & ys & Hwt).
      rewrite Hwt in Hw. 
      rewrite <-Hwt in Hw.
      simpl.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      assert (Hst: source Node eqN R bu (xs ++ [(d, d, 1)]) = true).
      rewrite Hwt; simpl; apply refN.
      assert (Htt: target Node eqN R d (xs ++ [(d, d, 1)]) = true).
      rewrite target_end;
      simpl; apply refN.
      specialize (IHxs m bu d Hm Hst Htt Hw).
      rewrite Hwt.
      rewrite Hwt in IHxs.
      (* Proof hinges on this lemma *)
      eapply append_node_rest_rev.
      simpl.
      exact Hm.
      exact Hs.
      simpl.
      intro Hf; congruence.
      remember ((bu, bv, bw) :: ys) as bys.
      simpl.
      rewrite Heqbys.
      rewrite <-Heqbys.
      rewrite Hwl, Hwll.
      rewrite Hwt in Hw.
      rewrite Hw.
      reflexivity.
      simpl.
      eapply in_flat_map_bool_second.
      intros ? ? ? Hxa.
      apply all_paths_cong.
      exact Hm.
      exact Hxa.
      apply memN.
      exact IHxs.
  Qed.



  (*

  Lemma I_need_this : 
    forall xs c d, 
    source c (xs ++ [(d, d, 1)]) = true ->
    target d (xs ++ [(d, d, 1)]) = true ->
    well_formed_path_aux m (xs ++ [(d, d, 1)]) = true ->
    exists ys, 
      (List.lenght ys < List.length finN) /\ 
      source c (ys ++ [(d, d, 1)]) = true /\ 
      target d (ys ++ [(d, d, 1)]) = true /\
      well_formed_path_aux m (xs ++ [(d, d, 1)]) = true 

  *)

      
      




  Lemma path_split_measure : forall l l₁ l₂, 
    triple_elem_list _ _ _ eqN eqN eqR l (l₁ ++ l₂) = true  -> 
    measure_of_path _ _ oneR mulR l =r= 
    measure_of_path _ _ oneR mulR l₁ * 
    measure_of_path _ _ oneR mulR l₂ = true.
  Proof using Node R congrM congrR eqN eqR mulR 
  mul_associative oneR one_left_identity_mul refR symR.
    induction l.
    - simpl; intros ? ? Hl.
      destruct l₁; 
      destruct l₂; 
      simpl in * |- *.
      apply symR. 
      apply one_left_identity_mul.
      all: congruence.
    - simpl; intros ? ? Hl.
      destruct a. 
      destruct p.
      destruct l₁; 
      destruct l₂; 
      simpl in * |- *.
      congruence.
      repeat destruct p.
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlr].
      apply Bool.andb_true_iff in Hl.
      destruct Hl as [Hl Hlrr].
      assert (Ht : 1 * (r0 * measure_of_path _ _ oneR mulR l₂) =r= 
        (r0 * measure_of_path _ _ oneR mulR l₂) = true).
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
      assert (Ht : r0 * (measure_of_path _ _ oneR mulR l₁ * 1) =r= 
      r0 * measure_of_path _ _ oneR mulR l₁ * 1 = true).
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
      assert (Ht : r0 * (measure_of_path _ _ oneR mulR l₁ * 
        (r1 * measure_of_path _ _ oneR mulR l₂)) =r= 
        r0 * measure_of_path _ _ oneR mulR l₁ * 
        (r1 * measure_of_path _ _ oneR mulR l₂) = true).
      apply mul_associative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply congrM.
      exact Hlr.
      exact IHl.
      apply refR.
  Qed.



  
  Lemma fold_map_pullout : forall l w,
    fold_right (fun a b => a + b) 0 
      (map (fun y => w * measure_of_path _ _  oneR mulR y) l) =r=
    w * fold_right (fun a b => a + b) 0 
      (map (@measure_of_path Node R oneR mulR) l) = true.
  Proof using Node R congrP congrR eqR left_distributive_mul_over_plus
  mulR oneR plusR refR symR zeroR zero_right_anhilator_mul.
    induction l.
    - simpl; intros ?.
      apply symR, 
      zero_right_anhilator_mul.
    - simpl; intros ?.
      assert (Ht: w *
        (measure_of_path Node R oneR mulR a +
        fold_right (λ a0 b : R, a0 + b) 0 
        (map (measure_of_path Node R oneR mulR) l)) =r= 
        w * measure_of_path Node R oneR mulR a + 
        w * fold_right (λ a0 b : R, a0 + b) 0 
        (map (measure_of_path Node R oneR mulR) l) = true).
      apply left_distributive_mul_over_plus.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply congrP.
      apply refR.
      apply IHl.
      apply refR.
  Qed.


  

  Lemma map_measure_simp_gen :
    forall (l : list (list (Node * Node * R))) 
    (m : Matrix Node R) (c a : Node),
    mat_cong Node eqN R eqR m ->
    (forall xs, 
      In_eq_bool _ _ _ eqN eqN eqR xs l = true -> 
      xs <> [] /\ source Node eqN R a xs = true) ->
    list_eqv _ eqR 
      (map (measure_of_path _ _  oneR mulR) 
           (append_node_in_paths Node R m c l))
      (map (fun y => m c a * 
        measure_of_path _ _  oneR mulR y) l) = true.
  Proof using Node R congrM eqN eqR mulR oneR refN refR symN.
    induction l as [|ys yss IH].
    - simpl; intros ? ? ? Hm Hin.
      reflexivity.
    - simpl; intros ? ? ? Hm Hin.
      assert (Ht : (triple_elem_list _ _ _ eqN eqN eqR ys ys || 
        In_eq_bool _ _ _ eqN eqN eqR ys yss)%bool = true).
      apply Bool.orb_true_iff.
      left. 
      apply triple_elem_eq_list_refl;
      try assumption.
      pose proof (Hin ys Ht) as Ha.
      destruct Ha as [Ha Hs].
      destruct ys. 
      congruence. 
      simpl.
      repeat destruct p.
      simpl. 
      simpl in Hs.
      apply Bool.andb_true_iff.
      split.
      apply congrM.
      apply Hm. 
      apply refN.
      apply symN. 
      exact Hs.
      apply refR. 
      apply IH. 
      exact Hm.
      intros ? Hxs.
      apply Hin.
      apply Bool.orb_true_iff.
      right. 
      exact Hxs.
  Qed.



  Lemma map_measure_simp : 
    forall m n c d a, 
    mat_cong Node eqN R eqR m -> 
    list_eqv _ eqR 
    (map (measure_of_path _ _  oneR mulR) 
      (append_node_in_paths Node R m c 
        (all_paths_klength _ eqN _ oneR finN m n a d)))
    (map (fun y => m c a * measure_of_path _ _ oneR mulR y) 
      (all_paths_klength _ eqN _ oneR finN m n a d)) = true.
  Proof using Node R congrM eqN eqR finN 
  mulR oneR refN refR symN symR trnN trnR.
    intros ? ? ? ? ? Hm.
    apply map_measure_simp_gen.
    exact Hm.
    intros ? Hin.
    pose proof source_target_and_non_empty_kpath n m a d xs 
      Hm Hin as (Ha & Hb & Hc).
    split; assumption.
  Qed.



  Lemma fold_right_congr : 
    forall l₁ l₂,
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





  

















End Pathprops.


  



    
    
    

   