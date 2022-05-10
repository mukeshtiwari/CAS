From Coq Require Import
     List
     Utf8
     FunctionalExtensionality
     BinNatDef
     Lia
     Even.
From CAS Require Import
     coq.common.compute
     coq.eqv.properties
     coq.eqv.list
     coq.po.properties
     coq.po.from_sg
     coq.sg.properties
     coq.algorithm.matrix_definition
     coq.algorithm.weighted_path. 
Import ListNotations.



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

  Definition weighted_arc : Type := Node * Node * R. 

  Definition weighted_path := list weighted_arc.

  Definition weighted_path_set := finite_set weighted_path.


  Definition Cong m              := mat_cong Node eqN R eqR m.
  Definition all_k_paths         := all_paths_klength Node eqN R oneR finN. 
  Definition append_all_paths    := append_node_in_paths Node R. 
  Definition is_source_of c p    := source Node eqN R c p = true.
  Definition is_target_of c p    := target Node eqN R c p = true.
  Definition test_is_target_of c p    := target Node eqN R c p.  
  Definition is_eqR a b          := eqR a b = true.
  Definition is_eqN a b          := eqN a b = true.    
  Definition w                   := measure_of_path Node R oneR mulR.
  Definition Wf m p              := well_formed_path_aux Node eqN R eqR m p = true. 
  Definition brel_path p1 p2     := brel_triple_list Node Node R eqN eqN eqR p1 p2 = true.
  Definition in_path_set t X       := in_triple_list_list Node Node R  eqN eqN eqR X t = true.
  Definition test_in_path_set t X  := in_triple_list_list Node Node R  eqN eqN eqR X t.  
  Definition list_of_R_eq l1 l2 := brel_list eqR l1 l2 = true.
  Definition list_of_N_eq l1 l2 := brel_list eqN l1 l2 = true.   
  
  Local Infix "=p=" := brel_path (at level 70).
  Local Infix "=lr=" := list_of_R_eq (at level 70).
  Local Infix "=ln=" := list_of_N_eq (at level 70).    
  Local Infix "[is source of]" := is_source_of (at level 70).
  Local Infix "[is target of]" := is_target_of (at level 70).
  Local Infix "[?is target of?]" := test_is_target_of (at level 70).        
  Local Infix "[in set]" := in_path_set (at level 70).
  Local Infix "[?in set?]" := test_in_path_set (at level 70).    

  Local Notation "0" := zeroR.
  Local Notation "1" := oneR.
  Local Infix "+" := plusR.
  Local Infix "*" := mulR. 
  Local Infix "=r?=" := eqR (at level 70).
  Local Infix "=n?=" := eqN (at level 70).
  Local Infix "=r=" := is_eqR (at level 70).
  Local Infix "=n=" := is_eqN (at level 70).  

  Definition diagonal_all_ones m := (forall c d, (c =n= d) -> (m c d =r= 1)). 


  
(*
  Variables 
    (zero_left_identity_plus  : forall r : R, 0 + r =r= r = true)
    (zero_right_identity_plus : forall r : R, r + 0 =r= r = true)
    (plus_associative : forall a b c : R, a + (b + c) =r= 
      (a + b) + c = true)
    (plus_commutative  : forall a b : R, a + b =r= b + a = true)
    (plus_idempotence : forall a : R, a + a =r= a = true)
    (zero_stable : forall a : R, 1 + a =r= 1 = true)
    (one_left_identity_mul  : forall r : R, 1 * r =r= r = true)
    (one_right_identity_mul : forall r : R, r * 1 =r= r = true)
    (mul_associative : forall a b c : R, a * (b * c) =r= (a * b) * c = true)

    (left_distributive_mul_over_plus : forall a b c : R, 
      a * (b + c) =r= a * b + a * c = true)
    
    (zero_left_anhilator_mul  : forall a : R, 0 * a =r= 0 = true)
    (zero_right_anhilator_mul : forall a : R, a * 0 =r= 0 = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)
*) 

  
  Lemma non_empty_paths_in_kpath (m : Matrix Node R) : 
    ∀ (k : nat) (c d : Node) (xs : weighted_path),
       xs [in set] (all_k_paths m k c d) -> xs <> [].
Admitted.     
(*  
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
*) 

  
  Lemma source_in_kpath (m : Matrix Node R) : 
    ∀ (k : nat) (c d : Node) (p : weighted_path), 
       p [in set] (all_k_paths m k c d) -> c [is source of] p.
    Admitted. 
  (*
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

*)  


(* move to weighted_paths? *) 
  Lemma target_tail_forward : 
    ∀ (p : weighted_path) (d : Node), 
      d [is target of] (List.tl p) -> d [is target of] p.
  Admitted.
(*  
  Proof.
    destruct p.
    - simpl; intros ? ?.
      exact H.
    - simpl; intros ? ?.
      repeat destruct p.
      destruct xs.
      simpl in H.
      congruence.
      exact H.
  Qed.
 *)
  

(*  
  Definition in_eq_bool_cong (f : Node → weighted_path_set) :=
    forall (x a : Node) (y : weighted_path),  
    (x =n= a) = true -> 
    In_eq_bool _ _ _ eqN eqN eqR y (f a) = 
    In_eq_bool _ _ _ eqN eqN eqR y (f x).

  Lemma all_paths_cong : 
    forall n m d,
    mat_cong Node eqN R eqR m -> 
    in_eq_bool_cong Node eqN R eqR (λ x : Node, all_paths_klength  _ eqN _ oneR finN m n x d).
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


*)     
  Lemma target_in_kpath (m : Matrix Node R) (cong : Cong m) : 
    ∀ (k : nat) (c d : Node) (p : weighted_path),
        p [in set] (all_k_paths m k c d) -> d [is target of] p.
  Admitted.
(*  
Proof.     
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
*)       

  
  
  Lemma source_target_and_non_empty_kpath (m : Matrix Node R) (cong : Cong m) : 
    ∀ (k : nat) (c d : Node) (p : weighted_path),
     p [in set] (all_k_paths m k c d) ->
        p <> [] ∧
        c [is source of] p ∧
        d [is target of] p. 
Admitted.     
(*  
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
*)     



(* paths generated by all_paths_klength function are well formed

  Lemma all_paths_well_formed_in_kpaths : 
    forall (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R)),
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs (all_paths_klength _ eqN _ 
    oneR finN m n c d) = true ->
    well_formed_path_aux Node eqN R eqR m xs = true.
*) 
  
  (* paths generated by all_paths_klength function are well formed *)
  Lemma all_paths_well_formed_in_kpaths
        (m : Matrix Node R)
        (cong : Cong m)
        (diag : diagonal_all_ones m): 
    ∀ (k : nat) (c d : Node) (p : weighted_path),
       p [in set] (all_k_paths m k c d) -> Wf m p.
Admitted.     
(*  
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
*) 

  Lemma path_end_unit_loop (m : Matrix Node R) : 
    ∀ k p c d,  p [in set]  (all_k_paths m k c d) ->
       ∃ q, p =p= (q ++ [(d, d, 1)]).  
  Admitted.
(*  
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
 *)



  Lemma all_paths_in_klength (m : Matrix Node R) (cong : Cong m): 
    ∀ (k : nat) (c d : Node) p,
       p [in set] (all_k_paths m k c d) -> (List.length p = S k).
  Admitted.
(*  
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
 *)
  
  Lemma source_target_non_empty_kpath_and_well_formed
       (m : Matrix Node R) (cong : Cong m) (diag : diagonal_all_ones m) : 
    ∀ (k : nat) (c d : Node) (p : weighted_path),
       p [in set] (all_k_paths m k c d) ->
       p <> [] ∧
       c [is source of] p ∧ d [is target of] p ∧ Wf m p ∧
      (List.length p = S k)%nat ∧
      ∃ q, p =p= (q ++ [(d, d, 1)]).
Admitted. 
(*
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
*) 

(* move to weighted_paths? *) 
  Lemma target_end : 
    forall (p : weighted_path) (x : weighted_arc) (d : Node),
      (d [?is target of?] (p ++ [x])) = (d [?is target of?] [x]).
Admitted.     
(*   
  Proof.
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
*) 


 
  (* *)
  Lemma source_target_non_empty_kpath_and_well_formed_rev (m : Matrix Node R) (cong : Cong m) :
    ∀ (p : weighted_path) (c d : Node) ,
        c [is source of] (p ++ [(d, d, 1)]) ->
        d [is target of] (p ++ [(d, d, 1)]) ->
        Wf m (p ++ [(d, d, 1)])->
          (p ++ [(d, d, 1)]) [in set] (all_k_paths m (List.length p) c d).
Admitted.       
(*        
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
*) 



  (* move to weighted_paths? *)

  Definition sum_list := fold_right plusR 0.  
  Lemma fold_map_pullout : ∀ X v,
    sum_list (map (fun y => v * (w y)) X)
    =r=
    v * sum_list(map (@measure_of_path Node R oneR mulR) X).
  Admitted.
(*  
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
*) 

  

  Lemma map_measure_simp_gen (m : Matrix Node R) (cong : Cong m):
    forall (l : weighted_path_set) (c a : Node),
    (forall xs, xs [in set] l -> xs <> [] /\ a [is source of] xs) ->
              (map w (append_all_paths  m c l))
              =lr= 
              (map (fun y => m c a * (w y)) l).
  Admitted.
(*  
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
*) 


  Lemma map_measure_simp (m : Matrix Node R) (cong : Cong m): 
    ∀k c d a, 
    (map w (append_all_paths m c (all_k_paths m k a d)))
      =lr= 
    (map (fun y => (m c a) * (w y)) (all_k_paths m k a d)).
  Admitted.
(*  
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

*) 

(* move to weighted paths? *)   
  Lemma fold_right_congr : forall l₁ l₂, l₁ =lr= l₂ -> sum_list l₁ =r= sum_list l₂.
Admitted.     
(*  
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
 *)

  (* this should be the result of simpler lemmas *) 
  Lemma append_node_app (m : Matrix Node R) : 
    ∀ (X₁ X₂ : weighted_path_set) (c : Node), 
       sum_list (map w (append_all_paths m c (X₁ ++ X₂))) 
       =r=
       sum_list (map w ((append_all_paths m c X₁) ++ (append_all_paths m c X₂))).
  Admitted.
(*  
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
*) 

  (* x * l1 + x * l2 + x * l3 = x * (l1 + l2 + l3) 
  Lemma fold_right_measure : forall n m c a d,
    mat_cong Node eqN R eqR m -> 
    (fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map (measure_of_path Node R 1 mulR)
      (append_node_in_paths Node R m c 
        (all_paths_klength _ eqN _ oneR finN m n a d))) =r=
    m c a *
    fold_right (λ b v : R, b + v) 0
      (map (measure_of_path Node R 1 mulR) 
        (all_paths_klength _ eqN _ oneR finN m n a d))) = true.
e*)
  Lemma fold_right_measure (m : Matrix Node R) (cong : Cong m):
    ∀ k c a d,
      sum_list (map w (append_all_paths m c (all_k_paths m k a d)))
      =r=
      (m c a) * (sum_list (map w (all_k_paths m k a d))).
Admitted.     
(*      
        
  Proof using Node R congrM congrP congrR eqN eqR finN
  left_distributive_mul_over_plus mulR oneR plusR refN refR symN symR trnN trnR
  zeroR zero_right_anhilator_mul.
    intros ? ? ? ? ? Hm.
    assert (Ht : 
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map (measure_of_path Node R 1 mulR)
      (append_node_in_paths Node R m c 
        (all_paths_klength _ eqN _ oneR finN m n a d))) =r= 
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0
    (map (fun y => m c a * measure_of_path Node R 1 mulR y) 
      (all_paths_klength _ eqN _ oneR finN m n a d)) = true).
    apply fold_right_congr.
    apply map_measure_simp.
    exact Hm.
    rewrite <-Ht; clear Ht.
    apply congrR.
    apply refR.
    apply symR.
    apply fold_map_pullout.
  Qed.
*) 

(* move ?*) 
  Lemma path_reconstruction (m : Matrix Node R) (cong : Cong m): 
    ∀ (p : weighted_path),  Wf m p -> 
        (construct_path_from_nodes _ _ (collect_nodes_from_a_path Node R p) m) =p= p.         
  Admitted.
(*  
  Proof using Node R congrR eqN eqR refN refR symN.
    induction l.
    + intros * Hm Hw. 
      simpl; reflexivity.
    + intros * Hm Hw. 
      simpl.
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
      assert (Hwt: (well_formed_path_aux _ eqN _ eqR m 
        ((au, av, aw) :: (pu, pv, pw) :: l) = 
        (m au av =r= aw) && ((av =n= pu) && 
        well_formed_path_aux _ eqN _ eqR m ((pu, pv, pw) :: l)))%bool).
      simpl. reflexivity.
      rewrite Hwt in Hw; clear Hwt.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      specialize (IHl m Hm Hw).
      assert (Hwt: construct_path_from_nodes _ _ 
        (au :: collect_nodes_from_a_path Node R ((pu, pv, pw) :: l)) m =
        (au, pu, m au pu) :: 
        construct_path_from_nodes _ _ 
          (collect_nodes_from_a_path _ _ ((pu, pv, pw) :: l)) m).
      simpl. destruct l.
      reflexivity. reflexivity.
      rewrite Hwt; clear Hwt.
      remember (construct_path_from_nodes _ _ 
      (collect_nodes_from_a_path _ _ ((pu, pv, pw) :: l)) m) as ml.
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
*) 

(* move ? *)   
  Lemma source_list_construction (m : Matrix Node R) (cong : Cong m):
    forall p c, Wf m p -> c [is source of] p -> 
               ∃ d q, p =p= ((c, d, m c d) :: q). 
Admitted. 
    (*
Proof using Node R congrR 
  eqN eqR refN refR symN symR.
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
      apply triple_elem_eq_list_refl;
      try assumption.
  Qed.
*) 

(*
  Lemma target_list_construction : 
    forall l c m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux _ eqN _ eqR m l = true -> 
    target _ eqN R c l = true ->
    exists d lc, 
    triple_elem_list  _ _ _ eqN eqN eqR 
      l (lc ++ [(d, c, m d c)]) = true.
*) 
  
  Lemma target_list_construction (m : Matrix Node R) (cong : Cong m): 
    ∀ p c, Wf m p -> c [is target of] p ->
             ∃ d q, p =p= (q ++ [(d, c, m d c)]).
  Admitted.
(*  
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
      assert (Hwt: (well_formed_path_aux _ eqN _ eqR m ((au, av, aw) :: (pu, pv, pw) :: l) = 
        (m au av =r= aw) && ((av =n= pu) && well_formed_path_aux _ eqN _ eqR m ((pu, pv, pw) :: l)))%bool).
      simpl. reflexivity.
      rewrite Hwt in Hw; clear Hwt.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      assert (Hwt : target _ eqN R c ((au, av, aw) :: (pu, pv, pw) :: l) = 
      target _ eqN R c ((pu, pv, pw) :: l)). simpl. reflexivity.
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
*) 

  

  (* move! *) 
  Lemma keep_collecting_dropping_dual : 
    forall l au, l =p= 
      (keep_collecting Node eqN R au l ++ keep_dropping Node eqN R au l).
  Admitted.
(*  
  Proof.
    induction l as [|((ah, bh), ch) l].
    + intros ?; simpl; reflexivity.
    + intros ?; simpl.
      case (au =n= bh) eqn:Ha.
      rewrite <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl. 
      apply triple_elem_eq_list_refl;
      try assumption.
      rewrite <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl.
      apply IHl.
  Qed.
*) 

  (* move! *) 
  Lemma elem_path_triple_tail_true : forall l av,
    elem_path_triple_tail Node eqN R av l = true ->
    exists ll au aw lr, 
      l =p= (ll ++ [(au, av, aw)] ++ lr) /\ 
      elem_path_triple_tail Node eqN R  av ll = false /\ 
      (ll ++ [(au, av, aw)]) =p= (keep_collecting Node eqN R av l).
  Admitted. Print elem_path_triple_tail. 
(*  
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
      apply triple_elem_eq_list_refl;
      try assumption.
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
*) 


  Lemma elem_path_triple_tail_simp : 
    forall l av, 
    elem_path_triple_tail  Node eqN R av l = true ->
    exists ll au aw, 
      (ll ++ [(au, av, aw)]) =p= (keep_collecting _ eqN _ av l).
  Admitted.
(*  
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
*) 

  (* move.  This is some type of congruence for target *)
  Lemma keep_collecting_rewrite : 
    forall p q t, p =p= q -> t [is target of] p -> t [is target of] q. 
Admitted. 
(*    
Admitted.   
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
*) 


HEre. 
  Lemma elim_path_triple_connect_compute_loop_true_first : 
    forall l,
    elem_path_triple Node eqN R l = true -> 
    elem_path_triple_compute_loop Node eqN R l = None.
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


  Lemma elim_path_triple_connect_compute_loop_true_second : 
    forall l,
    elem_path_triple_compute_loop Node eqN R l = None -> 
    elem_path_triple Node eqN R l = true.
  Proof.
    induction l as [|((au, av), aw) l].
    + intros He; simpl in He.
      simpl. reflexivity.
    + intros He; simpl in * |- *.
      case (au =n= av) eqn:Hb.
      congruence.
      simpl.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hbe.
      congruence.
      simpl. 
      apply IHl; assumption.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_true_none_eqv : 
    forall l, 
    elem_path_triple_compute_loop Node eqN R l = None 
    <-> 
    elem_path_triple Node eqN R l = true.
  Proof.
    intros ?; split; intro H.
    apply elim_path_triple_connect_compute_loop_true_second; assumption.
    apply elim_path_triple_connect_compute_loop_true_first; assumption.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_false_first : 
    forall l,
    elem_path_triple Node eqN R l = false -> 
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop Node eqN R l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path Node eqN R au lc. 
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
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      simpl in He.
      repeat eexists.
      simpl. rewrite Ha, Hb.
      f_equal.
      congruence.
      simpl. 
      apply refN.
      apply target_tail_forward; simpl.
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
    Some lc = elem_path_triple_compute_loop Node eqN R l ->
    elem_path_triple Node eqN R l = false.
  Proof.
    induction l as [|((au, av), aw) l].
    + intros ? Hs; simpl in Hs;
      congruence.
    + intros ? Hs; simpl in * |- *.
      case (au =n= av) eqn:Ha.
      simpl. reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      simpl. reflexivity.
      simpl.
      eapply IHl; exact Hs.
  Qed.


  Lemma elim_path_triple_connect_compute_loop_false_eqv : 
    forall l,
    elem_path_triple Node eqN R l = false <-> 
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop Node eqN R l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path Node eqN R au lc.
  Proof.
    intros *; split; intros He.
    apply  elim_path_triple_connect_compute_loop_false_first; assumption.
    destruct He as (au & av & aw & lc & lcc & Hs & Hlcc & Hc).
    eapply elim_path_triple_connect_compute_loop_false_second; 
    exact Hs.
  Qed.


  Lemma elem_path_triple_compute_loop_triple_middle_element : 
    forall l ll lm lr, 
    (ll, lm, lr) = elem_path_triple_compute_loop_triple Node eqN R l ->
    lm = elem_path_triple_compute_loop Node eqN R l.
  Proof.
    induction l as [|((au, av), aw) l].
    + intros ? ? ? Hl; simpl in Hl; simpl;
      inversion Hl; subst; reflexivity.
    + intros ? ? ? Hl.
      simpl in * |- *.
      case (au =n= av) eqn:Ha.
      inversion Hl; subst; reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      inversion Hl; subst; reflexivity.
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as ((al, bl), cl).
      inversion Hl; subst; clear Hl.
      eapply IHl.
      reflexivity.
  Qed.


  Lemma elem_path_triple_compute_loop_triple_combined_list : forall l,
    match elem_path_triple_compute_loop_triple Node eqN R l with
    | (fp, None, tp) => triple_elem_list _ _ _ eqN eqN eqR l (fp ++ tp) = true
    | (fp, Some sp, tp) => triple_elem_list _ _ _ eqN eqN eqR l (fp ++ sp ++ tp) = true
    end. 
  Proof.
    induction l as [|((au, av), aw) l].
    + simpl; reflexivity.
    + simpl. 
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as ((la, lb), lc).
      case (au =n= av) eqn:Ha.
      rewrite List.app_nil_l, 
      <-List.app_comm_cons.
      rewrite refN, refN, refR.
      simpl. 
      apply triple_elem_eq_list_refl;
      try assumption.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
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



  Lemma elem_path_triple_tail_rewrite : 
    forall l lr au, 
    triple_elem_list _ _ _ eqN eqN eqR l lr = true ->
    elem_path_triple_tail Node eqN R au l = false ->
    elem_path_triple_tail Node eqN R au lr = false.
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
    elem_path_triple_tail Node eqN R au l = false ->
    triple_elem_list _ _ _ eqN eqN eqR l (ll ++ lr) = true ->
    elem_path_triple_tail Node eqN R au ll = false /\
    elem_path_triple_tail Node eqN R au lr = false.
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



  Lemma elem_path_triple_compute_loop_first_element_elementry : 
    forall l ll lm lr ,
    (ll, lm, lr) = elem_path_triple_compute_loop_triple Node eqN R l ->
    elem_path_triple Node eqN R ll = true.
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
      case (elem_path_triple_tail Node eqN R au l) eqn:Hb.
      inversion Hl; subst;
      reflexivity.
      remember (elem_path_triple_compute_loop_triple Node eqN R l) as elp.
      destruct elp as ((al, bl), cl).
      inversion Hl; subst; clear Hl.
      simpl.
      rewrite Ha; simpl.
      pose proof elem_path_triple_compute_loop_triple_combined_list l as Hep.
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as ((atl, btl), ctl).
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



  Lemma length_leq_lt : 
    ∀ (l : weighted_path),
    l <> [] -> 
    ((List.length l) < 
      List.length 
        (collect_nodes_from_a_path Node R l))%nat.
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
    forall (c : list Node) 
    (l : weighted_path),
    c <> [] ->  
    (List.length c <= List.length l)%nat ->
    (List.length c < 
    List.length (collect_nodes_from_a_path Node R l))%nat.
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
    forall (l : weighted_path) m a,
    well_formed_path_aux Node eqN R eqR m l = true -> 
    elem_path_triple_tail Node eqN R a l = true ->
    in_list eqN (collect_nodes_from_a_path Node R l) a = true.
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
    ∀ (l : weighted_path) m, 
      well_formed_path_aux Node eqN R eqR m l = true -> 
      elem_path_triple Node eqN R l = false -> 
      no_dup Node eqN (collect_nodes_from_a_path Node R l) = false.
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
      case (elem_path_triple_tail Node eqN R au bl) eqn:Hep.
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
    well_formed_path_aux Node eqN R eqR m bl = true ->
    elem_path_triple_tail Node eqN R au bl = false ->
    in_list eqN (collect_nodes_from_a_path Node R bl) au = false.
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
    ∀ (l : weighted_path) (m : Matrix Node R), 
      well_formed_path_aux Node eqN R eqR m l = true ->
      no_dup Node eqN (collect_nodes_from_a_path Node R l) = false -> 
      elem_path_triple Node eqN R l = false.
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
      case ((elem_path_triple_tail Node eqN R au bl)) eqn:Hep.
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

  
  
  Lemma all_paths_in_klength_paths_cycle : 
    forall (c : list Node)
    (l : weighted_path) m,
    well_formed_path_aux Node eqN R eqR m l = true ->
    covers _ eqN c (collect_nodes_from_a_path Node R l) -> 
    (List.length c < List.length (collect_nodes_from_a_path Node R l))%nat ->
    elem_path_triple Node eqN R l = false.
  Proof.
    intros * Hw Hc Hl.
    eapply elem_path_collect_node_from_path_second.
    exact Hw.
    destruct (covers_dup Node eqN refN symN trnN  
        _ _ Hc Hl) as 
    [a [l₁ [l₂ [l₃ Hll]]]].
    eapply list_eqv_no_dup_rewrite;
    try assumption.
    exact Hll.
    simpl.
    apply no_dup_false_one;
    try assumption.
  Qed.


  (* if you give me path of length >= finN then there is loop *)
  Lemma all_paths_in_klength_paths_cycle_finN : 
    forall (l : weighted_path) m,
    (List.length finN <= List.length l)%nat ->
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists au av aw lc lcc, 
      Some lc = elem_path_triple_compute_loop Node eqN R l /\
      ((au, av, aw) :: lcc) = lc /\ cyclic_path Node eqN R au lc.
  Proof.
    intros ? ? Hfin Hw.
    assert(empN : finN <> []).
    destruct finN.
    simpl in lenN; try nia.
    intro H. congruence.
    pose proof length_collect_node_gen finN
      l empN Hfin as Hf.
    pose proof covers_list_elem Node eqN finN 
      (collect_nodes_from_a_path Node R l) memN as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      finN l m Hw Hcov Hf as Hwt.
    eapply elim_path_triple_connect_compute_loop_false_first;
    try assumption.
  Qed.



  Lemma triple_compute_connect_with_triple_elem_forward : 
    forall l, 
    elem_path_triple Node eqN R l = false ->
    exists ll lm lr, (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l.
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
      case (elem_path_triple_tail Node eqN R au l) eqn:Hel.
      eauto.
      simpl in Ha.
      destruct (IHl Ha) as 
      (ll & lm & lr & Hb).
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as 
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
    elem_path_triple_compute_loop_triple Node eqN R l ->
    elem_path_triple Node eqN R l = false.
  Proof.
    induction l as [|((au, av), aw) l].
    + simpl.
      intros * Ha.
      congruence.
    + simpl.
      intros * Ha.
      case (au =n= av) eqn:Hauv.
      reflexivity.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hel.
      reflexivity.
      simpl.
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as 
      ((bu, bv), bw).
      inversion Ha;
      subst; clear Ha.
      exact (IHl bu lm bw eq_refl).
  Qed.
      

  Lemma triple_compute_connect_with_triple_elem : 
    forall l, 
    elem_path_triple Node eqN R l = false <->
    exists ll lm lr, (ll, Some lm, lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l.
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
    triple_elem_list _ _ _ eqN eqN eqR lm ln = true ->
    target Node eqN R a ((au, av, aw) :: ln) = true ->
    target Node eqN R a ((au, av, aw) :: lm) = true.
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
    elem_path_triple Node eqN R l = false ->
    exists ll au av aw lm lr, 
      (ll, Some ((au, av, aw) :: lm), lr) = 
      elem_path_triple_compute_loop_triple Node eqN R l /\ 
      cyclic_path Node eqN R au ((au, av, aw) :: lm) /\ 
      elem_path_triple Node eqN R ll = true /\ 
      triple_elem_list _ _ _ eqN eqN eqR 
        l (ll ++  ((au, av, aw) :: lm) ++ lr) = true.
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
      apply triple_elem_eq_list_refl;
      try assumption.
      simpl in Ha.
      case (elem_path_triple_tail Node eqN R au l) eqn:Hel.
      simpl in Ha.
      exists [], au, av, aw,
      (keep_collecting Node eqN R au l),
      (keep_dropping Node eqN R au l).
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
      apply triple_elem_eq_list_sym;
      try assumption.
      exact Hd.
      eapply target_tail_forward.
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
      destruct (elem_path_triple_compute_loop_triple Node eqN R l) as 
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
    forall (l : weighted_path) m,
    (List.length finN <= List.length l)%nat ->
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists ll au av aw lm lr, 
    (ll, Some ((au, av, aw) :: lm), lr) = 
    elem_path_triple_compute_loop_triple Node eqN R l /\ 
    cyclic_path Node eqN R au ((au, av, aw) :: lm) /\  (* Loop so we can remove this *)
    elem_path_triple Node eqN R ll = true /\ (* Elementry Path *)
    triple_elem_list _ _ _ eqN eqN eqR l (ll ++  ((au, av, aw) :: lm) ++ lr) = true. 
    (* lr is the rest of path *)
  Proof.
    intros ? ? Hfin Hw.
    assert(empN : finN <> []).
    destruct finN.
    simpl in lenN; try nia.
    intro H. congruence.
    pose proof length_collect_node_gen finN 
      l empN Hfin as Hf.
    pose proof covers_list_elem Node eqN finN 
      (collect_nodes_from_a_path Node R l) memN as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      finN l m Hw Hcov Hf as Hwt.
    eapply triple_compute_connect_with_triple_elem_stronger.
    exact Hwt.
  Qed.



  Definition zwf (x y : weighted_path) := 
      (List.length x < List.length y)%nat.

  Lemma zwf_well_founded : well_founded zwf.
  Proof.
    exact (Wf_nat.well_founded_ltof _ 
      (fun x => List.length x)).
  Defined.
  

    

  (* easy proof List.length finN <= List.length l -> loop *)
  Lemma elem_path_length : 
    forall (l : weighted_path) m, 
    elem_path_triple Node eqN R l = true ->
    well_formed_path_aux Node eqN R eqR m l = true -> 
    (List.length l < List.length finN)%nat.
  Proof.
    intros l m He Hw.
    assert (Hwt : (length l < length finN)%nat \/ 
    (length finN <= length l)%nat).
    nia.
    destruct Hwt as [Hwt | Hwt].
    exact Hwt.
    assert(empN : finN <> []).
    destruct finN.
    simpl in lenN; try nia.
    intro H. congruence.
    pose proof length_collect_node_gen finN 
    l empN Hwt as Hf.
    pose proof covers_list_elem _ _ finN 
      (collect_nodes_from_a_path Node R l) memN as Hcov.
    pose proof all_paths_in_klength_paths_cycle
      finN l m Hw Hcov Hf as Hat.
    rewrite Hat in He.
    congruence.
  Qed.


  
  (* I can take any path l and turn it into elementry path 
      by keep applying *)
  Lemma reduce_path_into_elem_path : 
    forall (l : weighted_path) m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists lm, 
      well_formed_path_aux Node eqN R eqR m lm = true /\ 
      elem_path_triple Node eqN R lm = true.
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
        case (elem_path_triple_tail Node eqN R au bl) eqn:Heab.
        destruct (elem_path_triple_tail_true bl _ Heab) as 
        (llt & aut & awt & lrt & Ha & Hb & Hc).
        (* discard (llt ++ [(aut, au, awt)]) and 
          call the recursive function on lrt *)
        assert (Hd : well_formed_path_aux Node eqN R eqR m lrt = true).
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



  (* Every well formed path can be reduced into 
      an well formed elementry path, i.e., path 
      without loop and it's length < finN *)
  Lemma reduce_path_into_elem_path_gen : 
    forall (l : weighted_path) m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m l = true ->
    exists lm, 
      well_formed_path_aux Node eqN R eqR m lm = true /\ 
      elem_path_triple Node eqN R lm = true /\ 
      (List.length lm < List.length finN)%nat.
  Proof.
    intros ? ? Hm Hw.
    destruct (reduce_path_into_elem_path l m Hm Hw) 
    as (lm & Hwa & Hwe).
    pose proof (elem_path_length lm m Hwe Hwa) as Hp.
    exists lm.
    repeat split; try assumption.
  Qed.


  Lemma well_founded_rev : 
    forall lm aut avt awt au av aw cut cvt cwt lr m,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux Node eqN R eqR m
      ([(aut, avt, awt)] ++ ((au, av, aw) :: lm) ++ (cut, cvt, cwt) :: lr) = true ->
    cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
    avt =n= cut = true. 
  Proof.
    intros * Hm Hw Hc.
    unfold cyclic_path in Hc. 
    destruct Hc as (_ & Hcb & Hcc).
    assert (Hlt : lm = [] ∨ exists c d mcd lm',
      lm = lm' ++ [((c, d), mcd)]).
    destruct lm as [|((pa, pb), pc) lm]. 
    left; reflexivity.
    right.
    assert (Hne : (pa, pb, pc) :: lm  <> []).
    intro Hf; congruence.
    destruct (@exists_last _ ((pa, pb, pc) :: lm) Hne) 
    as (lm' & ((but, bvt), bwt) & Hc).
    exists but, bvt, bwt, lm'.
    exact Hc.
    destruct Hlt as [Hlt | Hlt].
    +
      rewrite Hlt in Hw, Hcb, Hcc.
      simpl in Hw. 
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwlll Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwllll Hw].
      apply trnN with au.
      exact Hwll.
      apply trnN with av;
      try assumption.
    +
      destruct Hlt as (c & d & mcd & lm' & Hlm).
      rewrite Hlm in Hw, Hcb, Hcc.
      assert (Htt : (au, av, aw) :: lm' ++ [(c, d, mcd)] = 
      ((au, av, aw) :: lm') ++ [(c, d, mcd)]).
      simpl; reflexivity.
      rewrite Htt in Hcc.
      rewrite target_end in Hcc.
      simpl in Hcc.
      clear Htt.
      assert (Htt : [(aut, avt, awt)] ++ ((au, av, aw) :: lm' ++ [(c, d, mcd)]) ++ (cut, cvt, cwt) :: lr =
      [(aut, avt, awt); (au, av, aw)] ++ (lm' ++ [(c, d, mcd)] ++ (cut, cvt, cwt) :: lr)).
      simpl. f_equal.
      f_equal.
      rewrite <-List.app_assoc.
      f_equal.
      rewrite Htt in Hw; 
      clear Htt. 
      destruct (well_formed_path_snoc [(aut, avt, awt); (au, av, aw)] _ 
        m Hw) as (Ha & Hb).
      simpl in Ha.
      destruct (well_formed_path_snoc lm' _
        m Hb) as (Hc & Hd).
      simpl in Hd.
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Hal Ha].
      apply Bool.andb_true_iff in Ha.
      destruct Ha as [Ha _].
      apply Bool.andb_true_iff in Hd.
      destruct Hd as [Hdl Hd].
      apply Bool.andb_true_iff in Hd.
      destruct Hd as [Hd _].
      apply trnN with au.
      exact Ha.
      apply trnN with d;
      try assumption.
  Qed.
      

    








  
  Lemma well_formed_loop_removal : 
    forall ll lr lm au av aw m,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m 
      (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
    cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
    well_formed_path_aux Node eqN R eqR m ((ll ++ lr)) = true.
  Proof.
    induction ll as [|((aut, avt), awt) ll].
    + intros * Hm Hw Hc.
      rewrite List.app_nil_l in Hw.
      rewrite List.app_nil_l.
      destruct (well_formed_path_snoc _ _ m Hw) as [_ Hwt].
      exact Hwt.
    + intros * Hm Hw Hc.
      simpl.
      destruct ll as [|((but, bvt), bwt) ll].
      simpl.
      destruct lr as [|((cut, cvt), cwt) lr].
      destruct (well_formed_path_snoc _ _ _ Hw) as [Ha Hb].
      simpl in Ha.
      exact Ha.
      apply Bool.andb_true_iff.
      split.
      simpl in Hw.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hw _].
      exact Hw.
      apply Bool.andb_true_iff.
      split.
      eapply well_founded_rev; 
      try assumption.
      exact Hm.
      exact Hw.
      exact Hc.

      apply well_formed_path_snoc in Hw.
      destruct Hw as [_ Hw].
      apply well_formed_path_snoc in Hw.
      destruct Hw as [_ Hw].
      exact Hw.
      assert(Hlt : ((but, bvt, bwt) :: ll) ++ lr = 
        (but, bvt, bwt) :: ll ++ lr).
      simpl; reflexivity.
      rewrite Hlt.
      assert (Hbt : (((aut, avt, awt) :: (but, bvt, bwt) :: ll) ++ ((au, av, aw) :: lm) ++ lr) = 
        (aut, avt, awt) :: ((but, bvt, bwt) :: ll ++ ((au, av, aw) :: lm) ++ lr)).
      simpl; reflexivity.
      rewrite Hbt in Hw.
      clear Hbt.
      remember ((but, bvt, bwt) :: ll ++ ((au, av, aw) :: lm) ++ lr) as bl.
      simpl in Hw.
      rewrite Heqbl in Hw.
      rewrite <-Heqbl in Hw.
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwl Hw].
      apply Bool.andb_true_iff in Hw.
      destruct Hw as [Hwll Hw].
      apply Bool.andb_true_iff.
      split.
      exact Hwl.
      apply Bool.andb_true_iff.
      split.
      exact Hwll.
      rewrite Heqbl in Hw.
      exact (IHll _ _ _ _ _ _ Hm Hw Hc).
  Qed.
      
      

  Lemma triple_well_formed_rewrite_gen :
    forall l lw m d,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux Node eqN R eqR m 
      (l ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR
      l lw = true ->
    well_formed_path_aux  Node eqN R eqR m 
      (lw ++ [(d, d, 1)]) = true.
  Proof.
    induction l as [|((au, av), aw) l].
      + intros [|((bu, bv), bw) lw] ? ? Hm Hw Ht.
        exact Hw.
        simpl in Ht. 
        lia.
      + intros ? ? ? Hm Hw Ht.
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
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [_ Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hwr].
        apply Bool.andb_true_iff in Hwr.
        destruct Hwr as [Hwr _].
        rewrite Hwr.
        simpl.
        rewrite Bool.andb_true_r.
        apply symN in Htrrr.
        apply trnN with av;
        try assumption.
        simpl in Htr.
        congruence.
        assert (Hwt: (well_formed_path_aux _ eqN _ eqR m 
          (((au, av, aw) :: (cu, cv, cw) :: l) ++ [(d, d, 1)]) = 
          (m au av =r= aw) && ((av =n= cu) && 
          well_formed_path_aux _ eqN _ eqR m ((cu, cv, cw) :: l ++ [(d, d, 1)])))%bool).
        simpl. reflexivity.
        rewrite Hwt in Hw; clear Hwt.
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwl Hw].
        apply Bool.andb_true_iff in Hw.
        destruct Hw as [Hwll Hw].
        specialize (IHl lw m d Hm Hw Htr).
        simpl. apply Bool.andb_true_iff.
        split. 
        rewrite <-Hwl.
        apply congrR.
        apply Hm.
        apply symN; assumption.
        apply symN; assumption.
        apply symR; assumption.
        destruct lw.
        simpl in Htr;
        congruence. 
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


  Lemma triple_well_formed_rewrite :
    forall l ll lm lr m d au av aw,
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m 
      (l ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      l (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
    well_formed_path_aux Node eqN R eqR m
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true.
  Proof.
    intros * Hm Hw Ht.
    simpl.
    assert (Htt : ll ++ (au, av, aw) :: lm ++ lr ++ [(d, d, 1)] = 
      (ll ++ (au, av, aw) :: lm ++ lr) ++ [(d, d, 1)]).
    rewrite <-List.app_assoc; simpl.
    f_equal.
    f_equal.
    rewrite <-List.app_assoc;
    reflexivity.
    rewrite Htt; clear Htt.
    eapply triple_well_formed_rewrite_gen;
    try assumption.
    exact Hw.
    exact Ht.
  Qed.



  Lemma source_loop_removal : 
    forall ll lr lm au av aw c d m,
    mat_cong Node eqN R eqR m ->
    well_formed_path_aux Node eqN R eqR m
         (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true -> 
    source Node eqN R c
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true ->
    cyclic_path Node eqN R au ((au, av, aw) :: lm) ->
    source Node eqN R c ((ll ++ lr) ++ [(d, d, 1)]) = true.
  Proof.
    intros * Hw Hm Hs Hc.
    assert (Hlt : lm = [] ∨ exists c d mcd lm',
      lm = lm' ++ [((c, d), mcd)]).
    destruct lm as [|((pa, pb), pc) lm]. 
    left; reflexivity.
    right.
    assert (Hne : (pa, pb, pc) :: lm  <> []).
    intro Hf; congruence.
    destruct (@exists_last _ ((pa, pb, pc) :: lm) Hne) 
    as (lm' & ((but, bvt), bwt) & Hd).
    exists but, bvt, bwt, lm'.
    exact Hd.

    destruct ll as [|((bu, bv), bw) ll];
    destruct lr as [|((cu, cv), cw) lr].
    destruct Hlt as [Hlt | Hlt].
    rewrite Hlt in Hc, Hs, Hm.
    simpl in * |- *.
    unfold cyclic_path in Hc.
    simpl in Hc.
    destruct Hc as (_ & _ & Hc).
    apply trnN with au;
    try assumption.
    apply trnN with av; 
    try assumption.
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [_ Hm].
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [Hm _].
    exact Hm.
    destruct Hlt as (cx & dx & mcd & lm' & Hlm).
    simpl.
    rewrite Hlm in Hm, Hc.
    simpl in Hs.
    rewrite List.app_nil_l in Hm.
    unfold cyclic_path in Hc.
    assert (Htt : ((au, av, aw) :: lm' ++ [(cx, dx, mcd)]) ++ [] ++ [(d, d, 1)] =
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)] ++ [(d, d, 1)]).
    simpl.
    f_equal.
    rewrite <-List.app_assoc.
    reflexivity.
    rewrite Htt in Hm;
    clear Htt.
    pose proof well_formed_path_snoc _ _ _ 
      Hm as (Ha & Hb).
    simpl in Hb.
    destruct Hc as (_ & _ & Hc).
    assert (Htt : (au, av, aw) :: lm' ++ [(cx, dx, mcd)] = 
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)]).
    simpl; reflexivity.
    rewrite Htt in Hc;
    clear Htt.
    rewrite target_end in Hc.
    simpl in Hc.
    apply trnN with au;
    try assumption.
    apply trnN with dx;
    try assumption.
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [_ Hb].
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [Hb _].
    exact Hb.
    destruct Hlt as [Hlt | Hlt].
    rewrite Hlt in Hm, Hs, Hc.
    simpl.
    simpl in Hs.
    rewrite List.app_nil_l in Hm.
    simpl in Hm.
    unfold cyclic_path in Hc.
    destruct Hc as (_ & _ & Hc).
    simpl in Hc.
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [_ Hm].
    apply Bool.andb_true_iff in Hm.
    destruct Hm as [Hm _].
    apply trnN with au;
    try assumption.
    apply trnN with av;
    try assumption.
    destruct Hlt as (cx & dx & mcd & lm' & Hlm).
    simpl.
    rewrite Hlm in Hm, Hc.
    simpl in Hs.
    rewrite List.app_nil_l in Hm.
    assert (Htt : ((au, av, aw) :: lm' ++ [(cx, dx, mcd)]) ++ ((cu, cv, cw) :: lr) ++ [(d, d, 1)] = 
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)] ++ ((cu, cv, cw) :: lr) ++ [(d, d, 1)]).
    simpl.
    f_equal.
    rewrite <-List.app_assoc.
    simpl; reflexivity.
    rewrite Htt in Hm;
    clear Htt.
    pose proof well_formed_path_snoc _ _ _ 
      Hm as (Ha & Hb).
    simpl in Hb.
    unfold cyclic_path in Hc.
    destruct Hc as (_ & _ & Hc).
    assert (Htt : (au, av, aw) :: lm' ++ [(cx, dx, mcd)] = 
    ((au, av, aw) :: lm') ++ [(cx, dx, mcd)]).
    simpl; reflexivity.
    rewrite Htt in Hc;
    clear Htt.
    rewrite target_end in Hc.
    simpl in Hc.
    apply trnN with au;
    try assumption.
    apply trnN with dx;
    try assumption.
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [_ Hb].
    apply Bool.andb_true_iff in Hb.
    destruct Hb as [Hb _].
    exact Hb.
    simpl.
    simpl in Hs.
    exact Hs.
    simpl.
    simpl in Hs.
    exact Hs.
  Qed.


  Lemma triple_source_rewrite_gen :
    forall l₁ l₂ c d,  
    source Node eqN R c 
      (l₁ ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      l₁ l₂ = true ->
    source Node eqN R c (l₂ ++ [(d, d, 1)]) = true.
  Proof.
    destruct l₁ as [|((au, av), aw) l₁];
    destruct l₂ as [|((bu, bv), bw) l₂];
    intros ? ? Hs Ht;
    simpl in * |- *;
    try assumption;
    try congruence.
    apply trnN with au;
    try assumption.
    case (au =n= bu) eqn:Haubu.
    reflexivity.
    simpl in Ht;
    congruence.
  Qed.
  


  Lemma triple_source_rewrite :
    forall l ll lm lr c d au av aw, 
    source Node eqN R c 
      (l ++ [(d, d, 1)]) = true ->
    triple_elem_list Node Node R eqN eqN eqR 
      l (ll ++ ((au, av, aw) :: lm) ++ lr) = true ->
    source Node eqN R c
      (ll ++ ((au, av, aw) :: lm) ++ lr ++ [(d, d, 1)]) = true.
  Proof.
    intros * Hs Ht.
    simpl.
    assert (Htt : ll ++ (au, av, aw) :: lm ++ lr ++ [(d, d, 1)] = 
      (ll ++ (au, av, aw) :: lm ++ lr) ++ [(d, d, 1)]).
    rewrite <-List.app_assoc; simpl.
    f_equal.
    f_equal.
    rewrite <-List.app_assoc;
    reflexivity.
    rewrite Htt; clear Htt.
    eapply triple_source_rewrite_gen.
    exact Hs.
    exact Ht.
  Qed.

  Definition is_lte a b := brel_lte_left eqR plusR a b = true.
  Local Infix "<=" := is_lte (at level 70).

  
  Lemma cycle_path_dup_remove (right_distributive_mul_over_plus : forall a b c : R, (a + b) * c =r= a * c + b * c = true): 
    forall ll lm lr,  w (ll ++ lr) <= w (ll ++ lm ++ lr).
  Proof.
    intros *.
    unfold Orel.
    assert (Ht : (measure_of_path Node R oneR mulR (ll ++ lr) + 
      measure_of_path Node R oneR mulR (ll ++ lm ++ lr) =r=
      measure_of_path Node R oneR mulR (ll ++ lr)) = 
      ((measure_of_path Node R oneR mulR ll * measure_of_path Node R oneR mulR lr) + 
        (measure_of_path Node R oneR mulR ll * 
        (measure_of_path Node R oneR mulR lm * measure_of_path Node R oneR mulR lr)) =r= 
        (measure_of_path Node R oneR mulR ll * measure_of_path Node R oneR mulR lr))).
    apply congrR.
    apply congrP.
    apply path_split_measure;
    apply triple_elem_eq_list_refl;
    try assumption.
    rewrite <- (path_split_measure (ll ++ lm ++ lr)
      ll (lm ++ lr) (triple_elem_eq_list_refl _ _ _ eqN eqN eqR refN refN refR (ll ++ lm ++ lr))). 
    apply congrR.
    apply refR.
    apply congrM.
    apply refR.
    apply symR.
    apply path_split_measure;
    apply triple_elem_eq_list_refl;
    try assumption.
    apply path_split_measure;
    apply triple_elem_eq_list_refl;
    try assumption.
    rewrite Ht; clear Ht.
    remember (measure_of_path Node R oneR mulR ll) as a.
    remember (measure_of_path Node R oneR mulR lm) as b.
    remember (measure_of_path Node R oneR mulR lr) as c.
    assert (Ht : (a * c + a * (b * c) =r= a * c) = 
      (a * c + a * b * c =r= a * c)).
    apply congrR.
    apply congrP.
    apply refR.
    apply mul_associative.
    apply refR.
    rewrite Ht; clear Ht.
    eapply path_weight_rel;
    try assumption.
    apply zero_stable.
    apply one_left_identity_mul.
  Qed.
  

  Lemma orel_rewrite :
    forall l lm lr,  
    triple_elem_list Node Node R eqN eqN eqR
      l lm = true ->
    Orel R plusR eqR (measure_of_path Node R 1 mulR lr)
      (measure_of_path Node R 1 mulR lm) ->
    Orel R plusR eqR (measure_of_path Node R 1 mulR lr)
      (measure_of_path Node R 1 mulR l).
  Proof.
    induction l as [|((au, av), aw) l];
    destruct lm as [|((bu, bv), bw) lm];
    intros * Ht Horel;
    simpl in Ht; try congruence.
    simpl.
    simpl in Horel.
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htr].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htrr].
    apply Bool.andb_true_iff in Ht.
    destruct Ht as [Ht Htrrr].
    unfold Orel in * |- *.
    rewrite <-Horel.
    apply congrR.
    apply congrP.
    apply refR.
    apply congrM.
    exact Htrr.
    pose proof path_split_measure l [] lm as Hlm.
    simpl in Hlm.
    specialize (Hlm Htr).
    rewrite <-Hlm.
    apply congrR.
    apply refR.
    apply symR.
    apply one_left_identity_mul.
    apply refR.
  Qed.


  Lemma reduce_path_into_simpl_path (right_distributive_mul_over_plus : forall a b c : R, (a + b) * c =r= a * c + b * c = true):
    forall (l : weighted_path) m c d,
    (length finN <= length l)%nat ->
    mat_cong Node eqN R eqR m -> 
    well_formed_path_aux Node eqN R eqR m (l ++ [(d, d, 1)]) = true ->
    source _ eqN _ c (l ++ [(d, d, 1)]) = true -> 
    target _ eqN _ d (l ++ [(d, d, 1)]) = true ->
    exists ys, 
      (List.length ys < List.length finN)%nat ∧
      well_formed_path_aux Node eqN R eqR m (ys ++ [(d, d, 1)]) = true ∧
      source _ eqN _ c (ys ++ [(d, d, 1)]) = true ∧
      target _ eqN _ d (ys ++ [(d, d, 1)]) = true ∧
      Orel R plusR eqR 
        (measure_of_path Node R oneR mulR ys)
        (measure_of_path Node R oneR mulR l).
  Proof.
    intros l.
    induction (zwf_well_founded l) as [l Hf IHl].
    unfold zwf in * |- *.
    intros ? ? ? Hfl Hm Hw Hs Ht.
    destruct (well_formed_path_snoc l ([(d, d, 1)]) m Hw) as 
    (Ha & Hb).
    destruct (all_paths_in_klength_paths_cycle_finN_stronger l 
      m Hfl Ha) as (ll & au & av & aw & lm & lr & He 
      & Hc & Hep & Hte).
    assert (Hlt : (length (ll ++ lr) < length l)%nat).
    pose proof (length_rewrite _ _ _ eqN eqN eqR _ _ Hte) as Hlf.
    rewrite Hlf. 
    simpl.
    rewrite app_length.
    rewrite app_length.
    simpl.
    rewrite app_length.
    nia.
    assert (Hdisj : (length (ll ++ lr) < length finN)%nat ∨ 
      (length finN <= length (ll ++ lr))%nat).
    nia.
    destruct Hdisj as [Hdisj | Hdisj].
    exists (ll ++ lr).
    repeat split.
    exact Hdisj.
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvt.
    pose proof well_formed_loop_removal _ _ _ _ _ _ _ Hm Hvt Hc as Han.
    rewrite <-List.app_assoc.
    exact Han.
    pose proof triple_source_rewrite _ _ _ _ _ _ _ _ _ Hs Hte as Hvta.
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvtb.
    pose proof source_loop_removal _ _ _ _ _ _ _ _ _ Hm Hvtb Hvta Hc as Han.
    exact Han.
    rewrite target_end.
    simpl; apply refN.
    eapply orel_rewrite.
    try assumption.
    exact Hte.
    eapply cycle_path_dup_remove. exact right_distributive_mul_over_plus.

    (* Now we are in Inductive case *)
    specialize (IHl (ll ++ lr) Hlt m c d Hdisj Hm).
    (* By same reasoning that I did in non inductive case *)
    assert (Hwt : well_formed_path_aux Node eqN R eqR m ((ll ++ lr) ++ [(d, d, 1)]) = true).
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvt.
    pose proof well_formed_loop_removal _ _ _ _ _ _ _ Hm Hvt Hc as Han.
    rewrite <-List.app_assoc.
    exact Han.
    assert (Hst : source Node eqN R c ((ll ++ lr) ++ [(d, d, 1)]) = true).
    pose proof triple_source_rewrite _ _ _ _ _ _ _ _ _ Hs Hte as Hvta.
    pose proof triple_well_formed_rewrite _ _ _ _ _ _ _ _ _ Hm Hw Hte as Hvtb.
    pose proof source_loop_removal _ _ _ _ _ _ _ _ _ Hm Hvtb Hvta Hc as Han.
    exact Han.
    assert (Htt: target Node eqN R d ((ll ++ lr) ++ [(d, d, 1)]) = true).
    rewrite target_end;
    simpl; apply refN.
    destruct (IHl Hwt Hst Htt) as 
    (ys & Hlfin & Hwf & Hsn & Htn & Horel).
    exists ys.
    repeat split.
    exact Hlfin.
    exact Hwf.
    exact Hsn.
    exact Htn.
    eapply orel_rewrite.
    exact Hte.
    pose proof cycle_path_dup_remove right_distributive_mul_over_plus
      ll ((au, av, aw) :: lm) lr as Hcp.
    eapply orel_trans;
    try assumption.
    exact Horel.
    exact Hcp.
  Qed.


  
  Lemma source_rewrite_gen : 
    ∀ (l₁ l₂ : weighted_path) (c : Node),
    source Node eqN R c l₁ = true ->
    triple_elem_list Node Node R eqN eqN eqR l₁ l₂ = true ->
    source Node eqN R c l₂ = true.
  Proof.
    destruct l₁ as [|((au, av), aw) l₁];
    destruct l₂ as [|((bu, bv), bw) l₂];
    intros ? Hs Ht;
    simpl in * |- *;
    try assumption;
    try congruence.
    apply trnN with au;
    try assumption.
    case (au =n= bu) eqn:Haubu.
    reflexivity.
    simpl in Ht;
    congruence.
  Qed.
  


  Lemma target_rewrite_gen : 
    ∀ (l₁ l₂ : weighted_path) (c : Node),
    target Node eqN R c l₁ = true ->
    triple_elem_list Node Node R eqN eqN eqR l₁ l₂ = true ->
    target Node eqN R c l₂ = true.
  Proof.
    induction l₁ as [|((au, av), aw) l₁];
    destruct l₂ as [|((bu, bv), bw) l₂];
    intros ? Htn Hte;
    simpl in Hte;
    try congruence.
    apply Bool.andb_true_iff in Hte.
    destruct Hte as [Hte Hter].
    apply Bool.andb_true_iff in Hte.
    destruct Hte as [Hte Hterr].
    destruct l₁ as [|((cu, cv), cw) l₁];
    destruct l₂ as [|((du, dv), dw) l₂].
    simpl.
    simpl in Htn.
    apply trnN with av;
    try assumption.
    apply Bool.andb_true_iff in Hte.
    destruct Hte as [_ Hte];
    exact Hte.
    simpl in Hter;
    congruence.
    simpl in Hter;
    congruence.
    remember ((cu, cv, cw) :: l₁) as cl.
    remember ((du, dv, dw) :: l₂) as dl.
    simpl.
    rewrite Heqdl.
    rewrite <-Heqdl.
    simpl in Htn.
    rewrite Heqcl in Htn.
    rewrite <-Heqcl in Htn.
    eapply IHl₁.
    exact Htn.
    exact Hter.
  Qed.
  
  
  Lemma reduce_path_gen_lemma (right_distributive_mul_over_plus : forall a b c : R,  (a + b) * c =r= a * c + b * c = true): 
    ∀ (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : weighted_path),
    (length finN <= n)%nat ->
    (forall c d, (c =n= d) = true -> (m c d =r= 1) = true) -> 
    mat_cong Node eqN R eqR m ->  
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR 
        finN m n c d) = true ->
    exists ys, 
      (length ys < length finN)%nat ∧
      In_eq_bool Node Node R eqN eqN eqR (ys ++ [(d, d, 1)])
        (all_paths_klength Node eqN R 1 finN m (length ys) c d) = true ∧
      Orel R plusR eqR 
        (measure_of_path Node R oneR mulR ys)
        (measure_of_path Node R oneR mulR xs).
  Proof.
    intros * Hfin Hcd Hm Hin.
    destruct (source_target_non_empty_kpath_and_well_formed 
      n m c d xs Hcd Hm Hin) as 
    (Hxs & Hsn & Htn & Hw & Hl & xs' & Hxs').
    pose proof reduce_path_into_simpl_path right_distributive_mul_over_plus xs' m c d as Hpath.
    pose proof length_rewrite _ _ _ eqN eqN eqR _ _ Hxs' as Hlen.
    rewrite app_length in Hlen.
    simpl in Hlen.
    assert (Hxsp : length xs' = n).
    nia.
    assert (Hfn : (length finN <= length xs')%nat).
    nia.
    clear Hlen; clear Hxsp.
    destruct (Hpath Hfn Hm (well_formed_path_rewrite _ _ _ Hm Hw Hxs')
      (source_rewrite_gen _ _ _ Hsn Hxs')
      (target_rewrite_gen _ _ _ Htn Hxs')) as 
    (ys & Hly & Hwfy & Hsy & Hty & Horel).
    pose proof source_target_non_empty_kpath_and_well_formed_rev ys m 
      c d Hm Hsy Hty Hwfy.
    exists ys.
    repeat split;
    try assumption.
    eapply orel_rewrite.
    exact Hxs'.
    unfold Orel.
    assert(Htt: 
      (measure_of_path Node R 1 mulR ys + measure_of_path Node R 1 mulR (xs' ++ [(d, d, 1)]) =r=
      measure_of_path Node R 1 mulR ys) = 
      (measure_of_path Node R 1 mulR ys + 
      (measure_of_path Node R 1 mulR xs' * measure_of_path Node R 1 mulR [(d, d, 1)]) =r=
      measure_of_path Node R 1 mulR ys)).
    apply congrR.
    apply congrP.
    apply refR.
    eapply path_split_measure.
    apply triple_elem_eq_list_refl;
    try assumption.
    apply refR.
    rewrite Htt; clear Htt.
    simpl.
    unfold Orel in Horel.
    rewrite <-Horel.
    apply congrR.
    apply congrP.
    apply refR.
    remember (measure_of_path Node R 1 mulR xs') as axs.
    assert (Htt: (axs * (1 * 1) =r= axs) = 
    (axs * (1 * 1) =r= axs * 1)).
    apply congrR.
    apply refR.
    apply symR.
    apply one_right_identity_mul.
    rewrite Htt; clear Htt.
    apply congrM.
    apply refR.
    apply one_right_identity_mul.
    apply refR.
  Qed.


  Lemma fold_right_dist_eqr_aide :
    forall a b c d e : R, b =r= d + e = true ->
    a + b =r= a + d + e = true.
  Proof using R congrP congrR eqR plusR plus_associative refR symR.
    intros ? ? ? ? ? H.
    assert (Ht : a + d + e =r= a + (d + e) = true).
    apply symR. 
    apply plus_associative.
    apply symR. 
    rewrite <-Ht; clear Ht.
    apply congrR. 
    apply refR.
    apply congrP. 
    apply refR.
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
      apply fold_right_dist_eqr_aide. 
      exact a.
      apply IHl₁.
  Qed.


  (* x * l1 + x * l2 + x * l3 = x * (l1 + l2 + l3) *)
  Lemma fold_map_rel : forall l m n c d,
    mat_cong _ eqN _ eqR m ->  
    fold_right (λ u v : R, u + v) 0
      (map (measure_of_path Node R 1 mulR)
        (append_node_in_paths Node R m c
          (flat_map (λ x : Node, all_paths_klength _ eqN _ oneR finN m n x d) l))) 
    =r= 
    fold_right (fun x t => m c x * 
      (fold_right (fun b v => b + v) 0 
        (map (measure_of_path Node R 1 mulR) (all_paths_klength _ eqN _ oneR finN m n x d))) + t) 0 l 
    = true.
  Proof using Node R congrM congrP congrR eqN eqR finN
  left_distributive_mul_over_plus mulR oneR plusR plus_associative refN refR
  symN symR trnN trnR zeroR zero_left_identity_plus zero_right_anhilator_mul.
    induction l as [|a l IHL].
    - simpl; intros ? ? ? ? Hm.
      apply refR.
    - simpl; intros ? ? ? ? Hm.
      pose proof append_node_app (all_paths_klength _ eqN _ oneR finN m n a d)
        (flat_map (λ x : Node, all_paths_klength _ eqN _ oneR finN m n x d) l)
        m c as Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR.
      rewrite map_app.
      pose proof fold_right_dist_eqr 
      (map (measure_of_path Node R 1 mulR)
        (append_node_in_paths Node R m c (all_paths_klength _ eqN _ oneR finN m n a d)))
      (map (measure_of_path Node R 1 mulR)
      (append_node_in_paths Node R m c
        (flat_map (λ x : Node, all_paths_klength _ eqN _ oneR finN m n x d) l))) as Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      apply refR.
      apply symR.
      apply congrP. 
      apply fold_right_measure.
      exact Hm.
      apply IHL.
      exact Hm.
  Qed.


  Lemma fold_right_cong : 
    forall l (g f: Node -> R -> R) a,
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
  
  


  Lemma fold_right_rewrite : 
    forall l₁ l₂ x, 
    brel_list eqR l₁ l₂ = true ->
    (fold_right (λ b a : R, b + a) 0 l₂ =r= 
    x + fold_right (λ b a : R, b + a) 0 l₂) = true ->
    (fold_right (λ b a : R, b + a) 0 l₁ =r= 
    x + fold_right (λ b a : R, b + a) 0 l₁) = true.
  Proof.
    intros * Hl Hf.
    rewrite <-Hf.
    apply congrR.
    exact (fold_right_congr _ _ Hl).
    apply congrP.
    apply refR.
    exact (fold_right_congr _ _ Hl).
  Qed.

  


  Lemma fold_right_replace : 
    forall l a,
    fold_right (λ x y : R, x + y) a l =r= 
    a + fold_right (λ x y : R, x + y) 0 l = true.
  Proof.
    induction l.
    + intros *.
      simpl.
      apply symR.
      apply zero_right_identity_plus.
    + intros *.
      simpl. 
      specialize (IHl a0).
      remember (fold_right (λ x y : R, x + y) a0 l) as al0.
      remember (fold_right (λ x y : R, x + y) 0 l) as al. 
      assert (Htt : 
      (a + al0 =r= a0 + (a + al)) =
      (a + al0 =r= (a + al) + a0)).
      apply congrR.
      apply refR.
      apply plus_commutative.
      rewrite Htt; clear Htt.
      assert (Htt : 
      (a + al0 =r= a + al + a0) = 
      (a + al0 =r= a + (al + a0))).
      apply congrR.
      apply refR.
      apply symR.
      apply plus_associative.
      rewrite Htt; clear Htt.
      apply congrP.
      apply refR.
      rewrite <-IHl.
      apply congrR.
      apply refR.
      apply plus_commutative.
  Qed.



  Lemma plus_idempotence_reduction : 
    forall (l : list R) (x : R),
    in_list eqR l x = true ->
    sum_all_rvalues R zeroR plusR l =r= 
    x + sum_all_rvalues R zeroR plusR l = true.
  Proof.
    intros ? ? Hl.
    unfold sum_all_rvalues.
    destruct (list_split_gen R eqR refR symR l x Hl) as 
    (l₁ & l₂ & Hlt).
    eapply fold_right_rewrite.
    exact Hlt.
    rewrite <- (fold_right_dist_eqr l₁ ([x] ++ l₂)).
    apply congrR.
    apply refR.
    simpl.
    rewrite fold_right_app.
    simpl.
    remember (fold_right (λ b a : R, b + a) 0 l₂) as fl₂.
    simpl.
    assert (Htt : 
    (x + fold_right (λ b a : R, b + a) (x + fl₂) l₁ =r=
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0 l₁ + (x + fl₂)) =
    (x + ((x + fl₂) + fold_right (λ b a : R, b + a) 0 l₁) =r=
    fold_right (λ u₁ v₁ : R, u₁ + v₁) 0 l₁ + (x + fl₂))).
    apply congrR.
    apply congrP.
    apply refR.
    erewrite <-fold_right_replace.
    apply congrR.
    apply refR.
    apply refR.
    apply refR.
    rewrite Htt; clear Htt.
    remember (fold_right (λ b a : R, b + a) 0 l₁) as fl₁.
    (* use idempotence *)
    apply symR.
    assert(Htt : (fl₁ + (x + fl₂) =r= x + (x + fl₂ + fl₁)) = 
    (fl₁ + (x + fl₂) =r= x + (x + (fl₂ + fl₁)))).
    apply congrR.
    apply refR.
    apply congrP.
    apply refR.
    apply symR.
    apply plus_associative.
    rewrite Htt;
    clear Htt.
    assert(Htt : 
    (fl₁ + (x + fl₂) =r= x + (x + (fl₂ + fl₁))) =
    (fl₁ + (x + fl₂) =r= (x + x) + (fl₂ + fl₁))).
    apply congrR.
    apply refR.
    apply plus_associative.
    rewrite Htt;
    clear Htt.
    assert (Htt: 
    (fl₁ + (x + fl₂) =r= x + x + (fl₂ + fl₁)) =
    (fl₁ + (x + fl₂) =r= x + (fl₂ + fl₁))).
    apply congrR.
    apply refR.
    apply congrP.
    apply plus_idempotence.
    apply refR.
    rewrite Htt;
    clear Htt.
    assert (Htt: 
    (fl₁ + (x + fl₂) =r= x + (fl₂ + fl₁)) =
    ((x + fl₂ + fl₁) =r= x + (fl₂ + fl₁))).
    apply congrR.
    apply plus_commutative.
    apply refR.
    rewrite Htt;
    clear Htt.
    apply symR.
    apply plus_associative.
  Qed.
    

  
  Lemma sum_all_flat_paths_app : 
    forall l₁ l₂,
    sum_all_flat_paths Node R zeroR oneR plusR mulR (l₁ ++ l₂) =r= 
    sum_all_flat_paths Node R zeroR oneR plusR mulR l₁ + 
    sum_all_flat_paths Node R zeroR oneR plusR mulR l₂ = true.
  Proof.
    induction l₁ as [|((au, av), alp) l₁].
    + intros ?.
      simpl.
      assert(Htt: 
      (sum_all_flat_paths Node R 0 1 plusR mulR l₂ =r=
      0 + sum_all_flat_paths Node R 0 1 plusR mulR l₂) =
      (sum_all_flat_paths Node R 0 1 plusR mulR l₂ =r=
      sum_all_flat_paths Node R 0 1 plusR mulR l₂)).
      apply congrR.
      apply refR.
      apply zero_left_identity_plus.
      rewrite Htt; clear Htt.
      apply refR.
    + intros ?.
      simpl.
      assert(Htt:
      (measure_of_path Node R 1 mulR alp +
      sum_all_flat_paths Node R 0 1 plusR mulR (l₁ ++ l₂) =r=
      measure_of_path Node R 1 mulR alp +
      sum_all_flat_paths Node R 0 1 plusR mulR l₁ +
      sum_all_flat_paths Node R 0 1 plusR mulR l₂) = 
      (measure_of_path Node R 1 mulR alp +
      sum_all_flat_paths Node R 0 1 plusR mulR (l₁ ++ l₂) =r=
      measure_of_path Node R 1 mulR alp +
      (sum_all_flat_paths Node R 0 1 plusR mulR l₁ +
      sum_all_flat_paths Node R 0 1 plusR mulR l₂))).
      apply congrR.
      apply refR.
      apply symR.
      apply plus_associative.
      rewrite Htt; clear Htt.
      apply congrP.
      apply refR.
      eapply IHl₁.
  Qed.

      
  Lemma fold_right_sum_all_flat_paths : 
    forall al,   
    (sum_all_rvalues R 0 plusR
    (get_all_rvalues Node R 1 mulR al) =r=
    sum_all_flat_paths Node R 0 1 plusR mulR al) = true.
  Proof.
    induction al as [|((au, av), alh) al].
    + simpl.
      apply refR.
    + simpl.
      apply congrP.
      apply refR.
      apply IHal.
  Qed. 

  
  Lemma flat_map_path_partial_sum : 
    forall n m c d, 
    partial_sum_paths Node eqN R zeroR oneR plusR mulR finN m n c d =r= 
    sum_all_flat_paths Node R zeroR oneR plusR mulR
    (enum_all_paths_flat Node eqN R oneR finN m n c d) = true.
  Proof.
      induction n.
      + intros ? ? ?.
        simpl.
        unfold construct_all_paths.
        simpl.
        case (c =n= d) eqn:Hcd.
        simpl.
        assert(Htt: (1 =r= 1 * 1 + 0) =
        (1 =r= 1 + 0)).
        apply congrR.
        apply refR.
        apply congrP.
        apply one_left_identity_mul.
        apply refR.
        rewrite Htt; clear Htt.
        apply symR.
        apply zero_right_identity_plus.
        simpl.
        apply refR.
      + intros ? ? ?.
        simpl.
        assert(Htt: 
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
             (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (construct_all_paths Node eqN R 1 finN m (S n) c d ++
           enum_all_paths_flat Node eqN R 1 finN m n c d)) =
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
            (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (construct_all_paths Node eqN R 1 finN m (S n) c d) +
        sum_all_flat_paths Node R 0 1 plusR mulR
          (enum_all_paths_flat Node eqN R 1 finN m n c d))).
        apply congrR.
        apply refR.
        apply sum_all_flat_paths_app.
        rewrite Htt; clear Htt.
        assert(Htt:
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
             (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (construct_all_paths Node eqN R 1 finN m (S n) c d) +
        sum_all_flat_paths Node R 0 1 plusR mulR
          (enum_all_paths_flat Node eqN R 1 finN m n c d)) =
        (partial_sum_paths Node eqN R 0 1 plusR mulR finN m n c d +
        sum_all_rvalues R 0 plusR
          (get_all_rvalues Node R 1 mulR
              (construct_all_paths Node eqN R 1 finN m (S n) c d)) =r=
        sum_all_flat_paths Node R 0 1 plusR mulR
          (enum_all_paths_flat Node eqN R 1 finN m n c d) + 
        sum_all_flat_paths Node R 0 1 plusR mulR
        (construct_all_paths Node eqN R 1 finN m (S n) c d))).
        apply congrR.
        apply refR.
        apply plus_commutative.
        rewrite Htt; clear Htt.
        apply congrP.
        apply IHn.
        apply fold_right_sum_all_flat_paths.
  Qed.

  
  Lemma in_eq_bool_path_measure : 
    forall lpp ys alph, 
    In_eq_bool Node Node R eqN eqN eqR ys
    (map (λ '(y, lt), let '(_, _) := y in lt) lpp) = true ->
    (measure_of_path Node R 1 mulR ys + measure_of_path Node R 1 mulR alph =r=
      measure_of_path Node R 1 mulR ys) = true -> 
    sum_all_flat_paths Node R 0 1 plusR mulR lpp + 
    measure_of_path Node R 1 mulR alph =r= 
    sum_all_flat_paths Node R 0 1 plusR mulR lpp = true.
  Proof.
    induction lpp as [|((au, av), lpph) lpp].
    + intros ? ? Hin Hm.
      simpl in Hin.
      congruence.
    + intros ? ? Hin Hm.
      simpl in Hin.
      simpl.
      apply Bool.orb_true_iff in Hin.
      destruct Hin as [Hin | Hin].
      pose proof path_split_measure ys [] lpph Hin as Ht.
      simpl in Ht.
      remember (measure_of_path Node R 1 mulR lpph) as a.
      remember (sum_all_flat_paths Node R 0 1 plusR mulR lpp) as b.
      remember (measure_of_path Node R 1 mulR alph) as c.
      remember (measure_of_path Node R 1 mulR ys) as d.
      assert (Htt: 
      (a + b + c =r= a + b) = (1 * a + b + c =r= 1 * a + b)).
      apply congrR.
      apply congrP.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      apply refR.
      apply congrP.
      apply symR.
      apply one_left_identity_mul.
      apply refR.
      rewrite Htt; clear Htt.
      assert(Htt:
      (1 * a + b + c =r= 1 * a + b) =  (d + b + c =r= d + b)).
      apply congrR.
      apply congrP.
      apply congrP.
      apply symR.
      exact Ht.
      apply refR.
      apply refR.
      apply congrP.
      apply symR.
      exact Ht.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt: 
      (d + b + c =r= d + b) = 
      (d + (b + c) =r= d + b)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt: (d + (b + c) =r= d + b) =
      (d + (c + b) =r= d + b)).
      apply congrR.
      apply congrP.
      apply refR.
      apply plus_commutative.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt: 
      (d + (c + b) =r= d + b) =
      (d + c + b =r= d + b)).
      apply congrR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      apply congrP.
      exact Hm.
      apply refR.
      remember (measure_of_path Node R 1 mulR lpph) as a.
      assert (Htt: 
      (a + sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph =r=
      a + sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (a + (sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph) =r=
      a + sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      apply congrP.
      apply refR.
      eapply IHlpp.
      exact Hin.
      exact Hm.
  Qed.



    


  Lemma sum_all_flat_paths_idempotence : 
    forall lp lpp, 
    (forall xs, In_path_membership Node eqN R eqR xs lp = true ->
     exists ys, 
      In_path_membership Node eqN R eqR ys lpp = true ∧ 
      measure_of_path Node R 1 mulR (tp Node R ys) +
      measure_of_path Node R 1 mulR (tp Node R xs) =r=
      measure_of_path Node R 1 mulR (tp Node R ys) = true) ->
    sum_all_flat_paths Node R 0 1 plusR mulR lp +
    sum_all_flat_paths Node R 0 1 plusR mulR lpp =r= 
    sum_all_flat_paths Node R 0 1 plusR mulR lpp = true.
  Proof.
    induction lp as [|((au, av), alph) lp].
    + intros * Hin.
      simpl.
      apply zero_left_identity_plus.
    + intros * Hin.
      simpl.
      assert (Htt : In_path_membership Node eqN R eqR (au, av, alph) ((au, av, alph) :: lp) = true).
      simpl.
      rewrite triple_elem_eq_list_refl;
      try assumption.
      reflexivity.
      destruct (Hin _ Htt) as (ys & Ha & Hb).
      simpl in Hb; clear Htt.
      destruct ys as((ays, bys), ys).
      unfold In_path_membership in Ha.
      simpl in Hb.
      assert (Htt: 
      (measure_of_path Node R 1 mulR alph +
      sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (measure_of_path Node R 1 mulR alph +
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply symR.
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      assert (Htt:
      (measure_of_path Node R 1 mulR alph +
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
       sum_all_flat_paths Node R 0 1 plusR mulR lpp) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) = 
      ((sum_all_flat_paths Node R 0 1 plusR mulR lp +
        sum_all_flat_paths Node R 0 1 plusR mulR lpp) + 
        measure_of_path Node R 1 mulR alph =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply plus_commutative.
      apply refR.
      rewrite Htt; clear Htt.
      assert(Htt:
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      (sum_all_flat_paths Node R 0 1 plusR mulR lpp +
      measure_of_path Node R 1 mulR alph) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply symR. 
      apply plus_associative.
      apply refR.
      rewrite Htt; clear Htt.
      pose proof (in_eq_bool_path_measure _ _ _ Ha Hb) as Hr.
      assert(Htt:
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      (sum_all_flat_paths Node R 0 1 plusR mulR lpp +
       measure_of_path Node R 1 mulR alph) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) =
      (sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lpp)).
      apply congrR.
      apply congrP.
      apply refR.
      exact Hr.
      apply refR.
      rewrite Htt; clear Htt.
      eapply IHlp.
      intros ? Hinp.
      specialize (Hin xs).
      unfold In_path_membership in Hin, Hinp.
      destruct xs in * |- *.
      destruct p in * |- *.
      simpl in * |- *.
      rewrite Hinp in Hin.
      rewrite Bool.orb_true_r in Hin.
      specialize (Hin eq_refl).
      destruct Hin as (yst & Hc & Hd).
      exists yst.
      split;
      try assumption.
  Qed.


      


  
  Lemma in_eq_bool_enum_path :
    forall n w ys m c d, 
    (w <= n)%nat ->  
    In_eq_bool Node Node R eqN eqN eqR (ys ++ [(d, d, 1)])
    (all_paths_klength Node eqN R 1 finN m w c d) = true ->
    In_eq_bool Node Node R eqN eqN eqR (ys ++ [(d, d, 1)])
    (map (λ '(y, lt), let '(_, _) := y in lt)
     (enum_all_paths_flat Node eqN R 1 finN m n c d)) = true.
  Proof.
    induction n. 
    + intros * Hl Hin.
      destruct w.
      simpl in * |- *.
      unfold construct_all_paths.
      rewrite map_map.
      simpl.
      rewrite map_id.
      exact Hin.
      simpl in Hl.
      nia.
    + intros * Hl Hin.
      simpl.
      rewrite map_app.
      unfold construct_all_paths.
      rewrite map_map, map_id.
      apply in_eq_bool_mem_second.
      assert (Htw : w = S n \/ (w <= n)%nat).
      nia.
      destruct Htw as [Htw | Htw].
      left.
      rewrite <-Htw.
      exact Hin.
      right.
      specialize (IHn w ys m c d Htw Hin).
      exact IHn.
  Qed.





  Lemma sum_all_flat_paths_fixpoint (right_distributive_mul_over_plus : forall a b c : R, 
        (a + b) * c =r= a * c + b * c = true): 
    forall k c d m,
    (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
    mat_cong Node eqN R eqR m ->
    sum_all_flat_paths Node R zeroR oneR plusR mulR
      (enum_all_paths_flat Node eqN R oneR finN m (length finN - 1)%nat c d) =r=
    sum_all_flat_paths Node R zeroR oneR plusR mulR
      (enum_all_paths_flat Node eqN R oneR finN m (k + length finN - 1)%nat c d) = true.
  Proof.
    induction k.
    + intros ? ? ? Huv Hm.
      simpl.
      apply refR. 
    + intros ? ? ? Huv Hm.
      assert (Htt : (S k + length finN - 1)%nat = 
      S (k + length finN - 1)). nia.
      rewrite Htt; clear Htt.
      simpl.
      remember (construct_all_paths Node eqN R 1 finN m (S (k + length finN - 1)) c d) as ls.
      remember (enum_all_paths_flat Node eqN R 1 finN m (k + length finN - 1) c d) as lss.
      assert(Htt:
      (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR (ls ++ lss)) =
      (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) =r=
      sum_all_flat_paths Node R 0 1 plusR mulR ls +
      sum_all_flat_paths Node R 0 1 plusR mulR lss)).
      apply congrR.
      apply refR.
      apply sum_all_flat_paths_app.
      rewrite Htt; clear Htt.
      subst.
      assert(Hl : (length finN <= S (k + length finN - 1))%nat).
      nia.
      pose proof reduce_path_gen_lemma right_distributive_mul_over_plus (S (k + length finN - 1))
        m c d as Hpl.
      unfold Orel in Hpl.
      specialize (IHk c d m Huv Hm).
      remember (construct_all_paths Node eqN R 1 finN m (S (k + length finN - 1)) c d) as lp.
      remember (enum_all_paths_flat Node eqN R 1 finN m (k + length finN - 1) c d) as lpp.
      remember (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d)) as sc.
      assert(Htt: 
      (sc =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lp +
      sum_all_flat_paths Node R 0 1 plusR mulR lpp) = 
      (sc =r=
      sum_all_flat_paths Node R 0 1 plusR mulR lp + sc)).
      apply congrR.
      apply refR.
      apply congrP.
      apply refR.
      apply symR.
      exact IHk.
      rewrite Htt; clear Htt.
      subst.
      remember (construct_all_paths Node eqN R 1 finN m (S (k + length finN - 1)) c d) as lp.
      remember (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) as lpp.
      pose proof sum_all_flat_paths_idempotence lp lpp as Hsu.
      assert (Htt: ∀ xs : Path Node R,
      In_path_membership Node eqN R eqR xs lp = true
      → ∃ ys : Path Node R,
          In_path_membership Node eqN R eqR ys lpp = true
          ∧ (measure_of_path Node R 1 mulR (tp Node R ys) +
              measure_of_path Node R 1 mulR (tp Node R xs) =r=
              measure_of_path Node R 1 mulR (tp Node R ys)) = true).
      intros ? Hin.
      unfold In_path_membership in Hin.
      destruct xs.
      destruct p.
      rewrite Heqlp in Hin.
      unfold construct_all_paths in Hin.
      rewrite map_map in Hin.
      rewrite map_id in Hin.
      destruct (Hpl l Hl Huv Hm Hin) as 
      (ys & Hln & Hina & Hmb).
      exists (c, d, (ys ++ [(d, d, 1)])).
      split.
      rewrite Heqlpp.
      unfold In_path_membership.
      assert(Hlt: (length ys <= (length finN - 1))%nat).
      nia.
      eapply in_eq_bool_enum_path.
      exact Hlt.
      exact Hina.
      simpl.
      assert (Htt: (measure_of_path Node R 1 mulR (ys ++ [(d, d, 1)]) +
      measure_of_path Node R 1 mulR l =r=
      measure_of_path Node R 1 mulR (ys ++ [(d, d, 1)]))= 
      (measure_of_path Node R 1 mulR ys * (1 * 1) +
      measure_of_path Node R 1 mulR l =r=
      measure_of_path Node R 1 mulR ys * (1 * 1))).
      apply congrR.
      apply congrP.
      pose proof path_split_measure (ys ++ [(d, d, 1)]) ys [(d, d, 1)] as Htv.
      simpl in Htv.
      rewrite triple_elem_eq_list_refl in Htv;
      try assumption.
      exact (Htv eq_refl).
      apply refR.
      pose proof path_split_measure (ys ++ [(d, d, 1)]) ys [(d, d, 1)] as Htv.
      simpl in Htv.
      rewrite triple_elem_eq_list_refl in Htv;
      try assumption.
      exact (Htv eq_refl).
      rewrite Htt; clear Htt.
      rewrite <-Hmb.
      apply congrR.
      apply congrP.
      remember (measure_of_path Node R 1 mulR ys) as a.
      rewrite <- (one_right_identity_mul a).
      apply congrR.
      apply congrM.
      apply refR.
      apply one_left_identity_mul.
      apply refR.
      apply refR.
      remember (measure_of_path Node R 1 mulR ys) as a.
      rewrite <- (one_right_identity_mul a).
      apply congrR.
      apply congrM.
      apply refR.
      apply one_left_identity_mul.
      apply refR.
      specialize (Hsu Htt).
      apply symR.
      exact Hsu.
  Qed.


 
  Lemma zero_stable_partial_sum_path (right_distributive_mul_over_plus : forall a b c : R, 
        (a + b) * c =r= a * c + b * c = true) : 
    forall k m,
    (∀ u v : Node, (u =n= v) = true → (m u v =r= 1) = true) ->
    mat_cong Node eqN R eqR m -> 
    (forall (c d : Node), 
      partial_sum_paths _ eqN _  0 1 plusR mulR finN m (length finN - 1)%nat c d =r= 
      partial_sum_paths _ eqN _  0 1 plusR mulR finN m (k + length finN - 1)%nat c d = true).
  Proof.
    intros * Huv Hm ? ?.
    assert (Htt: 
    (partial_sum_paths Node eqN R 0 1 plusR mulR finN m (length finN - 1) c d =r=
    partial_sum_paths Node eqN R 0 1 plusR mulR finN m (k + length finN - 1) c d) =
    (sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (length finN - 1) c d) =r= 
    sum_all_flat_paths Node R 0 1 plusR mulR
      (enum_all_paths_flat Node eqN R 1 finN m (k + length finN - 1) c d))).
    apply congrR.
    apply flat_map_path_partial_sum.
    apply flat_map_path_partial_sum.
    rewrite Htt; clear Htt.
    apply sum_all_flat_paths_fixpoint;
      try assumption.
  Qed.


End Pathprops.


  



    
    
    

   
