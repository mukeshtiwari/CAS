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


  

End Pathdefs.

Section Pathprops.

  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN).

    (* carrier set and the operators *)
    Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).

  (* append node path function contains only 
    non-empty list *)  
  Lemma append_node_in_paths_non_empty_list : 
    forall (l : list (list (Node * Node * R))) 
      (m : Matrix Node R) (c : Node),  
    all_elems_non_empty_list _ 
    (append_node_in_paths Node R m c l) = true.
  Proof.
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
    forall (l : list (list (Node * Node * R))) 
    (m : Matrix Node R) (c : Node) 
    (xs : list (Node * Node * R)), 
    In_eq_bool _ _ _  eqN eqN eqR xs 
      (append_node_in_paths Node R m c l) = true -> 
    exists y ys, 
      triple_elem_list _ _ _ eqN eqN eqR 
        xs ((c, y, m c y) :: ys) = true /\
      source Node eqN R c xs = true /\ 
      source Node eqN R y ys = true /\ 
      ys <> [].
  Proof.
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
    forall (n : nat) (m : Matrix Node R) 
    (c d : Node) (xs : list (Node * Node * R))
    (finN : list Node), 
    In_eq_bool _ _ _ eqN eqN eqR xs 
      (all_paths_klength _ eqN _ oneR finN m n c d) = true -> 
    xs <> [].
  Proof.
    induction n.
    - simpl; intros ? ? ? ? ? Hin.
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
    - simpl; intros ? ? ? ? ? Hin.
      destruct (append_node_in_paths_eq
        (flat_map (λ x : Node, 
          all_paths_klength  _ eqN _ oneR finN m n x d) finN)
        m c xs Hin) as [y [ys [Hl Hr]]].
      intro Hf. 
      rewrite Hf in Hl.
      simpl in Hl. 
      congruence.
  Qed.




End Pathprops.


  



    
    
    

   