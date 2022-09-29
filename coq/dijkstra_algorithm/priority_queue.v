Require Import List ListSet.
Import ListNotations.

(* Find a library with proofs *)
Section Priority_Queue.


  Context 
    {A : Type}
    {Hdec : forall (x y : A), {x = y} + {x <> y}}.

  Context 
    {U : Type} (* Type *)
    {C : U -> U -> bool}. (* Comparison operator *)


  (* This function returns the minimum node *)
  Fixpoint find_min_node
    (ua : U * A)
    (ls : list (U * A)) : U * A :=
  match ls with 
  | [] => ua
  | (uy, ay) :: t => 
    match C (fst ua) uy with 
    (* ua is so far minimal element *)
    | true =>  find_min_node ua t 
    (* (uy, ay) is minimal element *)
    | false => find_min_node (uy, ay) t 
    end
  end.


  (* This theorem asserts that ur is a minimum 
    element *)
  Theorem find_min_node_empty_list : 
    forall ls u a ur ar, 
    find_min_node (u, a) ls = (ur, ar) ->
    forall x y, In (x, y) ls -> C ur x = true.
  Proof.
    induction ls as [|(uax, uay) ls IHn].
    + intros ? ? ? ? Ha ? ? Hb.
      simpl in Ha.
      inversion Hb.
    + intros ? ? ? ? Ha ? ? Hb.
      destruct Hb as [Hb | Hb].
      inversion Hb;
      subst; clear Hb.
      - (* ur is a minimum element *)
        simpl in Ha.
  Admitted.
  (* Why am I trying to prove this? *)    

  


  Definition remove_min
    (vs : list A) (* list of nodes *)
    (f : A -> U) :  (* one row *)
    option (A * list A) :=
  match vs with 
  | [] => None
  | h :: t => 
    match find_min_node (f h, h) 
      (List.map (fun x => (f x, x)) t) 
    with 
    | (_, qk) => Some (qk, List.remove Hdec qk vs) 
    end
  end.
  

  Lemma remove_min_none_implies_empty_pq : 
    forall (vs : list A) (f : A -> U),
    remove_min vs f = None <-> vs = [].
  Proof.
    split; intros H.
    + refine(
      match vs as vs' 
        return vs = vs' -> _ 
      with
      | [] => fun Heq => eq_refl 
      | _ :: _ => fun Heq => _  
      end eq_refl).
      rewrite Heq in H.
      simpl in H.
      destruct (find_min_node (f a, a) 
      (List.map (fun x => (f x, x)) l));
      inversion H.
    + subst; exact eq_refl.
  Qed.


End Priority_Queue