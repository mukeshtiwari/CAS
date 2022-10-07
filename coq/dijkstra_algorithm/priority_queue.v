Require Import List ListSet PeanoNat.
From CAS Require Import 
  coq.po.from_sg
  coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory.


Import ListNotations.


(* Find a library with proofs *)
Section Priority_Queue_Def.


  Definition Node := nat.
  
  Context 
    {T : Type} (* Type *)
    {C : T -> T -> bool}. (* Comparison operator *)


  (* This function returns the minimum node *)
  Fixpoint find_min_node
    (ua : T * Node)
    (ls : list (T * Node)) : T * Node :=
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



  Definition remove_min
    (vs : list Node) (* list of nodes *)
    (f : Node -> T) :  (* one row *)
    option (Node * list Node) :=
  match vs with 
  | [] => None
  | h :: t => 
    match find_min_node (f h, h) 
      (List.map (fun x => (f x, x)) t) 
    with 
    | (_, qk) => Some (qk, List.remove Nat.eq_dec qk vs) 
    end
  end.

End Priority_Queue_Def. (* End of Definitions *)
  
Section Priority_Queue_Proofs.

  Context 
    {T : Type}
    {zero one : T}
    {add mul : T -> T -> T}
    {eqT : brel T}
    {refT : brel_reflexive T eqT}
    {symT : brel_symmetric T eqT}
    {trnT : brel_transitive T eqT}.


  (* This theorem asserts that ur is a minimum 
    element *)
  Theorem find_min_node_empty_list : 
    forall ls u a ur ar, 
    @find_min_node _ (brel_lte_left eqT add) 
      (u, a) ls = (ur, ar) ->
    forall x y, In (x, y) ls -> brel_lte_left eqT add ur x = true.
  Proof.
  Admitted.
  

  

  Lemma remove_min_none_implies_empty_pq : 
    forall (vs : list Node) (f : Node -> T),
    @remove_min _ (brel_lte_left eqT add) vs f = None 
    <-> vs = [].
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
      destruct (find_min_node (f n, n) 
      (List.map (fun x => (f x, x)) l));
      inversion H.
    + subst; exact eq_refl.
  Qed.


End Priority_Queue_Proofs.