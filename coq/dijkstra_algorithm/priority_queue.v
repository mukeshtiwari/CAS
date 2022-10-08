Require Import List ListSet PeanoNat Utf8.
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
  Definition find_min_node
    (ua : T * Node)
    (ls : list (T * Node)) : T * Node :=
    List.fold_right (λ '(uaxls, uayls) '(uax, uay),
      if C uax uaxls then (uax, uay) else (uaxls, uayls))
      ua ls.

  
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
    {add : T -> T -> T}
    {eqT : brel T}
    {refT : brel_reflexive T eqT}
    {symT : brel_symmetric T eqT}
    {trnT : brel_transitive T eqT}
    {add_sel : forall (a b : T), 
      ((eqT (add a b) a) = true) + ((eqT (add a b) b) = true)}.


  (* This theorem asserts that ur is a minimum 
    element wrt (brel_lte_left eqT add) *)
   (* I need + to be selective! *)
  Theorem find_min_node_empty_list : 
    forall ls u a ur ar, 
    @find_min_node _ (brel_lte_left eqT add) 
      (u, a) ls = (ur, ar) ->
    forall x y, In (x, y) ls -> 
    brel_lte_left eqT add ur x = true.
  Proof.
    refine(fix Fn ls {struct ls} :=
      match ls as ls' return ls = ls' -> _ 
      with 
      | [] => _ 
      | (ah, bh) :: lst => 
        match lst as lst' 
          return lst = lst' -> _ 
        with 
        | [] => _ 
        | (ahh, bhh) :: lstt => _ 
        end eq_refl
      end eq_refl).
      + intros Ha ? ? ? ? Hb ? ? Hc.
        simpl in Hc;
        tauto.
      + intros Ha Hb ? ? ? ? Hc ? ? [Hd | Hd].
        ++
          simpl in Hc.
          unfold brel_lte_left in * |- *.
          inversion Hd; subst;
          clear Hd.
          case (eqT u (add u x)) eqn:Ht.
          inversion Hc; subst; clear Hc.
          exact Ht.
          inversion Hc; subst; clear Hc.
          (* we need selectivity *)
          case (add_sel ur ur) eqn:Ha;
          apply symT; exact e.
        ++ simpl in Hd.
           tauto.
      + intros Ha Hb ? ? ? ? Hc ? ? Hd.
        rewrite <-Ha in Hb, Hc, Hd.
        destruct Hd as [Hd | Hd].
        ++
          unfold brel_lte_left.
          simpl in Hc.
          destruct (find_min_node (u, a) lst) as (uax, uay) eqn:Ht.
          unfold brel_lte_left in Hc.
          case (eqT uax (add uax ah)) eqn:Heqt.
          inversion Hc. 
          inversion Hd.
          rewrite <-H0, <-H2.
          exact Heqt.
          inversion Hc.
          inversion Hd.
          rewrite <-H0, <-H2.
          (* we need selectivity *)
          case (add_sel ah ah) eqn:He;
          apply symT; exact e.
        ++ (* inductive case *)
          simpl in Hc.
          destruct (find_min_node (u, a) lst) as (uax, uay) eqn:Ht.
          unfold brel_lte_left in Hc.
          case (eqT uax (add uax ah)) eqn:Heqt.
          inversion Hc.
          rewrite <-H0.
          eapply Fn.
          exact Ht.
          exact Hd.
          unfold brel_lte_left.
          inversion Hc.
          rewrite <-H0.
          (* Now I know that ah is the minimum 
            element *)
          pose proof (Fn lst _ _ _ _ Ht x y Hd) as He.
          unfold brel_lte_left in He.
          (* From He, I know that 
            uax is lowest element.
            If I use add_sel lemma 
            I know in Heqt 
            add uax ah = ah 
            eqT uax ah = false 
          *)
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


  Lemma remove_min_some_implies_non_empty_pq : 
    forall (vs : list Node) 
    (vss : list Node) (qk : Node) (f : Node -> T), 
    @remove_min _ (brel_lte_left eqT add) vs f = Some (qk, vss)
    -> exists (vsl vsr : list Node),
       vss = vsl ++ vsr ∧ 
       vs = vsl ++ [qk] ++ vsr.
  Proof.
    induction vs.
    + intros ? ? ? Hr.
      simpl in Hr.
      congruence.
    + intros ? ? ?.
      simpl; intros Ha.
      destruct (find_min_node (f a, a) (map (λ x : Node, (f x, x)) vs))
        eqn:Hb.
      
    

  Admitted.


  Lemma remove_min_some_implies_least_element : 
    forall (vs : list Node) (f : Node -> T)
    (vss : list Node) (qk : Node), 
    @remove_min _ (brel_lte_left eqT add) vs f = Some (qk, vss)
    -> (forall x : Node, In x vs -> 
        brel_lte_left eqT add (f qk) (f x) = true). 
  Proof.
  Admitted.







End Priority_Queue_Proofs.