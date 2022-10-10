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


  Theorem find_min_node_list_split : 
    forall ls u a ur ar, 
    @find_min_node _ (brel_lt_left eqT add) 
      (u, a) ls = (ur, ar) ->
      (ur, ar) = (u, a) ∨
      ∃ lsl lsr, ls = lsl ++ [(ur, ar)] ++ lsr.
  Proof.
    refine(fix Fn ls {struct ls} :=
      match ls as ls' return ls = ls' -> _ 
      with 
      | [] => _ 
      | (ah, bh) :: lst => _
      end eq_refl).
    + intros Ha ? ? ? ? Hb.
      left; simpl in Hb.
      auto.
    + intros Ha ? ? ? ? Hb.
      simpl in Hb.
      destruct (find_min_node (u, a) lst) 
        as (uax, uay) eqn:Ht.
      unfold brel_lt_left, theory.below,
      brel_lte_left, and.bop_and, uop_not in Hb.
      destruct (Fn lst _ _ _ _ Ht) as [Hc | Hc].
      ++
        case (eqT uax (add uax ah)) eqn:He;
        case (eqT ah (add ah uax)) eqn:Hf; 
        simpl in Hb;
        inversion Hb; 
        inversion Hc;
        subst.
        +++
          right.
          exists [], lst.
          simpl.
          reflexivity.
        +++
          left; reflexivity.
        +++
          right.
          exists [], lst. 
          simpl; reflexivity.
        +++
          right.
          exists [], lst.
          simpl; reflexivity.
      ++
        destruct Hc as (lsl & lsr & Hd).
        case (eqT uax (add uax ah)) eqn:He;
        case (eqT ah (add ah uax)) eqn:Hf; 
        simpl in Hb;
        inversion Hb;
        subst.
        +++
          right.
          exists [], (lsl ++ [(uax, uay)] ++ lsr);
          simpl; reflexivity.
        +++
          right.
          exists ((ah, bh) :: lsl),
            lsr; simpl; reflexivity.
        +++
          right.
          exists [], (lsl ++ [(uax, uay)] ++ lsr);
          simpl; reflexivity.
        +++
          right.
          exists [], (lsl ++ [(uax, uay)] ++ lsr);
          simpl; reflexivity.
  Qed.

        

  (* This theorem asserts that ur is a minimum 
    element wrt (brel_lte_left eqT add) *)
   (* I need + to be selective! *)
  Theorem find_min_node_list : 
    forall ls u a ur ar, 
    @find_min_node _ (brel_lt_left eqT add) 
      (u, a) ls = (ur, ar) ->
    forall x y, In (x, y) ls -> 
    brel_lt_left eqT add ur x = true.
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
          unfold brel_lt_left,theory.below,
          brel_lte_left, and.bop_and, uop_not
          in * |- *.
          case (eqT u (add u ah)) eqn:He;
          case (eqT ah (add ah u)) eqn:Hf; 
          simpl in Hc.
         
          +++
            inversion Hc; inversion Hd; 
            subst; clear Hc; clear Hd.
          (* This does not look provable,
             unless we assume that all 
             the T values are unique! 
             if we take add_sel axiom, 
             add x x = x, 
             eqT x x = true 
             true & false = true. 

             This is only provable 
             when all the T values are 
             different, i.e., u <> x!
          *)  
          admit.
          +++
            inversion Hc; inversion Hd; 
            subst; clear Hc; clear Hd. 
            (* We can prove this *)
            admit.
          +++
            inversion Hc; inversion Hd; 
            subst; clear Hc; clear Hd.
            (* does not look provable, 
              unless all the T values are
              unique *)
            admit.
          +++
            inversion Hc; inversion Hd; 
            subst; clear Hc; clear Hd.
             



    
          

  
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
    unfold remove_min.
    refine(fix Fn vs {struct vs} :=
      match vs as vs' return vs = vs' -> _ 
      with 
      | [] => fun Hv vss qk f Ha => _ 
      | hdvs :: tlvs => fun Hv vss qk f Ha => _ 
      end eq_refl).
    + 
      simpl in Ha.
      congruence.
    +
      simpl in Ha.
      destruct (find_min_node (f hdvs, hdvs) 
        (map (λ x : Node, (f x, x)) tlvs)) as (ua, ub) eqn:Hb.
      destruct (Nat.eq_dec ub hdvs) as [Hc | Hc].
      ++ 
        inversion Ha; clear Ha.
        exists [], tlvs.
        repeat split.
        (* This goal will only be true 
          when qk does not appear in 
          tlvs. Now, it should be the 
          case because nodes are 
          unique *)
        admit.
        rewrite <-H0, <-Hc.
        reflexivity.
      ++ 
        inversion Ha.
        

    
   
      
     

  Lemma remove_min_some_implies_least_element : 
    forall (vs : list Node) (f : Node -> T)
    (vss : list Node) (qk : Node), 
    @remove_min _ (brel_lte_left eqT add) vs f = Some (qk, vss)
    -> forall x : Node, In x vs -> 
        brel_lte_left eqT add (f qk) (f x) = true. 
  Proof.
    intros.
  Admitted.







End Priority_Queue_Proofs.