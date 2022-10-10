Require Import List ListSet PeanoNat Utf8
  Mergesort.
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
    {eqT : brel T}
    {add : binary_op T}.

  Definition lte (a b : T * Node) :=
    (brel_lte_left eqT add) (fst a) (fst b).


  Fixpoint find_min_node 
    (m : T * Node)
    (carry : list (T * Node))
    (l : list (T * Node)) : (T * Node) * list (T * Node) :=
    match l with 
    | [] => (m, carry)
    | h :: l' => 
      if lte h m then find_min_node h (m :: carry) l' 
      else find_min_node m (h :: carry) l' 
    end. 

 
  Definition remove_min_pq 
    (pq : list (T * Node)) :
    option ((T * Node) * list (T * Node)) :=
  match pq with 
  | [] => None
  | h :: t => Some (find_min_node h [] t)
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
    {commutative : forall (a b : T), 
      (eqT (add a b) (add b a)) = true}
    {add_sel : forall (a b : T), 
      ((eqT (add a b) a) = true) + ((eqT (add a b) b) = true)}.

  
  Theorem find_min_node_list_split : 
    forall ls ua ur ar carry, 
    @find_min_node T eqT add
      ua carry ls  = (ur, ar) ->
      ur = ua ∨
      ∃ lsl lsr, ls = lsl ++ [ur] ++ lsr ++ carry.
  Proof.
    refine(fix Fn ls {struct ls} :=
      match ls as ls' return ls = ls' -> _ 
      with 
      | [] => _ 
      | (ah, bh) :: lst => _
      end eq_refl).
    + intros Ha ? ? ? ? Hb.
      left;
      inversion Hb; auto.
    + intros Ha ? ? ? ? Hb.
      simpl in Hb;
      unfold lte, brel_lte_left in Hb;
      simpl in Hb.
      destruct ua as (uah, uat) eqn:Hua;
      destruct ur as (uar, hrt) eqn:Hur;
      simpl in Hb;
      destruct (eqT ah (add ah uah)) eqn:Ht.
      ++
        (* ah is minimum *)
        (* it's easy *) 
       
  Admitted.

  (* everything is fine upto this point *)


  (* This theorem asserts that ur is a minimum 
    element wrt (brel_lte_left eqT add) *)
   (* I need + to be selective! 
      + to be commutative and we 
      total order 
   *)
  Theorem find_min_node_least_elem : 
    forall ls ua ur ar, 
    @find_min_node _ (brel_lte_left eqT add) 
      ua ls = (ur, ar) ->
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