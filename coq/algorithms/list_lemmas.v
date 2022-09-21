(* This file contains list proofs which are not in coq/eqv/list.v *)

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
  coq.eqv.structures
  coq.eqv.theory
  coq.eqv.product
  coq.sg.properties
  coq.eqv.list.
Import ListNotations.


Section Listsingledefs.

  Variables
    (A : Type)
    (eqA : brel A).

    
  (* c covers l, i.e., every element of l appears in c *)
  Definition covers (c l : list A) : Prop :=
    ∀ x,  in_list eqA l x = true ->  in_list eqA c x = true.


  Fixpoint enum_list_dec (n : nat) : list nat :=
    match n with
    | O => [O]
    | S n' => n :: enum_list_dec n' 
    end.
 
End Listsingledefs.

Section Listsingleprops.
  
  Variables
    (A : Type)
    (eqA : brel A)
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA).

  Definition is_eq x y := eqA x y = true.
  Definition not_eq x y := eqA x y = false.  
  Definition is_list_eq a b := brel_list eqA a b = true.
  Definition is_in_list a l := in_list eqA l a = true.
  Definition not_in_list a l := in_list eqA l a = false.

  Local Infix "=L=" :=  is_list_eq (at level 70).
  Local Infix "=A=" :=  is_eq (at level 70).
  Local Infix "<A>" :=  not_eq (at level 70).  
  Local Infix "[in]" := is_in_list (at level 70).
  Local Infix "[!in]" := not_in_list (at level 70).

  (* tgg *) 
  Lemma list_mem_left_congruence : ∀ l c a,  c =A= a -> c [in] l -> a [in] l.
  Proof. induction l.
         + intros c a I J. compute in J. congruence. 
         + intros c d I J.
           apply in_list_cons_elim in J; auto. 
           apply in_list_cons_intro; auto.
           destruct J as [J | J]. 
           ++ left. exact (trnA _ _ _ J I). 
           ++ right. exact (IHl _ _ I J). 
  Qed.
  
  Lemma list_mem_not : ∀ l c a,  c =A= a -> a [!in] l -> c [!in] l.
  Proof. intros l c a I J.
         case_eq(in_list eqA l c); intro K; auto.
         unfold not_in_list in J. 
         rewrite (list_mem_left_congruence _ _ _ I K) in J. 
         congruence.
  Qed.          
(*  
  Proof.
    induction l; 
    simpl; 
    intros ? ? Heq Hf.
    + reflexivity.
    + apply Bool.orb_false_iff in Hf.
      destruct Hf as [Hfa Hfb].
      apply Bool.orb_false_iff.
      split.
      case_eq (eqA c a); 
      intro Hf; auto.
      apply symA in Hf.
      assert (Ht := trnA a c a0 Hf Heq).
      apply symA in Ht. 
      rewrite Hfa in Ht.
      inversion Ht.
      apply IHl with (a := a0).
      exact Heq. 
      exact Hfb.
  Qed.
*) 
  
  Lemma list_mem_true_false : ∀ l a c, a [!in] l -> c [in] l -> c <A> a.
  Proof. intros l a c I J.
         case_eq(eqA c a); intro K; auto.
         unfold not_in_list in I. 
         rewrite (list_mem_left_congruence _ _ _ K J) in I. 
         congruence.
  Qed.          
(*  
  Proof.
    induction l; 
    simpl; 
    intros ? ? Ha Hb.
    + inversion Hb.
    + apply Bool.orb_false_iff in Ha.
      apply Bool.orb_true_iff in Hb.
      destruct Ha as [Ha₁ Ha₂].
      destruct Hb as [Hb | Hb].
      apply symA in Hb.

      case_eq (eqA c a0); intros Hf; auto.
      pose proof (trnA _ _ _ Hb Hf) as Ht.
      apply symA in Ht. 
      rewrite Ha₁ in Ht.
      inversion Ht.
      apply IHl; assumption.
  Qed.
*) 




  Lemma list_split : 
    ∀ l c, l <> [] -> c [in] l-> no_dup _ eqA l = true
           -> exists l₁ l₂ : list A, 
               l =L= (l₁ ++ [c] ++ l₂) /\ c [!in] l₁ /\ c [!in] l₂.
  Proof.
    induction l; simpl.
    + intros ? H₁ H₂ H₃.
      inversion H₂.
    + intros c H₁ H₂ H₃.
      apply Bool.andb_true_iff in H₃.
      destruct H₃ as [Hl₃ Hr₃].
      apply Bool.orb_true_iff in H₂. fold (in_list eqA l c) in H₂. 
      destruct H₂ as [H₂ | H₂].
      ++ exists [], l; simpl; subst.
         apply Bool.negb_true_iff in Hl₃.
         split. apply Bool.andb_true_iff.
         split. apply symA. apply H₂.
         apply brel_list_reflexive; auto. 
         split. compute. reflexivity. 
         apply list_mem_not with (a := a). exact H₂. 
         exact Hl₃.          
      ++ destruct l as [|b l].
         +++ compute in H₂. discriminate H₂.
         +++ assert (Ht : b :: l <> []). intro Hf. inversion Hf.
             destruct (IHl c Ht H₂ Hr₃) as [la [lb [Ha [Hb Hc]]]].
             exists (a :: la), lb.
             assert (Hlf : (a :: la) ++ c :: lb = a :: la ++ c :: lb).
                simpl. reflexivity.
             rewrite Hlf. clear Hlf.
             apply Bool.negb_true_iff in Hl₃.
             split. apply Bool.andb_true_iff.
             split. apply refA.
             exact Ha.
             split. simpl.
             apply Bool.orb_false_iff.
             split. apply list_mem_true_false with (l := b :: l).
             exact Hl₃. exact H₂.
             exact Hb. exact Hc.
  Qed.
      

  Lemma list_split_gen : 
    ∀ (l : list A) (c : A), c [in] l -> exists l₁ l₂ : list A, l =L= (l₁ ++ [c] ++ l₂).
  Proof.
    induction l; simpl.
    + intros ? H₁. compute in  H₁. discriminate  H₁. 
    + intros c H₁.
      apply Bool.orb_true_iff in H₁.
      destruct H₁ as [H₁ | H₁].
      exists [], l.
      simpl.
      apply Bool.andb_true_iff.
      split. apply symA; assumption.
      apply brel_list_reflexive; auto. 
      destruct (IHl c H₁) as [l₁ [l₂ Hl]].
      exists (a :: l₁), l₂.
      simpl.
      apply Bool.andb_true_iff; split.
      apply refA. exact Hl.
  Qed.

  (*
Lemma list_eqv_in_list_rewrite :
      forall l c x, 
      list_eqv _ eqA c l = true ->
      in_list eqA c x = true ->
      in_list eqA l x = true.
    Proof.
      induction l; 
      destruct c; 
      simpl;
      intros ? Ha Hb.
      + congruence.
      + congruence.
      + congruence.
      + apply Bool.andb_true_iff in Ha.
        destruct Ha as [Hal Har].
        case (eqA x a0) eqn:Hxn.
        rewrite (trnA _ _ _ Hxn Hal).
        reflexivity.
        simpl in Hb.
        erewrite IHl.
        apply Bool.orb_true_iff.
        right.
        reflexivity.
        exact Har.
        exact Hb.
    Qed.

*) 

    Lemma list_eqv_in_list_rewrite : ∀ l c x, c =L= l -> x [in] c -> x [in] l.
    Proof.
      induction l; 
      destruct c; 
      simpl;
      intros ? Ha Hb.
      + congruence. 
      + compute in Ha. congruence. 
      + compute in Hb. congruence. 
      + apply Bool.andb_true_iff in Ha.
        fold (brel_list eqA c l) in Ha. 
        destruct Ha as [Hal Har].
        apply in_list_cons_intro; auto.         (** NB **) 
        apply in_list_cons_elim in Hb; auto.    (** NB **) 
        destruct Hb as [Hb | Hb].
        ++ left. exact (trnA _ _ _ (symA _ _ Hal) Hb). 
        ++ right. exact (IHl _ _ Har Hb). 
    Qed.

    

    Lemma length_le_Sn : 
      ∀ l c n, (length c < n)%nat -> c =L= l -> (length l < n)%nat.
    Proof.
      induction l.
      + simpl;
        intros * Ha Hb.
        nia.
      + simpl; 
        intros * Ha Hb.
        simpl in *.
        destruct c.
        - simpl in Hb. compute in Hb. discriminate Hb. 
        - simpl in Ha, Hb.
          apply Bool.andb_true_iff in Hb.
          destruct Hb as [Hbl Hbr].
          destruct n.
          nia.
          assert (Hc: (length c < n)%nat).
          nia.
          specialize (IHl _ _ Hc Hbr).
          nia.
    Qed.

    Lemma covers_list_elem : 
      ∀ (c l : list A) ,(∀ y : A, y [in] c) -> covers _ eqA c l.
    Proof.
      unfold covers.
      destruct c as [|a c].
      + intros ? Hy ? Hl.
        specialize (Hy x).
        simpl in Hy. compute in Hy. discriminate Hy.
      + intros ? Hy ? Hl.
        simpl in *.
        exact (Hy x). 
    Qed.


    Lemma in_list_mem_ex_one :
      ∀ l₁ l₂ a x, x <A> a -> x [in] (l₁ ++ a :: l₂) -> x [in] (l₁ ++ l₂).
    Proof.
      induction l₁; simpl.
      +  intros l₂ a x Hxa Hlx.
         apply in_list_cons_elim in Hlx; auto.
         destruct Hlx as [H | H]. 
         ++ apply symA in H. rewrite Hxa in H. discriminate H. 
         ++ exact H. 
      + intros l₂ a' x Hxa Hlx.
        apply in_list_cons_intro; auto. 
        apply in_list_cons_elim in Hlx; auto.         
        destruct Hlx as [H | H].
        ++ left. exact H.
        ++ apply in_list_concat_elim in H; auto.      (* NB *)    
           destruct H as [H | H].
           +++ right. apply in_list_concat_intro; auto. (* NB *)    
           +++ case_eq(eqA x a); intro G.
               ++++ left. apply symA. exact G. 
               ++++ right. apply (IHl₁ l₂ a' x Hxa).
                    apply in_list_concat_intro; auto. (* NB *)    
    Qed.


    Lemma covers_dup : 
      ∀ l (c : list A), 
      covers _ eqA c l ->  (length c < List.length l)%nat -> 
         exists a l₁ l₂ l₃, l =L= (l₁ ++ [a] ++ l₂ ++ [a] ++ l₃).
    Proof.
      induction l. 
      + simpl.
        intros * Ha Hb.
        nia.
      +
        (* a can be repeated or not *)
        simpl.
        intros * Ha Hb.
        unfold covers in Ha.
        destruct (in_list eqA l a) eqn:Hal.
        (* a in in the list and we have loop *)
        destruct (list_split_gen l a Hal) as 
          [l₁ [l₂ Hlt]].
        exists a, [], l₁, l₂.
        simpl in *.
        admit. 
(*        rewrite refA, Hlt.
        reflexivity.*) 
        (* a is not in l *)
        pose proof (Ha a) as Hw.
        simpl in Hw.
        rewrite refA in Hw.
        simpl in Hw.
        specialize (Hw eq_refl).
        destruct (list_split_gen c a Hw) as 
        [l₁ [l₂ Hlt]].
        specialize (IHl (l₁ ++ l₂)).
        assert (Hcov : covers _ eqA (l₁ ++ l₂) l).
        unfold covers.
        intros ? Hin.
        (* from Hal and Hin, we know that x <> a *)
        pose proof list_mem_true_false l _ _ Hal Hin as Hax.
        (* get a concrete instance *)
        pose proof (Ha x) as Hx.
        simpl in Hx.
        rewrite Hax, Hin in Hx.
        specialize (Hx eq_refl).
        pose proof list_eqv_in_list_rewrite _ _ _ 
          Hlt Hx as Hinc.
        eapply in_list_mem_ex_one;
        [exact Hax|
        simpl in Hinc;
        exact Hinc].
        specialize (IHl Hcov).
        pose proof length_le_Sn  
          _ _ _ Hb Hlt as Hwt.
        simpl in Hwt.
        rewrite app_length in Hwt.
        simpl in Hwt.
        rewrite PeanoNat.Nat.add_succ_r in Hwt.
        rewrite <-app_length in Hwt.
        assert (Hvt : (length (l₁ ++ l₂) < length l)%nat).
        nia.
        destruct (IHl Hvt) as
          (av & lv₁ & lv₂ & lv₃ & Hlp).
        exists av, (a :: lv₁), lv₂, lv₃.
        simpl.
        admit. 
Admitted. 

    Lemma list_eqv_in_list_rewrite_gen :
      ∀ l₁ l₂ a n,  a =A= n -> l₁ =L= l₂ -> n [in] l₂ -> a [in] l₁. 
    Proof.
      induction l₁ as [|a₁ l₁]; 
      destruct l₂ as [|b₂ l₂]; 
      simpl;
      intros ? ? Ha Hb Hc.
      + compute in Hc. discriminate Hc. 
      + compute in Hb. discriminate Hb. 
      + compute in Hc. discriminate Hc. 
      + apply Bool.andb_true_iff in Hb.
        destruct Hb as [Hbl Hbr].
        case_eq(eqA n b₂); intro Hxn. 
        (* pose proof (trnA _ _ _ Ha Hxn) as Han.        WHY pose proof??? *)
        ++ assert (Han := trnA _ _ _ Ha Hxn). 
           apply symA in Hbl.
           apply in_list_cons_intro; auto.               (* NB *) 
           left. 
           exact (symA _ _ (trnA _ _ _ Han Hbl)).
        ++  fold (brel_list eqA l₁ l₂) in Hbr. 
            apply in_list_cons_intro; auto.             (* NB *) 
            case_eq(eqA a₁ a); intro H.
            +++ left; auto. 
            +++ right. apply in_list_cons_elim in Hc; auto.  (* NB *) 
                destruct Hc as [Hc | Hc]. 
                ++++ apply symA in Hc. rewrite Hc in Hxn. discriminate Hxn. 
                ++++ exact (IHl₁ _ _ _ Ha Hbr Hc). 
    Qed.


    Lemma list_eqv_no_dup_rewrite :
      ∀ l₁ l₂, l₁ =L= l₂ -> no_dup _ eqA l₂ = false -> no_dup _ eqA l₁ = false.
    Proof.
      induction l₁.
      + simpl.
        intros ? Ha Hb.
        destruct l₂.
        ++ simpl in Hb.
           congruence.
        ++ compute in Ha. congruence. 
      + (* inductive case *)
        simpl.
        intros ? Ha Hb.
        destruct l₂.
        ++ simpl in Hb.
           congruence.
        ++ simpl in Hb.
           apply Bool.andb_true_iff in Ha.
           destruct Ha as [Hal Har].
           apply Bool.andb_false_iff in Hb.
           destruct Hb as [Hb | Hb].
           apply Bool.negb_false_iff in Hb.
           rewrite (list_eqv_in_list_rewrite_gen _ _ 
           _ _ Hal Har Hb).
           reflexivity.
           erewrite IHl₁.
           apply Bool.andb_false_iff.
           right.
           reflexivity.
           exact Har.
           exact Hb.
    Qed.


End Listsingleprops.


Section Listtripledefs.

  Variables
    (A B C : Type)
    (rA : brel A)
    (rB : brel B)
    (rC : brel C)
    (conA : brel_congruence A rA rA)    
    (refA : brel_reflexive A rA)
    (symA : brel_symmetric A rA)
    (trnA : brel_transitive A rA)
    (conB : brel_congruence B rB rB)        
    (refB : brel_reflexive B rB)
    (symB : brel_symmetric B rB)
    (trnB : brel_transitive B rB)
    (conC : brel_congruence C rC rC)        
    (refC : brel_reflexive C rC)
    (symC : brel_symmetric C rC)
    (trnC : brel_transitive C rC).


  Definition brel_triple : brel ((A * B) * C) := brel_product (brel_product rA rB) rC. 

  Lemma brel_triple_congruence : brel_congruence _ brel_triple brel_triple.
  Proof. apply brel_product_congruence; auto.
         apply brel_product_congruence; auto.
  Qed.          

  Lemma brel_triple_reflexive : brel_reflexive _ brel_triple.
  Proof. apply brel_product_reflexive; auto.
         apply brel_product_reflexive; auto.
  Qed.          

  Lemma brel_triple_symmetric : brel_symmetric _ brel_triple.
  Proof. apply brel_product_symmetric; auto.
         apply brel_product_symmetric; auto.
  Qed. 

  Lemma brel_triple_transitive : brel_transitive _ brel_triple.
  Proof. apply brel_product_transitive; auto.
         apply brel_product_transitive; auto.
  Qed. 

   Definition brel_triple_list : brel (list (A * B * C)) := brel_list brel_triple.   
   
   Lemma brel_triple_list_congruence : brel_congruence _ brel_triple_list brel_triple_list.
   Proof. apply brel_list_congruence.
          exact brel_triple_symmetric.
          exact brel_triple_transitive.
          exact brel_triple_congruence.
   Qed.     

   Lemma brel_triple_list_reflexive : brel_reflexive _ brel_triple_list.
   Proof. apply brel_list_reflexive. exact brel_triple_reflexive. Qed.

   Lemma brel_triple_list_symmetric : brel_symmetric _ brel_triple_list.
   Proof. apply brel_list_symmetric. exact brel_triple_symmetric. Qed.
   
   Lemma brel_triple_list_transitive : brel_transitive _ brel_triple_list.
   Proof. apply brel_list_transitive. exact brel_triple_transitive. Qed.
   
  
  (* This function tests if l₁ in l₂ or not 
  Fixpoint In_eq_bool (l₁ : list (A * B * C))
    (l₂ : list (list (A * B * C))) : bool :=
    match l₂ with
    | [] => false
    | h :: t => ((triple_elem_list l₁ h) || (In_eq_bool l₁ t))%bool 
    end.
   *)
   Definition in_triple_list_list := in_list brel_triple_list.

   
End Listtripledefs.


(*
Section Listtripleprops.

  Variables
    (A B C : Type)
    (rA : brel A)
    (rB : brel B)
    (rC : brel C).


  Lemma length_rewrite : ∀ xs ys,
    brel_triple_list _ _ _ rA rB rC xs ys = true -> List.length xs = List.length ys.
  Proof.
    induction xs.
    + intros * Hin.
      destruct ys.
      reflexivity.
      simpl in Hin. compute in Hin. discriminate Hin. 
    + intros * Hin.
      destruct ys.
      simpl in Hin.
      destruct a as ((u, v), w).  compute in Hin. discriminate Hin. 
      simpl in * |- *.
      destruct a as ((au, av), aw).
      destruct p as ((pu, pv), pw).
      apply Bool.andb_true_iff in Hin.
      destruct Hin as [_ Hin].
      apply f_equal. 
      apply IHxs; assumption.
  Qed.

  
  Lemma path_tl_rewrite : ∀ lss xs ys, 
      @triple_elem_list _ _ _ rA rB rC xs ys = true ->
      In_eq_bool _ _ _ rA rB rC xs lss = true -> 
      In_eq_bool _ _ _ rA rB rC ys lss = true.
    Proof.
      induction lss.
      + intros * Ht Hin.
        simpl in Hin.
        congruence.
      + intros * Ht Hin.
        simpl in Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        simpl.
        apply Bool.orb_true_iff.
        left.
        apply triple_elem_eq_list_trans with xs.
        apply triple_elem_eq_list_sym; assumption.
        exact Hin.
        simpl. apply Bool.orb_true_iff. 
        right.
        apply IHlss with xs; assumption.
    Qed.

    Lemma triple_trim_tail : ∀ (xs : list (A * B * C)) 
      (a b : A * B * C) (c : list (A * B * C)),
      triple_elem_list _ _ _ rA rB rC xs (a :: b :: c) = true ->
      triple_elem_list _ _ _ rA rB rC (List.tl xs) (b :: c) = true.
    Proof.
      destruct xs.
      - simpl; intros ? ? ? He.
        congruence.
      - simpl; intros ? ? ? He.
        repeat destruct p in He.
        destruct a in He.
        destruct p in He.
        apply Bool.andb_true_iff in He.
        destruct He as [Hel Her].
        exact Her.
    Qed.

    Lemma in_eq_bool_mem_first : 
      ∀ (l₁ l₂ : list (list (A * B * C)))
      (y : list (A * B * C)), 
      In_eq_bool _ _ _ rA rB rC y (l₁ ++ l₂) = true -> 
      In_eq_bool _ _ _ rA rB rC y l₁ = true \/ 
      In_eq_bool _ _ _ rA rB rC y l₂ = true.
    Proof.
      induction l₁.
      - simpl; intros ? ? Hin.
        right. exact Hin.
      - simpl; intros ? ? Hin.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        left. 
        apply Bool.orb_true_iff.
        left. exact Hin.
        destruct (IHl₁ _ _ Hin) as [H | H].
        left. 
        apply Bool.orb_true_iff.
        right. exact H.
        right.
        exact H.
    Qed.


    Lemma in_eq_bool_mem_second : 
      ∀ (l₁ l₂ : list (list (A * B * C)))
      (y : list (A * B * C)),
      In_eq_bool _ _ _ rA rB rC y l₁ = true \/ 
      In_eq_bool _ _ _ rA rB rC y l₂ = true -> 
      In_eq_bool _ _ _ rA rB rC y (l₁ ++ l₂) = true.
    Proof.
      induction l₁.
      - simpl; intros ? ? [Hin | Hin]; 
        congruence.
      - simpl; intros ? ? [Hin | Hin].
        apply Bool.orb_true_iff in Hin.
        apply Bool.orb_true_iff.
        destruct Hin as [Hin | Hin].
        left. exact Hin.
        right. 
        exact (IHl₁ l₂ y (or_introl Hin)).
        apply Bool.orb_true_iff.
        right.
        exact (IHl₁ l₂ y (or_intror Hin)).
    Qed.


    Lemma in_flat_map_bool_first : 
      ∀ (l : list A) (y : list (A * B * C))
      (f : A -> list (list (A * B * C))),
      In_eq_bool _ _ _ rA rB rC y (flat_map f l) = true -> 
      (exists x : A, in_list rA l x = true /\ 
      In_eq_bool _ _ _ rA rB rC y (f x) = true).
    Proof.
      induction l.
      - simpl; intros ? ? Hin.
        congruence.
      - simpl; intros ? ? Hin.
        apply in_eq_bool_mem_first in Hin.
        destruct Hin as [Hin | Hin].
        exists a. split.
        apply Bool.orb_true_iff.
        left. apply refA.
        exact Hin.
        destruct (IHl _ _ Hin) as [x [Hl Hr]].
        exists x. split.
        apply Bool.orb_true_iff.
        right. exact Hl.
        exact Hr.
    Qed.



    Lemma in_flat_map_bool_second : 
      ∀ (l : list A) 
      (f : A -> list (list (A * B * C)))
      (y : list (A * B * C)) (x : A),
      (∀ (x a : A) (y : list (A * B * C)),  
        rA x a = true -> 
        In_eq_bool _ _ _ rA rB rC y (f a) = 
        In_eq_bool _ _ _ rA rB rC y (f x)) ->
      in_list rA l x = true -> 
      In_eq_bool _ _ _ rA rB rC y (f x) = true ->
      In_eq_bool _ _ _ rA rB rC y (flat_map f l) = true.
    Proof.
      induction l.
      - simpl; intros ? ? ? Hc Hin Hf.
        congruence.
      - simpl; intros ? ? ? Hc Hin Hf.
        apply Bool.orb_true_iff in Hin.
        destruct Hin as [Hin | Hin].
        apply in_eq_bool_mem_second.
        left. rewrite <-Hf.
        apply Hc. exact Hin.
        apply in_eq_bool_mem_second.
        right. apply IHl with (x := x).
        exact Hc.
        exact Hin.
        exact Hf.
    Qed.


    (* boolean equivalent of in_flat_map *)
    Lemma in_flat_map_bool : 
      ∀ (l : list A) (y : list (A * B * C))
      (f : A -> list (list (A * B * C))),
      (∀ (x a : A) (y : list (A * B * C)),  
        rA x a = true -> 
        In_eq_bool _ _ _ rA rB rC y (f a) = 
        In_eq_bool _ _ _ rA rB rC y (f x)) ->
      In_eq_bool _ _ _ rA rB rC y (flat_map f l) = true <-> 
      (exists x : A, in_list rA l x = true /\ 
      In_eq_bool _ _ _ rA rB rC y (f x) = true).
    Proof.
      intros ? ? ? Hc; split; intros H.
      apply in_flat_map_bool_first; exact H.
      destruct H as [x [Hl Hr]].
      apply in_flat_map_bool_second with (x := x).
      exact Hc. exact Hl. exact Hr.
    Qed.


    Lemma orb_eq : ∀ (a b c : bool), 
      a = c -> (a || b = c || b)%bool.
    Proof using -All.
      intros [|] [|] [|] H; simpl;
      try reflexivity; try congruence.
    Qed.

    Lemma andb_eq : ∀ (a b c d e f g: bool), 
      (a && b && c = e && f && g)%bool -> 
      (a && b && c && d = e && f && g && d)%bool.
    Proof using -All.
      intros [|] [|] [|] [|] [|] [|] [|] H; simpl in * |- *;
      try reflexivity; try congruence.
    Qed.



    Lemma triple_elem_eq : 
      ∀ bl lrt, 
      triple_elem_list _ _ _ rA rB rC bl lrt = true ->
      (length lrt < S (S (length bl)))%nat.
    Proof.
      (* proof by nia? *)
      induction bl as [|((bau, bav), baw) bl].
      + intros [|((aau, aav), aaw) lrt].
        intros Ha.
        simpl.
        nia.
        intros Ha.
        simpl in Ha.
        congruence.
      + intros [|((aau, aav), aaw) lrt].
        intros Ha.
        simpl.
        nia.
        intros Ha.
        simpl in Ha.
        simpl.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        specialize (IHbl _ Ha).
        nia.
    Qed.


    Lemma triple_elem_rewrite_le : 
      ∀ bl llt awt lrt, 
      triple_elem_list _ _ _ rA rB rC bl (llt ++ [awt] ++ lrt) = true ->
      (length lrt < S (length bl))%nat.
    Proof.
      induction bl as [|((bau, bav), baw) bl].
      + simpl.
        intros * Ha.
        assert (Hlt : exists avt llw, llt ++ awt :: lrt = avt :: llw).
        destruct llt.
        simpl.
        exists awt, lrt.
        reflexivity.
        simpl.
        exists p, (llt ++ awt :: lrt).
        reflexivity.
        destruct Hlt as [avt [llw Hlw]].
        rewrite Hlw in Ha.
        congruence.
      + 
        intros * Ha.
        simpl.
        destruct llt as [|((llta, lltb), lltc) llt].
        simpl in Ha.
        destruct awt as ((awta, awtb), awtc).
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        eapply triple_elem_eq.
        exact Ha.
        simpl in Ha.
        apply Bool.andb_true_iff in Ha.
        destruct Ha as [_ Ha].
        specialize (IHbl _ _ _ Ha).
        nia.
    Qed.

    Lemma list_tl_lia : ∀ (xs : list A) k, 
      List.tl xs <> [] -> (length (List.tl xs) = S k)%nat ->
      (length xs = S (S k))%nat.
    Proof using -All.
      induction xs.
      + intros * Hf Hin.
        simpl in * |- *.
        congruence.
      + intros * Hf Hin.
        simpl in * |- *.
        lia.
    Qed.

  Lemma elem_path_aux_true : 
    ∀ (l : list A) (a : A),
    in_list rA l a = true -> 
    exists l₁ l₂ : list A, 
    brel_list rA l (l₁ ++ [a] ++ l₂) = true.
  Proof using A rA refA symA.
    induction l.
    - simpl; intros ? H; 
      congruence.
    - simpl; intros ? H.
      apply Bool.orb_true_iff in H.
      destruct H as [H | H].
      exists [], l; simpl.
      apply Bool.andb_true_iff.
      split.
      apply symA; exact H.
      apply brel_list_reflexive; auto. 
      destruct (IHl a0 H) as [l₁ [l₂ Ht]].
      exists (a :: l₁), l₂.
      simpl. apply Bool.andb_true_iff.
      split. apply refA.
      exact Ht.
  Qed.

 
  Lemma in_list_true : 
    ∀ l₁ l₂ a, in_list rA (l₁ ++ a :: l₂) a = true.
  Proof.
    induction l₁.
    + simpl.
      intros ? ?.
      rewrite refA.
      reflexivity.
    + simpl.
      intros ? ?.
      rewrite IHl₁.
      apply Bool.orb_true_iff.
      right.
      reflexivity.
  Qed.


  Lemma no_dup_false_one : 
    ∀ l₁ l₂ l₃ a, no_dup A rA (l₁ ++ a :: l₂ ++ a :: l₃) = false.
  Proof.
    induction l₁.
    + simpl.
      intros *.
      rewrite in_list_true.
      simpl.
      reflexivity.
    + simpl.
      intros *.
      rewrite IHl₁.
      apply Bool.andb_false_iff.
      right.
      reflexivity.
  Qed.
  

    
End Listtripleprops.
    

*)     

    




