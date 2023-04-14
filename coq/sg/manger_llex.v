Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.trivial.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.minset. 
Require Import CAS.coq.eqv.manger_sets.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.reduce.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.

Require Import CAS.coq.theory.set.
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.uop.commutative_composition. 
Import ListNotations.
(* 
  A = type of active component
  P = type of passive component

  See cas/coq/uop/commutative_composition.v 
  for a description of the composition 
  of two reductions, r1 and 2, that 
  commute: 
     r1 (r1 s) = r1 (r2 s). 

  I believe this is the case for our manger reductions: 

   r1 = uop_manger_phase_1

   r2 = uop_manger_phase_2 

   both considered as reductions over 

   b = bop_union (brel_product eqA eqP). 

 *)

Section Theory.
  Variables
    (A P : Type)
    (zeroP : P) (* 0 *)
    (eqA lteA : brel A)
    (eqP : brel P)
    (addP : binary_op P)
    (wA : A)
    (wP : P) 
    (fA : A -> A) 
    (ntA : brel_not_trivial A eqA fA)
    (conA : brel_congruence A eqA eqA) 
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA)
    (conP : brel_congruence P eqP eqP)
    (cong_addP : bop_congruence P eqP addP) 
    (refP : brel_reflexive P eqP)
    (symP : brel_symmetric P eqP)
    (trnP : brel_transitive P eqP)
    (conLte : brel_congruence A eqA lteA) 
    (refLte : brel_reflexive A lteA)
    (trnLte : brel_transitive A lteA) 
    (ntot : brel_not_total A lteA)
    (addP_assoc : bop_associative P eqP addP)
    (addP_com : bop_commutative P eqP addP)
    (* idempotence is baked in this addP_cong *)
    (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
    (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true)
    (addP_gen_idempotent : ∀ x y : P, eqP x y = true → eqP (addP x y) y = true)
    (addP_assoc_cong : ∀ x y z : P, addP x (addP y z) = addP (addP x y) z)
    (addP_com_cong : ∀ x y : P, addP x y = addP y x).
    
  Local Definition eqAP : brel (A * P)
    := brel_product eqA eqP.
  
  Local Definition eqSAP : brel (finite_set (A * P))
    := brel_set eqAP.
  
  Local Definition bSAP : binary_op (finite_set (A * P))
    := bop_union eqAP.

  Lemma conAP : brel_congruence (A * P) eqAP eqAP.
  Proof. apply brel_product_congruence; auto. Qed. 

  Lemma refAP : brel_reflexive (A * P) eqAP.
  Proof. apply brel_product_reflexive; auto. Qed. 

  Lemma symAP : brel_symmetric (A * P) eqAP.
  Proof. apply brel_product_symmetric; auto. Qed. 

  Lemma trnAP : brel_transitive (A * P) eqAP.
  Proof. apply brel_product_transitive; auto. Qed. 

  Lemma conSAP : brel_congruence (finite_set (A * P)) eqSAP eqSAP.
  Proof. apply brel_set_congruence.
         - apply refAP. 
         - apply symAP.
         - apply trnAP.
  Qed. 


  Lemma refSAP : brel_reflexive (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_reflexive. 
         - apply refAP. 
         - apply symAP. 
  Qed. 

  Lemma symSAP : brel_symmetric (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_symmetric. Qed. 

  Lemma trnSAP : brel_transitive (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_transitive. 
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_cong : bop_congruence _ eqSAP bSAP.
  Proof. apply bop_union_congruence.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_associative : bop_associative _ eqSAP bSAP.
  Proof. apply bop_union_associative.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_commutative : bop_commutative _ eqSAP bSAP.
   Proof. apply bop_union_commutative.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_idempotent : bop_idempotent _ eqSAP bSAP.
  Proof. apply bop_union_idempotent.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed.

  (*  Ha! this is interesting. 
      The witness from sg.union.bop_union_not_selective for our type eqAP is (X, Y), where 
      X =  (wA, wP) ::nil 
      Y =  (fA wA, wP) ::nil
      where 
      Variable fA : A -> A. 
      Variable ntA brel_not_trivial A eqA fA.

      Ouch!  This does not work for Lemma nsel_witness_is_a_reduction_witness below. 
    
      That lemma needs 

        uop_manger { (wA, wP), (fA wA, wP)} not in { { (wA, wP) }, { (fA wA, wP)}}

      BUT, wA <> fA wA, so the minset of P2 will choose one of them!!! Ouch! 

    Solution?  It seems we need to come up with a bespoke proof of bSAP_not_selective
    just for this file, so that the witness makes this Lemma true. 
    But the witness has to be simple enough so that 
    we can prove fst_nsel_witness_is_fixed_point and snd_nsel_witness_is_fixed_point. 
    So, we need X and Y such that 

    1) uop_manger X = X
    2) uop_manger Y = Y
    3) uop_manger (X union Y) not in {X, Y}. 

    This can be done.  Here's how. 
    The whole scheme of manger only makes sence when lteA is a partial order. 
    So, let (a1, a2) be the witness for (ntot : brel_not_total A lteA), 
    then 
    X = {
    Y = {(a2, wP)} 
    will work since 
    uop_manger {(a1, wP), (a2, wP)} = {(a1, wP), (a2, wP)}. 

    Here is the bespoke proof of lack of selectivity for union: 
   *)
  Lemma bSAP_not_selective : bop_not_selective _ eqSAP bSAP.
  Proof. destruct ntot as [[a1 a2] [L R]].
         exists ((a1, wP)::nil, (a2, wP)::nil). split.
         - case_eq(eqSAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) ((a1, wP) :: nil)); intro H1; auto.
           apply brel_set_elim_prop in H1.
           destruct H1 as [H1 H2].
           assert (H3 : in_set eqAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) (a2, wP) = true).
           {
             apply in_set_bop_union_intro.
             + apply symAP.
             + apply trnAP.
             + right. apply in_set_cons_intro.
               * apply symAP.
               * left. apply refAP. 
           }
           assert (H4 := H1 _ H3).
           apply in_set_cons_elim in H4.
           + destruct H4 as [H4 | H4].
             * apply brel_product_elim in H4. destruct H4 as [H4 H5].
               assert (H6 := refLte a1).
               assert (H7 := conLte _ _ _ _ (refA a1) H4).
               rewrite H7 in H6. rewrite H6 in L.
               exact L. 
             * compute in H4.
               discriminate H4.
           + apply symAP.
           + apply symAP.
           + apply trnAP.
         - case_eq(eqSAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) ((a2, wP) :: nil)); intro H1; auto.
           apply brel_set_elim_prop in H1.
           destruct H1 as [H1 H2].
           assert (H3 : in_set eqAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) (a1, wP) = true).
           {
             apply in_set_bop_union_intro.
             + apply symAP.
             + apply trnAP.
             + left. apply in_set_cons_intro.
               * apply symAP.
               * left. apply refAP. 
           }
           assert (H4 := H1 _ H3).
           apply in_set_cons_elim in H4.
           + destruct H4 as [H4 | H4].
             * apply brel_product_elim in H4. destruct H4 as [H4 H5].
               assert (H6 := refLte a1).
               assert (H7 := conLte _ _ _ _ (refA a1) H4).
               rewrite H6 in H7. rewrite H7 in L.
               exact L. 
             * compute in H4.
               discriminate H4.
           + apply symAP.
           + apply symAP.
           + apply trnAP.
  Defined. 

  Local Notation "x =S= y" := (eqSAP x y = true) (at level 70,
  only parsing).
  Local Notation "[P1]" := (uop_manger_phase_1 eqA addP)
    (only parsing).  (* Phase 1 reduction *) 
  Local Notation "[P2]" := (@uop_manger_phase_2 A P lteA)
    (only parsing). (* Phase 2 reduction *)



  (* These admitted lemmas will come from Matrix.algorithm because 
    Tim is working on it, so for the moment I am admitting it. *)

  Lemma sum_fn_congruence_general_set :
    forall (Xa Xb : finite_set (A * P)),
    Xa =S= Xb ->
    eqP (matrix_algorithms.sum_fn zeroP addP snd Xa)
    (matrix_algorithms.sum_fn zeroP addP snd Xb) = true.
  Proof.
  Admitted.


  (* End of admit that will come from library *)



   (* This is easy.  *)
  Lemma sum_fn_filter_cong :
    forall (X Y: finite_set (A * P)) ap, 
    X =S= Y ->
    eqP 
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) X))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) Y)) = true.
  Proof.
    intros * Ha.
    eapply sum_fn_congruence_general_set,
    filter_congruence_gen;
    try assumption.
    intros (au, av) (bu, bv) Hb.
    eapply brel_product_elim in Hb.
    destruct Hb as (Hbl & Hbr).
    eapply conA; try assumption.
    eapply refA.
  Qed.
    


   (* This is easy!  *)
  Lemma bop_union_comm : 
    forall (X Y : finite_set (A * P)), 
    bop_union eqAP X Y =S= bop_union eqAP Y X.
  Proof.
    intros *.
    eapply brel_set_intro_prop;
    [eapply refAP|split; intros (ap, bp) Ha].
    +
      eapply in_set_uop_duplicate_elim_elim in Ha.
      eapply in_set_uop_duplicate_elim_intro;
      [eapply symAP|eapply trnAP|].
      eapply in_set_concat_intro.
      eapply in_set_concat_elim in Ha;
      [|eapply symAP].
      destruct Ha as [Ha | Ha];
      [right | left]; exact Ha.
    +
      eapply in_set_uop_duplicate_elim_elim in Ha.
      eapply in_set_uop_duplicate_elim_intro;
      [eapply symAP|eapply trnAP|].
      eapply in_set_concat_intro.
      eapply in_set_concat_elim in Ha;
      [|eapply symAP].
      destruct Ha as [Ha | Ha];
      [right | left]; exact Ha.
  Qed.


  (* easy *)
  Lemma bop_union_cong : 
    forall (X Y U : finite_set (A * P)), 
    X =S= Y ->
    (bop_union eqAP X U) =S= (bop_union eqAP Y U).
  Proof.
    intros * Ha.
    eapply brel_set_elim_prop in Ha;
    [|eapply symAP|eapply trnAP];
    destruct Ha as [Hal Har].
    eapply brel_set_intro_prop;
    [eapply refAP|split; intros (ap, bp) Hb].
    +
      eapply in_set_uop_duplicate_elim_elim in Hb.
      eapply in_set_uop_duplicate_elim_intro;
      [eapply symAP|eapply trnAP|].
      eapply in_set_concat_intro.
      eapply in_set_concat_elim in Hb;
      [|eapply symAP].
      destruct Hb as [Hb | Hb];
      [left | right].
      eapply Hal; exact Hb.
      exact Hb.
    +
      eapply in_set_uop_duplicate_elim_elim in Hb.
      eapply in_set_uop_duplicate_elim_intro;
      [eapply symAP|eapply trnAP|].
      eapply in_set_concat_intro.
      eapply in_set_concat_elim in Hb;
      [|eapply symAP].
      destruct Hb as [Hb | Hb];
      [left | right].
      eapply Har; exact Hb.
      exact Hb.
  Qed.

  (* should be in library *)
  Lemma in_set_congruence :
    forall (X : finite_set (A * P)) ap ax bp bx, 
    eqA ap ax = true -> eqP bp bx = true ->
    in_set eqAP X (ax, bx) = true ->
    in_set eqAP X (ap, bp) = true.
  Proof.
    induction X as [|(au, bu) X IHx].
    +
      intros * Ha Hb Hc.
      cbn in Hc; congruence.
    +
      intros * Ha Hb Hc.
      cbn in Hc |- *.
      eapply Bool.orb_true_iff in Hc.
      destruct Hc as [Hc | Hc].
      ++
        eapply Bool.andb_true_iff in Hc.
        destruct Hc as [Hcl Hcr].
        rewrite (trnA _ _ _ Ha Hcl), 
        (trnP _ _ _ Hb Hcr); cbn;
        reflexivity.
      ++
        eapply Bool.orb_true_iff;
        right; eapply IHx;
        [exact Ha | exact Hb | exact Hc].
  Qed.




  (* This is also easy*)
  Lemma bop_union_in_set_true_rewrite :
    forall (X Y : finite_set (A * P)) ax bx,
    in_set eqAP (X ++ Y) (ax, bx) = true -> 
    (bop_union eqAP ((ax, bx) :: X) Y) =S=
    (bop_union eqAP X Y).
  Proof.
    intros * Ha.
    eapply brel_set_intro_prop;
    [eapply refAP|split; intros (au, bu) Hb].
    +
      cbn in Hb; rewrite Ha in Hb.
      exact Hb.
    +
      cbn; rewrite Ha;
      exact Hb.
  Qed.
  

  (* This is also easy. *)
  Lemma bop_union_in_set_false_rewrite :
    forall (X Y : finite_set (A * P)) ax bx,
    in_set eqAP X (ax, bx) = false -> 
    (bop_union eqAP ((ax, bx) :: X) Y) =S=
    (ax, bx) :: (bop_union eqAP X Y).
  Proof.
    intros * Ha.
    eapply brel_set_intro_prop;
    [eapply refAP|split; intros (ap, bp) Hb].
    +
      cbn in Hb |- *.
      eapply Bool.orb_true_iff.
      case_eq (in_set eqAP (X ++ Y) (ax, bx));
      intro Hc; rewrite Hc in Hb.
      ++
        right.
        eapply in_set_uop_duplicate_elim_elim in Hb.
        eapply in_set_uop_duplicate_elim_intro;
        [eapply symAP|eapply trnAP|].
        eapply in_set_concat_intro.
        eapply in_set_concat_elim in Hb;
        [|eapply symAP].
        destruct Hb as [Hb | Hb];
        [left | right]; exact Hb.
      ++
        cbn in Hb; eapply Bool.orb_true_iff in Hb.
        destruct Hb as [Hb | Hb].
        left; exact Hb.
        right.
        eapply in_set_uop_duplicate_elim_elim in Hb.
        eapply in_set_uop_duplicate_elim_intro;
        [eapply symAP|eapply trnAP|].
        eapply in_set_concat_intro.
        eapply in_set_concat_elim in Hb;
        [|eapply symAP].
        destruct Hb as [Hb | Hb];
        [left | right]; exact Hb.
    +
      cbn in Hb |- *.
      eapply Bool.orb_true_iff in Hb.
      case_eq (in_set eqAP (X ++ Y) (ax, bx));
      intros Hc.
      ++
        destruct Hb as [Hb | Hb].
        +++
          eapply in_set_uop_duplicate_elim_intro;
          [eapply symAP|eapply trnAP|].
          eapply Bool.andb_true_iff in Hb.
          destruct Hb as [Hbl Hbr].
          (* congruence *)
          eapply in_set_congruence;
          [exact Hbl | exact Hbr | exact Hc].
        +++
          unfold bop_union in Hb.
          exact Hb.
      ++
        destruct Hb as [Hb | Hb].
        +++
          cbn; rewrite Hb; cbn;
          reflexivity.
        +++
          cbn; eapply Bool.orb_true_iff;
          right.
          eapply in_set_uop_duplicate_elim_elim in Hb.
          eapply in_set_uop_duplicate_elim_intro;
          [eapply symAP|eapply trnAP|];
          exact Hb.
  Qed.
  

  (* easy *)
  Lemma sum_fn_filter_bop_union_cong : 
    forall (X Y U : finite_set (A * P)) ap, 
    X =S= Y ->
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) (bop_union eqAP X U)))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) (bop_union eqAP Y U))) = true.
  Proof.
    intros * Ha.
    eapply sum_fn_filter_cong, bop_union_cong;
    try assumption.
  Qed.
 

  Lemma in_set_true_case_analysis : 
    forall (X Y : finite_set (A * P)) ax bx, 
    in_set eqAP (X ++ Y) (ax, bx) = true ->
    (in_set eqAP X (ax, bx) = true) ∨
    (in_set eqAP X (ax, bx) = false ∧ 
    in_set eqAP Y (ax, bx) = true).
  Proof.
    induction X as [|(ap, bp) X IHx].
    +
      intros * Ha.
      cbn in Ha |- *.
      right; refine (conj eq_refl Ha).
    + 
      intros * Ha.
      cbn in Ha |- *.
      case_eq (and.bop_and (eqA ax ap) (eqP bx bp));
      case_eq ((in_set eqAP (X ++ Y) (ax, bx)));
      intros Hb Hc; 
      rewrite Hb, Hc in Ha;
      cbn in Ha; try congruence.
      ++
        left; cbn;
        reflexivity.
      ++
        left; cbn;
        reflexivity.
      ++
        cbn; eapply IHx.
        exact Hb.
  Qed.


  (* This is easy*)
  Lemma in_set_false_case_analysis : 
    forall (X Y : finite_set (A * P)) ax bx, 
    in_set eqAP (X ++ Y) (ax, bx) = false ->
    in_set eqAP X (ax, bx) = false ∧ 
    in_set eqAP Y (ax, bx) = false.
  Proof.
    induction X as [|(ap, bp) X IHx].
    +
      intros * Ha.
      cbn in Ha |- *.
      exact (conj eq_refl Ha).
    +
      intros * Ha;
      cbn in Ha |- *.
      case_eq (and.bop_and (eqA ax ap) (eqP bx bp));
      case_eq ((in_set eqAP (X ++ Y) (ax, bx)));
      intros Hb Hc; 
      rewrite Hb, Hc in Ha;
      cbn in Ha; try congruence.
      cbn; eapply IHx; exact Hb.
  Qed.

  


  (* start of admit *)

  (* Difficult! generalise that empty list. This need 
    idempotence. It can't be proven without 
    idempotence. *)
  Lemma fold_left_in_set_true_rewrite : 
    forall (X U : finite_set (A * P)) ax bx,
    in_set eqAP (X ++ U) (ax, bx) = true -> 
    (fold_left (manger_merge_sets_new eqA addP) X
      (manger_merge_sets_new eqA addP U (ax, bx))) =S= 
    (fold_left (manger_merge_sets_new eqA addP) X U).
  Proof.
  Admitted.



  Lemma in_set_false_case_analysis_gen : 
    forall (X : finite_set (A * P)) ax bx, 
    in_set eqAP X (ax, bx) = false ->
    (forall ap bp, in_set eqAP X (ap, bp) = true ->
      (eqA ax ap = false ∨ 
      (eqA ax ap = true ∧ eqP bx bp = false))).
  Proof.
    induction X as [|(au, bu) X IHx].
    +
      intros * Ha * Hb.
      cbn in Hb; 
      congruence.
    +
      intros * Ha * Hb.
      cbn in Ha, Hb.
      eapply Bool.orb_false_iff in Ha.
      destruct Ha as (Hal & Har).
      case_eq (and.bop_and (eqA ap au) (eqP bp bu));
      case_eq ((in_set eqAP X (ap, bp))); 
      intros Hc Hd; rewrite Hc, Hd in Hb;
      cbn in Hb; try congruence.
      ++
        eapply Bool.andb_true_iff in Hd.
        destruct Hd as (Hdl & Hdr).
        case_eq (eqA ax au);
        case_eq (eqP bx bu);
        intros He Hf;
        rewrite He, Hf in Hal;
        cbn in Hal; try congruence;
        try auto.
      ++
        eapply Bool.andb_true_iff in Hd.
        destruct Hd as (Hdl & Hdr).
        case_eq (eqA ax au);
        case_eq (eqP bx bu);
        intros He Hf;
        rewrite He, Hf in Hal;
        cbn in Hal; try congruence.
        +++
          right;
          rewrite (trnA _ _ _ Hf (symA _ _ Hdl));
          refine (conj eq_refl _).
          case_eq (eqP bx bp);
          try reflexivity;
          intro Hg.
          rewrite (trnP _ _ _ Hg Hdr) in He;
          congruence.
        +++
          left; 
          case_eq (eqA ax ap);
          intro Hg; try reflexivity.
          rewrite (trnA _ _ _ Hg Hdl) in Hf;
          congruence.
        +++
          left;
          case_eq (eqA ax ap);
          intro Hg; try reflexivity.
          rewrite (trnA _ _ _ Hg Hdl) in Hf;
          congruence.
    ++
      eapply IHx; assumption.
  Qed.
      




 

  (* end of admit *)
  

  Lemma sum_fn_cong_bop_union_X_gen_acc : 
    forall (X Y U : finite_set (A * P)) ap, 
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap)
        (bop_union eqAP 
          (fold_left (manger_merge_sets_new eqA addP) X U) Y)))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) 
        (bop_union eqAP (bop_union eqAP X U) Y))) = true.
  Proof.
    induction X as [|(ax, bx) X IHx].
    +
      intros *; cbn.
      assert (Ha : (uop_duplicate_elim eqAP (uop_duplicate_elim eqAP U ++ Y)) =
        (uop_duplicate_elim eqAP (U ++ Y))). admit.
      rewrite Ha; now rewrite refP.
    +
      intros *; simpl.
      case_eq (in_set eqAP (X ++ U) (ax, bx));
      intros Ha.
      ++
        eapply trnP with 
        (matrix_algorithms.sum_fn zeroP addP snd
        (filter (λ '(x, _), eqA x ap) (bop_union eqAP
        (fold_left (manger_merge_sets_new eqA addP) X U) Y))).
        +++
          eapply sum_fn_filter_bop_union_cong;
          subst;
          eapply fold_left_in_set_true_rewrite;
          try assumption.
        +++
          eapply symP, trnP with 
            (matrix_algorithms.sum_fn zeroP addP snd
            (filter (λ '(x, _), eqA x ap) 
              (bop_union eqAP (bop_union eqAP X U) Y))).
          eapply  sum_fn_filter_cong, bop_union_cong.
          subst; eapply bop_union_in_set_true_rewrite;
          try assumption.
          eapply symP; subst; eapply IHx.
      ++
        (* It seems that I am running out of steam!
          I don't how to prove it.  *)
        unfold manger_merge_sets_new at 2;
        unfold manger_merge_sets_new_aux at 1;
        simpl;
        remember (fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
        (filter (λ '(s2, _), eqA ax s2) U) (ax, bx)) as Ua.
        destruct Ua as (Uax, Ubx).
        remember (filter (λ '(s2, _), negb (eqA ax s2)) U) as Ub.
        (* 
        (fold_left (manger_merge_sets_new eqA addP) X (Ub ++ [(Uax, Ubx)]))
        =S= 
        (fold_left (manger_merge_sets_new eqA addP) X Ub) ++ 
        ((fold_left (manger_merge_sets_new eqA addP) X [(Uax, Ubx)])
        *)
  Admitted.

        
  

  Lemma sum_fn_cong_bop_union_X : 
    forall (X Y : finite_set (A * P)) ap, 
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap)
        (bop_union eqAP 
          (fold_left (manger_merge_sets_new eqA addP) X []) Y)))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) (bop_union eqAP X Y))) = true.
  Proof.
    intros *.
    pose proof sum_fn_cong_bop_union_X_gen_acc X Y [] ap as Ha.
    cbn in Ha.
    assert (Hb : (bop_union eqAP X []) = X).
    admit.
    rewrite Hb in Ha.
    eapply Ha.
  Admitted.

    


  Lemma sum_fn_cong_bop_union_Y : 
    forall (X Y : finite_set (A * P)) ap, 
    eqP
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap)
        (bop_union eqAP X 
          (fold_left (manger_merge_sets_new eqA addP) Y []))))
    (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x ap) (bop_union eqAP X Y))) = true.
  Proof.
  Admitted.

  Lemma bop_congruence_bProp_fst : 
    forall (a : A),
    theory.bProp_congruence (A * P) (brel_product eqA eqP)
    (λ '(x, _), eqA x a).
  Proof.
    intros a.
    unfold theory.bProp_congruence.
    intros (aa, ap) (ba, bp) He.
    apply brel_product_elim in He.
    destruct He as [Hel Her].
    case_eq (eqA aa a); intro Hf.
    eapply symA in Hel.
    rewrite (trnA _ _ _  Hel Hf);
    reflexivity.
    case_eq (eqA ba a); intro Hg.
    rewrite (trnA _ _ _ Hel Hg) in Hf;
    congruence.
    reflexivity.
  Qed.

  Lemma bop_congruence_bProp_snd : 
    forall (pa : A),theory.bProp_congruence _  
    (brel_product eqA eqP)
    (λ '(s2, _), eqA pa s2).
  Proof.
    intros pa (aa, ap) (ba, bp) He.
    apply brel_product_elim in He.
    destruct He as [Hel Her].
    case_eq (eqA pa aa); intro Hf.
    rewrite (trnA pa aa ba Hf Hel);
    reflexivity.
    case_eq (eqA pa ba); intro Hg.
    apply symA in Hel.
    rewrite (trnA pa ba aa Hg Hel) in Hf;
    congruence.
    reflexivity.
  Qed.


  (* show [P1] is a reduction *)  
  Lemma P1_cong : uop_congruence _ eqSAP [P1].
  Proof.
    intros X Y Ha.
    eapply brel_set_intro_prop;
    [exact refAP| refine(pair _ _); intros (ap, bp) Hb].
    + 
      unfold uop_manger_phase_1, 
      manger_phase_1_auxiliary in Hb |- *;
      rewrite manger_merge_set_funex in Hb |- *.
      eapply in_set_fold_left_mmsn_intro with 
      (zeroP := zeroP); try assumption.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; try assumption.
        destruct Hb as [(q & Hbl) Hbr].
        eapply brel_set_elim_prop in Ha;
        [|exact symAP | eapply trnAP].
        destruct Ha as [Hal Har].
        exists q; eapply Hal;
        rewrite app_nil_r in Hbl;
        exact Hbl.
        cbn; reflexivity.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; cbn; try assumption;
        try reflexivity.
        destruct Hb as [Hbl Hbr].
        rewrite app_nil_r in Hbr |- *.
        rewrite <-list_filter_lib_filter_same,
        filter_arg_swap_gen with (a := ap), 
        list_filter_lib_filter_same; try assumption;
        try (apply refA).
        assert (Hc : (filter (λ '(x, _), eqA x ap) X) =S= 
        (filter (λ '(x, _), eqA x ap) Y)).
        eapply filter_congruence_gen; try assumption;
        try (apply bop_congruence_bProp_fst).
        eapply symP, trnP.
        eapply sum_fn_congruence_general_set,
        brel_set_symmetric; exact Hc.
        eapply symP; exact Hbr.
    +
      unfold uop_manger_phase_1, 
      manger_phase_1_auxiliary in Hb |- *;
      rewrite manger_merge_set_funex in Hb |- *.
      eapply in_set_fold_left_mmsn_intro with 
      (zeroP := zeroP); try assumption.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; try assumption.
        destruct Hb as [(q & Hbl) Hbr].
        eapply brel_set_elim_prop in Ha;
        [|exact symAP | eapply trnAP].
        destruct Ha as [Hal Har].
        exists q; eapply Har;
        rewrite app_nil_r in Hbl;
        exact Hbl.
        cbn; reflexivity.
      ++
        eapply in_set_fold_left_mmsn_elim with 
        (zeroP := zeroP) in Hb; cbn; try assumption;
        try reflexivity.
        destruct Hb as [Hbl Hbr].
        rewrite app_nil_r in Hbr |- *.
        rewrite <-list_filter_lib_filter_same,
        filter_arg_swap_gen with (a := ap), 
        list_filter_lib_filter_same; try assumption;
        try (apply refA).
        assert (Hc : (filter (λ '(x, _), eqA x ap) X) =S= 
        (filter (λ '(x, _), eqA x ap) Y)).
        eapply filter_congruence_gen; try assumption;
        try (apply bop_congruence_bProp_fst).
        eapply symP, trnP.
        eapply sum_fn_congruence_general_set;
        exact Hc.
        eapply symP; exact Hbr.
  Qed.

        

  
  Lemma P1_idem : uop_idempotent _ eqSAP [P1].
  Proof.
    eapply uop_manger_phase_1_uop_idempotent;
    try assumption.
    unfold bop_idempotent;
    intros.
    eapply addP_gen_idempotent;
    now rewrite refP.
  Qed.
  
  


  Lemma P1_left : bop_left_uop_invariant _ 
    eqSAP (bop_reduce [P1] bSAP) [P1].
  Proof.
    intros X Y;
    eapply brel_set_intro_prop;
    [exact refAP| refine(pair _ _); intros (ap, bp) Ha].
    +
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          eapply in_set_uop_manger_phase_1_elim in Hall;
          auto.
          destruct Hall as ((q' & Halll) & Hallr).
          exists q'.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          left; exact Halll.
        +++
          exists q.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          right; exact Halr.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in Har |- *;
        rewrite manger_merge_set_funex in Har.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply sum_fn_cong_bop_union_X].
    +
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          eexists.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          left;
          eapply in_set_uop_manger_phase_1_intro; auto;
          exists q; exact Hall.
        +++
          exists q.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          right; exact Halr.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in *;
        rewrite manger_merge_set_funex in *.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply symP, sum_fn_cong_bop_union_X].
  Qed.

      

  
  Lemma P1_right : bop_right_uop_invariant _ eqSAP (bop_reduce [P1] bSAP) [P1].
  Proof.
    intros X Y.
    eapply brel_set_intro_prop;
    [exact refAP| refine(pair _ _); intros (ap, bp) Ha].
    +
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          exists q.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          left; exact Hall.
        +++
          eapply in_set_uop_manger_phase_1_elim 
          in Halr; auto;
          destruct Halr as ((q' & Halrl) & Halrr).
          eexists.
          eapply in_set_bop_union_intro;
          [eapply symAP | eapply trnAP | ].
          right; exact Halrl.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in Har;
        rewrite manger_merge_set_funex in Har.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply sum_fn_cong_bop_union_Y].
    + 
      unfold bop_reduce in Ha |- *.
      eapply in_set_uop_manger_phase_1_elim in Ha; 
      auto.
      destruct Ha as ((q & Hal) & Har).
      unfold bSAP in Hal.
      eapply in_set_bop_union_elim in Hal; 
      [|eapply symAP].
      eapply in_set_uop_manger_phase_1_intro;
      auto.
      ++
        destruct Hal as [Hall | Halr].
        +++
          eexists.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          left; exact Hall.
        +++
          eexists.
          eapply in_set_bop_union_intro;
          [apply symAP | eapply trnAP|].
          right; eapply in_set_uop_manger_phase_1_intro;
          auto; exists q; exact Halr.
      ++
        unfold uop_manger_phase_1, 
        manger_phase_1_auxiliary in *;
        rewrite manger_merge_set_funex in *.
        eapply trnP;[exact Har |
        rewrite list_filter_lib_filter_same;
        eapply symP, sum_fn_cong_bop_union_Y].
  Qed.


  (* show [P2] is a reduction. 

     Mukesh: I've modified minset_union so that it is now
     compatible with our Manger definitions. 
     So, now we can get the following results about [P2] 
     from more general results about uop_minset and bop_minset_union. 
  *)  
  Lemma P2_cong : uop_congruence _ eqSAP [P2].
  Proof. unfold uop_manger_phase_2.
         apply uop_minset_congruence_weak.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.
  
  Lemma P2_idem : uop_idempotent _ eqSAP [P2].
  Proof. unfold uop_manger_phase_2.
         apply uop_minset_idempotent. 
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
  Qed.

  Lemma P2_left : bop_left_uop_invariant _ eqSAP (bop_reduce [P2] bSAP) [P2].
  Proof. apply minset_union_left_uop_invariant.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.

  Lemma P2_right : bop_right_uop_invariant _ eqSAP (bop_reduce [P2] bSAP) [P2].
  Proof. apply minset_union_right_uop_invariant.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.




 

  Lemma cong_manger_preorder : (brel_congruence (A * P) 
    (brel_product eqA eqP) (manger_pre_order lteA)).
  Proof.
    intros (a, b) (c, d) (u, v) (w, x) Ha Hb.
    cbn. unfold brel_trivial.
    f_equal.
    eapply brel_product_elim in Ha, Hb.
    eapply conLte.
    exact (fst Ha).
    exact (fst Hb).
  Qed.


  Lemma ref_manger_pre_order :
    (brel_reflexive (A * P) (manger_pre_order lteA)).
  Proof.
   intros (a, b).
   cbn.
   rewrite refLte;
   unfold brel_trivial;
   reflexivity.
  Qed.
  
  Lemma tran_manger_pre_order : 
    brel_transitive (A * P) (manger_pre_order lteA).
  Proof.
    intros (a, b) (c, d) (e, f) Ha Hb;
    cbn in Ha, Hb |- *.
    unfold brel_trivial in Ha, Hb |- *;
    rewrite Bool.andb_true_r in Ha, Hb |- *.
    rewrite trnLte;
    [reflexivity | exact Ha | exact Hb].
  Qed.




  

 


  Lemma set_are_eq_reduce : 
    forall (X : finite_set (A * P)) a p,
    (∀ t : A * P,
      in_set (brel_product eqA eqP) X t = true ->
      theory.below (manger_pre_order lteA) (a, p) t = false) ->
    (List.filter (λ '(x, _), eqA x a) X) =S= 
    (List.filter (λ '(x, _), eqA x a) 
        (uop_minset (manger_pre_order lteA) X)).
  Proof.
    intros * Ha.
    eapply brel_set_intro_prop.
    + exact refAP.
    +
      split.
      ++
        intros (au, bu) Hb.
        rewrite list_filter_lib_filter_same in Hb |- *.
        eapply in_set_filter_elim in Hb.
        destruct Hb as [Hbl Hbr].
        * 
          eapply in_set_filter_intro;
          [eapply symAP | eapply bop_congruence_bProp_fst| ].
          split;
          [exact Hbl |].
          eapply in_minset_intro;
          [eapply refAP | eapply symAP | eapply cong_manger_preorder |
          eapply ref_manger_pre_order |].
          split;
          [exact Hbr | intros (ta, tb) Hc].
          specialize (Ha _ Hc).
          eapply theory.below_false_intro.
          eapply theory.below_false_elim in Ha.
          destruct Ha as [Ha | Ha].
          **
            left; rewrite <- Ha.
            unfold manger_pre_order, brel_product,
            brel_trivial in Ha |- *;
            repeat rewrite Bool.andb_true_r in |- *.
            eapply conLte;
            [eapply refA | exact Hbl].
          **
            right; rewrite <-Ha.
            unfold manger_pre_order, brel_product,
            brel_trivial in |- *;
            repeat rewrite Bool.andb_true_r in |- *.
            eapply conLte;
            [exact Hbl | eapply refA].
        *
          eapply bop_congruence_bProp_fst.
      ++
        intros (au, bu) Hb.
        rewrite list_filter_lib_filter_same in Hb |- *.
        eapply in_set_filter_elim in Hb;
        [|eapply bop_congruence_bProp_fst].
        destruct Hb as [Hbl Hbr].
        eapply in_minset_elim in Hbr;
        [|eapply refAP | eapply symAP | eapply cong_manger_preorder|
        eapply ref_manger_pre_order | eapply tran_manger_pre_order ].
        eapply in_set_filter_intro;
        [eapply symAP | eapply bop_congruence_bProp_fst|].
        split;
        [exact Hbl | ].
        destruct Hbr as (Hbrl & Hbrr).
        exact Hbrl.
  Qed.
      



          

  (* In this proof, let's not unfold uop_minset *)
  Lemma matrix_algorithm_addP : 
    forall (X : finite_set (A * P)) a p,
    (∀ t : A * P,
      in_set (brel_product eqA eqP) X t = true ->
      theory.below (manger_pre_order lteA) (a, p) t = false) ->
    eqP 
    (matrix_algorithms.sum_fn zeroP addP 
      snd (List.filter (λ '(x, _), eqA x a) X))
    (matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x a) 
        (uop_minset (manger_pre_order lteA) X))) = true.
  Proof.
    intros * Ha.
    pose proof set_are_eq_reduce X a p Ha as Hb.
    remember (List.filter (λ '(x, _), eqA x a) X) as Xa.
    remember (List.filter (λ '(x, _), eqA x a)
      (uop_minset (manger_pre_order lteA) X)) as Xb.
    eapply sum_fn_congruence_general_set;
    try assumption.
  Qed.
     

   (* 
    Tim: Now, show that the two reductions commute! 
    **** I hope this is true! *****
    Seems true but difficult.

    Mukesh: yes, it's true and difficult as well.
    
  *)

  Lemma P1_P2_commute : ∀ X, ([P2] ([P1] X)) =S= ([P1] ([P2] X)).
  Proof.
    intros ?.
    eapply brel_set_intro_prop.
    + exact refAP.
    +
      split.
      ++
        intros (a, p) Ha.
        eapply in_set_uop_manger_phase_2_elim in Ha;
        try assumption.
        destruct Ha as (Hal & Har).
        (* from Hal we know that 
        *)
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Hal;
        try assumption.
        destruct Hal as ((qt & Hall) & Halr).
        (*  from Halr we know that sum of 
        all 'a's is equal to p *)
        (* now apply intro rule in the goal *)
        eapply in_set_uop_manger_phase_1_intro with 
        (zeroP := zeroP);
        try assumption.
        (* What should be q ?? 
        What is uop_manger_phase_2 is doing? *)
        eexists.
        eapply in_set_uop_manger_phase_2_intro;
        try assumption.
        exact Hall.
        intros * Hb.
        eapply Har.
        eapply in_set_uop_manger_phase_1_intro 
        with (zeroP := zeroP); try assumption.
        exists q; exact Hb.
        instantiate (1 :=
        (matrix_algorithms.sum_fn zeroP addP snd 
          (List.filter (λ '(x, _), eqA x b) X)));
        eapply refP.
        rewrite <-list_filter_lib_filter_same in 
        Halr.
        (* comment *)
        unfold uop_manger_phase_2.
        (* from Har, I can infer below *)
        assert (Hc : ∀ (b : A) (q : P),
          in_set (brel_product eqA eqP) X (b, q) = true → 
          theory.below lteA a b = false).
        intros * Ha. eapply Har.
        eapply in_set_uop_manger_phase_1_intro
        with (zeroP := zeroP); try assumption.
        exists q; exact Ha.
        instantiate (1 :=
        (matrix_algorithms.sum_fn zeroP addP snd 
          (List.filter (λ '(x, _), eqA x b) X)));
        eapply refP.
        (* think! *)
        assert (He : ∀ t : A * P,
          in_set (brel_product eqA eqP) X t = true → 
          theory.below (manger_pre_order lteA) (a, p) t = false).
        intros (c, d) He.
        specialize (Hc c d He).
        eapply theory.below_false_elim in Hc.
        eapply theory.below_false_intro.
        destruct Hc as [Hc | Hc].
        left; cbn; rewrite Hc; reflexivity.
        right; cbn; rewrite Hc; reflexivity. 
        (* end comment here *)
        eapply trnP.
        exact Halr.
        eapply matrix_algorithm_addP.
        exact He.
      ++
        intros (a, p) Ha.
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Ha;
        try assumption.
        destruct Ha as ((qt & Hal) & Har).
        eapply in_set_uop_manger_phase_2_elim in Hal;
        try assumption.
        destruct Hal as (Hall & Halr).
        eapply in_set_uop_manger_phase_2_intro;
        try assumption.
        +++
          eapply in_set_uop_manger_phase_1_intro
          with (zeroP := zeroP); try assumption.
          exists qt; exact Hall.
          unfold uop_manger_phase_2 in Har.
          pose proof in_minset_implies_in_set
          (A * P) (brel_product eqA eqP)
          symAP (manger_pre_order lteA) as Hb.
          rewrite <-list_filter_lib_filter_same in Har.
          (* comment here *)

          assert (He : ∀ t : A * P,
          in_set (brel_product eqA eqP) X t = true → 
          theory.below (manger_pre_order lteA) (a, p) t = false).
          intros (c, d) He.
          specialize (Halr c d He).
          eapply theory.below_false_elim in Halr.
          eapply theory.below_false_intro.
          destruct Halr as [Hc | Hc].
          left; cbn; rewrite Hc; reflexivity.
          right; cbn; rewrite Hc; reflexivity.
         
          (* end comment *)
          eapply trnP;
          [exact Har | eapply symP, matrix_algorithm_addP].
          exact He.
        +++
          intros * Hb.
          eapply in_set_uop_manger_phase_1_elim 
          with (zeroP := zeroP) in Hb; try assumption.
          destruct Hb as ((qp & Hbl) & Hbr).
          eapply Halr; exact Hbl.
    Qed.

    

  (* Given the above lemmas, we can now use the results of 
     cas/coq/uop/commutative_composition.v to 
     prove everything we need to build a 
     commutative and idempotent semigroup. 
     (Note : ignoring existence of id and ann for now ...) 
   *)

  Definition uop_manger := uop_compose [P2] [P1].
  Definition eq_manger :=  brel_reduce eqSAP uop_manger. 
  Definition bop_manger := bop_reduce uop_manger bSAP.

  (* to show non-selectivity of the reduced semigroup we need to prove some things about the witness for 
     non-selectivity of bSAP. 
  *) 
  Lemma fst_nsel_witness_is_fixed_point : let (s, _) := projT1 bSAP_not_selective in uop_manger s =S= s.
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         compute. 
         rewrite refA. rewrite refP. rewrite refA. rewrite refP. reflexivity.
  Qed. 

  Lemma snd_nsel_witness_is_fixed_point : let (_, s) := projT1 bSAP_not_selective in uop_manger s =S= s.
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         compute. 
         rewrite refA. rewrite refP. rewrite refA. rewrite refP. reflexivity.
  Qed. 

  

  Lemma uop_manger_is_reduction : bop_uop_invariant eqSAP bSAP uop_manger.
  Proof. apply uop_compose_is_reduction.
         - exact symSAP. 
         - exact trnSAP. 
         - exact P1_cong. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

  Lemma bop_manger_congruence :
    bop_congruence _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_congruence. 
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

  Lemma bop_manger_associative :
    bop_associative _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_associative.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact bSAP_associative.           
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

    Lemma bop_manger_commutative :
    bop_commutative _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_commutative.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute.
         - exact bSAP_commutative. 
  Qed. 
 
  Lemma bop_manger_idempotent :
    bop_idempotent _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_idempotent.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute.
         - exact bSAP_idempotent. 
  Qed. 

  Lemma bop_manger_not_selective :
    bop_not_selective _ eq_manger bop_manger.
  Proof.
    destruct ntot as ((a₁, a₂) & Ha).
    exists ([(a₁, wP)], [(a₂, wP)]);
    cbn.
  Admitted. 

End Theory.   

