Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.manger_sets.
Require Import CAS.coq.eqv.reduce
  CAS.coq.uop.commutative_composition
  CAS.coq.uop.properties.

Require Import CAS.coq.sg.properties
  CAS.coq.sg.product.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.reduce. 

(* for testing *)
Require Import CAS.coq.sg.manger_llex.
Require Import CAS.coq.eqv.nat. 
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.po.from_sg.
Import ListNotations.


Section Computation.


(* 
  A = type of active component
  P = type of passive component
*)   

(* replace bSAP with this one *)

Definition manger_product_phase_0
  {A P : Type}
  (eqA : brel A)
  (eqP : brel P)                       
  (mulA : binary_op A)
  (mulP : binary_op P) : binary_op (finite_set (A * P)) := 
  bop_lift (brel_product eqA eqP) (bop_product mulA mulP). 

(* 
 Print bop_lift. 
 Print bop_list_product_left.
 Print ltran_list_product.
 Print uop_manger.
 Print uop_manger_phase_1.
 Print manger_phase_1_auxiliary.
*)

Definition bop_manger_product 
  {A P : Type}
  (eqA lteA : brel A)
  (eqP : brel P)            
  (addP : binary_op P)
  (mulA : binary_op A)
  (mulP : binary_op P) : binary_op (finite_set (A * P)) :=
  bop_reduce (@uop_manger A P eqA lteA addP) 
    (manger_product_phase_0 eqA eqP mulA mulP).


End Computation.



(* 
Section Testing.

(*  A = nat * nat, P = nat *) 
   
Local Definition eqA := brel_product brel_eq_nat brel_eq_nat. 
Local Definition addA := bop_product bop_min bop_min. 
Local Definition lteA := brel_lte_left eqA addA. 
Local Definition mulA := bop_product bop_plus bop_plus. 

Local Definition eqP  := brel_eq_nat.
Local Definition addP := bop_min. 
Local Definition mulP := bop_plus.

Local Definition manger_add := @bop_manger _ _ eqA lteA eqP addP.
Local Definition manger_mul := bop_manger_product eqA lteA eqP addP mulA mulP.
(*
  Check manger_add.
  : binary_op (finite_set (nat * nat * nat))

  Check manger_mul.
  : binary_op (finite_set (nat * nat * nat))
 *)

Open Scope nat_scope. 

Local Definition s1 := ((1, 2), 8) :: nil.
Local Definition s2 := ((3, 5), 9) :: nil.
Local Definition s3 := ((0, 5), 9) :: nil.
Local Definition s4 := ((1, 2), 10) :: nil.
Local Definition s5 := ((1, 2), 1):: ((1, 2), 2)::((1, 2), 3) :: nil.
Compute (manger_add s1 s2). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s3). (* = (0, 5, 9) :: (1, 2, 8) :: nil *)
Compute (manger_add s1 s4). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s1). (* = (1, 2, 8) :: nil *)
Compute (manger_add s5 nil). (* = (1, 2, 1) :: nil *)
Compute (manger_add nil s5). (* = (1, 2, 1) :: nil *)
Compute (manger_mul s1 s2). (* = (4, 7, 17) :: nil *) 
Compute (manger_mul s2 s5). (* = (4, 7, 10) :: nil *)
Compute (manger_add (manger_mul s5 s1) (manger_mul s5 s3)). 
(* (1, 7, 10) :: (2, 4, 9) :: nil *) 
Compute (manger_mul s5 (manger_add s1 s3)).                 
(* (2, 4, 9) :: (1, 7, 10) :: nil *) 

End Testing.
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
  (mulA : binary_op A)
  (mulP : binary_op P)
  (refA : brel_reflexive A eqA)
  (symA : brel_symmetric A eqA)
  (trnA : brel_transitive A eqA)
  (refP : brel_reflexive P eqP)
  (symP : brel_symmetric P eqP)
  (trnP : brel_transitive P eqP)
  (ntot : properties.brel_not_total A lteA)
  (conP : brel_congruence P eqP eqP)
  (cong_addP : bop_congruence P eqP addP) 
  (conLte : brel_congruence A eqA lteA) 
  (refLte : brel_reflexive A lteA)
  (trnLte : brel_transitive A lteA) 
  (addP_assoc : bop_associative P eqP addP)
  (addP_com : bop_commutative P eqP addP)
  (idemP : bop_idempotent P eqP addP)
  (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
  (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true).

(* Assumption about mulA and mulP  *)
Variables 
  (mulA_assoc : bop_associative A eqA mulA)
  (mulP_assoc : bop_associative P eqP mulP)
  (cong_mulA : bop_congruence A eqA mulA)
  (cong_mulP : bop_congruence P eqP mulP)
  (mulP_addP_right_distributive : 
    (bop_right_distributive P eqP addP mulP))
  (mulA_left_cancellative : bop_left_cancellative A lteA mulA)
  (mulA_right_cancellative : bop_right_cancellative A lteA mulA).

Local Notation "[EQP0]" :=  (brel_set (brel_product eqA eqP)) (only parsing).
Local Notation "[EQP1]" :=  (equal_manger_phase_1 eqA eqP addP) (only parsing). 
Local Notation "[MP1]" :=  (uop_manger_phase_1 eqA addP) (only parsing).
Local Notation "[MPP0]" :=  (manger_product_phase_0 eqA eqP mulA mulP) (only parsing).
Local Notation "[MP]" := (bop_manger_product eqA lteA eqP addP mulA mulP) (only parsing). 
Local Notation "[MR]" := (@uop_manger_phase_2 A P lteA) (only parsing).
Local Notation "[EQ]" := (equal_manger eqA lteA eqP addP) (only parsing).


    

(*
  X := [(a, b); (c, d); (a, e)]
  Y := [(u, v); (x, y); (x, t)]

  1. (uop_manger_phase_1 eqA addP X) =  
    [(a, b + e); (c, d)]
  
  2. (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y) = 
  [
    (mulA a u, mulP (b + e) v); 
    (mulA a x, mulP (b + e) y;
    (mulA a x, mulP (b + e) t);
    (mulA c u, mulP d v);
    (mulA c x, mulP d y);
    (mulA c x, mulP d t);
  ]

  3. (manger_product_phase_0 eqA eqP mulA mulP X Y) = 
  [
    (mulA a u, mulP b v);
    (mulA a x, mulP b y);
    (mulA a x, mulP b t);
    (mulA c u, mulP d v);
    (mulA c x, mulP d y);
    (mulA c x, mulP d t);
    (mulA a u, mulP e v);
    (mulA a x, mulP e y);
    (mulA a x, mulP e t)
  ]

  Now, let's say I want to filter (mulA a x) from 
  equation 3 and 2. 
  2 gives me:
  [
    (mulA a x, mulP (b + e) y;
    (mulA a x, mulP (b + e) t);
  ]
  and 3 gives me:
  [
    (mulA a x, mulP b y);
    (mulA a x, mulP b t);
    (mulA a x, mulP e y);
    (mulA a x, mulP e t)
  ]

  (* addP is + *)
  mulP needs to distribute over addP 
  Prove that:
  mulP (b + e) y + mulP (b + e) t = 
  mulP b y + mulP b t + mulP e y + 
  mulP e t 

*)

Lemma addP_gen_idempotent : 
  ∀ x y : P, 
  eqP x y = true → eqP (addP x y) y = true.
Proof. 
  intros * Ha.
  assert (Hb := cong_addP _ _ _ _ Ha (refP y)).
  assert (Hc := idemP y).
  exact (trnP _ _ _ Hb Hc).
Qed. 

Local Notation "x =S= y" := (manger_llex.eqSAP A P eqA eqP x y  = true) 
  (at level 70, only parsing).
Local Notation "a == b"   := (brel_product eqA eqP a b = true) 
  (at level 70).


Lemma bProp_cong : 
  forall au,
  theory.bProp_congruence (A * P) (brel_product eqA eqP)
  (λ '(x, _), eqA x au).
Proof.
  intros * (ax, bx) (aw, bw) Ha;
  cbn in Ha.
  eapply Bool.andb_true_iff in Ha.
  destruct Ha as (Hal & Har).
  case_eq (eqA ax au);
  case_eq (eqA aw au);
  intros Hb Hc; try reflexivity.
  rewrite (trnA _ _ _ (symA _ _ Hal) Hc) in 
  Hb; congruence.
  rewrite (trnA _ _ _ Hal Hb) in Hc;
  congruence.
Qed.

Lemma bop_cong : 
  bop_congruence (A * P) (brel_product eqA eqP) (bop_product mulA mulP).
Proof.
  eapply bop_product_congruence; assumption.
Qed.
    

Lemma bop_assoc : 
  bop_associative (A * P) (manger_llex.eqAP A P eqA eqP)
  (bop_product mulA mulP).
Proof.
  eapply bop_product_associative; assumption.
Qed.





Lemma manger_product_phase_0_cong : 
  bop_congruence _ 
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ? ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Ha, Hb;
  [| eapply symAP| eapply trnAP| eapply symAP|
  eapply trnAP]; try assumption;
  destruct Ha as (Hal & Har);
  destruct Hb as (Hbl & Hbr).
  eapply brel_set_intro_prop;
  [eapply refAP| split; intros (au, av) Hc];
  try assumption.
  +
    eapply in_set_bop_lift_elim in Hc;
    [| eapply refAP | eapply symAP];
    try assumption;
    destruct Hc as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc).
    eapply in_set_bop_lift_intro_v2;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply Hal; exact Ha |  eapply Hbl; exact Hb | 
    exact Hc]; try assumption.
  +
    eapply in_set_bop_lift_elim in Hc;
    [| eapply refAP | eapply symAP];
    try assumption;
    destruct Hc as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc).
    eapply in_set_bop_lift_intro_v2;
    [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong | 
    eapply Har; exact Ha | eapply Hbr; exact Hb | exact Hc ];
    try assumption.
Qed.



 (* 
 I am going to admit this because Tim 
  has changed the definition of sum_fn so the 
  proof will come from there. 
  
*)

Lemma sum_fn_phase_1 : 
  forall (s1 s2 : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP s1) s2))) = true <->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP s1 s2))) = true.
Proof.
Admitted. 
  




Lemma bop_left_uop_inv_phase_1 : 
  bop_left_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_1 eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_1 eqA addP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_1_elim 
    with (zeroP := zeroP) in Ha;
    try assumption;
    try (eapply addP_gen_idempotent).
    destruct Ha as ((q & Ha) & Hb).
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Haa & Hbb) & Hcc).
    eapply in_set_uop_manger_phase_1_elim 
    with (zeroP := zeroP) in Haa; 
    try assumption;
    try (eapply addP_gen_idempotent).
    destruct Haa as ((qt & Haa) & Hc).
    eapply in_set_uop_manger_phase_1_intro 
    with (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
    ++
      eexists.
      eapply brel_product_elim in Hcc;
      destruct Hcc as (Hccl & Hccr).
      eapply in_set_bop_lift_intro_v2 with 
      (x := (xa, qt)) (y := (ya, yb)); 
      try assumption;
      [eapply refAP | eapply trnAP | eapply symAP |
      eapply bop_cong | ]; try assumption.
      eapply brel_product_intro;
      [exact Hccl | instantiate (1:= (mulP qt yb));
      eapply refP].
    ++
      eapply sum_fn_phase_1; 
      try assumption.
  +
    eapply in_set_uop_manger_phase_1_elim 
    with (zeroP := zeroP) in Ha;
    try assumption;
    try (eapply addP_gen_idempotent).
    destruct Ha as ((q & Ha) & Hb).
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Haa & Hbb) & Hcc).
    eapply in_set_uop_manger_phase_1_intro 
    with (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
    ++
      eexists.
      eapply in_set_bop_lift_intro_v2 with (y := (ya, yb));
      [eapply refAP | eapply trnAP | eapply symAP | eapply 
      bop_cong |  | | ]; try assumption.
      eapply in_set_uop_manger_phase_1_intro 
      with (zeroP := zeroP); try assumption;
      try (eapply addP_gen_idempotent).
      * 
        eexists; exact Haa.
      *
        eapply refP.
      *
        eapply brel_product_elim in Hcc;
        destruct Hcc as (Hccl & Hccr).
        eapply brel_product_intro;
        [exact Hccl | eapply refP].
    ++
      rewrite  list_filter_lib_filter_same.
      rewrite <- list_filter_lib_filter_same in Hb.
      eapply sum_fn_phase_1;
      try assumption.
Qed.
    



(* I can find it in the library. *)
Lemma theory_below_cong : 
  forall au aw ab, 
  eqA au aw = true ->
  theory.below lteA au ab = false ->
  theory.below lteA aw ab = false.
Proof.
  intros * Ha Hb.
  eapply theory.below_false_elim in Hb.
  eapply theory.below_false_intro.
  destruct Hb as [Hb | Hb];
  [left | right].
  +
    rewrite <-Hb.
    eapply conLte;
    [eapply refA | eapply symA];
    try assumption.
  +
  rewrite <-Hb.
  eapply conLte;
  [eapply symA | eapply refA];
  try assumption.
Qed.
    

(* I can find it in the library. *)
Lemma theory_below_cong_second : 
  forall au aw ab, 
  eqA au aw = true ->
  theory.below lteA ab au = false ->
  theory.below lteA ab aw = false.
Proof.
  intros * Ha Hb.
  eapply theory.below_false_elim in Hb.
  eapply theory.below_false_intro.
  destruct Hb as [Hb | Hb];
  [left | right].
  +
    rewrite <-Hb.
    eapply conLte;
    [eapply symA | eapply refA];
    try assumption.
  +
  rewrite <-Hb.
  eapply conLte;
  [eapply refA | eapply symA];
  try assumption.
Qed.


Lemma bop_left_uop_inv_phase_2 : 
  bop_left_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_2 lteA)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_2 lteA).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce in Ha |- *.
    eapply in_set_uop_manger_phase_2_elim in Ha;
    try assumption.
    destruct Ha as (Hal & Har).
    eapply in_set_bop_lift_elim in Hal;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Hal as ((xa, xb) & (ya, yb) & (Ha & Hb) & Hc).
    (* intro rule *)
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply set.in_set_right_congruence with 
      (a := bop_product mulA mulP (xa, xb) (ya, yb)); 
      [eapply symAP | eapply trnAP | eapply brel_product_symmetric |];
      try assumption.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong|
      |exact Hb]; try assumption.
      eapply in_set_uop_manger_phase_2_elim in Ha;
      destruct Ha; try assumption.
    ++
      (* Challenging case*)
      intros * Hd.
      eapply in_set_uop_manger_phase_2_elim in Ha;
      try assumption;
      destruct Ha as (Hal & Harr).
      (* there is nothing below xa in s1 
        It is a bottom most element. 
      *)


      eapply in_set_bop_lift_elim in Hd;
      [| eapply refAP | eapply symAP];
      try assumption.
      destruct Hd as ((xaa, xbb) & (yaa, ybb) & (Hdl & Hdr) & Hdrr).
      eapply brel_product_elim in Hc;
      destruct Hc as (Hcl & Hcr).
      eapply brel_product_elim in Hdrr;
      destruct Hdrr as (Hdrrl & Hdrrr).



      (* replace au by mulA xa ya and b by mulA xaa yaa *)
      eapply theory_below_cong with (au := (mulA xa ya));
      [eapply symA | ]; try assumption.
      eapply theory_below_cong_second with (au := mulA xaa yaa);
      [eapply symA | ]; try assumption.

      (* 

      (* let's construct an element *)
      specialize (Har (mulA xa yaa) (mulP xb ybb)).

      (* construct an element *)
      assert (Hf : set.in_set (brel_product eqA eqP)
      (manger_product_phase_0 eqA eqP mulA mulP
      (uop_manger_phase_2 lteA s1) s2) (mulA xa yaa, mulP xb ybb) = true).
      eapply  in_set_bop_lift_intro_v2 with 
      (x := (xa, xb)) (y := (yaa, ybb));
      try assumption;
      [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong |
      eapply  in_set_uop_manger_phase_2_intro | 
      eapply brel_product_intro;[eapply refA | eapply refP]]; 
      try assumption.

      (* get an element *)
      specialize (Har Hf).
      (* replace au by mula xa ya in Har *)
      eapply theory_below_cong with (aw := mulA xa ya) in Har;
      try assumption.

     
      (* from Harr, I know that there is nothign below 
      xa. It is a bottom element *)
      pose proof (Harr _ _ Hdl) as Hg.
      (* 
        Intutively, from Har --assuming that 
        mulA is left cancellative-- 
        we have theory.below lteA ya yaa = false, i.e., 
        it is not the case that yaa is below ya 
        (ya <= yaa). 

        From Hg I know that it is not the case that
        xaa is below xa (xa <= xaa)

        Then it's true that (mulA xaa yaa) is not 
        below (mulA xa ya) 
        (mulA xa ya <= mulA xaa yaa)

      *)
    *)
    

    admit.

     
  +
    eapply in_set_uop_manger_phase_2_elim in Ha;
    try assumption.
    destruct Ha as (Hal & Har).
    eapply in_set_bop_lift_elim in Hal;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Hal as ((xa, xb) & (ya, yb) & (Ha & Hb) & Hc).
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply set.in_set_right_congruence with 
      (a := bop_product mulA mulP (xa, xb) (ya, yb)); 
      [eapply symAP | eapply trnAP | eapply brel_product_symmetric |];
      try assumption.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong|
      |exact Hb]; try assumption.

      (* mulA has to be right cancellative *)
      eapply in_set_uop_manger_phase_2_intro;
      try assumption.
      intros sa sb Hd.

      (* 
      (* specialise *)
      specialize (Har (mulA sa ya) (mulP sb yb)).
      assert (He : set.in_set (brel_product eqA eqP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 s2)
      (mulA sa ya, mulP sb yb) = true).
      eapply in_set_bop_lift_intro_v2 with 
      (x := (sa, sb)) (y := (ya, yb));
      [eapply refAP | eapply trnAP | eapply symAP |
      eapply bop_cong | exact Hd | exact Hb | ];
      try assumption.
      eapply brel_product_intro;
      [eapply refA | eapply refP].
      specialize (Har He).
      eapply brel_product_elim in Hc;
      destruct Hc as (Hcl & Hcr).
      eapply theory_below_cong with (aw := mulA xa ya) in Har;
      try assumption.
      *)

      
      (*
        if mulA is right cancellative, then 
        from Har we have the goal.
      *)
      admit.
    ++
      intros * Hd.
      eapply in_set_bop_lift_elim in Hd;
      [| eapply refAP | eapply symAP];
      try assumption.
      destruct Hd as ((xaa, xbb) & (yaa, ybb) & (Hdl & Hdr) & Hdrr).
      eapply in_set_uop_manger_phase_2_elim in Hdl;
      try assumption;
      destruct Hdl as (Hdll & Hdlr).

      (* from Hdlr, I know that 
      every element in s1 is not below xaa, i.e.,
      xaa is the bottom most element. 
      *)

      (* replace au and b *)
      eapply brel_product_elim in Hc;
      destruct Hc as (Hcl & Hcr).
      eapply brel_product_elim in Hdrr;
      destruct Hdrr as (Hdrrl & Hdrrr).
      eapply theory_below_cong with (au := (mulA xa ya));
      [eapply symA | ]; try assumption.
      eapply theory_below_cong_second with (au := mulA xaa yaa);
      [eapply symA | ]; try assumption.

      (* instantiate *)
      specialize (Har (mulA xaa yaa) (mulP xbb ybb)).
      assert (He : set.in_set (brel_product eqA eqP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 s2)
      (mulA xaa yaa, mulP xbb ybb) = true).
      eapply in_set_bop_lift_intro_v2 with 
      (x := (xaa, xbb)) (y := (yaa, ybb));
      [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong |
      | | eapply brel_product_intro;[eapply refA | eapply refP]]; 
      try assumption.
      (* get a concrete instance *)
      specialize (Har He).
      eapply theory_below_cong with (aw := mulA xa ya) in Har;
      try assumption.
Admitted.


(* I am going to admit this because Tim 
  has changed the definition of sum_fn so the 
proof will come from there. *)
Lemma sum_fn_phase_2 : 
  forall (s1 s2 : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP s1
        (uop_manger_phase_1 eqA addP s2)))) = true <->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP s1 s2))) = true.
Proof.
Admitted.


(* I need to generalise this to do induction. *)
Lemma bop_right_uop_inv_phase_1 : 
  bop_right_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_1 eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_1 eqA addP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_1_elim 
    with (zeroP := zeroP) in Ha;
    try assumption;
    try (eapply addP_gen_idempotent).
    destruct Ha as ((q & Ha) & Hb).
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Haa & Hbb) & Hcc).
    eapply in_set_uop_manger_phase_1_elim 
    with (zeroP := zeroP) in Hbb; 
    try assumption;
    try (eapply addP_gen_idempotent).
    destruct Hbb as ((qt & Hbb) & Hc).
    eapply in_set_uop_manger_phase_1_intro 
    with (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
    ++
      exists (mulP xb qt).
      eapply brel_product_elim in Hcc;
      destruct Hcc as (Hccl & Hccr).
      eapply in_set_bop_lift_intro_v2 with 
      (x := (xa, xb)) (y := (ya, qt)); 
      try assumption;
      [eapply refAP | eapply trnAP | eapply symAP |
      eapply bop_cong | ]; try assumption.
      eapply brel_product_intro;
      [exact Hccl | eapply refP].
    ++
      eapply sum_fn_phase_2; 
      try assumption.
  +
    eapply in_set_uop_manger_phase_1_elim 
    with (zeroP := zeroP) in Ha;
    try assumption;
    try (eapply addP_gen_idempotent).
    destruct Ha as ((q & Ha) & Hb).
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Haa & Hbb) & Hcc).
    eapply in_set_uop_manger_phase_1_intro 
    with (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
    ++
      eexists.
      eapply in_set_bop_lift_intro_v2;
      [eapply refAP | eapply trnAP | eapply symAP | eapply 
      bop_cong | exact Haa | | ]; try assumption.
      eapply in_set_uop_manger_phase_1_intro 
      with (zeroP := zeroP); try assumption;
      try (eapply addP_gen_idempotent).
      * 
        eexists; exact Hbb.
      *
        eapply refP.
      *
        eapply brel_product_elim in Hcc;
        destruct Hcc as (Hccl & Hccr).
        eapply brel_product_intro;
        [exact Hccl | eapply refP].
    ++ 
      rewrite list_filter_lib_filter_same.
      rewrite  <-list_filter_lib_filter_same in Hb.
      eapply sum_fn_phase_2;
      try assumption.
Qed.




Lemma bop_right_uop_inv_phase_2 : 
  bop_right_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_2 lteA)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_2 lteA).
Proof. 
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce in Ha |- *.
    eapply in_set_uop_manger_phase_2_elim in Ha;
    try assumption.
    destruct Ha as (Hal & Har).
    eapply in_set_bop_lift_elim in Hal;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Hal as ((xa, xb) & (ya, yb) & (Ha & Hb) & Hc).
    (* intro rule *)
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply set.in_set_right_congruence with 
      (a := bop_product mulA mulP (xa, xb) (ya, yb)); 
      [eapply symAP | eapply trnAP | eapply brel_product_symmetric |];
      try assumption.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong| |]; 
      try assumption.
      eapply in_set_uop_manger_phase_2_elim in Hb;
      destruct Hb; try assumption.
    ++
      intros * Hd.
      eapply in_set_uop_manger_phase_2_elim in Hb;
      try assumption;
      destruct Hb as (Hbl & Hbr).
      (* 
      From Hbr, I know there is nothing 
      below ya is s2, i.e., ya is 
      a bottom element. *)
      

      eapply in_set_bop_lift_elim in Hd;
      [| eapply refAP | eapply symAP];
      try assumption.
      destruct Hd as ((xaa, xbb) & (yaa, ybb) & (Hdl & Hdr) & Hdrr).
      eapply brel_product_elim in Hc;
      destruct Hc as (Hcl & Hcr).
      eapply brel_product_elim in Hdrr;
      destruct Hdrr as (Hdrrl & Hdrrr).

      (* replace au by mulA xa ya and b by mulA xaa yaa *)
      eapply theory_below_cong with (au := (mulA xa ya));
      [eapply symA | ]; try assumption.
      eapply theory_below_cong_second with (au := mulA xaa yaa);
      [eapply symA | ]; try assumption.
      (* 

      (* interesting! *)
      specialize (Har (mulA xaa ya) (mulP xbb yb)).
      assert (He : set.in_set (brel_product eqA eqP)
      (manger_product_phase_0 eqA eqP mulA mulP s1
      (uop_manger_phase_2 lteA s2)) (mulA xaa ya, mulP xbb yb) = true).
      eapply in_set_bop_lift_intro_v2;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | exact Hdl | 
      eapply in_set_uop_manger_phase_2_intro; 
      try assumption; [exact Hbl |] | 
      eapply brel_product_intro; 
      [eapply refA | eapply refP]]; try assumption.

      (* get an element *)
      specialize (Har He).

      (* replace au in Har *)
      eapply theory_below_cong with (aw := mulA xa ya) in Har;
      try assumption.

      (* relation between ya yaa *)
      pose proof (Hbr _ _ Hdr) as Hf.
      (*
        From Har, we have --assuming that mulA is
        right cancellative-- theory.below lteA xa xaa = false, i.e.,
        it is not the case that xaa is below xa 
        (xa <= xaa)

        From Hf, it is not the case that yaa is 
        below ya (ya <= yaa). 

        We are home. 
      
      *)
      *)

      admit.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha;
    try assumption.
    destruct Ha as (Hal & Har).
    eapply in_set_bop_lift_elim in Hal;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Hal as ((xa, xb) & (ya, yb) & (Ha & Hb) & Hc).
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply set.in_set_right_congruence with 
      (a := bop_product mulA mulP (xa, xb) (ya, yb)); 
      [eapply symAP | eapply trnAP | eapply brel_product_symmetric |];
      try assumption.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong| |]; 
      try assumption.

      (* 
      (* mulA has to be left cancellative  *)
      eapply in_set_uop_manger_phase_2_intro;
      try assumption.
      intros sa sb Hd.
      specialize (Har (mulA xa sa) (mulP xb sb)).
      assert (He : set.in_set (brel_product eqA eqP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 s2)
      (mulA xa sa, mulP xb sb) = true).
      eapply in_set_bop_lift_intro_v2 with 
      (x := (xa, xb)) (y := (sa, sb));
      [eapply refAP | eapply trnAP | eapply symAP |
      eapply bop_cong |  | | ];
      try assumption. 
      eapply brel_product_intro;
      [eapply refA | eapply refP].
      specialize (Har He).
      eapply brel_product_elim in Hc;
      destruct Hc as (Hcl & Hcr).
      eapply theory_below_cong with (aw := (mulA xa ya))
      in Har; try assumption.
      (* 
        if mulA is left cancellative, then from Har we are home!
      *)
      *)

      admit.
    ++
    intros * Hd.
    eapply in_set_bop_lift_elim in Hd;
    [| eapply refAP | eapply symAP];
    try assumption.
    destruct Hd as ((xaa, xbb) & (yaa, ybb) & (Hdl & Hdr) & Hdrr).
    eapply in_set_uop_manger_phase_2_elim in Hdr;
    try assumption;
    destruct Hdr as (Hdrl & Hdrrr).
    (* from Hdlr, I know that 
    every element in s1 is not below xaa.
    But what do we gain from this?? 
    *)

    (* replace au and b *)
    eapply brel_product_elim in Hc;
    destruct Hc as (Hcl & Hcr).
    eapply brel_product_elim in Hdrr;
    destruct Hdrr as (Hdrrl & Hdrrrr).
    eapply theory_below_cong with (au := (mulA xa ya));
    [eapply symA | ]; try assumption.
    eapply theory_below_cong_second with (au := mulA xaa yaa);
    [eapply symA | ]; try assumption.

    specialize (Har (mulA xaa yaa) (mulP xbb ybb)).
    assert (He : set.in_set (brel_product eqA eqP)
    (manger_product_phase_0 eqA eqP mulA mulP s1 s2)
    (mulA xaa yaa, mulP xbb ybb) = true).
    eapply in_set_bop_lift_intro_v2 with 
    (x := (xaa, xbb)) (y := (yaa, ybb));
    [eapply refAP | eapply trnAP | eapply symAP | eapply bop_cong |
    | | eapply brel_product_intro;[eapply refA | eapply refP]]; 
    try assumption.
    specialize (Har He).
    eapply theory_below_cong with (aw := mulA xa ya) in Har;
    try assumption.   
Admitted. 



(* This require mulA and mulP to be commutative  *)
Lemma manger_product_phase_0_commutative 
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP) : 
  bop_commutative (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply in_set_list_product_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Hb & Hc) & Hd). 
    unfold manger_llex.eqAP in Hd.
    (* What an awesome proof! This requires 
      mulA and mulP to commutative.
    *)
    assert (He : brel_product eqA eqP (au, av)
      (bop_product mulA mulP (ya, yb) (xa, xb)) = true).
    eapply brel_product_intro;
    eapply brel_product_elim in Hd;
    destruct Hd as (Hdl & Hdr);
   [exact (trnA _ _ _ Hdl (mulA_comm xa ya)) |
    exact (trnP _ _ _ Hdr (mulP_comm xb yb))].
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yb) (xa, xb));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption. 
    eapply in_set_list_product_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hc | exact Hb];
    try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    eapply in_set_list_product_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption.
    destruct Ha as ((xa, xb) & (ya, yb) & (Hb & Hc) & Hd). 
    unfold manger_llex.eqAP in Hd.
    assert (He : brel_product eqA eqP (au, av)
      (bop_product mulA mulP (ya, yb) (xa, xb)) = true).
    eapply brel_product_intro;
    eapply brel_product_elim in Hd;
    destruct Hd as (Hdl & Hdr);
     [exact (trnA _ _ _ Hdl (mulA_comm xa ya)) |
      exact (trnP _ _ _ Hdr (mulP_comm xb yb))].
    (*Now replace the pair (au, av) by He. 
      apply in_set_list_product_intro
    *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yb) (xa, xb));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption. 
    eapply in_set_list_product_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hc | exact Hb];
    try assumption.
Qed.
  

(* Proof starts from here *)


Lemma bop_left_uop_inv :
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (@uop_manger A P eqA lteA addP)
    (manger_product_phase_0 eqA eqP mulA mulP))
    (@uop_manger A P eqA lteA addP).
Proof.
  eapply composition_left_uop_invariant.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply P1_cong with (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.


(*
    The multiplicative component of the active part is 
    cancellative or multiplicative component of the 
    passive part is constant. 
    mulA is cancellative 
    Definition uop_manger := uop_compose [P2] [P1].
*)
Lemma bop_right_uop_inv :
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (@uop_manger A P eqA lteA addP)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (@uop_manger A P eqA lteA addP).
Proof.
  eapply composition_right_uop_invariant.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply P1_cong with (zeroP := zeroP); 
    try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.




Lemma bop_manger_product_congruence : 
  bop_congruence _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_congruence.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.

(* mulA and mulP has to be associative *)
Lemma bop_manger_product_phase_0_assoc : 
  bop_associative (finite_set (A * P)) (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros X Y Z.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Ha];
  try assumption.
  + eapply lift_lemma_1;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_assoc | exact Ha];
    try assumption.
  + eapply lift_lemma_2;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_assoc | exact Ha];
    try assumption.
Qed.
  

Lemma bop_manger_product_associative : 
  bop_associative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_associative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply bop_manger_product_phase_0_assoc.
  + eapply P1_cong with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply P1_idem;try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
Qed.



Lemma bop_manger_product_commutative 
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP) :
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  eapply uop_compose_bop_commutative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + eapply P1_idem;try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. 
    eapply P1_P2_commute with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply manger_product_phase_0_commutative; 
    try assumption.
Qed.


End Theory.  

