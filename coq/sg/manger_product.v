Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.

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
Compute (manger_add (manger_mul s5 s1) (manger_mul s5 s3)). (* (1, 7, 10) :: (2, 4, 9) :: nil *) 
Compute (manger_mul s5 (manger_add s1 s3)).                 (* (2, 4, 9) :: (1, 7, 10) :: nil *) 

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
  (mulA_comm : bop_commutative A eqA mulA)
  (mulP_comm : bop_commutative P eqP mulP)
  (cong_mulA : bop_congruence A eqA mulA)
  (cong_mulP : bop_congruence P eqP mulP).

Local Notation "[EQP0]" :=  (brel_set (brel_product eqA eqP)) (only parsing).
Local Notation "[EQP1]" :=  (equal_manger_phase_1 eqA eqP addP) (only parsing). 
Local Notation "[MP1]" :=  (uop_manger_phase_1 eqA addP) (only parsing).
Local Notation "[MPP0]" :=  (manger_product_phase_0 eqA eqP mulA mulP) (only parsing).
Local Notation "[MP]" := (bop_manger_product eqA lteA eqP addP mulA mulP) (only parsing). 
Local Notation "[MR]" := (@uop_manger_phase_2 A P lteA) (only parsing).
Local Notation "[EQ]" := (equal_manger eqA lteA eqP addP) (only parsing).


(* Begin Admit *)      

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
  (at level 70,only parsing).

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


(* It's good idea to create a hint database and 
  writing some custom tactics using coq-elpi *)
Lemma brel_set_manger_product_phase_0_dist : 
  forall (X Y U : finite_set (A * P)),
  brel_set (brel_product eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U)
  (manger_product_phase_0 eqA eqP mulA mulP X U ++
   manger_product_phase_0 eqA eqP mulA mulP Y U) = true.
Proof.
  intros *.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, ay) Ha]; try assumption.
  +
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption;
    destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
    (* Now replace *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (xa, xp) (ya, yp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
    ]; try assumption.
    (* case analysis on Ha *)
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    ++
      (* go left *)
      eapply set.in_set_concat_intro; left.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply 
      bop_cong | exact Ha | exact Hb];
      try assumption.
    ++
      (* go right *)
      eapply set.in_set_concat_intro; right.
      eapply in_set_bop_lift_intro;
      [eapply refAP | eapply trnAP | eapply symAP | eapply 
      bop_cong | exact Ha | exact Hb]; 
      try assumption.
  +
    (* I need find out (xa, xp) (ya, yp) such 
    that ax = mulA xa ya & ay = mulP xp yp from Ha *) 

    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    (* case analysis on Ha*)
    destruct Ha as [Ha | Ha].
    ++
      eapply in_set_bop_lift_elim in Ha;   
      [| eapply refAP | eapply symAP]; try assumption;
      destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
      eapply in_set_bop_lift_intro_v2;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | eapply set.in_set_concat_intro; left; 
      exact Ha | exact Hb | ]; try assumption.
    ++
       eapply in_set_bop_lift_elim in Ha;   
      [| eapply refAP | eapply symAP]; try assumption;
      destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
      eapply in_set_bop_lift_intro_v2;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | eapply set.in_set_concat_intro; right; 
      exact Ha | exact Hb | ]; try assumption.
Qed.

      

Lemma brel_set_manger_product_phase_0_comm : 
  forall (X Y U : finite_set (A * P)),
  brel_set (brel_product eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U)
  (manger_product_phase_0 eqA eqP mulA mulP (Y ++ X) U) = true.
Proof.
  intros *.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (ax, bx) Ha];
  try assumption.
  +
    eapply set.in_set_concat_intro.
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha];
    [right | left]; assumption.
  +
    eapply set.in_set_concat_intro.
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha];
    [right | left]; assumption.
Qed.



Lemma brel_set_manger_product_phase_0_swap : 
  forall (X Y U : finite_set (A * P)) au bu,
  brel_set (brel_product eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP (((au, bu) :: X) ++ Y) U)
  (manger_product_phase_0 eqA eqP mulA mulP (X ++ (au, bu) :: Y) U) = true.
Proof.
  intros *.
  remember (((au, bu) :: X)) as Xa.
  remember ((au, bu) :: Y) as Ya.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_transitive;
  [eapply refAP | eapply symAP | eapply trnAP | 
  eapply brel_set_manger_product_phase_0_dist | 
  eapply brel_set_symmetric]; 
  try assumption.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (ax, bx) Ha];
  try assumption.
  +
    subst; cbn in Ha |- *.
    eapply set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    eapply union.in_set_uop_duplicate_elim_elim,
    set.in_set_concat_elim in Ha;
    [| eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    ++
      (* go right; left *)
      eapply set.in_set_concat_intro; right;
      eapply union.in_set_dup_elim_intro;
      [eapply symAP | eapply trnAP | eapply 
      set.in_set_concat_intro; left]; try assumption.
    ++
      eapply set.in_set_concat_intro; left.
      unfold manger_product_phase_0, bop_lift.
      eapply union.in_set_dup_elim_intro;
      [eapply symAP | eapply trnAP | exact Ha];
      try assumption.
    ++
      eapply set.in_set_concat_intro; right;
      eapply union.in_set_dup_elim_intro;
      [eapply symAP | eapply trnAP | eapply 
      set.in_set_concat_intro; right]; try assumption.
      eapply union.in_set_uop_duplicate_elim_elim in Ha;
      try assumption.
  +
    (* other direction *)
    subst; 
    eapply set.in_set_concat_elim in Ha;
    [|eapply symAP]; try assumption.
    destruct Ha as [Ha | Ha].
    ++
      eapply set.in_set_concat_intro; left;
      cbn; eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ]; try assumption.
      eapply set.in_set_concat_intro; right.
      unfold manger_product_phase_0 in Ha.
      eapply in_set_bop_lift_elim in Ha;
      [| eapply refAP | eapply symAP]; try assumption;
      destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
      eapply set.in_set_right_congruence with 
      (bop_product mulA mulP (xa, xp) (ya, yp));
      [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
      ]; try assumption.
      eapply in_set_list_product_intro;
      [eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_cong | exact Ha | exact Hb];
      try assumption.
    ++
      cbn in Ha |- *;
      eapply union.in_set_uop_duplicate_elim_elim,
      set.in_set_concat_elim in Ha;
      [| eapply symAP]; try assumption.
      destruct Ha as [Ha | Ha].
      +++
        eapply set.in_set_concat_intro; left;
        eapply union.in_set_uop_duplicate_elim_intro;
        [eapply symAP | eapply trnAP | ]; 
        try assumption.
        eapply set.in_set_concat_intro; left; 
        assumption.
      +++
        eapply set.in_set_concat_intro; right;
        eapply union.in_set_uop_duplicate_elim_intro;
        [eapply symAP | eapply trnAP | ]; 
        try assumption.
Qed.


(* requires commutativity *)
Lemma brel_set_manger_product_phase_0_swap_v1: 
  forall (X Y : finite_set (A * P)),
  brel_set (brel_product eqA eqP) 
  (manger_product_phase_0 eqA eqP mulA mulP X Y)
  (manger_product_phase_0 eqA eqP mulA mulP Y X) = true.
Proof.
  intros *;
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (ax, bx) Ha];
  try assumption.
  +
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption;
    destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
    (* Now replace *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (xa, xp) (ya, yp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
    ]; try assumption.
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yp) (xa, xp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption;
    [eapply brel_product_symmetric| ];
    try assumption.
    eapply brel_product_intro;
    [eapply mulA_comm | eapply mulP_comm].
    eapply in_set_bop_lift_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hb  | exact Ha];
    try assumption.
  +
    eapply in_set_bop_lift_elim in Ha;
    [| eapply refAP | eapply symAP]; try assumption;
    destruct Ha as ((xa, xp) & (ya, yp) & (Ha & Hb) & Hc).
    (* Now replace *)
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (xa, xp) (ya, yp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric |
    ]; try assumption.
    eapply set.in_set_right_congruence with 
    (bop_product mulA mulP (ya, yp) (xa, xp));
    [eapply symAP | eapply trnAP | eapply brel_product_symmetric | ];
    try assumption;
    [eapply brel_product_symmetric| ];
    try assumption. 
    eapply brel_product_intro;
    [eapply mulA_comm | eapply mulP_comm].
    eapply in_set_bop_lift_intro;
    [eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | exact Hb  | exact Ha];
    try assumption.
Qed.


    


Lemma manger_product_phase_0_comm : 
  forall (X Y U : finite_set (A * P)) au ax bx,
  eqP 
    ((matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP
          (((ax, bx) :: X) ++ Y) U))))
    (matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP
          (X ++ ((ax, bx) :: Y)) U))) = true.
Proof.
  intros *.
  eapply sum_fn_congruence_general_set with 
  (eqA := eqA) (lteA := lteA) (fA := fA);
  try assumption.
  + eapply addP_gen_idempotent.
  +
    repeat rewrite  list_filter_lib_filter_same;
    eapply filter_congruence_gen; 
    try assumption; try (eapply bProp_cong).
    eapply brel_set_manger_product_phase_0_swap.
Qed.


Lemma manger_product_phase_0_dist : 
  forall (X Y U : finite_set (A * P)) au,
  eqP
  (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP (X ++ Y) U)))
  (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X U ++ 
        manger_product_phase_0 eqA eqP mulA mulP Y U))) = true.
Proof.
  intros *.
  eapply sum_fn_congruence_general_set with 
  (eqA := eqA) (lteA := lteA) (fA := fA);
  try assumption.
  + eapply addP_gen_idempotent.
  +
    repeat rewrite  list_filter_lib_filter_same;
    eapply filter_congruence_gen; 
    try assumption; try (eapply bProp_cong).
    eapply brel_set_manger_product_phase_0_dist.
Qed.
  



(* *)
Lemma set_in_set_non_empty_left : 
  forall (X Y : finite_set (A * P)) au q, 
  set.in_set (brel_product eqA eqP)
    (manger_product_phase_0 eqA eqP mulA mulP X Y) (au, q) = true ->
  brel_set (brel_product eqA eqP) [] X = false.
Proof.
  intros * Ha.
  eapply in_set_bop_lift_elim in Ha;
  [| eapply refAP | eapply symAP];
  try assumption;
  destruct Ha as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc);
  destruct Y; destruct X; cbn in Ha, Hb; 
  try congruence;
  cbn; split; try reflexivity.
Qed.



Lemma set_in_set_non_empty_right : 
  forall (X Y : finite_set (A * P)) au q, 
  set.in_set (brel_product eqA eqP)
    (manger_product_phase_0 eqA eqP mulA mulP X Y) (au, q) = true ->
  brel_set (brel_product eqA eqP) [] Y = false.
Proof.
  intros * Ha.
  eapply in_set_bop_lift_elim in Ha;
  [| eapply refAP | eapply symAP];
  try assumption;
  destruct Ha as ((xa, xb) & (ya, yb) & (Ha, Hb) & Hc);
  destruct Y; destruct X; cbn in Ha, Hb; 
  try congruence;
  cbn; split; try reflexivity.
Qed.


Lemma brel_set_manger_product_phase_0_non_empty_forward : 
  forall (s t : finite_set (A * P)),
  brel_set (brel_product eqA eqP) []
    (manger_product_phase_0 eqA eqP mulA mulP s t) = false ->
  brel_set (brel_product eqA eqP) [] s = false ∧
  brel_set (brel_product eqA eqP) [] t = false.
Proof.
  intros * Ha.
  eapply brel_set_false_elim_prop in Ha.
  destruct Ha as [((a1, b1) & Ha & Hb) | 
  ((a1, b1) & Ha & Hb)].
  +
    cbn in Ha; congruence.
  +
    refine (conj _ _ );
    [eapply set_in_set_non_empty_left |
    eapply set_in_set_non_empty_right]; exact Ha.
  + eapply refAP; try assumption.
  + eapply symAP; try assumption.
Qed.



Lemma non_empty_list : 
  forall (X Y : finite_set (A * P)),
  (∀ a : A * P,
    set.in_set (manger_llex.eqAP A P eqA eqP) X a = true ->
    set.in_set (manger_llex.eqAP A P eqA eqP) Y a = true) ->
  brel_set (brel_product eqA eqP) [] X = false ->
  brel_set (brel_product eqA eqP) [] Y = false.
Proof.
  intros * Ha Hb.
  destruct X as [|(ax, bx) X];
  cbn in Hb |- *;
  [congruence |].
  specialize (Ha (ax, bx));
  cbn in Ha; rewrite refA, refP in Ha;
  cbn in Ha.
  specialize (Ha eq_refl).
  destruct Y;
  cbn in Ha |- *;
  [congruence | reflexivity].
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



Lemma bop_left_uop_inv_phase_1 : 
  bop_left_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_1 eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_1 eqA addP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce in Ha |- *.
    (* induction on s2 ?? *)
    (* Pen-and-paper proof 
      Change Ha to 
      set.in_set (manger_llex.eqAP A P eqA eqP)
       (uop_manger_phase_1 eqA addP
          (manger_product_phase_0 eqA eqP mulA mulP
             s2 (uop_manger_phase_1 eqA addP s1))) (au, av) = true
      by using the theorem    
    
    
    *)
     

    (* Think, Think, Think Mukesh *)
    (* 
      Calculation using Ha
      s1 := [(a, b); (c, d); (a, e)]
      s2 := [(u, v); (x, y); (x, t)]

    1. (uop_manger_phase_1 eqA addP s1) = 
      [(a, b + e); (c, d)]
      ---------------------------------------
    2. (manger_product_phase_0 eqA eqP mulA mulP
        [(a, b + e); (c, d)] [(u, v); (x, y); (x, t)]) = 
        -----------------------------------------------
        [(a * u, (b + e) * v); (a * x, (b + e) * y); 
        (a * x, (b + e) * t); (c * u, d * v); (c * x, d * y);
        (c * x, d * t)]
        ----------------------------------------------
    3. (uop_manger_phase_1 eqA addP  
        [(a * u, (b + e) * v); (a * x, (b + e) * y); 
        (a * x, (b + e) * t); (c * u, d * v); (c * x, d * y);
        (c * x, d * t)] = 
        ---------------------------------------------
        [(a * u, (b + e) * v); (a * x; (b + e) * y + (b + e) * t);
        (c * u, d * v); (c * x; d * y + d * t)]
        -----------------------------------------

    Calculation using the goal:
    5. (manger_product_phase_0 eqA eqP mulA mulP 
      [(a, b); (c, d); (a, e)] [(u, v); (x, y); (x, t)] = 
      -------------------------------------------------
      [(a * u, b * v); (a * x, b * y); (a * x, b * t);
      (c * u, d * v); (c * x, d * y); (c * x, d * t);
      (a * u, e * v); (a * x, e * y); (a * x, e * t)] 
    --------------------------------------------------
    6. uop_manger_phase_1 eqA addP 
        [(a * u, v * v); (a * x, b * y); (a * x, b * t);
        (c * u, d * v); (c * x, d * y); (c * x, d * t);
        (a * u, e * v); (a * x, e * y); (a * x, e * t)] = 
      -------------------------------------------------
      [(a * u, b * v + e * v); (a * x, b * y + b * t + e * y + e * t); 
        (c * u, d * d); (c * x, d * y + d * t)] 


    The problem with current intro and elim rule is that 
    we throw some information 
      
    *)
Admitted.
    


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
Admitted.


(*  *)
Lemma fold_left_manger_merge_set_idempotent : 
  forall (X Y : finite_set (A * P)),
  no_dup eqA (map fst Y) = true -> 
  fold_left (manger_merge_sets_new eqA addP)
    (set.uop_duplicate_elim (brel_product eqA eqP) X) Y =S= 
  fold_left (manger_merge_sets_new eqA addP) X Y.
Proof.
  induction X as [| (ax, bx) X IHx].
  +
    intros * Ha; cbn.
    eapply refSAP; try assumption.
  +
    intros * Ha; cbn.
    case_eq (set.in_set (brel_product eqA eqP) X (ax, bx));
    intro Hb.
    ++
      specialize (IHx Y Ha).
      eapply trnSAP; try assumption;
      [exact IHx |].
      (*
        Two cases:
          ax ∉ (map fst Y) ∨ ax ∈ (map fst Y)
          1. ax ∉ (map fst Y)
            (filter (λ '(s2, _), negb (eqA ax s2)) Y ++
            [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
            (filter (λ '(s2, _), eqA ax s2) Y) (ax, bx)]))  =S= Y 
            we are home. 

          2. ax ∈ (map fst Y) then we can write Y as:
             Y =S= (ax, bx') :: Y₁  (and there is no ax in Y₁)

             Now we the goal simplifies
             (filter (λ '(s2, _), negb (eqA ax s2)) Y ++
              [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2))
              (filter (λ '(s2, _), eqA ax s2) Y) (ax, bx)])) =S=
             [(ax, bx + bx')] ++ Y₁

            (fold_left (manger_merge_sets_new eqA addP) X Y)
            (fold_left (manger_merge_sets_new eqA addP) X 
              ([(ax, bx ++ bx')] ++ Y₁)

            I believe I have proof for this. 

          
          
      *)
      admit.
      
      
    ++
      cbn.
      rewrite IHx;
      [reflexivity |].
      (* This is also true *)
     
Admitted.


Lemma manger_ltrtrans_duplicate_free : 
  forall (X Y Z : finite_set (A * P)) ah bh,
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  no_dup eqA (map fst (fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh) 
      (fold_left (manger_merge_sets_new eqA addP) X Y)) Z)) = true.
Proof.
  intros * Ha Hb.
Admitted.


Lemma ltran_fold_left_interaction : 
  forall (X Y : finite_set (A * P)) ah bh, 
  no_dup eqA (map fst Y) = true ->
  fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh) X) Y =S= 
  ltran_list_product (bop_product mulA mulP) (ah, bh)
    (fold_left (manger_merge_sets_new eqA addP) X Y).
Proof.
Admitted.


Lemma manger_manger_double_red : 
  forall (X Y Z : finite_set (A * P)), 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  (fold_left (manger_merge_sets_new eqA addP)
    (fold_left (manger_merge_sets_new eqA addP) X Y) Z) =S= 
    fold_left (manger_merge_sets_new eqA addP) (X ++ Y) Z.
Proof.
Admitted.


Lemma ltran_list_product_cong : 
  forall (X Y : finite_set (A * P)) ah bh, 
  X =S= Y ->
  ltran_list_product (bop_product mulA mulP) (ah, bh) X =S= 
  ltran_list_product (bop_product mulA mulP) (ah, bh) Y.
Admitted.






(* generalise version  *)
(* Challenging, yet nice, proof. *)
Lemma bop_right_uop_inv_phase_1_gen_foward : 
  forall (s1 s2 Y Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1
        (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z) 
          (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 (s2 ++ Y)) Z) 
        (au, av) = true.
Proof.
  (* Don't touch s2 *)
  (* Also, don't use fold_left *)
  refine (fix Fn s1 := 
    match s1 as s1' return s1 = s1' -> _ with 
    | [] => _ 
    | (ah, bh) :: t => _ 
    end eq_refl).
  +
    intros Ha * Hb Hc Hd.
    cbn in Hd |- *.
    exact Hd.
  +
    intros Ha * Hb Hc Hd;
    cbn in Hd |- *.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) 
    (fold_left (manger_merge_sets_new eqA addP) s2 Y)) as Ya.
    remember (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) 
    as Yb.
    (* 
      Now I invoke fold_left_manger_merge_set_idempotent 
    *)
    (* remove the set.uop_duplicate_elim from Hd and goal *)
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP)
      (Yb ++ bop_list_product_left (bop_product mulA mulP) t (s2 ++ Y)) Z);
      [| eapply symAP | eapply trnAP | 
      eapply fold_left_manger_merge_set_idempotent]; try assumption.
    erewrite in_set_left_congruence_v2 with 
    (Y := fold_left (manger_merge_sets_new eqA addP) 
      (Ya ++ bop_list_product_left (bop_product mulA mulP) t
      (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z) in Hd;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.

    (* some unfold of definitions to apply induction hypothesis *)
    unfold manger_product_phase_0, bop_lift in Hd, Fn.
    rewrite fold_left_app in Hd |- *.
    specialize (Fn t s2 Y 
      (fold_left (manger_merge_sets_new eqA addP) Ya Z) au av Hb).
    
    (* prove that it's duplicate free *)
    assert (He : no_dup eqA (map fst (fold_left 
      (manger_merge_sets_new eqA addP) Ya Z)) = true). 
    subst. eapply manger_ltrtrans_duplicate_free;
    try assumption.
    (* instantiate the IHn *)
    specialize (Fn He).
    (* remove uop_duplicate from Fn *)
    erewrite in_set_left_congruence_v2 with 
    (Y := (fold_left (manger_merge_sets_new eqA addP)
    (bop_list_product_left (bop_product mulA mulP) t
       (fold_left (manger_merge_sets_new eqA addP) s2 Y))
    (fold_left (manger_merge_sets_new eqA addP) Ya Z))) in Fn;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    specialize (Fn Hd).
    rewrite in_set_left_congruence_v2 with 
    (Y := (fold_left (manger_merge_sets_new eqA addP)
       (bop_list_product_left (bop_product mulA mulP) t (s2 ++ Y))
      (fold_left (manger_merge_sets_new eqA addP) Ya Z))) in Fn;
    [| eapply symAP | eapply trnAP | 
    eapply fold_left_manger_merge_set_idempotent]; try assumption.
    (* Now one more challenge left*)
    subst. clear Hd He.
    remember ((fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (
       ah, bh) (fold_left (manger_merge_sets_new eqA addP) s2 Y))
    Z)) as Za.
    remember ((fold_left (manger_merge_sets_new eqA addP)
    (ltran_list_product (bop_product mulA mulP) (ah, bh) (s2 ++ Y)) Z))
    as Zb.
    (* Now the challenge is to prove if this goal 
    is a reduction 
    If I can prove that Za and Zb are same, then we 
    are home. 
    *)    
    assert (Hd : Za =S= Zb).
    subst; eapply trnSAP
    with (t := ltran_list_product (bop_product mulA mulP) (ah, bh)
      (fold_left (manger_merge_sets_new eqA addP)
        (fold_left (manger_merge_sets_new eqA addP) s2 Y) Z));
    try assumption.
    eapply ltran_fold_left_interaction; try assumption.
    (* If we were not using a custom equality, this proof 
      could have been done in an hour. Equality is not making 
      the proof conceptually difficult but just a boring task. 
    Note to myself: If I am dealing with a custom equality, 
    either use typeclass or aac_tactic.   
    *)
    eapply symSAP, trnSAP with (t := ltran_list_product 
      (bop_product mulA mulP) (ah, bh) 
      (fold_left (manger_merge_sets_new eqA addP)  (s2 ++ Y) Z));
    try assumption.
    eapply ltran_fold_left_interaction; try assumption.
    (* no congruence for ltran_list_product ? *)
    eapply ltran_list_product_cong,
    symSAP, manger_manger_double_red;
    try assumption.
    eapply fold_left_in_set_mmsn_cong with (V := Za);
    try assumption;
    try (eapply addP_gen_idempotent).
Qed.

   


Lemma bop_right_uop_inv_phase_1_gen_backward : 
  forall (s1 s2 Y Z : finite_set (A * P)) au av, 
  no_dup eqA (map fst Y) = true ->
  no_dup eqA (map fst Z) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1 (s2 ++ Y)) Z) 
        (au, av) = true ->
  set.in_set (manger_llex.eqAP A P eqA eqP)
    (fold_left (manger_merge_sets_new eqA addP)
      (manger_product_phase_0 eqA eqP mulA mulP s1
        (fold_left (manger_merge_sets_new eqA addP) s2 Y)) Z) 
          (au, av) = true.
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
  [eapply refAP | split; intros (au, av) Ha]; try assumption.
  +
    unfold bop_reduce in Ha |- *.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha |- *.
    rewrite manger_merge_set_funex in Ha |- *.
    replace s2 with (s2 ++ []).
    eapply bop_right_uop_inv_phase_1_gen_foward;
    [try reflexivity | try reflexivity | exact Ha].
    eapply app_nil_r.
  +
    unfold bop_reduce in Ha |- *.
    unfold uop_manger_phase_1,
    manger_phase_1_auxiliary in Ha |- *.
    rewrite manger_merge_set_funex in Ha |- *.
    replace s2 with (s2 ++ []) in Ha.
    eapply bop_right_uop_inv_phase_1_gen_backward;
    [try reflexivity | try reflexivity | exact Ha].
    eapply app_nil_r.
Qed.



Lemma bop_right_uop_inv_phase_2 : 
  bop_right_uop_invariant (finite_set (A * P))
    (manger_llex.eqSAP A P eqA eqP)
    (bop_reduce (uop_manger_phase_2 lteA)
      (manger_product_phase_0 eqA eqP mulA mulP))
    (uop_manger_phase_2 lteA).
Proof. 
Admitted. 



(* This require mulA and mulP to be commutative  *)
Lemma manger_product_phase_0_commutative: 
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
  
Admitted.


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
Admitted.




Lemma bop_manger_product_congruence : 
  bop_congruence _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_congruence.
  + eapply symSAP.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent). 
  + admit.
  + admit.  
Admitted.


Lemma bop_manger_product_associative : 
  bop_associative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_associative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
Admitted.


Lemma bop_manger_product_commutative :
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  intros Hu Hv.
  eapply uop_compose_bop_commutative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
 Admitted. 



Lemma bop_manger_product_idempotent : 
  bop_idempotent _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  
  eapply uop_compose_bop_idempotent.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
Admitted.


(* Everything good upto this point *) 


(* With the assumption that we have, this is not 
provable. *)
Lemma bop_manger_product_not_selective :
  bop_not_selective _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  (* intros Hu Hv. *)
  destruct ntot as ((a₁, a₂) & Ha);
  exists ([(a₁, wP)], [(a₂, wP)]); compute;
  case_eq (eqA (mulA a₁ a₂) a₁); 
  case_eq (eqP (mulP wP wP) wP);
  case_eq (eqA a₁ (mulA a₁ a₂));
  case_eq (eqP wP (mulP wP wP));
  case_eq (eqA (mulA a₁ a₂) a₂);
  case_eq (eqP (mulP wP wP) wP);
  case_eq (eqA a₂ (mulA a₁ a₂));
  case_eq (eqP wP (mulP wP wP));
  intros Hb Hc Hd He Hf Hg Hi Hj;
  try eauto.
  +
    eapply symA in Hc.
    pose proof (trnA _ _ _ (symA _ _ Hj) Hc) as Hk.
    destruct Ha as (Hal & Har).
    assert (Hl := conLte _ _ _ _ (refA a₁) Hk).
    rewrite <-Hl in Hal.
    rewrite (refLte a₁) in Hal; congruence.
  + rewrite (symA _ _ Hc) in He; 
    congruence.
  +
    destruct Ha as (Hal & Har).
    refine (pair _ eq_refl).
    clear Hb Hd Hi Hf.
    
    (*
      a₁ = a₁ * a₂ 
      a₂ <> a₁ * a₂
      -------------
      a₁ <> a₂ 
      a₁ and a₂ are distinct, or incomprable, elements. 

      What information we get from Hal and Har?
      a₁ and a₂ are distinct, or incomprable, elements.

    
      lteA is reflexive and transitive, i.e., pre order. 
      In addition, it's not total. 

      Tim: what is the rationale for 
      not-total pre-order? 
      

    
    
    
    
    *)
    (* case where a₁ and a₂ are incomprable  *)
    (* What can I infer from Hal and Har *)
    (* We need some extra condition to prove this? *)
    admit.
    
  +
    rewrite (symA _ _ Hj) in Hg; 
    congruence.
  +
    rewrite (symA _ _ Hg) in Hj; 
    congruence.
  +
    destruct Ha as (Hal & Har).
    (* case where a₁ and a₂ are incomprable  *)
    admit.
Admitted.  

End Theory.  

