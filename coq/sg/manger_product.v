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

  
(* is this a reduction over manger_product_phase_0? 
 
   r1 = uop_manger_phase_1

*)   
(*
Definition manger_product_phase_1 
           {A P : Type}
           (eqA : brel A)
           (eqP : brel P)                       
           (addP : binary_op P)
           (mulA : binary_op A)
           (mulP : binary_op P) : binary_op (finite_set (A * P))
  := bop_reduce (uop_manger_phase_1 eqA addP) 
    (manger_product_phase_0 eqA eqP mulA mulP).



(* is this really the composition of reductions? 

   r2 = uop_manger_phase_2 
*) 

Definition bop_manger_product 
           {A P : Type}
           (eqA lteA : brel A)
           (eqP : brel P)            
           (addP : binary_op P)
           (mulA : binary_op A)
           (mulP : binary_op P) : binary_op (finite_set (A * P))
  := bop_reduce (@uop_manger_phase_2 A P lteA) 
    (manger_product_phase_1 eqA eqP addP mulA mulP). 
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

(* Assumption about mulA and mulP *)
Variables 
  (mulA_assoc : bop_associative A eqA mulA)
  (mulP_assoc : bop_associative P eqP mulP)
  (mulA_left : bop_is_left A eqA mulA)
  (mulP_left : bop_is_left P eqP mulP)
  (mulA_right : bop_is_right A eqA mulA)
  (mulP_right : bop_is_right P eqP mulP)
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
Lemma sum_fn_first : 
forall (X Y : finite_set (A * P)) au,
  eqP 
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y)))
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
Admitted.
    

Lemma sum_fn_second : 
  forall (X Y : finite_set (A * P)) au,
  eqP 
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (uop_manger_phase_1 eqA addP Y)))) 
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
Admitted.


(* end of Admit *)

Lemma addP_gen_idempotent : 
  ∀ x y : P, 
  eqP x y = true → eqP (addP x y) y = true.
Proof. 
  intros * Ha.
  assert (Hb := cong_addP _ _ _ _ Ha (refP y)).
  assert (Hc := idemP y).
  exact (trnP _ _ _ Hb Hc).
Qed. 

Lemma bop_left : 
  bop_is_left (A * P) (brel_product eqA eqP) (bop_product mulA mulP).
Proof.
  intros (sa, sb) (ta, tb).
  eapply brel_product_intro;
  [eapply mulA_left | eapply mulP_left].
Qed.
 

Lemma bop_right : 
  bop_is_right (A * P) (brel_product eqA eqP) (bop_product mulA mulP).
Proof.
  intros (sa, sb) (ta, tb).
  eapply brel_product_intro;
  [eapply mulA_right | eapply mulP_right].
Qed.

 

Lemma bop_cong : 
  bop_congruence (A * P) (brel_product eqA eqP) (bop_product mulA mulP).
Proof.
  intros (sfa, sfb) (ssa, ssb) (tfa, tfb) (tsa, tsb) Ha Hb.
  eapply brel_product_elim in Ha, Hb;
  destruct Ha as (Hal & Har);
  destruct Hb as (Hbl & Hbr);
  eapply brel_product_intro;
  [eapply cong_mulA; try assumption | 
  eapply cong_mulP; try assumption ].
Qed.
    

Lemma bop_assoc : 
  bop_associative (A * P) (manger_llex.eqAP A P eqA eqP)
  (bop_product mulA mulP).
Proof.
  intros (sa, sb) (ta, tb) (ua, ub).
  eapply brel_product_intro;
  [eapply mulA_assoc | eapply mulP_assoc].
Qed.


Lemma sum_fn_forward_first : 
  forall (X Y : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | eapply sum_fn_first].
Qed.


Lemma sum_fn_backward_first : 
  forall (X Y : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X Y ))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP
        (uop_manger_phase_1 eqA addP X) Y))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | 
  rewrite list_filter_lib_filter_same, 
  <-list_filter_lib_filter_same;
  eapply symP, sum_fn_first].
Qed.




  


Lemma sum_fn_forward_second : 
  forall (X Y : finite_set (A * P)) au av, 
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (uop_manger_phase_1 eqA addP Y)))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
     (List.filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | eapply sum_fn_second].
Qed.
  

Lemma sum_fn_backward_second : 
  forall (X Y : finite_set (A * P)) au av,
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
      (filter (λ '(x, _), eqA x au)
        (manger_product_phase_0 eqA eqP mulA mulP X Y))) = true ->
  eqP av
  (matrix_algorithms.sum_fn zeroP addP snd
    (List.filter (λ '(x, _), eqA x au)
      (manger_product_phase_0 eqA eqP mulA mulP X
        (uop_manger_phase_1 eqA addP Y)))) = true.
Proof.
  intros * Ha.
  eapply trnP;
  [exact Ha | 
  rewrite list_filter_lib_filter_same, 
  <-list_filter_lib_filter_same;
  eapply symP, sum_fn_second].
Qed.
  


Lemma manger_product_phase_0_cong :
  bop_congruence _ 
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ? ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Ha, Hb;
  [|eapply symAP | eapply trnAP | eapply symAP | eapply trnAP];
  try assumption; destruct Ha as (Hal & Har);
  destruct Hb as (Hbl & Hbr);
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Hc];
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Hc;
    [eapply symAP| eapply trnAP|]; try assumption;
    (* intro and elim rule for bop_list_product_left 
    from CAS.coq.sg.lift *)
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | | |];
    try assumption;[eapply bop_left | | ].
    ++
      eapply bop_list_product_is_left_elim in Hc;
      [|eapply trnAP | eapply symAP | ]; 
      try assumption; 
      [eapply Hal; exact Hc | eapply bop_left].
    ++
      eapply bop_list_product_is_right_elim in Hc;
      [|eapply refAP | eapply trnAP | eapply symAP | ]; 
      try assumption;[|eapply bop_right].
      *
        eapply Hbl in Hc;
        destruct t2; cbn in Hc;
        try congruence;
        cbn; reflexivity.
  + 
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Hc;
    [eapply symAP| eapply trnAP|]; try assumption;
    (* intro and elim rule for bop_list_product_left 
    from CAS.coq.sg.lift *)
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | | |];
    try assumption;[eapply bop_left | | ].
    ++
      eapply bop_list_product_is_left_elim in Hc;
      [|eapply trnAP | eapply symAP | ]; 
      try assumption;
      [eapply Har; exact Hc |
      eapply bop_left].
    ++
      eapply bop_list_product_is_right_elim in Hc;
      [|eapply refAP | eapply trnAP | eapply symAP | ]; 
      try assumption;[|eapply bop_right].
      *
        eapply Hbr in Hc;
        destruct s2; cbn in Hc;
        try congruence;
        cbn; reflexivity.
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


Lemma bop_left_uop_inv_phase_1 : 
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
    (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_left];
      try assumption; try (eapply addP_gen_idempotent);
      eapply in_set_uop_manger_phase_1_elim with 
      (zeroP := zeroP) in Hal; try assumption;
      try (eapply addP_gen_idempotent);
      destruct Hal as ((qt & Hala) & Halb);
      exists qt;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      (* This is the challenge! Because it's 
        demanding s2 to be non-empty *)
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_left | | ];
      try assumption.
    ++
      (* Think about it! *)
      eapply sum_fn_forward_first; 
      try assumption.
      
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_left];
      try assumption; eexists;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | | |];
      try assumption;[eapply bop_left | ].
      *
        eapply in_set_uop_manger_phase_1_intro with 
        (zeroP := zeroP); try assumption;
        try (eapply addP_gen_idempotent);
        [exists q; exact Hal | eapply refP].
    ++
      (* Think about it! *)
      eapply sum_fn_backward_first;
      try assumption.
Qed.
    


Lemma bop_right_uop_inv_phase_1 : 
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Proof.
  intros ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  + 
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hal |- *.
    eapply set_in_set_non_empty_right in Hal; cbn in Hal;
    congruence. reflexivity.
    ++
      eexists.
      eapply union.in_set_uop_duplicate_elim_intro;
      eapply union.in_set_uop_duplicate_elim_elim in Hal;
      [eapply symAP| eapply trnAP|]; try assumption;
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | | |];
      try assumption; [eapply bop_left | ].
      *
        eapply bop_list_product_is_left_elim in Hal;
        [|eapply trnAP | eapply symAP | ]; 
        try assumption; [exact Hal | eapply bop_left].
    ++
      (* May require some thinking*)
      eapply sum_fn_forward_second;
      try assumption.
  +
    eapply in_set_uop_manger_phase_1_intro with 
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent);
    eapply in_set_uop_manger_phase_1_elim with 
    (zeroP := zeroP) in Ha; try assumption;
    try (eapply addP_gen_idempotent);
    destruct Ha as ((q & Hal) & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] s1 = false).
    destruct s1; cbn in Hal |- *; congruence.
    ++
      eexists;
      eapply union.in_set_uop_duplicate_elim_intro;
      eapply union.in_set_uop_duplicate_elim_elim in Hal;
      [eapply symAP| eapply trnAP|]; try assumption;
      try (eapply addP_gen_idempotent);
      eapply bop_list_product_is_right_intro;
      [eapply refAP | eapply trnAP | eapply symAP |
        eapply bop_cong | eapply bop_right | | exact Hb];
      try assumption; try (eapply addP_gen_idempotent);
      eapply bop_list_product_is_right_elim in Hal;
      [|eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_right]; try assumption;
      try (eapply addP_gen_idempotent);
      eapply in_set_uop_manger_phase_1_intro with 
      (zeroP := zeroP); try assumption;
      try (eapply addP_gen_idempotent);
      [eexists; exact Hal | eapply refP].
    ++
      (* This about it *)
      eapply sum_fn_backward_second;
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
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
    destruct Ha as (Hal & Har);
    assert (Hb : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_left];
      try assumption;
      eapply in_set_uop_manger_phase_2_elim in Hal; try assumption;
      destruct Hal as (Hala & Halb);
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      (* This is the challenge! Because it's 
        demanding s2 to be non-empty *)
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_left | | ];
      try assumption.
    ++
      intros ? ? Hb.
      eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
      destruct Ha as (Hal & Har).
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_left_elim,
      in_set_uop_manger_phase_2_elim in Hal;
      try assumption;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption.
      destruct Hal as (Hala & Halb).
      eapply Halb.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hb;
      [exact Hb | eapply trnAP | eapply symAP | eapply bop_left];
      try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption.
    destruct Ha as (Hal & Har).
    assert (Hq : brel_set (brel_product eqA eqP) [] s2 = false).
    eapply set_in_set_non_empty_right; exact Hal.
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply  bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_left | |
        exact Hq]; try assumption;
      eapply union.in_set_uop_duplicate_elim_elim, 
      bop_list_product_is_left_elim in Hal;
      [|eapply trnAP | eapply symAP | eapply bop_left];
      try assumption;
      eapply in_set_uop_manger_phase_2_intro;
      try assumption;
      intros * Hc; eapply Har;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption;
      eapply  bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply bop_left | |
      exact Hq]; try assumption;
      exact Hc.
    ++
      intros ? ? Hb.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption; eapply Har;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hb;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply in_set_uop_manger_phase_2_elim in Hb;
      try assumption;
      destruct Hb as (Hbl & Hbr);
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_left | exact Hbl | ];
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
  [eapply refAP|split; intros (au, av) Ha]; 
  try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption;
    destruct Ha as (Hal & Har).
    assert (Hb : brel_set (brel_product eqA eqP) [] 
      (uop_manger_phase_2 lteA s2) = false).
    eapply set_in_set_non_empty_right; exact Hal.
    assert (Hc : brel_set (brel_product eqA eqP) [] s2 = false).
    destruct s2; cbn in Hb; try congruence;
    cbn; try reflexivity.
    eapply in_set_uop_manger_phase_2_intro; try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP | ];
      try assumption.
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_left | exact Hal | exact Hc];
      try assumption.
    ++
      intros * Hd.
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption; eapply Har;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hd;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption.
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption.
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_left | exact Hd | ];
      try assumption.
  +
    eapply in_set_uop_manger_phase_2_elim in Ha; try assumption.
    destruct Ha as (Hal & Har).
    assert (Hq : brel_set (brel_product eqA eqP) [] s1 = false).
    eapply set_in_set_non_empty_left; exact Hal.
    (* go right *)
    eapply in_set_uop_manger_phase_2_intro;
    try assumption.
    ++
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_right_intro;
      [eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_right | | exact Hq];
      try assumption;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_right_elim in Hal;
      [|eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_right];
      try assumption;
      eapply in_set_uop_manger_phase_2_intro;
      try assumption;
      intros * Hb; eapply Har;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_right_intro;
      [eapply  refAP | eapply  trnAP | eapply  symAP|
      eapply bop_cong | eapply bop_right | exact Hb | ];
      try assumption.
    ++
      assert (Hw : brel_set (brel_product eqA eqP) [] s2 = false).
      eapply set_in_set_non_empty_right; exact Hal.
      intros * Hb;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hal;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption; eapply Har;
      eapply union.in_set_uop_duplicate_elim_elim,
      bop_list_product_is_left_elim in Hb;
      [| eapply trnAP | eapply symAP | eapply bop_left];
      try assumption;
      eapply union.in_set_uop_duplicate_elim_intro;
      [eapply symAP | eapply trnAP |];
      try assumption;
      eapply bop_list_product_is_left_intro;
      [eapply trnAP | eapply symAP | eapply 
      bop_left | exact Hb | ];
      try assumption.
Qed.
      



Lemma bop_manger_product_congruence :
    bop_congruence _ (@eq_manger A P eqA lteA eqP addP) 
      (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  eapply uop_compose_bop_congruence.
  + eapply symSAP.
  + eapply trnSAP; 
    try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption;
    try (eapply addP_gen_idempotent).
Qed.


Lemma manger_product_phase_0_associative : 
  bop_associative (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ? ? ?.
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha]; 
  try assumption.
  +
    (* preprocessing *)
    assert (Hb : brel_set (brel_product eqA eqP) []
      (manger_product_phase_0 eqA eqP mulA mulP s t) = false).
    eapply set_in_set_non_empty_left; exact Ha.
    assert (Hc : brel_set (brel_product eqA eqP) [] s = false).
    destruct s; cbn in Hb |- *; [congruence | reflexivity].
    assert (Hd : brel_set (brel_product eqA eqP) []
      (manger_product_phase_0 eqA eqP mulA mulP t u) = false).
    eapply lift_lemma_1 in Ha;
    [eapply set_in_set_non_empty_right; exact Ha | eapply refAP |
    eapply trnAP | eapply symAP | eapply bop_cong | eapply bop_assoc];
    try assumption.
    assert (He : brel_set (brel_product eqA eqP) [] t = false).
    destruct t; cbn in Hd |- *; [congruence | reflexivity].
    (* I can use the fact the manger_product_0 
    is commutative but it's not necessary *)
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* go right *)
    eapply bop_list_product_is_right_elim in Ha;
    [ | eapply refAP | eapply trnAP | eapply symAP | 
      eapply bop_right]; try assumption.
    eapply bop_list_product_is_right_intro;
    [eapply refAP | eapply trnAP | eapply symAP |
    eapply bop_cong | eapply bop_right | | exact Hc];
    try assumption.
    eapply union.in_set_uop_duplicate_elim_intro;
    [eapply symAP | eapply trnAP | 
    eapply bop_list_product_is_right_intro; 
      [eapply refAP| eapply trnAP  | eapply symAP | 
      eapply bop_cong  | eapply bop_right | | ] ];
    try assumption.
  +
    (* preprocessing *)
    assert (Hb : brel_set (brel_product eqA eqP) []
    (manger_product_phase_0 eqA eqP mulA mulP t u) = false).
    eapply  set_in_set_non_empty_right; exact Ha.
    assert (Hc : brel_set (brel_product eqA eqP) [] t = false).
    destruct t; cbn in Hb |- *; [congruence | reflexivity].
    assert (Hd : brel_set (brel_product eqA eqP) [] u = false).
    eapply lift_lemma_2 in Ha; 
    [eapply set_in_set_non_empty_right; exact Ha |
    eapply refAP | eapply trnAP | eapply symAP | 
    eapply bop_cong | eapply bop_assoc]; try assumption.
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption.
    (* end of preprocessing *)
    (* go left *)
    eapply bop_list_product_is_left_elim in Ha;
    [| eapply trnAP | eapply symAP | eapply bop_left];
    try assumption.
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | eapply bop_left | 
    eapply union.in_set_uop_duplicate_elim_intro;
    [eapply symAP | eapply trnAP | 
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | eapply bop_left |  | ]] | 
    exact Hd]; try assumption.
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
  + eapply  manger_product_phase_0_associative.
  + eapply P1_cong with (fA := fA) (zeroP := zeroP) (lteA := lteA); 
    try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
Qed.


Lemma manger_product_phase_0_commutative : 
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
    [eapply symAP| eapply trnAP|]; try assumption;
    (* intro and elim rule for bop_list_product_left 
    from CAS.coq.sg.lift *)
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | | |];
    try assumption.
    ++
      eapply bop_left.
    ++
      eapply bop_list_product_is_right_elim in Ha;
      [|eapply refAP | eapply trnAP | eapply symAP | eapply bop_right]; 
      try assumption.
    ++
      destruct s; cbn in Ha;
      try congruence;
      cbn; reflexivity.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    eapply union.in_set_uop_duplicate_elim_elim in Ha;
    [eapply symAP| eapply trnAP|]; try assumption;
    (* intro and elim rule for bop_list_product_left 
    from CAS.coq.sg.lift *)
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | eapply symAP | | |];
    try assumption.
    ++
      eapply bop_left.
    ++
      eapply bop_list_product_is_right_elim in Ha;
      [|eapply refAP | eapply trnAP | eapply symAP | eapply bop_right]; 
      try assumption.
    ++
      destruct t; cbn in Ha;
      try congruence;
      cbn; reflexivity.
Qed.


Lemma bop_manger_product_commutative :
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  eapply uop_compose_bop_commutative.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption; 
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
  + eapply manger_product_phase_0_commutative.
Qed.


Lemma manger_product_phase_0_idem : 
  bop_idempotent (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
  intros ?;
  eapply brel_set_intro_prop;
  [eapply refAP | split; intros (au, av) Ha];
  try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_elim,
    bop_list_product_is_left_elim in Ha;
    [| eapply trnAP | eapply symAP | eapply bop_left];
    try assumption.
  +
    eapply union.in_set_uop_duplicate_elim_intro;
    [eapply symAP | eapply trnAP | ];
    try assumption;
    eapply bop_list_product_is_left_intro;
    [eapply trnAP | apply symAP | eapply bop_left | 
      exact Ha | ];
    try assumption;
    destruct s; cbn in Ha;
    try congruence; 
    cbn; reflexivity.
Qed.



Lemma bop_manger_product_idempotent :
  bop_idempotent _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  eapply uop_compose_bop_idempotent.
  + eapply refSAP; try assumption.
  + eapply symSAP; try assumption.
  + eapply trnSAP; try assumption.
  + eapply manger_product_phase_0_cong.
  + eapply P1_cong with (fA := fA) (lteA := lteA)
    (zeroP := zeroP); try assumption;
    try (eapply addP_gen_idempotent).
  + eapply P1_idem; try assumption;
    try (eapply addP_gen_idempotent).
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply P2_idem; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption; try (eapply addP_gen_idempotent).
  + eapply  manger_product_phase_0_idem.
Qed.
  


Lemma bop_manger_product_not_selective :
  bop_not_selective _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  destruct ntot as ((a₁, a₂) & Ha);
  exists ([(a₁, wP)], [(a₂, wP)]).
  (* Discuss this with Tim *)
Admitted.  

End Theory.  



