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

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.reduce. 

(* for testing *)
Require Import CAS.coq.sg.manger_llex.
Require Import CAS.coq.eqv.nat. 
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.po.from_sg.



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
   (* idempotence is baked in this addP_gen_idempotent but it can be proved *)
   (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
   (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true)
   (addP_gen_idempotent : ∀ x y : P, eqP x y = true → eqP (addP x y) y = true).

Local Notation "[EQP0]" :=  (brel_set (brel_product eqA eqP)) (only parsing).
Local Notation "[EQP1]" :=  (equal_manger_phase_1 eqA eqP addP) (only parsing). 
Local Notation "[MP1]" :=  (uop_manger_phase_1 eqA addP) (only parsing).
Local Notation "[MPP0]" :=  (manger_product_phase_0 eqA eqP mulA mulP) (only parsing).
Local Notation "[MP]" := (bop_manger_product eqA lteA eqP addP mulA mulP) (only parsing). 
Local Notation "[MR]" := (@uop_manger_phase_2 A P lteA) (only parsing).
Local Notation "[EQ]" := (equal_manger eqA lteA eqP addP) (only parsing).

(*
  Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r.  (* eqS (r (b (r s1) s2)) (r (b s1 s2))  = true. *)
bop_left_uop_invariant = 
λ (S : Type) (eq0 : brel S) (b : binary_op S) (r : unary_op S), ∀ s1 s2 : S, eq0 (b (r s1) s2) (b s1 s2) = true

eq0 (b (r s1) s2) (b s1 s2) = true
 

Lemma test0 : bop_left_uop_invariant _ [EQP0] [MPP0] [MP1].
 


Lemma test0_left (a : A) (p : P) : ∀ X Y, 
  set.in_set (brel_product eqA eqP) ([MP1] ([MPP0] ([MP1] X) Y)) (a, p) = true -> 
  set.in_set (brel_product eqA eqP) ([MP1] ([MPP0] X Y)) (a, p) = true.
Proof. intros X Y H1.
(*
      MP1 {(a1, b1), (a1, b2), (a3, b3)} x {(a4, b4)}
       =
      MP1 {(a1a4, b1b4), (a1a4, b2b4), (a3a4, b3b4)}
       =
      MP1 {(a1a4, b1b4+b2b4), (a3a4, b3b4)}
      = (if a1a4 = a3a4) 
      {(a1a4, b1b4+b2b4 + b3b4)}
        
vs 
     MP1 (MP1 {(a1, b1), (a1, b2), (a3, b3)}) x {(a4, b4)}
     =
     MP1 ({(a1, b1+b2), (a3, b3)}) x {(a4, b4)}
     =
     MP1 {(a1a4, (b1+b2)b4), (a3a4, b3b4)}
     =
     MP1 {(a1a4, (b1+b2)b4), (a3a4, b3b4)}
      = (if a1a4 = a3a4) 
     {(a1a4, (b1+b2)b4 + b3b4)}
 *)
Admitted.


Lemma test0_right (a : A) (p : P) : ∀ X Y, 
    set.in_set (brel_product eqA eqP) ([MP1] ([MPP0] X Y)) (a, p) = true -> 
  set.in_set (brel_product eqA eqP) ([MP1] ([MPP0] ([MP1] X) Y)) (a, p) = true.
Admitted. 
*)

Lemma manger_product_phase_0_cong :
  bop_congruence (finite_set (A * P)) (manger_llex.eqSAP A P eqA eqP)
  (manger_product_phase_0 eqA eqP mulA mulP).
Proof.
Admitted.

Lemma bop_left_uop_inv_phase_1 : 
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
    (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Admitted.

Lemma bop_right_uop_inv_phase_1 : 
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_1 eqA addP)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_1 eqA addP).
Admitted.

Lemma bop_left_uop_inv_phase_2 : 
  bop_left_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_2 lteA)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_2 lteA).
Admitted.

Lemma bop_right_uop_inv_phase_2 : 
  bop_right_uop_invariant (finite_set (A * P))
  (manger_llex.eqSAP A P eqA eqP)
  (bop_reduce (uop_manger_phase_2 lteA)
     (manger_product_phase_0 eqA eqP mulA mulP))
  (uop_manger_phase_2 lteA).
Admitted.



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
    (zeroP := zeroP); try assumption. 
  + eapply bop_left_uop_inv_phase_1.
  + eapply bop_right_uop_inv_phase_1.
  + eapply P2_cong; try assumption.
  + eapply bop_left_uop_inv_phase_2.
  + eapply bop_right_uop_inv_phase_2.
  + intros *. eapply P1_P2_commute with (fA := fA) (zeroP := zeroP);
    try assumption.
Qed.


Lemma bop_manger_product_associative :
  bop_associative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Proof.
  apply uop_compose_bop_associative.
Admitted.


Lemma bop_manger_product_commutative :
  bop_commutative _ (@eq_manger A P eqA lteA eqP addP)
  (bop_manger_product eqA lteA eqP addP mulA mulP).
Admitted.





  
(* 
Lemma test0 : bop_left_uop_invariant _ [EQP0] [MPP1] [MP1].
Proof. (* [EQP0] ([MPP1] ([MP1] X) Y) ([MPP1] X Y) = true *)
         intros X Y.
         unfold manger_product_phase_1.
         unfold bop_reduce.
         (* [EQP0] ([MP1] ([MPP0] ([MP1] X) Y)) ([MP1] ([MPP0] X Y)) = true *)
         apply brel_set_intro_prop. 
         - apply refAP; auto. 
         - split; intros [a p] H1. 
           + apply test0_left; auto. 
           + apply test0_right; auto. 
Qed.
*)
(*
Proof. 
       intro X; induction X; intro Y.
       - 
         (*   [EQP0] ([MPP0] nil Y) ([MPP0] nil Y) = true *)
         admit.
       - (* [EQP0] ([MPP0] ([MP1] (a :: X)) Y) ([MPP0] (a :: X) Y) = true *) 
         unfold uop_manger_phase_1.
         simpl. unfold manger_phase_1_auxiliary.
         
         admit.
Admitted. 
*) 

(* 
Lemma test1 : bop_left_uop_invariant _ [EQP0] [MPP0] [MP1].
Proof. intros X Y. unfold manger_product_phase_0.
       (* [EQP0] ([MPP0] ([MP1] X) Y) ([MPP0] X Y) = true *)
(*       intro X; induction X; intro Y.
       - unfold uop_manger_phase_1. simpl.
         (*   [EQP0] ([MPP0] nil Y) ([MPP0] nil Y) = true *)
         admit.
       - (* [EQP0] ([MPP0] ([MP1] (a :: X)) Y) ([MPP0] (a :: X) Y) = true *) 
         unfold uop_manger_phase_1.
         simpl. unfold manger_phase_1_auxiliary.
         
         admit. 
*)
Admitted. 

Lemma bop_manger_product_left_uop_invariant : 
    bop_left_uop_invariant _ [EQP1]  [MP] [MR]. 
Proof. intros X Y. unfold bop_manger_product.
       unfold bop_reduce.
       unfold equal_manger_phase_1.
       unfold bop_reduce.
       (*
         [EQP0] ([MP1] ([MR]        ([MPP1] ([MR] X) Y)))  ([MP1] ([MR] ([MPP1] X Y)))
         [EQP0] ([MP1] ([MR] ([MP1] ([MPP0] ([MR] X) Y)))) ([MP1] ([MR] ([MP1] ([MPP0] X Y))))

        *) 
Admitted.


Lemma bop_manger_product_right_uop_invariant : 
    bop_right_uop_invariant _ [EQ]  [MP] [MR]. 
Admitted. 
*)
  

End Theory.  



