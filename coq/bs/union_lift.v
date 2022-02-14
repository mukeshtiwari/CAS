Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.add_one. 

Section Theory.

  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable bS : binary_op S.
  
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
  
  Variable bcong : bop_congruence S r bS. 
  Variable assS : bop_associative S r bS. 


Lemma bop_union_lift_left_distributive : 
        bop_left_distributive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_lift_elim in H;
          auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
          apply in_set_bop_union_elim in P2; auto.
          destruct P2 as [R | R].
             left. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X Y a x y); auto. 
             right. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X Z a x y); auto. 
       
       apply in_set_bop_union_elim in H; auto. destruct H as [H | H].
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X (bop_union r Y Z) a x y); auto.
       apply in_set_bop_union_intro; auto.
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X (bop_union r Y Z) a x y); auto.
       apply in_set_bop_union_intro; auto. 
Qed. 

(* just a test *) 
Lemma bop_union_lift_left_distributive_dual : 
        bop_left_distributive (finite_set S) (brel_set r)  (bop_lift r bS) (bop_union r). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.
          apply in_set_bop_union_elim in H.
          destruct H as [H | H].
          + admit. (* need idempotence *) 
          + admit. (* need (X U Y) [^] (Z [^] W) = (X [^] Z) U (X [^] W) U (Y [^] Z) U (X [^] W) *) 
Admitted. 

(* just a test *) 
Lemma bop_union_lift_not_left_distributive_dual :
        bop_not_idempotent S r bS -> 
        bop_not_left_distributive (finite_set S) (brel_set r)  (bop_lift r bS) (bop_union r). 
Proof. intros [i nidem]. exists (i :: nil, (nil, nil)).  compute.
       rewrite nidem. assert (H : r i (bS i i) = false). admit.  rewrite H. reflexivity. 
Admitted. 

        
Lemma bop_union_lift_right_distributive : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_lift_elim in H;
          auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
          apply in_set_bop_union_elim in P1; auto.
          destruct P1 as [R | R].
             left. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong Y X a x y); auto. 
             right. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong Z X a x y); auto. 
       
       apply in_set_bop_union_elim in H; auto. destruct H as [H | H].
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong (bop_union r Y Z) X a x y); auto.
       apply in_set_bop_union_intro; auto.
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong (bop_union r Y Z) X a x y); auto.
       apply in_set_bop_union_intro; auto. 
Qed. 



Lemma bops_union_lift_left_left_absorptive : 
        bop_is_left S r bS -> bops_left_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IL X Y. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_lift_elim in H; auto. destruct H as [x [y [[H1 H2] H3]]].
             assert (H4 := IL x y).
             assert (H5 := tranS _ _ _ H3 H4).
             apply symS in H5. assert (H6 := in_set_right_congruence _ _ symS tranS _ _ _ H5 H1). exact H6. 
Qed. 

(* just a test *) 
Lemma bops_union_lift_left_left_absorptive_dual : 
        bop_is_left S r bS -> bops_left_left_absorptive (finite_set S) (brel_set r) (bop_lift r bS) (bop_union r). 
Proof. intros IL X Y. 
       (* hmm, should work as well *) 
Admitted.

Lemma bops_union_lift_not_left_left_absorptive : 
        bop_not_is_left S r bS -> bops_not_left_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros [[s t] P]. unfold bops_not_left_left_absorptive. 
       exists (s :: nil, t :: nil).
       case_eq(brel_set r (s :: nil) (bop_union r (s :: nil) (bop_lift r bS (s :: nil) (t :: nil)))); intro J1; auto.
          apply brel_set_elim in J1. destruct J1 as [L R].
          assert (K1 := brel_subset_elim _ _ symS tranS _ _ R (bS s t)).
          assert (K2 : in_set r (bop_union r (s :: nil) (bop_lift r bS (s :: nil) (t :: nil))) (bS s t) = true).
             apply in_set_bop_union_intro; auto.
             right. apply in_set_bop_lift_intro; auto.
             apply in_set_singleton_intro; auto.
             apply in_set_singleton_intro; auto.              
          assert (K3 := K1 K2).
          apply in_set_singleton_elim in K3; auto.
          apply symS in K3. rewrite K3 in P. discriminate P. 
Defined.

Definition bops_union_lift_left_left_absorptive_decide (ld : bop_is_left_decidable S r bS) : 
    bops_left_left_absorptive_decidable (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS)
  := match ld with
     | inl lla  => inl (bops_union_lift_left_left_absorptive lla)
     | inr nlla => inr (bops_union_lift_not_left_left_absorptive nlla)
     end.                                                          


Lemma bops_union_lift_left_right_absorptive : 
        bop_is_right S r bS -> bops_left_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IR X Y. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_lift_elim in H; auto. destruct H as [x [y [[H1 H2] H3]]].
             assert (H4 := IR x y).
             assert (H5 := tranS _ _ _ H3 H4).
             apply symS in H5. assert (H6 := in_set_right_congruence _ _ symS tranS _ _ _ H5 H2). exact H6. 
Qed. 

Lemma bops_union_lift_not_left_right_absorptive : 
        bop_not_is_right S r bS -> bops_not_left_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros [[s t] P]. 
       exists (t :: nil, s :: nil).
       case_eq(brel_set r (t :: nil) (bop_union r (t :: nil) (bop_lift r bS (s :: nil) (t :: nil)))); intro J1; auto.
          apply brel_set_elim in J1. destruct J1 as [L R].
          assert (K1 := brel_subset_elim _ _ symS tranS _ _ R (bS s t)).
          assert (K2 : in_set r (bop_union r (t :: nil) (bop_lift r bS (s :: nil) (t :: nil))) (bS s t) = true).
             apply in_set_bop_union_intro; auto.
             right. apply in_set_bop_lift_intro; auto.
             apply in_set_singleton_intro; auto.
             apply in_set_singleton_intro; auto.              
          assert (K3 := K1 K2).
          apply in_set_singleton_elim in K3; auto.
          apply symS in K3. rewrite K3 in P. discriminate P. 
Defined. 

Definition bops_union_lift_left_right_absorptive_decide (rd : bop_is_right_decidable S r bS) : 
    bops_left_right_absorptive_decidable (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS)
  := match rd with
     | inl lra  => inl (bops_union_lift_left_right_absorptive lra)
     | inr nlra => inr (bops_union_lift_not_left_right_absorptive nlra)
     end.                                                          


Lemma bops_union_lift_right_left_absorptive : 
        bop_is_left S r bS -> bops_right_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IL. 
       apply bops_left_left_absorptive_implies_right_left.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative; auto. 
       apply bops_union_lift_left_left_absorptive; auto. 
Qed. 


Lemma bops_union_lift_not_right_left_absorptive : 
        bop_not_is_left S r bS -> bops_not_right_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros NIL. 
       apply bops_not_left_left_absorptive_implies_not_right_left.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative; auto. 
       apply bops_union_lift_not_left_left_absorptive; auto. 
Defined. 

Definition bops_union_lift_right_left_absorptive_decide (ld : bop_is_left_decidable S r bS) : 
    bops_right_left_absorptive_decidable (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS)
  := match ld with
     | inl lla  => inl (bops_union_lift_right_left_absorptive lla)
     | inr nlla => inr (bops_union_lift_not_right_left_absorptive nlla)
     end.                                                          

Lemma bops_union_lift_right_right_absorptive : 
        bop_is_right S r bS -> bops_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IR. 
       apply bops_left_right_absorptive_implies_right_right.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative; auto. 
       apply bops_union_lift_left_right_absorptive; auto. 
Defined. 

Lemma bops_union_lift_not_right_right_absorptive : 
        bop_not_is_right S r bS -> bops_not_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros NIR. 
       apply bops_not_left_right_absorptive_implies_not_right_right.
       apply brel_set_transitive; auto. 
       apply bop_union_commutative; auto. 
       apply bops_union_lift_not_left_right_absorptive; auto. 
Defined.

Definition bops_union_lift_right_right_absorptive_decide (rd : bop_is_right_decidable S r bS) : 
    bops_right_right_absorptive_decidable (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS)
  := match rd with
     | inl lra  => inl (bops_union_lift_right_right_absorptive lra)
     | inr nlra => inr (bops_union_lift_not_right_right_absorptive nlra)
     end.                                                          



Lemma bops_union_lift_id_equals_ann : bops_exists_id_ann_equal (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS).
Proof. exists nil; split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_lift_nil_is_ann; auto.       
Defined.





(*
Lemma bops_lift_union_id_equals_ann (has_id : bop_exists_id S r bS) :
           bops_exists_id_ann_equal (finite_set S) (brel_set r) (bop_lift r bS) (bop_union r).
Proof. destruct has_id as [id P]. exists (id :: nil); split.
       apply bop_lift_is_id; auto.              
       apply bop_union_nil_is_ann; auto. 

Defined.


Lemma bops_union_lift_not_ann_equals_id (bS_id_d : bop_exists_id_decidable S r bS) (fin_d : carrier_is_finite_decidable S r):
              bops_not_id_equals_ann (finite_set S) (brel_set r) (bop_lift r bS) (bop_union r).
Proof. unfold bops_not_id_equals_ann.
       intro X. destruct bS_id_d as [[id Pid] | bS_no_id]; destruct fin_d as [FS | NFS]. 
       assert (lift_id := bop_lift_is_id S r bS refS tranS symS bcong id Pid).
       assert (union_ann := bop_union_enum_is_ann S r refS symS tranS FS).
       destruct FS as [enumS FinS]. simpl in union_ann.
       assert (set_sym := brel_set_symmetric S r).
       assert (set_trans := brel_set_transitive S r refS symS tranS).
       assert (id_unique := bop_is_id_equal (finite_set S) (brel_set r) set_sym set_trans (bop_lift r bS)  (id :: nil)). 
       assert (ann_unique := bop_is_ann_equal (finite_set S) (brel_set r) set_sym set_trans (bop_union r)  (enumS tt)). 
       assert (K : (brel_set r (id :: nil) X = false) + (brel_set r (enumS tt) X = false)). 
          case_eq(brel_set r (id :: nil) X); intro J1; case_eq(brel_set r (enumS tt) X); intro J2; auto.                
          apply set_sym in J2. 
          assert (F := set_trans _ _ _ J1 J2).
          apply brel_set_elim_prop in F; auto. destruct F as [L R]. 
          assert (Q: in_set r (enumS tt) (f id) = true). apply FinS. 
          assert (P := R (f id) Q). compute in P.
          destruct (ntS id) as [_ Z]. rewrite Z in P. discriminate P. 
       destruct K as [ K | K ].
       left. apply (bop_not_is_id_intro _ _ (id :: nil) X (bop_lift r bS) set_sym set_trans); auto. 
       right. apply (bop_not_is_ann_intro _ _ (enumS tt) X (bop_union r) set_sym set_trans); auto.
       
       right. apply bop_union_not_exists_ann; auto. 
       left.  apply bop_lift_not_exists_id; auto.
       left.  apply bop_lift_not_exists_id; auto.
Defined. 
*) 
End Theory. 

Section ACAS.

Section Proofs.   

Variables (S : Type)
          (wS : S)
          (rS : brel S)
          (bS : binary_op S)
          (f : S -> S)
          (ntS : brel_not_trivial S rS f)
          (* (fin_d : carrier_is_finite_decidable S rS)  *)
          (eqvS : A_eqv S)
          (sgS : sg_proofs S (A_eqv_eq _ eqvS) bS).         

Definition bs_proofs_union_lift_aux : 
  bs_proofs (finite_set S) (brel_set (A_eqv_eq _ eqvS)) (bop_union (A_eqv_eq _ eqvS)) (bop_lift (A_eqv_eq _ eqvS) bS) :=
let eqvP := A_eqv_proofs _ eqvS in
let rS   := A_eqv_eq _ eqvS in  
let refS := A_eqv_reflexive S rS eqvP  in
let symS := A_eqv_symmetric S rS eqvP  in
let trnS := A_eqv_transitive S rS eqvP in
let cnbS := A_sg_congruence S rS bS sgS in
let ilD  := A_sg_is_left_d S rS bS sgS in  
let irD  := A_sg_is_right_d S rS bS sgS in  
{|
  A_bs_left_distributive_d      := inl (bop_union_lift_left_distributive S rS bS refS symS trnS cnbS)
; A_bs_right_distributive_d     := inl (bop_union_lift_right_distributive S rS bS refS symS trnS cnbS)
; A_bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_decide S rS bS refS symS trnS cnbS irD 
; A_bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_decide S rS bS refS symS trnS cnbS irD
|}.


Definition bs_proofs_union_lift (c : cas_constant) : 
  bs_proofs (with_constant (finite_set S))
            (brel_sum brel_constant (brel_set (A_eqv_eq _ eqvS)))
            (bop_add_ann (bop_union (A_eqv_eq _ eqvS)) c) 
            (bop_add_id (bop_lift (A_eqv_eq _ eqvS) bS) c) :=
  let eq   := (A_eqv_eq _ eqvS) in
  let eqvP := A_eqv_proofs _ eqvS in 
   bs_proofs_add_one (finite_set S)
                     (brel_set eq)
                     c
                     (bop_union eq)
                     (bop_lift eq bS)
                     (eqv_proofs_set S eq eqvP)
                     (A_sg_proofs_from_sg_CI_proofs
                        (finite_set S)
                        (brel_set eq)
                        (bop_union eq)
                        (wS :: nil)
                        (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil) (* fix someday *) 
                        (brel_set_not_trivial S eq wS)
                        (eqv_proofs_set S  eq eqvP) 
                        (sg_CI_proofs_union eqvS))
                     bs_proofs_union_lift_aux.

Definition id_ann_proofs_union_lift (c : cas_constant) : 
  id_ann_proofs
            (with_constant (finite_set S))
            (brel_sum brel_constant (brel_set (A_eqv_eq _ eqvS)))
            (bop_add_ann (bop_union (A_eqv_eq _ eqvS)) c) 
            (bop_add_id (bop_lift (A_eqv_eq _ eqvS) bS) c) :=
let eq      := A_eqv_eq _ eqvS in
let eqvP    := A_eqv_proofs _ eqvS in  
let refS    := A_eqv_reflexive _ _ eqvP in
let symS    := A_eqv_symmetric _ _ eqvP in
let trnS    := A_eqv_transitive _ _ eqvP in 
let set_ref := brel_set_reflexive _ _ refS symS in
{|
  A_id_ann_plus_times_d :=
    Id_Ann_Proof_Equal _ _ _ _ 
    (bops_add_one_exists_id_ann_equal_left
      (finite_set S)
      (brel_set eq)
      c
      (bop_union eq)
      (bop_lift eq bS)
      set_ref 
      (bops_union_lift_id_equals_ann S eq bS refS symS trnS ))
  ; A_id_ann_times_plus_d :=
      Id_Ann_Proof_Equal _ _ _ _ 
    (bops_add_one_exists_id_ann_equal_right
      (finite_set S)
      (brel_set eq)
      c
      (bop_union eq)
      (bop_lift eq bS)
      set_ref)
|}. 


(*
Definition id_ann_proofs_union_lift : 
  ∀ (S : Type) (s : S) (rS : brel S) (bS : binary_op S) (f : S -> S),
    brel_not_trivial S rS f -> 
    carrier_is_finite_decidable S rS -> 
    bop_exists_id_decidable S rS bS -> 
    eqv_proofs S rS ->
    msg_proofs S rS bS ->
      id_ann_proofs (finite_set S) (brel_set rS) (bop_union rS) (bop_lift rS bS)
:= λ S s rS bS f ntS fin_d exists_idS eqvS sgS,
let refS := A_eqv_reflexive S rS eqvS  in
let symS := A_eqv_symmetric S rS eqvS  in
let trnS := A_eqv_transitive S rS eqvS in
let cnbS := A_msg_congruence S rS bS sgS in
let ilD  := A_msg_is_left_d S rS bS sgS in  
{|
      A_id_ann_exists_plus_id_d        := inl _ (bop_union_exists_id S rS refS symS trnS)
    ; A_id_ann_exists_plus_ann_d       := bop_union_exists_ann_decide S rS refS symS trnS fin_d
    ; A_id_ann_exists_times_id_d       := bop_lift_exists_id_decide S rS s bS refS symS trnS cnbS exists_idS 
    ; A_id_ann_exists_times_ann_d      := inl (bop_lift_exists_ann S rS bS)
    ; A_id_ann_plus_id_is_times_ann_d  := inl (bops_union_lift_id_equals_ann S rS bS refS symS trnS)
    ; A_id_ann_times_id_is_plus_ann_d := inr (bops_union_lift_not_ann_equals_id S rS s f ntS bS refS symS trnS cnbS exists_idS fin_d)
|}.

 *)

End Proofs.   

Section Combinators.


Definition A_bs_union_lift (S : Type) (sgS : A_sg S) (c : cas_constant) : A_bs (with_constant (finite_set S)) := 
let eqvS  := A_sg_eqv S sgS in
let rS    := A_eqv_eq S eqvS in   
let bS    := A_sg_bop S sgS in
let eqvP  := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
{| 
  A_bs_eqv           := A_eqv_add_constant _ (A_eqv_set S eqvS) c 
   ; A_bs_plus          := bop_add_ann (bop_union rS) c 
   ; A_bs_times         := bop_add_id (bop_lift rS bS) c 
   ; A_bs_plus_proofs   := sg_proofs_add_ann
                             (finite_set S)
                             (brel_set rS)
                             c
                             (bop_union rS)
                             (s :: nil)
                             (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                             (brel_set_not_trivial S rS s)
                             (eqv_proofs_set S  rS eqvP) 
                             (A_sg_proofs_from_sg_CI_proofs
                                (finite_set S)
                                (brel_set rS)
                                (bop_union rS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                                (brel_set_not_trivial S rS s)
                                (eqv_proofs_set S  rS eqvP) 
                                (sg_CI_proofs_union eqvS))
   ; A_bs_times_proofs  := sg_proofs_add_id
                             (finite_set S)
                             (brel_set rS)
                             c
                             (bop_lift rS bS)
                             (s :: nil)
                             (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                             (brel_set_not_trivial S rS s)
                             (eqv_proofs_set S  rS eqvP) 
                             (sg_lift_proofs S rS bS eqvP s f Pf (A_eqv_exactly_two_d _ eqvS) (A_sg_proofs S sgS))
   ; A_bs_id_ann_proofs := id_ann_proofs_union_lift S bS eqvS c 
   ; A_bs_proofs        := bs_proofs_union_lift S s bS eqvS (A_sg_proofs S sgS) c
   ; A_bs_ast           := Ast_bs_union_lift (A_sg_ast S sgS)
|}.


(* 
Definition A_bs_CI_union_lift : ∀ (S : Type),  A_msg S -> A_bs_CI (finite_set S)
:= λ S sgS,
let eqvS  := A_msg_eq S sgS in
let rS    := A_eqv_eq S eqvS in   
let bS    := A_msg_bop S sgS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
{| 
     A_bs_CI_eqv           := A_eqv_set S eqvS
   ; A_bs_CI_plus          := bop_union rS
   ; A_bs_CI_times         := bop_lift rS bS
   ; A_bs_CI_id_ann_proofs := id_ann_proofs_union_lift S s rS bS f Pf (A_eqv_finite_d S eqvS) (A_msg_exists_id_d S sgS) peqvS (A_msg_proofs S sgS)
   ; A_bs_CI_plus_proofs   := sg_CI_proofs_union eqvS
   ; A_bs_CI_times_proofs  := msg_lift_proofs S rS bS peqvS s f Pf (A_msg_proofs S sgS)
   ; A_bs_CI_proofs        := bs_proofs_union_lift S s rS bS f Pf (A_eqv_finite_d S eqvS) peqvS (A_msg_proofs S sgS)
   ; A_bs_CI_ast           := Ast_bs_union_lift (A_msg_ast S sgS)
|}.
*) 
End Combinators.   

End ACAS.

Section CAS.


Section Checks.   

Definition bops_union_lift_left_left_absorptive_check {S : Type} (ilD : @check_is_left S) : @check_left_left_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Left              => Certify_Left_Left_Absorptive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Left_Left_Absorptive ((s1 :: nil), (s2 :: nil))
end. 

Definition bops_union_lift_left_right_absorptive_check {S : Type} (ilD : @check_is_right S) : @check_left_right_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Right              => Certify_Left_Right_Absorptive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Left_Right_Absorptive ((s2 :: nil), (s1 :: nil))
end. 


Definition bops_union_lift_right_left_absorptive_check {S : Type} (ilD : @check_is_left S) :@check_right_left_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Left              => Certify_Right_Left_Absorptive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Right_Left_Absorptive ((s1 :: nil), (s2 :: nil))
end. 

Definition bops_union_lift_right_right_absorptive_check {S : Type} (ilD : @check_is_right S) : @check_right_right_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Right              => Certify_Right_Right_Absorptive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Right_Right_Absorptive ((s2 :: nil), (s1 :: nil))
end.

End Checks. 


Section Proofs. 

Definition bs_certs_union_lift_aux {S : Type} (sgS : @sg_certificates S) : @bs_certificates (finite_set S) := 
let ilD  := sg_is_left_d sgS in  
let irD  := sg_is_right_d sgS in  
{|
  bs_left_distributive_d      := Certify_Left_Distributive 
; bs_right_distributive_d     := Certify_Right_Distributive 
; bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_check ilD 
; bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_check irD 
; bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_check ilD 
; bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_check irD
|}.


Definition bs_certs_union_lift {S : Type} (eqvS : @eqv S) (sgS : @sg_certificates S) (c : cas_constant) : 
  @bs_certificates (with_constant (finite_set S)) := 
  let eq   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in 
   bs_certs_add_one c
                     (sg_certs_from_sg_CI_certs
                        (finite_set S)
                        (brel_set eq)
                        (bop_union eq)
                        (wS :: nil)
                        (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil) (* fix someday *) 
                        (sg_CI_certs_union eqvS))
                     (bs_certs_union_lift_aux sgS).


Definition id_ann_certs_union_lift {S : Type} (c : cas_constant) : 
  @id_ann_certificates (with_constant (finite_set S)) := 
{|
  id_ann_plus_times_d := Id_Ann_Cert_Equal (inr nil) 
; id_ann_times_plus_d := Id_Ann_Cert_Equal (inl c) 
|}. 

End Proofs.   

Section Combinators.


Definition bs_union_lift {S : Type} (sgS : @sg S) (c : cas_constant) :@bs (with_constant (finite_set S)) := 
let eqvS  := sg_eqv sgS in
let rS    := eqv_eq eqvS in   
let bS    := sg_bop sgS in
let s     := eqv_witness eqvS in
let f     := eqv_new eqvS in
{| 
     bs_eqv           := eqv_add_constant (eqv_set eqvS) c 
   ; bs_plus          := bop_add_ann (bop_union rS) c 
   ; bs_times         := bop_add_id (bop_lift rS bS) c 
   ; bs_plus_certs   := sg_certs_add_ann
                             c
                             (s :: nil)
                             (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                             (sg_certs_from_sg_CI_certs
                                (finite_set S)
                                (brel_set rS)
                                (bop_union rS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                                (sg_CI_certs_union eqvS))
   ; bs_times_certs  := sg_certs_add_id
                             c
                             (s :: nil)
                             (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                             (sg_lift_certs S rS s f (eqv_exactly_two_d eqvS) bS (sg_certs sgS))
   ; bs_id_ann_certs := id_ann_certs_union_lift c 
   ; bs_certs        := bs_certs_union_lift eqvS (sg_certs sgS) c
   ; bs_ast          := Ast_bs_union_lift (sg_ast sgS)
|}.
  

End Combinators.   

End CAS.

Section Verify.


Lemma correct_bops_union_lift_left_left_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_left_left_absorptive (finite_set S) (brel_set eq) (bop_union eq) (bop_lift eq bS)
                           (bops_union_lift_left_left_absorptive_decide S eq bS refS symS trnS cong il_d)
  =                                                                               
  bops_union_lift_left_left_absorptive_check (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_left_right_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_left_right_absorptive (finite_set S) (brel_set eq) (bop_union eq) (bop_lift eq bS)
                            (bops_union_lift_left_right_absorptive_decide S eq bS refS symS trnS cong ir_d)
  =
  bops_union_lift_left_right_absorptive_check (p2c_is_right_check S eq bS ir_d).
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_left_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_right_left_absorptive (finite_set S) (brel_set eq) (bop_union eq) (bop_lift eq bS)
                            (bops_union_lift_right_left_absorptive_decide S eq bS refS symS trnS cong  il_d)
  =
  bops_union_lift_right_left_absorptive_check (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_right_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_right_right_absorptive (finite_set S) (brel_set eq) (bop_union eq) (bop_lift eq bS)
                             (bops_union_lift_right_right_absorptive_decide S eq bS refS symS trnS cong ir_d) 
  =                                      
  bops_union_lift_right_right_absorptive_check (p2c_is_right_check S eq bS ir_d). 
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 


Lemma correct_bs_certs_union_lift_aux 
  (S : Type) (bS : binary_op S) (eqvS : A_eqv S) (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) : 
  P2C_bs _ _ _ _ (bs_proofs_union_lift_aux S bS eqvS sgP)
  = 
  bs_certs_union_lift_aux (P2C_sg S (A_eqv_eq S eqvS) bS sgP).
Proof. destruct sgP. unfold bs_proofs_union_lift_aux, bs_certs_union_lift_aux, P2C_sg, P2C_bs; simpl.
       destruct A_sg_is_left_d as [L | [[a b] NL]]; destruct A_sg_is_right_d as [R | [[c d] NR]]; simpl; reflexivity. 
Qed.

Theorem correct_bs_union_lift (S : Type) (sgS: A_sg S) (c : cas_constant):  
   bs_union_lift (A2C_sg S sgS) c
   =
   A2C_bs _ (A_bs_union_lift S sgS c). 
Proof. unfold bs_union_lift, bs_union_lift, A2C_bs, A2C_sg. destruct sgS. simpl.
       rewrite correct_eqv_set.              
       rewrite correct_eqv_add_constant. 
       rewrite bop_union_certs_correct.
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id.       
       rewrite correct_sg_lift_certs. 

       (*
       Check correct_bs_certs_union_lift_aux.              
       Check correct_bs_certs_add_one.       


       rewrite correct_id_ann_certs_union_lift.

      bs_certs_union_lift (A2C_eqv S A_sg_eqv)
        (P2C_sg S (A_eqv_eq S A_sg_eqv) A_sg_bop A_sg_proofs) c;
       
      P2C_bs (with_constant (finite_set S))
        (brel_sum brel_constant (brel_set (A_eqv_eq S A_sg_eqv)))
        (bop_add_ann (bop_union (A_eqv_eq S A_sg_eqv)) c)
        (bop_add_id (bop_lift (A_eqv_eq S A_sg_eqv) A_sg_bop) c)
        (bs_proofs_union_lift S (A_eqv_witness S A_sg_eqv) A_sg_bop A_sg_eqv
           A_sg_proofs c);

correct_bs_certs_union_lift_aux
     : ∀ (S : Type) (bS : binary_op S) (eqvS : A_eqv S) 
         (sgP : sg_proofs S (A_eqv_eq S eqvS) bS),
         P2C_bs (finite_set S) (brel_set (A_eqv_eq S eqvS))
           (bop_union (A_eqv_eq S eqvS)) (bop_lift (A_eqv_eq S eqvS) bS)
           (bs_proofs_union_lift_aux S bS eqvS sgP) =
         bs_certs_union_lift_aux (P2C_sg S (A_eqv_eq S eqvS) bS sgP)

correct_bs_certs_add_one
     : ∀ (S : Type) (c : cas_constant) (rS : brel S) 
         (eqvS : eqv_proofs S rS) (plusS timesS : binary_op S) 
         (sgS : sg_proofs S rS plusS) (bsS : bs_proofs S rS plusS timesS),
         P2C_bs (with_constant S) (brel_sum brel_constant rS)
           (bop_add_ann plusS c) (bop_add_id timesS c)
           (bs_proofs_add_one S rS c plusS timesS eqvS sgS bsS) =
         bs_certs_add_one c (P2C_sg S rS plusS sgS)
           (P2C_bs S rS plusS timesS bsS)
      

       reflexivity.
Qed. 
        *)
Admitted.        

(* 
Theorem correct_bs_union_lift : ∀ (S : Type) (sgS: A_msg S), 
   bs_CI_union_lift S (A2C_msg S sgS) 
   =
   A2C_bs_CI (finite_set S) (A_bs_CI_union_lift S sgS). 
Proof. intros S sgS. 
       unfold bs_CI_union_lift, A_bs_CI_union_lift, A2C_bs_CI, A2C_msg. destruct sgS. simpl. 
       rewrite <- bop_union_certs_correct.
       rewrite correct_msg_lift_certs. 
       rewrite correct_bs_certs_union_lift.
       rewrite correct_eqv_set.
       rewrite <- correct_id_ann_certs_union_lift.
       reflexivity.
Qed. 

*) 
End Verify. 










