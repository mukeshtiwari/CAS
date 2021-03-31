Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.bs.add_ann_add_id.
Require Import CAS.coq.bs.add_id_add_ann. 


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

Lemma bops_union_lift_id_equals_ann : bops_id_equals_ann (finite_set S) (brel_set r) (bop_union r) (bop_lift r bS).
Proof. exists nil; split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_lift_nil_is_ann; auto.       
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

End Theory. 

Section ACAS.

(* before mm 
Definition bs_proofs_union_lift : 
  ∀ (S : Type) (s : S) (rS : brel S) (bS : binary_op S) (f : S -> S) (ntS : brel_not_trivial S rS f) (fin_d : carrier_is_finite_decidable S rS), 
     eqv_proofs S rS -> msg_proofs S rS bS -> 
        bs_proofs (finite_set S) (brel_set rS) (bop_union rS) (bop_lift rS bS)
  := λ S s rS bS f ntS fin_d eqvS sgS,
let refS := A_eqv_reflexive S rS eqvS  in
let symS := A_eqv_symmetric S rS eqvS  in
let trnS := A_eqv_transitive S rS eqvS in
let cnbS := A_msg_congruence S rS bS sgS in
let ilD  := A_msg_is_left_d S rS bS sgS  in
let irD  := A_msg_is_right_d S rS bS sgS in
let idD  := A_msg_exists_id_d S rS bS sgS in 
{|
  A_bs_left_distributive_d      := inl (bop_union_lift_left_distributive S rS bS refS symS trnS cnbS)
; A_bs_right_distributive_d     := inl (bop_union_lift_right_distributive S rS bS refS symS trnS cnbS)
; A_bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_decide S rS bS refS symS trnS cnbS irD 
; A_bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_decide S rS bS refS symS trnS cnbS irD
; A_bs_plus_id_is_times_ann_d   := inl (bops_union_lift_id_equals_ann S rS bS refS symS trnS)
; A_bs_times_id_is_plus_ann_d   := inr (bops_union_lift_not_ann_equals_id S rS s f ntS bS refS symS trnS cnbS idD fin_d)
|}. 
 *)

Definition bs_proofs_union_lift : 
  ∀ (S : Type) (s : S) (rS : brel S) (bS : binary_op S) (f : S -> S) (ntS : brel_not_trivial S rS f) (fin_d : carrier_is_finite_decidable S rS), 
    eqv_proofs S rS ->
    msg_proofs S rS bS -> 
        bs_proofs (finite_set S) (brel_set rS) (bop_union rS) (bop_lift rS bS)
  := λ S s rS bS f ntS fin_d eqvS sgS,
let refS := A_eqv_reflexive S rS eqvS  in
let symS := A_eqv_symmetric S rS eqvS  in
let trnS := A_eqv_transitive S rS eqvS in
let cnbS := A_msg_congruence S rS bS sgS in
let ilD  := A_msg_is_left_d S rS bS sgS in  
let irD  := A_msg_is_right_d S rS bS sgS in  
{|
  A_bs_left_distributive_d      := inl (bop_union_lift_left_distributive S rS bS refS symS trnS cnbS)
; A_bs_right_distributive_d     := inl (bop_union_lift_right_distributive S rS bS refS symS trnS cnbS)
; A_bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_decide S rS bS refS symS trnS cnbS irD 
; A_bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_decide S rS bS refS symS trnS cnbS irD
|}.



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
   ; A_bs_CI_plus_proofs   := sg_CI_proofs_union S eqvS
   ; A_bs_CI_times_proofs  := msg_lift_proofs S rS bS peqvS s f Pf (A_msg_proofs S sgS)
   ; A_bs_CI_proofs        := bs_proofs_union_lift S s rS bS f Pf (A_eqv_finite_d S eqvS) peqvS (A_msg_proofs S sgS)
   ; A_bs_CI_ast           := Ast_bs_union_lift (A_msg_ast S sgS)
|}.

  
End ACAS.

Section CAS.


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



Definition bs_certs_union_lift : ∀ {S : Type}, @msg_certificates S -> @bs_certificates (finite_set S) 
  := λ {S} sgS,
let ilD  := msg_is_left_d sgS in  
let irD  := msg_is_right_d sgS in  
{|
  bs_left_distributive_d      := Certify_Left_Distributive 
; bs_right_distributive_d     := Certify_Right_Distributive 
; bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_check ilD 
; bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_check irD 
; bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_check ilD 
; bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_check irD
|}.

Definition id_ann_certs_union_lift : ∀ {S : Type}, @check_exists_id S -> @check_is_finite S -> @id_ann_certificates (finite_set S)
:= λ {S} exists_id_d finite_d,
{|
      id_ann_exists_plus_id_d        := Certify_Exists_Id nil 
    ; id_ann_exists_plus_ann_d       := check_union_exists_ann finite_d
    ; id_ann_exists_times_id_d       := bop_lift_exists_id_check exists_id_d  
    ; id_ann_exists_times_ann_d      := Certify_Exists_Ann nil 
    ; id_ann_plus_id_is_times_ann_d  := Certify_Plus_Id_Equals_Times_Ann nil
    ; id_ann_times_id_is_plus_ann_d  := Certify_Not_Times_Id_Equals_Plus_Ann 
|}.


Definition bs_CI_union_lift : ∀ (S : Type),  @msg S -> @bs_CI (finite_set S)
:= λ S sgS,
let eqvS  := msg_eq sgS in
let rS    := eqv_eq eqvS in   
let bS    := msg_bop sgS in
let s     := eqv_witness eqvS in
let f     := eqv_new eqvS in
{| 
     bs_CI_eqv          := eqv_set eqvS
   ; bs_CI_plus         := bop_union rS
   ; bs_CI_times        := bop_lift rS bS
   ; bs_CI_id_ann_certs := id_ann_certs_union_lift (msg_exists_id_d sgS) (eqv_finite_d eqvS)             
   ; bs_CI_plus_certs   := sg_CI_certs_union eqvS
   ; bs_CI_times_certs  := msg_lift_certs S rS s f bS (msg_certs sgS)
   ; bs_CI_certs        := bs_certs_union_lift (msg_certs sgS)
   ; bs_CI_ast          := Ast_bs_union_lift (msg_ast sgS)
|}.




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


Lemma correct_bs_certs_union_lift 
  (S : Type) (s : S) (eq : brel S) (f : S -> S) (ntS : brel_not_trivial S eq f) (fin_d : carrier_is_finite_decidable S eq) 
  (bS : binary_op S)
  (eqvP : eqv_proofs S eq) 
  (sgP : msg_proofs S eq bS) : 
  P2C_bs (finite_set S) (brel_set eq) (bop_union eq) (bop_lift eq bS) (bs_proofs_union_lift S s eq bS f ntS fin_d eqvP sgP)
  = 
  bs_certs_union_lift (P2C_msg S eq bS sgP).
Proof. destruct sgP. unfold bs_proofs_union_lift, bs_certs_union_lift, P2C_msg, P2C_bs; simpl.
       destruct A_msg_is_left_d as [L | [[a b] NL]]; destruct A_msg_is_right_d as [R | [[c d] NR]]; simpl; reflexivity. 
Qed.


Lemma correct_id_ann_certs_union_lift 
      (S : Type) 
      (eqv : A_eqv S)
      (bS : binary_op S) 
      (id_d : bop_exists_id_decidable S (A_eqv_eq S eqv) bS)
      (msgP : msg_proofs S (A_eqv_eq S eqv) bS): 
    id_ann_certs_union_lift (p2c_exists_id_check S (A_eqv_eq S eqv) bS id_d)
                            (p2c_is_finite_check S (A_eqv_eq S eqv) (A_eqv_finite_d S eqv))
    = 
    P2C_id_ann (finite_set S) 
               (brel_set (A_eqv_eq S eqv))
               (bop_union (A_eqv_eq S eqv))
               (bop_lift (A_eqv_eq S eqv) bS)
               (id_ann_proofs_union_lift S (A_eqv_witness S eqv) (A_eqv_eq S eqv) bS 
                                         (A_eqv_new S eqv)
                                         (A_eqv_not_trivial S eqv)
                                         (A_eqv_finite_d S eqv)
                                         id_d
                                         (A_eqv_proofs S eqv)
                                         msgP). 
Proof. unfold id_ann_certs_union_lift, id_ann_proofs_union_lift, P2C_id_ann, p2c_exists_id_check, p2c_is_finite_check. 
       destruct id_d as [ [id Pid] | Nid];
       destruct eqv; destruct msgP;
       destruct A_eqv_finite_d as [[f Pf] | NF]; simpl in *; simpl; try reflexivity. 
Qed. 

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


End Verify. 










