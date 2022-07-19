Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.cast_up. 

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

(* strict absorption *)
Lemma bops_union_lift_not_left_strictly_absorptive : 
        bops_not_left_strictly_absorptive (finite_set S) 
        (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. 
      exists (nil, nil).
      compute.
      right; auto.
Qed.


Lemma bops_union_lift_not_right_strictly_absorptive : 
        bops_not_right_strictly_absorptive (finite_set S) 
        (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. 
      exists (nil, nil).
      compute.
      right; auto.
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



Lemma bops_lift_union_id_equals_ann_decide 
      (id_d : bop_exists_id_decidable S r bS)
      (fin_d : carrier_is_finite_decidable S r):
  exists_id_ann_decidable (finite_set S) (brel_set r) (bop_lift r bS) (bop_union r).
Proof. destruct id_d as [idP | nidP]; destruct fin_d as [finP | nfinP].
       + assert (A : bops_exists_id_ann_not_equal (finite_set S) (brel_set r) (bop_lift r bS) (bop_union r)).
            assert (ann  := bop_union_enum_is_ann S r refS symS tranS finP). 
            destruct idP as [id P]. destruct finP as [h Q]. simpl in ann. 
            exists (id :: nil, h tt). split. split. 
            apply bop_lift_is_id; auto. 
            exact ann. 
            case_eq(brel_set r (id :: nil) (h tt)); intro F; auto.
            apply brel_set_elim_prop in F; auto.  destruct F as [F1 F2]. 
            assert (G := F2 (f id) (Q (f id))).
            compute in G.
            destruct (ntS id) as [K J]. rewrite J in G. 
            discriminate G. 
         exact (Id_Ann_Proof_Not_Equal _ _ _ _ A). 
       + exact (Id_Ann_Proof_Id_None _ _ _ _ 
                  (bop_lift_exists_id S r bS refS tranS symS bcong idP, 
                   bop_union_not_exists_ann S r refS symS tranS nfinP)).               
       + exact (Id_Ann_Proof_None_Ann _ _ _ _ 
                  (bop_lift_not_exists_id S r bS refS tranS symS wS nidP, 
                   bop_union_exists_ann S r refS symS tranS finP)).               
       + exact (Id_Ann_Proof_None _ _ _ _ 
                  (bop_lift_not_exists_id S r bS refS tranS symS wS nidP, 
                   bop_union_not_exists_ann S r refS symS tranS nfinP)).               
Defined.  



End Theory. 

Section ACAS.

Section Proofs.   

Variables (S : Type)
          (eqvS : A_eqv S)
          (bS : binary_op S)
          (sgS : sg_proofs S (A_eqv_eq _ eqvS) bS).

Definition id_ann_proofs_union_lift 
      (id_d : bop_exists_id_decidable S (A_eqv_eq _ eqvS) bS)
      (fin_d : carrier_is_finite_decidable S (A_eqv_eq _ eqvS)) :
  id_ann_proofs
            (finite_set S)
            (brel_set (A_eqv_eq _ eqvS))
            (bop_union (A_eqv_eq _ eqvS))
            (bop_lift (A_eqv_eq _ eqvS) bS) :=
let eq      := A_eqv_eq _ eqvS in
let f       := A_eqv_new _ eqvS in
let wS      := A_eqv_witness _ eqvS in
let ntS     := A_eqv_not_trivial _ eqvS in  
let eqvP    := A_eqv_proofs _ eqvS in  
let refS    := A_eqv_reflexive _ _ eqvP in
let symS    := A_eqv_symmetric _ _ eqvP in
let trnS    := A_eqv_transitive _ _ eqvP in
let bcong   := A_sg_congruence _ _ _ sgS in 
{|
  A_id_ann_plus_times_d := Id_Ann_Proof_Equal _ _ _ _ (bops_union_lift_id_equals_ann S eq bS refS symS trnS)
; A_id_ann_times_plus_d := bops_lift_union_id_equals_ann_decide S eq wS f ntS bS refS symS trnS bcong id_d fin_d 
|}. 



Definition bs_proofs_union_lift : 
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



Definition bops_lift_union_id_equals_ann_certify 
      (id_d  : @check_exists_id S)
      (fin_d : @check_is_finite S): @exists_id_ann_certificate (finite_set S) := 
match id_d with
| Certify_Exists_Id id =>
  match fin_d with
  | Certify_Is_Finite h  => Id_Ann_Cert_Not_Equal (id :: nil, h tt)
  | _                    => Id_Ann_Cert_Id_None (id :: nil) 
  end 
| _ =>
  match fin_d with
  | Certify_Is_Finite h  => Id_Ann_Cert_None_Ann (h tt)    
  | _                    => Id_Ann_Cert_None
  end 
end .


End Proofs.   

Section Combinators.



Definition A_bs_union_lift (S : Type) (sgS : A_sg S) : A_bs (finite_set S) := 
let eqvS  := A_sg_eqv S sgS in
let rS    := A_eqv_eq S eqvS in   
let bS    := A_sg_bop S sgS in
let eqvP := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
{| 
     A_bs_eqv           := A_eqv_set S eqvS
   ; A_bs_plus          := bop_union rS
   ; A_bs_times         := bop_lift rS bS
   ; A_bs_id_ann_proofs := id_ann_proofs_union_lift S eqvS bS (A_sg_proofs S sgS) (A_sg_exists_id_d S sgS) (A_eqv_finite_d S eqvS)
   ; A_bs_plus_proofs   := A_sg_proofs_from_sg_CI_proofs
                                (finite_set S)
                                (brel_set rS)
                                (bop_union rS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                                (brel_set_not_trivial S rS s)
                                (eqv_proofs_set S  rS eqvP) 
                                (sg_CI_proofs_union eqvS)
   ; A_bs_times_proofs  := sg_lift_proofs S rS bS eqvP s f Pf (A_eqv_exactly_two_d _ eqvS) (A_sg_proofs S sgS)
   ; A_bs_proofs        := bs_proofs_union_lift S eqvS bS (A_sg_proofs S sgS)
   ; A_bs_ast           := Ast_bs_union_lift (A_sg_ast S sgS)
|}.

End Combinators.   

End ACAS.

Section AMCAS.

Open Scope string_scope.

Definition A_mcas_bs_union_lift (S : Type) (A : A_sg_mcas S) : A_bs_mcas (finite_set S) :=
match A_sg_mcas_cast_up _ A with
| A_MCAS_sg _ B         => A_bs_classify _ (A_BS_bs _ (A_bs_union_lift _ B))
| A_MCAS_sg_Error _ sl  => A_BS_Error _ sl
| _                     => A_BS_Error _ ("Internal Error : mcas_bs_union_lift_with_one" :: nil)
end.

End AMCAS.




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

Definition bs_certs_union_lift {S : Type} (sgS : @sg_certificates S) : @bs_certificates (finite_set S) := 
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



Definition id_ann_certs_union_lift {S : Type} 
      (id_d : @check_exists_id S)
      (fin_d : @check_is_finite S) : @id_ann_certificates (finite_set S) := 
{|
  id_ann_plus_times_d := Id_Ann_Cert_Equal nil 
; id_ann_times_plus_d := bops_lift_union_id_equals_ann_certify S id_d fin_d 
|}. 


End Proofs.   

Section Combinators.




Definition bs_union_lift {S : Type} (sgS : @sg S) : @bs (finite_set S) := 
let eqvS  := sg_eqv sgS in
let rS    := eqv_eq eqvS in   
let bS    := sg_bop sgS in
let s     := eqv_witness eqvS in
let f     := eqv_new eqvS in
{| 
     bs_eqv           := eqv_set eqvS
   ; bs_plus          := bop_union rS
   ; bs_times         := bop_lift rS bS
   ; bs_id_ann_certs  := id_ann_certs_union_lift (sg_exists_id_d sgS) (eqv_finite_d eqvS)
   ; bs_plus_certs    := sg_certs_from_sg_CI_certs
                                (finite_set S)
                                (brel_set rS)
                                (bop_union rS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                                (sg_CI_certs_union eqvS)
   ; bs_times_certs  := sg_lift_certs S rS s f  (eqv_exactly_two_d eqvS) bS (sg_certs sgS)
   ; bs_certs        := bs_certs_union_lift (sg_certs sgS)
   ; bs_ast          := Ast_bs_union_lift (sg_ast sgS)
|}.

End Combinators.   

End CAS.

Section AMCAS.

Open Scope string_scope.

Definition mcas_bs_union_lift  {S : Type} (A : @sg_mcas S) : @bs_mcas (finite_set S) :=
match sg_mcas_cast_up _ A with
| MCAS_sg B         => bs_classify (BS_bs (bs_union_lift B))
| MCAS_sg_Error sl  => BS_Error sl
| _                 => BS_Error ("Internal Error : mcas_bs_union_lift" :: nil)
end.

End AMCAS.


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
  (S : Type) (bS : binary_op S) (eqvS : A_eqv S) (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) : 
  P2C_bs _ _ _ _ (bs_proofs_union_lift S eqvS bS sgP)
  = 
  bs_certs_union_lift (P2C_sg S (A_eqv_eq S eqvS) bS sgP).
Proof. destruct sgP. unfold bs_proofs_union_lift, bs_certs_union_lift, P2C_sg, P2C_bs; simpl.
       destruct A_sg_is_left_d as [L | [[a b] NL]]; destruct A_sg_is_right_d as [R | [[c d] NR]]; simpl; reflexivity. 
Qed.

Lemma correct_id_ann_certs_union_lift
      (S : Type)
      (eqvS : A_eqv S)
      (bS : binary_op S)
      (id_d : bop_exists_id_decidable S (A_eqv_eq S eqvS) bS)
      (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) :
      id_ann_certs_union_lift (p2c_exists_id_check _ _ _ id_d) (p2c_is_finite_check _ _ (A_eqv_finite_d _ eqvS)) 
      = 
      P2C_id_ann (finite_set S) (brel_set (A_eqv_eq _ eqvS)) (bop_union (A_eqv_eq _ eqvS)) (bop_lift (A_eqv_eq _ eqvS) bS)
                 (id_ann_proofs_union_lift S eqvS bS sgP id_d (A_eqv_finite_d _ eqvS)).
Proof.   unfold id_ann_certs_union_lift, id_ann_proofs_union_lift, P2C_id_ann, p2c_is_finite_check, p2c_exists_id_check; simpl.
         destruct id_d as [[id idP] | nidP]; destruct (A_eqv_finite_d _ eqvS) as [[h finP] | nfinP]; simpl; 
         try reflexivity. 
Qed.


Theorem correct_bs_union_lift (S : Type) (sgS: A_sg S):  
   bs_union_lift (A2C_sg S sgS)
   =
   A2C_bs _ (A_bs_union_lift S sgS). 
Proof. unfold bs_union_lift, bs_union_lift, A2C_bs, A2C_sg. destruct sgS. simpl.
       rewrite correct_eqv_set.              
       rewrite correct_sg_lift_certs.
       rewrite <- correct_bs_certs_union_lift.              
       rewrite <- correct_id_ann_certs_union_lift.
       rewrite correct_bop_union_certs.
       unfold sg_certs_from_sg_CI_certs, A_sg_proofs_from_sg_CI_proofs.
       rewrite <- correct_sg_certs_from_sg_C_certs.               
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       reflexivity.
Qed.


Theorem correct_mcas_bs_union_lift (S : Type) (sgS : A_sg_mcas S) : 
         mcas_bs_union_lift (A2C_mcas_sg S sgS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_union_lift _ sgS).
Proof. unfold mcas_bs_union_lift, A_mcas_bs_union_lift. 
       rewrite correct_sg_mcas_cast_up.       
       destruct (A_sg_cas_up_is_error_or_sg S sgS) as [[l1 A] | [s1 A]]. 
       + rewrite A; simpl. reflexivity. 
       + rewrite A; simpl. rewrite correct_bs_union_lift. 
         apply correct_bs_classify_bs. 
Qed. 


End Verify. 










