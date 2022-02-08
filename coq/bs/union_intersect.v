Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.sum. 
Require Import CAS.coq.eqv.add_constant. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 
Require Import CAS.coq.bs.add_one.
Require Import CAS.coq.bs.add_zero. 

Section Theory.

  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.


Lemma bops_union_intersect_left_distributive : 
        bop_left_distributive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. intros s t u. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H;
          auto. destruct H as [ L R ]. 
          apply in_set_bop_union_elim in R; auto.
          destruct R as [R | R].
             left. apply in_set_bop_intersect_intro; auto. 
             right. apply in_set_bop_intersect_intro; auto. 
       apply in_set_bop_intersect_intro; auto. 
       apply in_set_bop_union_elim in H; auto. 
       destruct H as [H | H]; split; apply in_set_bop_intersect_elim in H; auto. 
           destruct H as [ L _ ]; auto.            
           destruct H as [ L R ]. apply in_set_bop_union_intro; auto.
           destruct H as [ L _ ]; auto.                       
           destruct H as [ L R ]. apply in_set_bop_union_intro; auto.
Qed. 

Lemma bops_union_intersect_right_distributive : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bop_intersect_commutative; auto. 
       apply bops_union_intersect_left_distributive; auto. 
Defined. 


Lemma bops_union_intersect_left_left_absorptive : 
        bops_left_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_intersect_elim in H; auto. destruct H as [L R]; auto.            
Qed. 


Lemma bops_union_intersect_left_right_absorptive : 
        bops_left_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r) . 
Proof. apply bops_left_left_absorptive_implies_left_right; auto. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_intersect_commutative; auto. 
       apply bops_union_intersect_left_left_absorptive; auto. 
Qed. 


Lemma bops_union_intersect_right_left_absorptive : 
        bops_right_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bop_intersect_commutative; auto. 
       apply bops_union_intersect_left_right_absorptive; auto. 
Qed. 


Lemma bops_union_intersect_right_right_absorptive : 
       bops_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_intersect_commutative; auto. 
       apply bops_union_intersect_right_left_absorptive; auto. 
Qed.

(*
Lemma bops_union_intersect_id_equals_ann : 
  bops_id_equals_ann (finite_set S) (brel_set r) (bop_union r) (bop_intersect r).
Proof. exists nil. split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_intersect_nil_is_ann; auto. 
Defined.
*) 
 (* intersect union theorems *)

Lemma bops_intersect_union_left_distributive : 
        bop_left_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t u. 
       apply brel_set_intro_prop; auto. split; intros a H.        
          apply in_set_bop_intersect_intro; auto. split; apply in_set_bop_union_intro; auto. 
             apply in_set_bop_union_elim in H; auto. destruct H as [H | H ]. 
                left. assumption. 
                apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
                right. assumption. 
             apply in_set_bop_union_elim in H; auto. destruct H as [H | H ]. 
                left. assumption. 
                apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
                right. assumption. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
          apply in_set_bop_union_elim in L; apply in_set_bop_union_elim in R; auto. 
          destruct L as [L |L]; destruct R as [R | R]. 
             left. assumption. 
             left. assumption. 
             left. assumption. 
             right. apply in_set_bop_intersect_intro; auto. 
Qed. 

Lemma bops_intersect_union_right_distributive : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence; auto. 
       apply bop_intersect_commutative; auto. 
       apply bop_union_commutative; auto. 
       apply bops_intersect_union_left_distributive; auto. 
Qed. 

Lemma bops_intersect_union_left_left_absorptive : 
        bops_left_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_intersect_intro; auto. split; auto. 
             apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]; auto. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive : 
        bops_left_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_left_left_absorptive_implies_left_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bops_intersect_union_left_left_absorptive; auto. 
Qed. 


Lemma bops_intersect_union_right_left_absorptive : 
        bops_right_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence; auto. 
       apply bop_intersect_commutative; auto. 
       apply bop_union_commutative; auto. 
       apply bops_intersect_union_left_right_absorptive; auto. 
Qed. 

Lemma bops_intersect_union_right_right_absorptive : 
        bops_right_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bops_intersect_union_right_left_absorptive; auto. 
Qed. 

Lemma bops_intersect_union_id_equals_ann : bops_exists_id_ann_equal  (finite_set S) (brel_set r) (bop_union r) (bop_intersect r).
Proof. exists nil; split.
       apply bop_union_nil_is_id; auto.
       apply bop_intersect_nil_is_ann; auto.
Defined. 

End Theory.

Section ACAS.

Definition distributive_lattice_proofs_union_intersect : 
  ∀ (S : Type) (eq : brel S) ,
     eqv_proofs S eq -> 
     distributive_lattice_proofs
       (finite_set S)
       (brel_set eq)
       (bop_union eq)
       (bop_intersect eq)
:= λ S eq eqvS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in
let tranS := A_eqv_transitive _ _ eqvS in      
{|
  A_distributive_lattice_absorptive        := bops_union_intersect_left_left_absorptive S eq refS symS tranS 
; A_distributive_lattice_absorptive_dual   := bops_intersect_union_left_left_absorptive S eq refS symS tranS 
; A_distributive_lattice_distributive      := bops_union_intersect_left_distributive S eq refS symS tranS 
|}.

(* this should really be the result of a proofs combinator in add_one *) 
Definition distributive_lattice_proofs_union_intersect_with_one 
     (S : Type)
     (c : cas_constant)
     (eq : brel S) 
     (eqvS : eqv_proofs S eq) : 
     distributive_lattice_proofs
       (with_constant (finite_set S))
       (brel_sum brel_constant (brel_set eq))
       (bop_add_ann (bop_union eq) c) 
       (bop_add_id (bop_intersect eq) c) := 
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in
let tranS := A_eqv_transitive _ _ eqvS in
let U_I_LLA := bops_union_intersect_left_left_absorptive S eq refS symS tranS in
let U_I_RLA := bops_union_intersect_right_left_absorptive S eq refS symS tranS in
let I_U_LLA := bops_intersect_union_left_left_absorptive S eq refS symS tranS in 
{|
  A_distributive_lattice_absorptive        :=
    bops_add_one_left_left_absorptive
      _
      (brel_set eq)
      c
      (bop_union eq)
      (bop_intersect eq)    
      (brel_set_symmetric S eq) 
      (bop_union_idempotent S eq refS symS tranS) 
      U_I_LLA 
; A_distributive_lattice_absorptive_dual   :=
    bops_add_zero_left_left_absorptive  (* adding one is adding zero on the dual *) 
      _
      (brel_set eq)
      c
      (bop_intersect eq)      
      (bop_union eq)
      (brel_set_reflexive S eq refS symS)       
      I_U_LLA 
; A_distributive_lattice_distributive     :=
    bops_add_one_left_distributive
      _
      (brel_set eq)
      c
      (bop_union eq)
      (bop_intersect eq)
      (brel_set_reflexive S eq refS symS)       
      (brel_set_symmetric S eq) 
      (bop_union_idempotent S eq refS symS tranS) 
      U_I_LLA
      U_I_RLA       
      (bops_union_intersect_left_distributive S eq refS symS tranS) 
|}.

Definition bounded_proofs_union_intersect
           (S : Type)
           (eq : brel S)
           (eqvP : eqv_proofs S eq)
           (c : cas_constant) :
           dually_bounded_proofs
            (with_constant (finite_set S))
            (brel_sum brel_constant (brel_set eq)) 
            (bop_add_ann (bop_union eq) c)
            (bop_add_id (bop_intersect eq) c) :=
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let tranS := A_eqv_transitive _ _ eqvP in      
{|
  A_bounded_plus_id_is_times_ann :=
    bops_add_one_exists_id_ann_equal_left
       _
       (brel_set eq)
       c
       (bop_union eq)
       (bop_intersect eq)
       (brel_set_reflexive S eq refS symS) 
       (bops_intersect_union_id_equals_ann S eq refS symS tranS) 
; A_bounded_times_id_is_plus_ann :=
    bops_add_one_exists_id_ann_equal_right
       _
       (brel_set eq)
       c
       (bop_union eq)
       (bop_intersect eq)
       (brel_set_reflexive S eq refS symS) 
|}.


Definition A_bs_union_intersect (S : Type) (c : cas_constant) (eqv : A_eqv S) :
          A_distributive_lattice (with_constant (finite_set S)) := 
let eq         := A_eqv_eq S eqv in
let s          := A_eqv_witness S eqv in
let f          := A_eqv_new S eqv in
let ntS        := A_eqv_not_trivial S eqv in
let eqvP       := A_eqv_proofs S eqv in
let new_eqv    := A_eqv_set S eqv in
let union      := bop_union eq in
let intersect  := bop_intersect eq in 
let unionP     := sg_CI_proofs_union eqv in
let intersectP := sg_CI_proofs_intersect S eqv in 
{|
  A_distributive_lattice_eqv           := A_eqv_add_constant _ new_eqv c  
; A_distributive_lattice_join          := bop_add_ann union c 
; A_distributive_lattice_meet          := bop_add_id intersect c  
; A_distributive_lattice_id_ann_proofs := bounded_proofs_union_intersect S eq eqvP c 
; A_distributive_lattice_join_proofs   := sg_CI_proofs_add_ann _ _ c union nil (A_eqv_proofs _ new_eqv) unionP 
; A_distributive_lattice_meet_proofs   := sg_CI_proofs_add_id _ _ c intersect nil (A_eqv_proofs _ new_eqv) intersectP
; A_distributive_lattice_proofs        := distributive_lattice_proofs_union_intersect_with_one S c eq eqvP
; A_distributive_lattice_ast           := Ast_union_intersect (c, A_eqv_ast S eqv) 
|}.


End ACAS.

Section AMCAS.

Definition A_mcas_bs_union_intersect (S : Type) (c : cas_constant) (eqv : A_eqv S) :=
    A_BS_distributive_lattice _ (A_bs_union_intersect S c eqv).

End AMCAS.

    
Section CAS.

Definition distributive_lattice_certs_union_intersect (S : Type) : @distributive_lattice_certificates (finite_set S) := 
  {| 
     distributive_lattice_distributive      := Assert_Left_Distributive 
   ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
   ; distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
  |}.


Definition distributive_lattice_certs_union_intersect_with_one (S : Type) : @distributive_lattice_certificates (with_constant (finite_set S)) := 
  {| 
     distributive_lattice_distributive      := Assert_Left_Distributive 
   ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
   ; distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
  |}.


Definition bounded_certs_union_intersect
           (S : Type) (c : cas_constant) : 
           @dually_bounded_certificates (with_constant (finite_set S)) := 
{|
  bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal (inr nil) 
; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal (inl c) 
|}.


Definition bs_union_intersect {S : Type} (c : cas_constant) (eqv : @eqv S) :
  @distributive_lattice (with_constant (finite_set S)) := 
let eq  := eqv_eq eqv in
{|
  distributive_lattice_eqv          := eqv_add_constant (eqv_set eqv) c
; distributive_lattice_join         := bop_add_ann (bop_union eq) c 
; distributive_lattice_meet         := bop_add_id (bop_intersect eq) c 
; distributive_lattice_id_ann_certs := bounded_certs_union_intersect S c 
; distributive_lattice_join_certs   := sg_CI_certs_add_ann c (sg_CI_certs_union eqv)
; distributive_lattice_meet_certs   := sg_CI_certs_add_id c (sg_CI_certs_intersect eqv)
; distributive_lattice_certs        := distributive_lattice_certs_union_intersect_with_one S
; distributive_lattice_ast          := Ast_union_intersect (c, eqv_ast eqv) 
|}.
  

End CAS.

Section MCAS.

Definition mcas_bs_union_intersect (S : Type) (c : cas_constant) (eqv : @eqv S) :=
    BS_distributive_lattice (bs_union_intersect c eqv).

End MCAS.


Section Verify.

Lemma correct_proofs_union_intersect (S : Type) (eqv : A_eqv S) :
  distributive_lattice_certs_union_intersect S
  =                                            
  P2C_distributive_lattice (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv)) (bop_intersect (A_eqv_eq S eqv))
                           (distributive_lattice_proofs_union_intersect S (A_eqv_eq S eqv) (A_eqv_proofs S eqv)). 
Proof. compute. reflexivity. Qed.


 
Lemma correct_id_ann_proofs_union_intersect (S : Type) (c : cas_constant) (eq : brel S) (eqvP : eqv_proofs S eq) :
  bounded_certs_union_intersect _ c 
  = 
  P2C_dually_bounded
               (with_constant (finite_set S))
               (brel_sum brel_constant (brel_set eq)) 
               (bop_add_ann (bop_union eq) c)
               (bop_add_id (bop_intersect eq) c) 
               (bounded_proofs_union_intersect S eq eqvP c). 
Proof. unfold bounded_certs_union_intersect, bounded_proofs_union_intersect, P2C_dually_bounded.
       compute. reflexivity. 
Qed.

Lemma correct_certs_union_intersect 
  (S : Type)
  (c : cas_constant) 
  (eq : brel S) 
  (eqvP : eqv_proofs S eq) : 
  distributive_lattice_certs_union_intersect_with_one S 
  =                                   
  P2C_distributive_lattice
    (with_constant (finite_set S))
    (brel_sum brel_constant (brel_set eq))
    (bop_add_ann (bop_union eq) c)
    (bop_add_id (bop_intersect eq) c)
    (distributive_lattice_proofs_union_intersect_with_one S c eq eqvP).
Proof. unfold distributive_lattice_certs_union_intersect_with_one,
       distributive_lattice_proofs_union_intersect_with_one, P2C_distributive_lattice.
       simpl. reflexivity. 
Qed. 

Theorem correct_union_intersect (S : Type) (c : cas_constant) (eqv: A_eqv S) : 
    bs_union_intersect c (A2C_eqv S eqv)
    =
    A2C_distributive_lattice _ (A_bs_union_intersect S c eqv).
Proof. unfold bs_union_intersect, A_bs_union_intersect, A2C_distributive_lattice; simpl.
       rewrite correct_eqv_set.
       rewrite correct_eqv_add_constant.        
       rewrite bop_union_certs_correct.
       rewrite <- correct_sg_CI_certs_add_ann.        
       rewrite bop_intersect_certs_correct.
       rewrite <- correct_sg_CI_certs_add_id.
       destruct eqv. simpl. 
       rewrite <- correct_id_ann_proofs_union_intersect.       
       rewrite <- correct_certs_union_intersect.        
       reflexivity.
Qed. 

Theorem bop_mcas_union_intersect_correct (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
         mcas_bs_union_intersect _ c (A2C_eqv S eqvS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_union_intersect _ c eqvS). 
Proof. unfold mcas_bs_union_intersect, A_mcas_bs_union_intersect, A2C_mcas_bs. 
       rewrite correct_union_intersect. 
       reflexivity. 
Qed.  

 
End Verify.   

