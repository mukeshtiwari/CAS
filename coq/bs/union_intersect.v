Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.bs.add_ann_add_id. 
Require Import CAS.coq.bs.add_id_add_ann. 
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.theory.facts.

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

Lemma bops_union_intersect_id_equals_ann : 
  bops_id_equals_ann (finite_set S) (brel_set r) (bop_union r) (bop_intersect r).
Proof. exists nil. split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_intersect_nil_is_ann; auto. 
Defined.

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



Lemma bops_intersect_union_id_equals_ann : bops_id_equals_ann  (finite_set S) (brel_set r) (bop_union r) (bop_intersect r).
Proof. exists nil; split. apply bop_union_nil_is_id; auto. apply bop_intersect_nil_is_ann; auto. Defined. 

Lemma bops_union__intersect_id_equals_ann_decidable (fin_d : carrier_is_finite_decidable S r) :
  bops_id_equals_ann_decidable (finite_set S) (brel_set r) (bop_intersect r) (bop_union r).
Proof. unfold bops_id_equals_ann_decidable. destruct fin_d as [fS | nfs]. 
       left. unfold bops_id_equals_ann.
             exists ((projT1 fS) tt). split.
             apply bop_intersect_enum_is_id; auto. 
             apply bop_union_enum_is_ann; auto. 
       right. unfold bops_not_id_equals_ann. intro X.
              left. apply (bop_intersect_not_exists_id _ r wS f ntS refS symS tranS nfs X); auto.
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

(*

Problem : I can't always build this ... 

Definition bounded_proofs_union_intersect (S: Type) := 
{|
  A_bounded_plus_id_is_times_ann := bops_id_equals_ann S eq plus times 
; A_bounded_times_id_is_plus_ann := bops_id_equals_ann S eq times plus 
|}.
 *)

Definition id_ann_proofs_union_intersect (S : Type) (eqv: A_eqv S) := 
let eqvP := A_eqv_proofs S eqv in
let symS := A_eqv_symmetric _ _ eqvP in
let refS := A_eqv_reflexive _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in
let eqS  := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
let f    := A_eqv_new S eqv in
let ntS  := A_eqv_not_trivial S eqv in
let fin_d := A_eqv_finite_d S eqv in 
{|
   A_id_ann_exists_plus_id_d       := inl _ (bop_union_exists_id S eqS refS symS trnS)
 ; A_id_ann_exists_plus_ann_d      := bop_union_exists_ann_decide S eqS refS symS trnS fin_d
 ; A_id_ann_exists_times_id_d      := bop_intersect_exists_id_decide S eqS s f ntS refS symS trnS fin_d
 ; A_id_ann_exists_times_ann_d     := inl _ (bop_intersect_exists_ann S eqS refS symS trnS)
 ; A_id_ann_plus_id_is_times_ann_d := inl _ (bops_intersect_union_id_equals_ann S eqS refS symS trnS)
 ; A_id_ann_times_id_is_plus_ann_d := bops_union__intersect_id_equals_ann_decidable S eqS s f ntS refS symS trnS fin_d
|}.

Definition A_distributive_prelattice_union_intersect : ∀ (S : Type),  A_eqv S -> A_distributive_prelattice (finite_set S)
  := λ S eqv,
  let eq  := A_eqv_eq S eqv in
  let s   := A_eqv_witness S eqv in
  let f   := A_eqv_new S eqv in
  let ntS := A_eqv_not_trivial S eqv in
  let eqP := A_eqv_proofs S eqv in 
{|
  A_distributive_prelattice_eqv           := A_eqv_set S eqv
; A_distributive_prelattice_join          := bop_union eq
; A_distributive_prelattice_meet          := bop_intersect eq
; A_distributive_prelattice_id_ann_proofs := id_ann_proofs_union_intersect S eqv                                                          
; A_distributive_prelattice_join_proofs   := sg_CI_proofs_union S eqv
; A_distributive_prelattice_meet_proofs   := sg_CI_proofs_intersect S eqv
; A_distributive_prelattice_proofs        := distributive_lattice_proofs_union_intersect S eq eqP
; A_distributive_prelattice_ast           := Ast_union_intersect (A_eqv_ast S eqv) 
|}.


End ACAS.

Section CAS.

Definition distributive_lattice_certs_union_intersect : ∀ (S : Type), @distributive_lattice_certificates (finite_set S)
  := λ S,    
  {| 
     distributive_lattice_distributive      := Assert_Left_Distributive 
   ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
   ; distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
  |}.

Definition  check_times_id_is_plus_ann_union_intersect {S : Type} (d : @check_is_finite S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Times_Id_Equals_Plus_Ann  (fS tt)
     | Certify_Is_Not_Finite => Certify_Not_Times_Id_Equals_Plus_Ann 
     end.

Definition id_ann_certs_union_intersect {S : Type} (eqv: @eqv S) := 
let fin_d := eqv_finite_d eqv in 
{|
   id_ann_exists_plus_id_d       := Certify_Exists_Id nil 
 ; id_ann_exists_plus_ann_d      := check_union_exists_ann fin_d
 ; id_ann_exists_times_id_d      := check_intersect_exists_id fin_d
 ; id_ann_exists_times_ann_d     := Certify_Exists_Ann nil
 ; id_ann_plus_id_is_times_ann_d := Certify_Plus_Id_Equals_Times_Ann nil 
 ; id_ann_times_id_is_plus_ann_d := check_times_id_is_plus_ann_union_intersect fin_d
|}.


Definition distributive_prelattice_union_intersect : ∀ {S : Type},  @eqv S -> @distributive_prelattice (finite_set S)
  := λ {S} eqv,
  let eq  := eqv_eq eqv in
  let s   := eqv_witness eqv in
  let f   := eqv_new eqv in
{|
  distributive_prelattice_eqv          := eqv_set eqv  
; distributive_prelattice_join         := bop_union eq
; distributive_prelattice_meet         := bop_intersect eq
; distributive_prelattice_id_ann_certs := id_ann_certs_union_intersect eqv
; distributive_prelattice_join_certs   := sg_CI_certs_union eqv
; distributive_prelattice_meet_certs   := sg_CI_certs_intersect eqv
; distributive_prelattice_certs        := distributive_lattice_certs_union_intersect S
; distributive_prelattice_ast          := Ast_union_intersect (eqv_ast eqv) 
|}.
  

End CAS.

Section Verify.

Lemma correct_proofs_union_intersect (S : Type) (eqv : A_eqv S) :
  distributive_lattice_certs_union_intersect S
  =                                            
  P2C_distributive_lattice (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv)) (bop_intersect (A_eqv_eq S eqv))
                           (distributive_lattice_proofs_union_intersect S (A_eqv_eq S eqv) (A_eqv_proofs S eqv)). 
Proof. compute. reflexivity. Qed.


Lemma correct_id_ann_proofs_union_intersect (S : Type) (eqv : A_eqv S) :
  id_ann_certs_union_intersect (A2C_eqv S eqv)
  = 
  P2C_id_ann (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv))
                                            (bop_intersect (A_eqv_eq S eqv)) (id_ann_proofs_union_intersect S eqv). 
Proof. destruct eqv; unfold id_ann_certs_union_intersect, id_ann_proofs_union_intersect, P2C_id_ann, A2C_eqv; simpl. 
       destruct A_eqv_finite_d as [[f fS] | nfS]; simpl; reflexivity. 
Qed. 
Theorem correct_distributive_prelattice_union_intersect : ∀ (S : Type) (eqv: A_eqv S), 
    distributive_prelattice_union_intersect (A2C_eqv S eqv) 
    =
    A2C_distributive_prelattice _ (A_distributive_prelattice_union_intersect S eqv). 
Proof. intros S eqv.
       unfold distributive_prelattice_union_intersect, A_distributive_prelattice_union_intersect, A2C_distributive_prelattice; simpl.
       rewrite correct_eqv_set.
       rewrite bop_union_certs_correct.
       rewrite bop_intersect_certs_correct.
       rewrite <- correct_proofs_union_intersect. 
       rewrite <- correct_id_ann_proofs_union_intersect.
       reflexivity.
Qed. 
  
 
End Verify.   

