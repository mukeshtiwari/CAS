Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
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


Definition A_distributive_lattice_union_intersect : ∀ (S : Type),  A_eqv S -> A_distributive_lattice (finite_set S)
  := λ S eqv,
  let eq  := A_eqv_eq S eqv in
  let s   := A_eqv_witness S eqv in
  let f   := A_eqv_new S eqv in
  let ntS := A_eqv_not_trivial S eqv in
  let eqP := A_eqv_proofs S eqv in 
{|
  A_distributive_lattice_eqv         := A_eqv_set S eqv
; A_distributive_lattice_join        := bop_union eq
; A_distributive_lattice_meet        := bop_intersect eq
; A_distributive_lattice_join_proofs := sg_CI_proofs_union S eq s f ntS eqP (A_eqv_finite_d S eqv)
; A_distributive_lattice_meet_proofs := sg_CI_proofs_intersect S eq s f ntS eqP (A_eqv_finite_d S eqv)
; A_distributive_lattice_proofs      := distributive_lattice_proofs_union_intersect S eq eqP
; A_distributive_lattice_join_ast    := Ast_bop_union (A_eqv_ast S eqv)
; A_distributive_lattice_meet_ast    := Ast_bop_intersect (A_eqv_ast S eqv)
; A_distributive_lattice_ast         := Ast_distributive_lattice_union_intersect (A_eqv_ast S eqv) 
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



Definition distributive_lattice_union_intersect : ∀ (S : Type),  @eqv S -> @distributive_lattice (finite_set S)
  := λ S eqv,
  let eq  := eqv_eq eqv in
  let s   := eqv_witness eqv in
  let f   := eqv_new eqv in
{|
  distributive_lattice_eqv         := eqv_set eqv  
; distributive_lattice_join        := bop_union eq
; distributive_lattice_meet        := bop_intersect eq
; distributive_lattice_join_certs  := sg_CI_certs_union s f (eqv_finite_d eqv)
; distributive_lattice_meet_certs  := sg_CI_certs_intersect s f (eqv_finite_d eqv)
; distributive_lattice_certs       := distributive_lattice_certs_union_intersect S
; distributive_lattice_join_ast    := Ast_bop_union (eqv_ast eqv)
; distributive_lattice_meet_ast    := Ast_bop_intersect (eqv_ast eqv)
; distributive_lattice_ast         := Ast_distributive_lattice_union_intersect (eqv_ast eqv) 
|}.
  

End CAS.

Section Verify.

Lemma correct_proofs_union_intersect (S : Type) (eqv : A_eqv S) :
  distributive_lattice_certs_union_intersect S
  =                                            
  P2C_distributive_lattice (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv)) (bop_intersect (A_eqv_eq S eqv))
                           (distributive_lattice_proofs_union_intersect S (A_eqv_eq S eqv) (A_eqv_proofs S eqv)). 
Proof. compute. reflexivity. Qed. 

Theorem correct_distributive_lattice_union_intersect : ∀ (S : Type) (eqv: A_eqv S), 
    distributive_lattice_union_intersect S (A2C_eqv S eqv) 
    =
    A2C_distributive_lattice _ (A_distributive_lattice_union_intersect S eqv). 
Proof. intros S eqv.
       unfold distributive_lattice_union_intersect, A_distributive_lattice_union_intersect, A2C_distributive_lattice; simpl.
       rewrite correct_eqv_set.
       rewrite bop_union_certs_correct.
       rewrite bop_intersect_certs_correct.
       rewrite <- correct_proofs_union_intersect. 
       reflexivity.
Qed. 
  
 
End Verify.   

