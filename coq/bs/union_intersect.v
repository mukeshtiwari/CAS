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

Section UnionIntersect.   
(* 

Issue with (union, intersect): If the carrier set S is infinite, 
then the annihilator for intersect (id for union) is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the annihilator for intersect (id for union). 

The "bops_intersect_union_..._raw" results below capture the interaction 
of these binary operators before the id (annihilator) is added. 

*) 

(* ************************************* raw ************************************* *)


  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.


Lemma bop_union_intersect_left_distributive_raw : 
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

Lemma bop_union_intersect_right_distributive_raw : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_intersect_left_distributive_raw; auto. 
Defined. 


Lemma bops_union_intersect_left_left_absorptive_raw : 
        bops_left_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_intersect_elim in H; auto. destruct H as [L R]; auto.            
Qed. 


Lemma bops_union_intersect_left_right_absorptive_raw : 
        bops_left_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r) . 
Proof. apply bops_left_left_absorptive_implies_left_right; auto. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bops_union_intersect_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_right_left_absorptive_raw : 
        bops_right_left_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bops_union_intersect_left_right_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_right_right_absorptive_raw : 
       bops_right_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bops_union_intersect_right_left_absorptive_raw; auto. 
Qed. 



(* ************************************* cooked ************************************* *) 

Variable c : cas_constant.

Lemma bops_union_intersect_left_distributive : 
        bop_left_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_ann_add_id_left_distributive. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_left_absorptive_raw; auto. 
       apply bops_union_intersect_right_left_absorptive_raw; auto. 
       apply bop_union_intersect_left_distributive_raw; auto.        
Qed. 


Lemma bops_union_intersect_right_distributive : 
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_ann_add_id_right_distributive. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_right_absorptive_raw; auto. 
       apply bops_union_intersect_right_right_absorptive_raw; auto. 
       apply bop_union_intersect_right_distributive_raw; auto.        
Qed. 


Lemma bops_union_intersect_left_left_absorptive : 
        bops_left_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_ann_add_id_left_left_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_left_right_absorptive : 
        bops_left_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_ann_add_id_left_right_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_union_intersect_right_left_absorptive : 
        bops_right_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_ann_add_id_right_left_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_right_left_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_right_right_absorptive : 
        bops_right_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c).
Proof. apply bops_add_ann_add_id_right_right_absorptive. 
       apply brel_set_symmetric; auto. 
       apply bop_union_idempotent_raw; auto. 
       apply bops_union_intersect_right_right_absorptive_raw; auto. 
Qed. 


Lemma bops_union_intersect_ann_equals_id : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_id_equals_ann. 
       apply brel_set_reflexive; auto. 
Qed. 


Lemma bops_union_intersect_id_equals_ann : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_ann_add_id_id_equals_ann. 
       apply brel_set_reflexive; auto.
       exists nil; split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_intersect_nil_is_ann; auto.       
Defined.

End UnionIntersect.

Section IntersectUnion.

(* 

Issue with (intersect, union): If the carrier set S is infinite, 
then the id for intersect (annihilator for union) is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the id for intersect (annihilator for union). 

The "bops_intersect_union_..._raw" results below capture the interaction 
of these binary operators before the id (annihilator) is added. 

 *)


  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

(* ************************************* raw ************************************* *) 

Lemma bop_intersect_union_left_distributive_raw : 
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

Lemma bop_intersect_union_right_distributive_raw : 
        bop_right_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bop_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bop_intersect_union_left_distributive_raw; auto. 
Qed. 

Lemma bops_intersect_union_left_left_absorptive_raw : 
        bops_left_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_intersect_intro; auto. split; auto. 
             apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]; auto. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive_raw : 
        bops_left_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_left_left_absorptive_implies_left_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_left_absorptive_raw : 
        bops_right_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_left_right_absorptive_implies_right_left. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_intersect_commutative_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_intersect_union_right_right_absorptive_raw : 
        bops_right_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bops_right_left_absorptive_implies_right_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence_raw; auto. 
       apply bop_union_commutative_raw; auto. 
       apply bops_intersect_union_right_left_absorptive_raw; auto. 
Qed. 

(* ************************************* cooked ************************************* *) 

Variable c : cas_constant. 
Lemma bops_intersect_union_left_distributive : 
        bop_left_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_left_distributive. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_union_left_distributive_raw; auto.        
Qed. 


Lemma bops_intersect_union_right_distributive : 
        bop_right_distributive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_right_distributive. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_union_right_distributive_raw; auto.        
Qed. 


Lemma bops_intersect_union_left_left_absorptive : 
        bops_left_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_left_left_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_left_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_left_right_absorptive : 
        bops_left_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_left_right_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_left_right_absorptive_raw; auto. 
Qed. 

Lemma bops_intersect_union_right_left_absorptive : 
        bops_right_left_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_right_left_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_right_left_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_right_right_absorptive : 
        bops_right_right_absorptive 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_right_right_absorptive. 
       apply brel_set_reflexive; auto. 
       apply bops_intersect_union_right_right_absorptive_raw; auto. 
Qed. 


Lemma bops_intersect_union_id_equals_ann : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c). 
Proof. apply bops_add_id_add_ann_id_equals_ann. 
       apply brel_set_reflexive; auto. 
Qed. 


Lemma bops_intersect_union_ann_equals_id : 
        bops_id_equals_ann 
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set r) c)
            (@bop_add_ann (finite_set S) (bop_union r) c)
            (@bop_add_id (finite_set S) (bop_intersect r) c). 
Proof. apply bops_add_id_add_ann_ann_equals_id. 
       apply brel_set_reflexive; auto. 
       exists nil; split. 
       apply bop_union_nil_is_id; auto.
       apply bop_intersect_nil_is_ann; auto.        
Qed.

  
End IntersectUnion.   

End Theory.

Section ACAS.

Definition bs_proofs_union_intersect : 
  ∀ (S : Type) (eq : brel S) (c : cas_constant),
     eqv_proofs S eq -> 
     distributive_lattice_proofs
       (with_constant (finite_set S)) 
       (@brel_add_constant (finite_set S) (brel_set eq) c)
       (@bop_add_ann (finite_set S) (bop_union eq) c)
       (@bop_add_id (finite_set S) (bop_intersect eq) c)
:= λ S eq c eqvS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in
let tranS := A_eqv_transitive _ _ eqvS in      
{|
  A_distributive_lattice_absorptive        := bops_union_intersect_left_left_absorptive S eq refS symS tranS c
; A_distributive_lattice_absorptive_dual   := bops_intersect_union_left_left_absorptive S eq refS symS tranS c
; A_distributive_lattice_distributive      := bops_union_intersect_left_distributive S eq refS symS tranS c
|}. 


Definition A_dl_union_intersect : ∀ (S : Type),  A_eqv S -> cas_constant -> A_distributive_lattice (with_constant (finite_set S)) 
  := λ S eqv c,
  let eq  := A_eqv_eq S eqv in
  let s   := A_eqv_witness S eqv in
  let f   := A_eqv_new S eqv in
  let ntS := A_eqv_not_trivial S eqv in
  let eqP := A_eqv_proofs S eqv in 
{|
  A_distributive_lattice_eqv         := A_eqv_add_constant (finite_set S) (A_eqv_set S eqv) c 
; A_distributive_lattice_join        := @bop_add_ann (finite_set S) (bop_union eq) c
; A_distributive_lattice_meet        := @bop_add_id (finite_set S) (bop_intersect eq) c
; A_distributive_lattice_join_proofs := sg_CI_proofs_union S eq c s f ntS eqP 
; A_distributive_lattice_meet_proofs := sg_CI_proofs_intersect S eq c s f ntS eqP 
; A_distributive_lattice_proofs      := bs_proofs_union_intersect S eq c eqP 
; A_distributive_lattice_ast         := Ast_distributive_lattice_union_intersect(c, A_eqv_ast S eqv) 
|}.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   

