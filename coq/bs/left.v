Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.sg.left.
Require Import CAS.coq.sg.cast_up.

Section Theory.

Variable S : Type.
Variable rS : brel S.
Variable wS : S.
Variable f : S -> S. 
Variable nt : brel_not_trivial S rS f. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS. 
Variable addS  : binary_op S.
Variable congS: brel_congruence S rS rS.
Variable idemS : bop_idempotent S rS addS.
Variable commS : bop_commutative S rS addS. 

Lemma bops_sg_left_left_distributive : bop_left_distributive S rS addS bop_left. 
Proof. intros s1 s2 s3 ; compute.  exact (symS _ _ (idemS s1)).  Qed. 

Lemma bops_sg_left_right_distributive : bop_right_distributive S rS addS bop_left. 
Proof. intros s1 s2 s3 ; compute.  apply refS. Qed. 

Lemma bops_sg_left_left_left_absorptive : bops_left_left_absorptive S rS addS bop_left. 
Proof. intros s1 s2 ; compute. exact (symS _ _ (idemS s1)).  Qed. 

Lemma bops_sg_left_not_left_right_absorptive : bops_not_left_right_absorptive S rS addS bop_left. 
Proof.  exists (cef_commutative_implies_not_is_left rS addS wS f).
        compute. destruct (nt wS) as [L R]. 
        case_eq(rS (addS (f wS) wS) wS); intro F. 
           case_eq(rS (f wS) (addS (f wS) wS)); intro G; auto. 
           assert (K := tranS _ _ _ G F).
           rewrite K in R. exact R.
           case_eq(rS wS (addS wS (f wS))); intro G; auto.
           assert (K := commS wS (f wS)).
           assert (J := tranS _ _ _ G K). 
           apply symS in J.  rewrite J in F. exact F.
Defined.

Lemma bops_sg_left_not_id_equals_ann : bops_not_id_equals_ann S rS addS bop_left. 
Proof. compute. intros s. right. destruct (nt s) as [_ F]. exists (f s). right. exact F. Defined. 

Lemma bops_left_sg_not_id_equals_ann : bops_not_id_equals_ann S rS bop_left addS. 
Proof. compute. intros s. left. destruct (nt s) as [F _]. exists (f s). left. exact F. Defined. 

End Theory.



(*

Section ACAS.
Definition semiring_proofs_sg_left 
    (S : Type)
    (rS : brel S)
    (addS : binary_op S)
    (s : S)
    (f : S -> S)
    (nt : brel_not_trivial S rS f)
    (eqvP : eqv_proofs S rS)
    (sgP : sg_CI_proofs S rS addS) : semiring_proofs S rS addS bop_left 
:= 
let refS   := A_eqv_reflexive S rS eqvP in
let symS   := A_eqv_symmetric S rS eqvP in
let trnS   := A_eqv_transitive S rS eqvP in
let idemS  := A_sg_CI_idempotent S rS addS sgP in
let commS := A_sg_CI_commutative S rS addS sgP in
{|
  A_semiring_left_distributive       := bops_sg_left_left_distributive S rS symS addS idemS
; A_semiring_right_distributive      := bops_sg_left_right_distributive S rS refS addS
; A_semiring_left_left_absorptive_d  := inl (bops_sg_left_left_left_absorptive S rS symS addS idemS)
; A_semiring_left_right_absorptive_d := inr (bops_sg_left_not_left_right_absorptive S rS s f nt symS trnS addS commS)
; A_semiring_plus_id_is_times_ann_d  := inr (bops_sg_left_not_id_equals_ann S rS f nt addS)
; A_semiring_times_id_is_plus_ann_d  := inr (bops_left_sg_not_id_equals_ann S rS f nt addS)
|}.

End ACAS.

Section CAS.

Definition semiring_certs_sg_left 
    (S : Type)
    (rS : brel S)
    (addS : binary_op S)
    (s : S)
    (f : S -> S) : @semiring_certificates S 
:= 
{|
  semiring_left_distributive       := Assert_Left_Distributive 
; semiring_right_distributive      := Assert_Right_Distributive 
; semiring_left_left_absorptive_d  := Certify_Left_Left_Absorptive 
; semiring_left_right_absorptive_d := let (s1, s2) := cef_commutative_implies_not_is_left rS addS s f in Certify_Not_Left_Right_Absorptive (s1, s2)
; semiring_plus_id_is_times_ann_d  := Certify_Not_Plus_Id_Equals_Times_Ann
; semiring_times_id_is_plus_ann_d  := Certify_Not_Times_Id_Equals_Plus_Ann
|}.

End CAS.

Section Verify.

End Verify.     
*) 

