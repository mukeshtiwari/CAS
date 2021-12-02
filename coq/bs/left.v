Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

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

Lemma bs_left_left_distributive : bop_left_distributive S rS addS bop_left. 
Proof. intros s1 s2 s3 ; compute.  exact (symS _ _ (idemS s1)).  Qed. 

Lemma bs_left_right_distributive : bop_right_distributive S rS addS bop_left. 
Proof. intros s1 s2 s3 ; compute.  apply refS. Qed. 

Lemma bs_left_left_left_absorptive : bops_left_left_absorptive S rS addS bop_left. 
Proof. intros s1 s2 ; compute. exact (symS _ _ (idemS s1)).  Qed.

Lemma bs_left_not_left_right_absorptive : bops_not_left_right_absorptive S rS addS bop_left. 
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

Definition bs_left_exists_id_ann_decidable (id_d : bop_exists_id_decidable S rS addS) : 
  exists_id_ann_decidable S rS addS bop_left :=
  match id_d with
  | inl id => Id_Ann_Proof_Id_None _ _ _ _ (id, bop_left_not_exists_ann S rS f nt)
  | inr nid => Id_Ann_Proof_None _ _ _ _ (nid, bop_left_not_exists_ann S rS f nt)                                    
  end. 

Definition bs_left_exists_id_ann_decidable_dual (ann_d : bop_exists_ann_decidable S rS addS) : 
  exists_id_ann_decidable S rS bop_left addS :=
  match ann_d with
  | inl ann  => Id_Ann_Proof_None_Ann _ _ _ _ (bop_left_not_exists_id S rS f nt, ann)
  | inr nann => Id_Ann_Proof_None _ _ _ _ (bop_left_not_exists_id S rS f nt, nann)                                    
  end. 


End Theory.

Section ACAS.

Definition bs_left_id_ann_proofs (S : Type) (sg : A_sg_CS S) :=
let eqv   := A_sg_CS_eqv S sg in
let wS    := A_eqv_witness _ eqv in
let f     := A_eqv_new _ eqv in
let nt    := A_eqv_not_trivial _ eqv in
let eq    := A_eqv_eq _ eqv in
let addS  := A_sg_CS_bop S sg in
let id_d  := A_sg_CS_exists_id_d S sg in
let ann_d := A_sg_CS_exists_ann_d S sg in 
{|
  A_id_ann_plus_times_d := bs_left_exists_id_ann_decidable S eq f nt addS id_d 
; A_id_ann_times_plus_d := bs_left_exists_id_ann_decidable_dual S eq f nt addS ann_d 
|}.

Definition bs_left_semiring_proofs_from_sg_CS (S : Type) (sg : A_sg_CS S) :=
let eqv   := A_sg_CS_eqv S sg in
let eqvP  := A_eqv_proofs S eqv in  
let wS    := A_eqv_witness _ eqv in
let f     := A_eqv_new _ eqv in
let nt    := A_eqv_not_trivial _ eqv in
let rS    := A_eqv_eq _ eqv in
let addS  := A_sg_CS_bop S sg in
let refS   := A_eqv_reflexive S rS eqvP in
let symS   := A_eqv_symmetric S rS eqvP in
let trnS   := A_eqv_transitive S rS eqvP in
let idemS  := bop_selective_implies_idempotent S rS addS (A_sg_CS_selective S rS addS (A_sg_CS_proofs S sg)) in 
let commS  := A_sg_CS_commutative S rS addS (A_sg_CS_proofs S sg) in 
{|
  A_semiring_left_distributive       := bs_left_left_distributive S rS symS addS idemS
; A_semiring_right_distributive      := bs_left_right_distributive S rS refS addS
; A_semiring_left_left_absorptive_d  := inl (bs_left_left_left_absorptive S rS symS addS idemS)
; A_semiring_left_right_absorptive_d := inr (bs_left_not_left_right_absorptive S rS wS f nt symS trnS addS commS)
|}.

Definition A_bs_left_from_sg_CS (S : Type) (sg : A_sg_CS S) : A_selective_presemiring S :=
let eqv  := A_sg_CS_eqv S sg in
{|
  A_selective_presemiring_eqv           := eqv 
; A_selective_presemiring_plus          := A_sg_CS_bop S sg  
; A_selective_presemiring_times         := bop_left 
; A_selective_presemiring_plus_proofs   := A_sg_CS_proofs S sg 
; A_selective_presemiring_times_proofs  := msg_proofs_left S eqv
; A_selective_presemiring_id_ann_proofs := bs_left_id_ann_proofs S sg 
; A_selective_presemiring_proofs        := bs_left_semiring_proofs_from_sg_CS S sg 
; A_selective_presemiring_ast           := Ast_sg_left (A_sg_CS_ast S sg) (* Fix someday *) 
|}.


End ACAS.

Section CAS.
(*
Definition semiring_certs_bs_left 
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
; semiring_left_right_absorptive_d := let (s1, s2) := cef_commutative_implies_not_is_left rS addS s f
                                      in Certify_Not_Left_Right_Absorptive (s1, s2)
|}.
*) 
End CAS.

Section Verify.

End Verify.     


