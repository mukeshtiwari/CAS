Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.sg.right.
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

Lemma bops_sg_right_left_distributive : bop_left_distributive S rS addS bop_right. 
Proof. intros s1 s2 s3; compute. apply refS. Qed. 

Lemma bops_sg_right_right_distributive : bop_right_distributive S rS addS bop_right. 
Proof. intros s1 s2 s3; compute.  exact (symS _ _ (idemS s1)).  Qed. 

Lemma bops_sg_right_not_left_left_absorptive : bops_not_left_left_absorptive S rS addS bop_right.
Proof. exists(cef_commutative_implies_not_is_left rS addS wS f); compute.
       destruct (nt wS) as [L R]. 
       case_eq(rS (addS (f wS) wS) wS); intro F. 
           case_eq(rS (f wS) (addS (f wS) wS)); intro G; auto. 
           assert (K := tranS _ _ _ G F).
           rewrite K in R. exact R.
           case_eq(rS wS (addS wS (f wS))); intro G; auto.
           assert (K := commS wS (f wS)).
           assert (J := tranS _ _ _ G K). 
           apply symS in J.  rewrite J in F. exact F.
Defined. 

Lemma bops_sg_right_left_right_absorptive : bops_left_right_absorptive S rS addS bop_right.
Proof. intros s1 s2; compute.  exact (symS _ _ (idemS s1)).  Qed.   

Lemma bops_sg_right_not_id_equals_ann : bops_not_id_equals_ann S rS addS bop_right. 
Proof. compute. intros s. right. destruct (nt s) as [_ F]. exists (f s). left. exact F. Qed. 

Lemma bops_right_sg_not_id_equals_ann : bops_not_id_equals_ann S rS bop_right addS. 
Proof. compute. intros s. left. destruct (nt s) as [F _]. exists (f s). right. exact F. Qed. 

End Theory.

Section ACAS.
(*
  
Definition semiring_proofs_sg_right 
    (S : Type)
    (rS : brel S)
    (addS : binary_op S)
    (s : S)
    (f : S -> S)
    (nt : brel_not_trivial S rS f)
    (eqvP : eqv_proofs S rS)
    (sgP : sg_CI_proofs S rS addS) : semiring_proofs S rS addS bop_right 
:= 
let refS   := A_eqv_reflexive S rS eqvP in
let symS   := A_eqv_symmetric S rS eqvP in
let trnS   := A_eqv_transitive S rS eqvP in
let idemS  := A_sg_CI_idempotent S rS addS sgP in
let commS := A_sg_CI_commutative S rS addS sgP in
{|
  A_semiring_left_distributive       := bops_sg_right_left_distributive S rS refS addS 
; A_semiring_right_distributive      := bops_sg_right_right_distributive S rS symS addS idemS
; A_semiring_left_left_absorptive_d  := inr (bops_sg_right_not_left_left_absorptive S rS s f nt symS trnS addS commS)
; A_semiring_left_right_absorptive_d := inl (bops_sg_right_left_right_absorptive S rS symS addS idemS)
; A_semiring_plus_id_is_times_ann_d  := inr (bops_sg_right_not_id_equals_ann S rS f nt addS)
; A_semiring_times_id_is_plus_ann_d  := inr (bops_right_sg_not_id_equals_ann S rS f nt addS)
|}.

Definition A_dioid_sg_right  (S : Type) (sg : A_sg_CI S) :=
let eqv   := A_sg_CI_eqv S sg            in
let eq    := A_eqv_eq S eqv          in
let s     := A_eqv_witness S eqv     in
let f     := A_eqv_new S eqv         in
let nt    := A_eqv_not_trivial S eqv in
let eqvP  := A_eqv_proofs S eqv      in   
let plusS := A_sg_CI_bop S sg           in 
{|
  A_dioid_eqv          := eqv 
; A_dioid_plus         := plusS 
; A_dioid_times        := bop_right 
; A_dioid_plus_proofs  := A_sg_CI_proofs S sg
; A_dioid_times_proofs := msg_proofs_right S eq s f nt eqvP 
; A_dioid_proofs       := semiring_proofs_sg_right S eq plusS s f nt eqvP (A_sg_CI_proofs S sg)  
; A_dioid_plus_ast     := A_sg_CI_bop_ast S sg 
; A_dioid_times_ast    := Ast_bop_right (A_eqv_ast S eqv) 
; A_dioid_ast          := Ast_dioid_sg_right (A_sg_CI_ast S sg)
|}.

Definition A_selective_dioid_sg_right  (S : Type) (sg : A_sg_CS S) :=
let eqv   := A_sg_CS_eqv S sg            in
let eq    := A_eqv_eq S eqv          in
let s     := A_eqv_witness S eqv     in
let f     := A_eqv_new S eqv         in
let nt    := A_eqv_not_trivial S eqv in
let eqvP  := A_eqv_proofs S eqv      in   
let plusS := A_sg_CS_bop S sg           in 
{|
  A_selective_dioid_eqv          := eqv 
; A_selective_dioid_plus         := plusS 
; A_selective_dioid_times        := bop_right 
; A_selective_dioid_plus_proofs  := A_sg_CS_proofs S sg
; A_selective_dioid_times_proofs := msg_proofs_right S eq s f nt eqvP 
; A_selective_dioid_proofs       := semiring_proofs_sg_right S eq plusS s f nt eqvP (A_sg_CI_proofs_from_sg_CS_proofs S eq plusS (A_sg_CS_proofs S sg))
; A_selective_dioid_plus_ast     := A_sg_CS_bop_ast S sg 
; A_selective_dioid_times_ast    := Ast_bop_right (A_eqv_ast S eqv) 
; A_selective_dioid_ast          := Ast_selective_dioid_sg_right (A_sg_CS_ast S sg)
|}.

*) 
End ACAS.

Section CAS.
(*
Definition semiring_certs_sg_right 
    (S : Type)
    (rS : brel S)
    (addS : binary_op S)
    (s : S)
    (f : S -> S) : @semiring_certificates S 
:= 
{|
  semiring_left_distributive       := Assert_Left_Distributive 
; semiring_right_distributive      := Assert_Right_Distributive 
; semiring_left_left_absorptive_d  := let (s1, s2) := cef_commutative_implies_not_is_left rS addS s f in Certify_Not_Left_Left_Absorptive (s1, s2)
; semiring_left_right_absorptive_d := Certify_Left_Right_Absorptive 
; semiring_plus_id_is_times_ann_d  := Certify_Not_Plus_Id_Equals_Times_Ann
; semiring_times_id_is_plus_ann_d  := Certify_Not_Times_Id_Equals_Plus_Ann
|}.


Definition dioid_sg_right  (S : Type) (sg : @sg_CI S) :=
let eqv   := sg_CI_eqv sg        in
let eq    := eqv_eq eqv          in
let s     := eqv_witness eqv     in
let f     := eqv_new eqv         in
let plusS := sg_CI_bop sg        in 
{|
  dioid_eqv          := eqv 
; dioid_plus         := plusS 
; dioid_times        := bop_right 
; dioid_plus_certs   := sg_CI_certs sg
; dioid_times_certs  := msg_certs_right s f 
; dioid_certs        := semiring_certs_sg_right S eq plusS s f 
; dioid_plus_ast     := sg_CI_bop_ast sg 
; dioid_times_ast    := Ast_bop_right (eqv_ast eqv) 
; dioid_ast          := Ast_dioid_sg_right (sg_CI_ast sg)
|}.



Definition selective_dioid_sg_right  (S : Type) (sg : @sg_CS S) :=
let eqv   := sg_CS_eqv sg        in
let eq    := eqv_eq eqv          in
let s     := eqv_witness eqv     in
let f     := eqv_new eqv         in
let plusS := sg_CS_bop sg        in 
{|
  selective_dioid_eqv          := eqv 
; selective_dioid_plus         := plusS 
; selective_dioid_times        := bop_right 
; selective_dioid_plus_certs   := sg_CS_certs sg
; selective_dioid_times_certs  := msg_certs_right s f 
; selective_dioid_certs        := semiring_certs_sg_right S eq plusS s f 
; selective_dioid_plus_ast     := sg_CS_bop_ast sg 
; selective_dioid_times_ast    := Ast_bop_right (eqv_ast eqv) 
; selective_dioid_ast          := Ast_selective_dioid_sg_right (sg_CS_ast sg)
|}.

*)   

End CAS.

Section Verify.
(*
Lemma correct_dioid_sg_right_certs
  (S : Type)
  (eq : brel S)
  (wS : S)
  (f : S -> S)
  (nt : brel_not_trivial S eq f) 
  (addS : binary_op S)
  (eqvP : eqv_proofs S eq)
  (sgP : sg_CI_proofs S eq addS) :   
  P2C_semiring S eq addS bop_right (semiring_proofs_sg_right S eq addS wS f nt eqvP sgP)
  = 
  semiring_certs_sg_right S eq addS wS f. 
Proof. destruct sgP. compute; auto. Qed. 
  

Theorem correct_dioid_sg_right  (S : Type) (sg : A_sg_CI S) :
   A2C_dioid S (A_dioid_sg_right S sg) =  dioid_sg_right S (A2C_sg_CI S sg). 
Proof. destruct sg. destruct A_sg_CI_proofs.
       unfold dioid_sg_right, A_dioid_sg_right, A2C_dioid, A2C_sg_CI; simpl.
       unfold P2C_sg_CI; simpl.
       rewrite <- correct_msg_certs_right.
       rewrite correct_dioid_sg_right_certs.
       reflexivity. 
Qed.   

Theorem correct_selective_dioid_sg_right  (S : Type) (sg : A_sg_CS S) :
   A2C_selective_dioid S (A_selective_dioid_sg_right S sg) =  selective_dioid_sg_right S (A2C_sg_CS S sg). 
Proof. destruct sg. destruct A_sg_CS_proofs.
       unfold selective_dioid_sg_right, A_selective_dioid_sg_right, A2C_selective_dioid, A2C_sg_CS; simpl.
       unfold P2C_sg_CS; simpl.
       rewrite <- correct_msg_certs_right.
       rewrite correct_dioid_sg_right_certs.
       reflexivity. 
Qed.   
*) 
End Verify.     