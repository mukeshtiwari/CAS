Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.right.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.



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
Variable commS : bop_commutative S rS addS. 

Lemma bs_right_left_distributive : bop_left_distributive S rS addS bop_right. 
Proof. intros s1 s2 s3; compute. apply refS. Qed. 

Lemma bs_right_right_distributive (idemS : bop_idempotent S rS addS) : bop_right_distributive S rS addS bop_right. 
Proof. intros s1 s2 s3; compute.  exact (symS _ _ (idemS s1)).  Qed.

Lemma bs_right_not_right_distributive (nidemS : bop_not_idempotent S rS addS) : bop_not_right_distributive S rS addS bop_right. 
Proof. destruct nidemS as [a A]. exists (a, (a, a)). compute.
       case_eq(rS a (addS a a)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        

Lemma bs_right_left_left_absorptive (isl : bop_is_left S rS addS) : bops_left_left_absorptive S rS addS bop_right.
Proof. intros s1 s2; compute.  apply symS. exact (isl s1 s2). Qed.

Lemma bs_right_not_left_left_absorptive (nisl : bop_not_is_left S rS addS) : bops_not_left_left_absorptive S rS addS bop_right.
Proof. destruct nisl as [[s1 s2] A]. exists (s1, s2). compute. 
       case_eq(rS s1 (addS s1 s2)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        
       
Lemma bs_right_left_right_absorptive (idemS : bop_idempotent S rS addS) : bops_left_right_absorptive S rS addS bop_right.
Proof. intros s1 s2; compute.  exact (symS _ _ (idemS s1)).  Qed.   

Lemma bs_right_not_left_right_absorptive (nidemS : bop_not_idempotent S rS addS) : bops_not_left_right_absorptive S rS addS bop_right. 
Proof. destruct nidemS as [a A]. exists (a, a). compute.
       case_eq(rS a (addS a a)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        

Lemma bs_right_right_left_absorptive (isr : bop_is_right S rS addS) : bops_right_left_absorptive S rS addS bop_right.
Proof. intros s1 s2; compute.  apply symS. exact (isr s2 s1). Qed.


Lemma bs_right_not_right_left_absorptive (nisr : bop_not_is_right S rS addS) : bops_not_right_left_absorptive S rS addS bop_right.
Proof. destruct nisr as [[s1 s2] A]. exists (s2, s1). compute. 
       case_eq(rS s2 (addS s1 s2)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        

Lemma bs_right_right_right_absorptive (idemS : bop_idempotent S rS addS) : bops_right_right_absorptive S rS addS bop_right.
Proof. intros s1 s2; compute.  apply symS. exact (idemS s1).  Qed.   

Lemma bs_right_not_right_right_absorptive (nidemS : bop_not_idempotent S rS addS) : bops_not_right_right_absorptive S rS addS bop_right. 
Proof. destruct nidemS as [a A]. exists (a, a). compute.
       case_eq(rS a (addS a a)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        



(* strict absorptivity. We insist on idempotence! *)
Lemma bs_right_not_left_strictly_absorptive : 
  bop_idempotent S rS addS  ->
  bops_not_left_strictly_absorptive S rS addS bop_right.
Proof.
  intros Ha.
  exists (wS, wS); compute.
  right.
  apply symS, Ha.
Qed.

Lemma bs_right_not_right_strictly_absorptive : 
  bop_idempotent S rS addS  ->
  bops_not_right_strictly_absorptive S rS addS bop_right.
Proof.
  intros Ha.
  exists (wS, wS); compute.
  right.
  apply symS.
  apply Ha.
Qed.



Definition bs_right_exists_id_ann_decide (id_d : bop_exists_id_decidable S rS addS) : 
  exists_id_ann_decidable S rS addS bop_right :=
  match id_d with
  | inl id => Id_Ann_Proof_Id_None _ _ _ _ (id, bop_right_not_exists_ann S rS f nt)
  | inr nid => Id_Ann_Proof_None _ _ _ _ (nid, bop_right_not_exists_ann S rS f nt)                                    
  end. 

Definition bs_right_exists_id_ann_decide_dual (ann_d : bop_exists_ann_decidable S rS addS) : 
  exists_id_ann_decidable S rS bop_right addS :=
  match ann_d with
  | inl ann  => Id_Ann_Proof_None_Ann _ _ _ _ (bop_right_not_exists_id S rS f nt, ann)
  | inr nann => Id_Ann_Proof_None _ _ _ _ (bop_right_not_exists_id S rS f nt, nann)                                    
  end. 

End Theory.

Section ACAS.
 

Definition bs_right_proofs {S : Type} (sg : A_sg S) :=
let eqv   := A_sg_eqv S sg in
let eqvP  := A_eqv_proofs S eqv in  
let rS    := A_eqv_eq _ eqv in
let addS  := A_sg_bop S sg in
let refS   := A_eqv_reflexive S rS eqvP in
let symS   := A_eqv_symmetric S rS eqvP in
let sgP    := A_sg_proofs _ sg in
{|
  A_bs_left_distributive_d        := inl (bs_right_left_distributive S rS refS addS)
; A_bs_right_distributive_d       := match A_sg_idempotent_d _ _ _ sgP with
                                   | inl idemS  => inl (bs_right_right_distributive S rS symS addS idemS)
                                   | inr nidemS => inr (bs_right_not_right_distributive S rS symS addS nidemS)
                                   end 
; A_bs_left_left_absorptive_d   := match A_sg_is_left_d _ _ _ sgP with
                                   | inl is_left     => inl (bs_right_left_left_absorptive S rS symS addS is_left)
                                   | inr not_is_left => inr (bs_right_not_left_left_absorptive S rS symS addS not_is_left)
                                   end 
; A_bs_left_right_absorptive_d  := match A_sg_idempotent_d _ _ _ sgP with
                                   | inl idemS  => inl (bs_right_left_right_absorptive S rS symS addS idemS)
                                   | inr nidemS => inr (bs_right_not_left_right_absorptive S rS symS addS nidemS)
                                   end 
; A_bs_right_left_absorptive_d  := match A_sg_is_right_d _ _ _ sgP with
                                   | inl is_right     => inl (bs_right_right_left_absorptive S rS symS addS is_right)
                                   | inr not_is_right => inr (bs_right_not_right_left_absorptive S rS symS addS not_is_right)
                                   end 
; A_bs_right_right_absorptive_d := match A_sg_idempotent_d _ _ _ sgP with
                                   | inl idemS  => inl (bs_right_right_right_absorptive S rS symS addS idemS)
                                   | inr nidemS => inr (bs_right_not_right_right_absorptive S rS symS addS nidemS)
                                   end 
|}.

Definition bs_right_id_ann_proofs {S : Type} (sg : A_sg S) :=
let eqv   := A_sg_eqv S sg in
let eq    := A_eqv_eq _ eqv in
let f     := A_eqv_new _ eqv in
let nt    := A_eqv_not_trivial _ eqv in
let addS  := A_sg_bop S sg in
{|
  A_id_ann_plus_times_d := bs_right_exists_id_ann_decide S eq f nt addS (A_sg_exists_id_d _ sg)
; A_id_ann_times_plus_d := bs_right_exists_id_ann_decide_dual S eq f nt addS (A_sg_exists_ann_d _ sg)
|}.



Definition A_bs_right (S : Type) (sg : A_sg S) : A_bs S :=
{|
  A_bs_eqv           := A_sg_eqv _ sg
; A_bs_plus          := A_sg_bop _ sg  
; A_bs_times         := bop_right
; A_bs_plus_proofs   := A_sg_proofs _ sg 
; A_bs_times_proofs  := sg_proofs_right _ (A_sg_eqv _ sg)
; A_bs_id_ann_proofs := bs_right_id_ann_proofs sg 
; A_bs_proofs        := bs_right_proofs sg 
; A_bs_ast           := Ast_bs_right (A_sg_ast _ sg) 
|}.


End ACAS.

Section AMCAS.

Open Scope string_scope.  
  
Definition A_mcas_bs_right (S : Type) (A : A_sg_mcas S) : A_bs_mcas S := 
match A_sg_mcas_cast_up _ A with
| A_MCAS_sg _ A'         => A_bs_classify _ (A_BS_bs _ (A_bs_right _ A'))
| A_MCAS_sg_Error _ sl1  => A_BS_Error _ sl1
| _                      => A_BS_Error _ ("Internal Error : mcas_bs_right" :: nil)
end.

End AMCAS.


Section CAS.

Definition bs_right_certs (S : Type) (sg : @sg S) :=
let sgP   := sg_certs sg in 
{|
  bs_left_distributive_d      := Certify_Left_Distributive 
; bs_right_distributive_d     := match sg_idempotent_d sgP with
                                   | Certify_Idempotent       => Certify_Right_Distributive 
                                   | Certify_Not_Idempotent a => Certify_Not_Right_Distributive (a, (a, a)) 
                                   end 
; bs_left_left_absorptive_d   := match sg_is_left_d sgP with
                                   | Certify_Is_Left            => Certify_Left_Left_Absorptive 
                                   | Certify_Not_Is_Left (a, b) => Certify_Not_Left_Left_Absorptive (a, b) 
                                   end 
; bs_left_right_absorptive_d  := match sg_idempotent_d sgP with
                                   | Certify_Idempotent       => Certify_Left_Right_Absorptive 
                                   | Certify_Not_Idempotent a => Certify_Not_Left_Right_Absorptive (a, a) 
                                   end 
; bs_right_left_absorptive_d  := match sg_is_right_d sgP with
                                   | Certify_Is_Right            => Certify_Right_Left_Absorptive 
                                   | Certify_Not_Is_Right (a, b) => Certify_Not_Right_Left_Absorptive (b, a) 
                                   end 
; bs_right_right_absorptive_d := match sg_idempotent_d sgP with
                                   | Certify_Idempotent       => Certify_Right_Right_Absorptive 
                                   | Certify_Not_Idempotent a => Certify_Not_Right_Right_Absorptive (a, a) 
                                   end 

|}.


Definition bs_right_exists_id_ann_check {S : Type} (id_d : @check_exists_id S) : @exists_id_ann_certificate S :=
  match id_d with
  | Certify_Exists_Id id => Id_Ann_Cert_Id_None id 
  | _ => Id_Ann_Cert_None 
  end. 

Definition bs_right_exists_id_ann_check_dual {S : Type} (ann_d : @check_exists_ann S) : @exists_id_ann_certificate S :=
  match ann_d with
  | Certify_Exists_Ann ann  => Id_Ann_Cert_None_Ann ann
  | _ => Id_Ann_Cert_None
  end. 

Definition bs_right_id_ann_certs {S : Type} (sg : @sg S) :=
{|
  id_ann_plus_times_d := bs_right_exists_id_ann_check (sg_exists_id_d sg)
; id_ann_times_plus_d := bs_right_exists_id_ann_check_dual (sg_exists_ann_d sg)
|}.


Definition bs_right {S : Type} (sg : @sg S) : @bs S :=
let eqv  := sg_eqv sg in
{|
  bs_eqv          := eqv 
; bs_plus         := sg_bop sg  
; bs_times        := bop_right 
; bs_plus_certs   := sg_certs sg 
; bs_times_certs  := sg_certs_right eqv
; bs_id_ann_certs := bs_right_id_ann_certs sg 
; bs_certs        := bs_right_certs S sg 
; bs_ast          := Ast_bs_right (sg_ast sg)
|}.

End CAS.


Section AMCAS.

Open Scope string_scope.  
  
Definition mcas_bs_right {S : Type} (A : @sg_mcas S) : @bs_mcas S := 
match sg_mcas_cast_up _ A with
| MCAS_sg A'         => bs_classify (BS_bs (bs_right A'))
| MCAS_sg_Error sl1  => BS_Error sl1
| _                  => BS_Error ("Internal Error : mcas_bs_right" :: nil)
end.

End AMCAS.

Section Verify.

  
Section Decide.

Variables (S : Type) (eq : brel S) (f : S -> S) (nt : brel_not_trivial S eq f) (addS : binary_op S).     

Lemma correct_bs_right_exists_id_ann_check (id_d : bop_exists_id_decidable S eq addS) : 
   bs_right_exists_id_ann_check
      (p2c_exists_id_check S eq addS id_d) 
   = p2c_exists_id_ann S eq addS bop_right
       (bs_right_exists_id_ann_decide S eq f nt addS id_d). 
Proof. destruct id_d as [[id idP] | nid]; compute; reflexivity. Qed. 

Lemma correct_bs_right_exists_id_ann_check_dual (ann_d : bop_exists_ann_decidable S eq addS) : 
   bs_right_exists_id_ann_check_dual
      (p2c_exists_ann_check S eq addS ann_d) 
   = p2c_exists_id_ann S eq bop_right addS 
       (bs_right_exists_id_ann_decide_dual S eq f nt addS ann_d). 
Proof. destruct ann_d as [[ann annP] | nann]; compute; reflexivity. Qed. 

End Decide.   

Lemma correct_bs_right_id_ann_certs (S : Type) (sgS : A_sg S) :
   bs_right_id_ann_certs (A2C_sg S sgS)
   =
   P2C_id_ann S (A_eqv_eq S (A_sg_eqv S sgS))
              (A_sg_bop S sgS)
              bop_right
              (bs_right_id_ann_proofs sgS).
Proof. unfold bs_right_id_ann_certs, bs_right_id_ann_proofs, P2C_id_ann,
       A2C_sg; simpl. destruct sgS. destruct A_sg_eqv. simpl.
       rewrite <- correct_bs_right_exists_id_ann_check. 
       rewrite <- correct_bs_right_exists_id_ann_check_dual.
       reflexivity.
Qed.

Lemma correct_bs_right_certs (S : Type) (sgS : A_sg S) :
   bs_right_certs S (A2C_sg S sgS)
   = 
   P2C_bs S (A_eqv_eq S (A_sg_eqv S sgS)) (A_sg_bop S sgS) bop_right (bs_right_proofs sgS).   
Proof. unfold bs_right_certs, bs_right_proofs, A2C_sg, P2C_bs; simpl.
       destruct sgS. destruct A_sg_proofs. simpl. 
       destruct A_sg_idempotent_d as [idemS | [a nidemS]];
       destruct A_sg_is_left_d as [isL | [[b c] nisL]];
       destruct A_sg_is_right_d as [isR | [[d e] nisR]]; simpl;
       reflexivity. 
Qed.

Theorem correct_bs_right (S : Type) (sgS : A_sg S) : 
         bs_right (A2C_sg S sgS) 
         = 
         A2C_bs S (A_bs_right S sgS). 
Proof. unfold bs_right, A_bs_right, A2C_bs; simpl. 
       rewrite <- correct_sg_certs_right.
       rewrite <- correct_bs_right_certs.
       rewrite <- correct_bs_right_id_ann_certs. 
       reflexivity. 
Qed.


Theorem correct_mcas_bs_right (S : Type) (sgS : A_sg_mcas S) : 
         mcas_bs_right (A2C_mcas_sg S sgS) 
         = 
         A2C_mcas_bs S (A_mcas_bs_right S sgS). 
Proof.  unfold mcas_bs_right, A_mcas_bs_right.
        rewrite correct_sg_mcas_cast_up.       
        destruct (A_sg_cas_up_is_error_or_sg S sgS) as [[l A] | [sg' A]]; rewrite A; simpl.
        + reflexivity.
        + rewrite correct_bs_right. 
          apply correct_bs_classify_bs.
Qed.

End Verify.     


