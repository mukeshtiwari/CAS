Require Import Coq.Bool.Bool. 
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.theory.facts. 

Section Theory.
Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable bS : binary_op S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable refS : brel_reflexive S rS.
Variable congS : bop_congruence S rS bS.
(* Variable assS : bop_associative S rS bS. *) 

Notation "a <+> b"  := (brel_add_constant b a) (at level 15).
Notation "a [+] b"  := (bop_add_ann b a)       (at level 15).

Lemma bop_add_ann_congruence : bop_congruence (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl; intros H1 H2;auto. Qed. 

Lemma bop_add_ann_associative : bop_associative S rS bS -> bop_associative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros assS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; auto. Qed. 

Lemma bop_add_ann_idempotent : bop_idempotent S rS bS → bop_idempotent (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros idemS [s1 | t1]; simpl; auto. Qed. 

Lemma bop_add_ann_not_idempotent : bop_not_idempotent S rS bS → bop_not_idempotent (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [s P]. exists (inr _ s). simpl. assumption. Defined. 

Lemma bop_add_ann_commutative : bop_commutative S rS bS → bop_commutative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros commS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_commutative : bop_not_commutative S rS bS → bop_not_commutative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t); simpl. assumption. Defined. 

Lemma bop_add_ann_selective : bop_selective S rS bS → bop_selective (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros selS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_ann_not_selective : bop_not_selective S rS bS → bop_not_selective (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s1 s2] P]. exists (inr _ s1, inr _ s2). simpl. assumption. Defined. 

Lemma bop_add_ann_exists_ann : bop_exists_ann (with_constant S ) (c <+> rS) (c [+] bS).
Proof. exists (inl S c). intros [a | b]; compute; auto. Defined. 

Lemma bop_add_ann_exists_id : bop_exists_id S rS bS -> bop_exists_id (with_constant S ) (c <+> rS) (c [+] bS).
Proof. intros [annS pS]. exists (inr _ annS). intros [s | t]; compute; auto. Defined. 

Lemma bop_add_ann_not_exists_id : bop_not_exists_id S rS bS -> bop_not_exists_id (with_constant S ) (c <+> rS) (c [+] bS).
Proof. intros naS. intros [x | x]. exists (inr _ wS). compute; auto. destruct (naS x) as [y D].  exists (inr _ y). compute. exact D. Defined. 

Lemma bop_add_ann_not_is_left : bop_not_is_left (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. exists (inr _ wS, inl _ c). simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_is_right : bop_not_is_right (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. exists (inl _ c, inr _ wS). simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_left_cancellative : bop_not_left_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))); simpl. destruct (Pf wS) as [L _]. split; auto. Defined. 

Lemma bop_add_ann_not_right_cancellative : bop_not_right_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))); simpl. destruct (Pf wS) as [L _]. split; auto. Defined. 

Lemma bop_add_ann_not_left_constant : bop_not_left_constant (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inr _ wS, (inr _ wS, inl _ c)); simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_right_constant : bop_not_right_constant (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inr _ wS, (inr _ wS, inl _ c)); simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_anti_left : bop_not_anti_left (with_constant S) (c <+> rS) (c [+] bS).
Proof. unfold bop_not_anti_left. exists (inl c, inr wS); simpl. reflexivity. Defined. 

Lemma bop_add_ann_not_anti_right : bop_not_anti_right (with_constant S) (c <+> rS) (c [+] bS).
Proof. unfold bop_not_anti_right. exists (inl c, inr wS); simpl. reflexivity.  Defined.

(* Decide *)

Definition bop_add_ann_idempotent_decide : 
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_ann_idempotent idemS)
   | inr not_idemS => inr _ (bop_add_ann_not_idempotent not_idemS)
   end.  

Definition bop_add_ann_commutative_decide : 
     bop_commutative_decidable S rS bS  → bop_commutative_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_ann_commutative commS)
   | inr not_commS => inr _ (bop_add_ann_not_commutative not_commS)
   end. 

Definition bop_add_ann_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_ann_selective selS)
   | inr not_selS   => inr _ (bop_add_ann_not_selective not_selS)
   end. 

Definition bop_add_ann_exists_id_decide : bop_exists_id_decidable S rS bS  →  bop_exists_id_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl eann  => inl _ (bop_add_ann_exists_id eann)
   | inr neann => inr _ (bop_add_ann_not_exists_id neann)
   end. 

End Theory.

Section ACAS.

Definition sg_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S) (f : S -> S),
     brel_not_trivial S rS f -> 
     eqv_proofs S rS -> 
     sg_proofs S rS bS -> 
        sg_proofs (with_constant S) (brel_add_constant rS c) (bop_add_ann bS c)
:= λ S rS c bS s f Pf eqvS sgS,
{|
  A_sg_associative   := bop_add_ann_associative S rS c bS (A_sg_associative _ _ _ sgS)                                                
; A_sg_congruence    := bop_add_ann_congruence S rS c bS (A_sg_congruence _ _ _ sgS)  
; A_sg_commutative_d := bop_add_ann_commutative_decide S rS c bS (A_sg_commutative_d _ _ _ sgS)
; A_sg_selective_d   := bop_add_ann_selective_decide S rS c bS (A_sg_selective_d _ _ _ sgS)
; A_sg_is_left_d     := inr _ (bop_add_ann_not_is_left S rS c bS s) 
; A_sg_is_right_d    := inr _ (bop_add_ann_not_is_right S rS c bS s)
; A_sg_idempotent_d  := bop_add_ann_idempotent_decide S rS c bS (A_sg_idempotent_d _ _ _ sgS)
; A_sg_exists_id_d   := bop_add_ann_exists_id_decide S rS c bS s (A_sg_exists_id_d _ _ _ sgS) 
; A_sg_exists_ann_d  := inl _ (bop_add_ann_exists_ann S rS c bS)
; A_sg_left_cancel_d    :=  inr _ (bop_add_ann_not_left_cancellative S rS c bS s f Pf)
; A_sg_right_cancel_d   := inr _ (bop_add_ann_not_right_cancellative S rS c bS s f Pf)
; A_sg_left_constant_d  := inr _ (bop_add_ann_not_left_constant S rS c bS s)
; A_sg_right_constant_d := inr _ (bop_add_ann_not_right_constant S rS c bS s)
; A_sg_anti_left_d      := inr _ (bop_add_ann_not_anti_left S rS c bS s)
; A_sg_anti_right_d     := inr _ (bop_add_ann_not_anti_right S rS c bS s)
|}. 


Definition sg_C_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S) (f : S -> S),
     brel_not_trivial S rS f -> eqv_proofs S rS -> sg_C_proofs S rS bS -> 
        sg_C_proofs (with_constant S) (brel_add_constant rS c) (bop_add_ann bS c)
:= λ S rS c bS s f Pf eqvS sgS, 
{|
  A_sg_C_associative   := bop_add_ann_associative S rS c bS (A_sg_C_associative _ _ _ sgS)
; A_sg_C_congruence    := bop_add_ann_congruence S rS c bS (A_sg_C_congruence _ _ _ sgS) 
; A_sg_C_commutative   := bop_add_ann_commutative S rS c bS (A_sg_C_commutative _ _ _ sgS)
; A_sg_C_selective_d   := bop_add_ann_selective_decide S rS c bS (A_sg_C_selective_d _ _ _ sgS)
; A_sg_C_idempotent_d  := bop_add_ann_idempotent_decide S rS c bS (A_sg_C_idempotent_d _ _ _ sgS)
; A_sg_C_exists_id_d   := bop_add_ann_exists_id_decide S rS c bS s  (A_sg_C_exists_id_d _ _ _ sgS) 
; A_sg_C_exists_ann_d  := inl _ (bop_add_ann_exists_ann S rS c bS)
; A_sg_C_left_cancel_d    := inr _ (bop_add_ann_not_left_cancellative  S rS c bS s f Pf)
; A_sg_C_right_cancel_d   := inr _ (bop_add_ann_not_right_cancellative  S rS c bS s f Pf) 
; A_sg_C_left_constant_d  := inr _ (bop_add_ann_not_left_constant S rS c bS s)
; A_sg_C_right_constant_d := inr _ (bop_add_ann_not_right_constant S rS c bS s)
; A_sg_C_anti_left_d      := inr _ (bop_add_ann_not_anti_left S rS c bS s)
; A_sg_C_anti_right_d     := inr _ (bop_add_ann_not_anti_right S rS c bS s)
|}. 

Definition sg_CI_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S), 
     eqv_proofs S rS -> sg_CI_proofs S rS bS -> 
        sg_CI_proofs (with_constant S) (brel_add_constant rS c) (bop_add_ann bS c)
:= λ S rS c bS s eqvS sgS, 
{|
  A_sg_CI_associative        := bop_add_ann_associative S rS c bS (A_sg_CI_associative _ _ _ sgS)
; A_sg_CI_congruence         := bop_add_ann_congruence S rS c bS (A_sg_CI_congruence _ _ _ sgS) 
; A_sg_CI_commutative        := bop_add_ann_commutative S rS c bS (A_sg_CI_commutative _ _ _ sgS)
; A_sg_CI_idempotent         := bop_add_ann_idempotent S rS c bS (A_sg_CI_idempotent _ _ _ sgS)
; A_sg_CI_selective_d        := bop_add_ann_selective_decide S rS c bS (A_sg_CI_selective_d _ _ _ sgS)
; A_sg_CI_exists_id_d        := bop_add_ann_exists_id_decide S rS c bS s (A_sg_CI_exists_id_d _ _ _ sgS) 
; A_sg_CI_exists_ann_d       := inl _ (bop_add_ann_exists_ann S rS c bS)
|}. 

Definition sg_CS_proofs_add_ann : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S), 
     eqv_proofs S rS -> sg_CS_proofs S rS bS -> 
        sg_CS_proofs (with_constant S) (brel_add_constant rS c) (bop_add_ann bS c)
:= λ S rS c bS s eqvS sgS, 
{|
  A_sg_CS_associative   := bop_add_ann_associative S rS c bS (A_sg_CS_associative _ _ _ sgS)
; A_sg_CS_congruence    := bop_add_ann_congruence S rS c bS (A_sg_CS_congruence _ _ _ sgS) 
; A_sg_CS_commutative   := bop_add_ann_commutative S rS c bS (A_sg_CS_commutative _ _ _ sgS)
; A_sg_CS_selective     := bop_add_ann_selective S rS c bS (A_sg_CS_selective _ _ _ sgS)
; A_sg_CS_exists_id_d   := bop_add_ann_exists_id_decide S rS c bS s (A_sg_CS_exists_id_d _ _ _ sgS) 
; A_sg_CS_exists_ann_d  := inl _ (bop_add_ann_exists_ann S rS c bS)
|}. 


Definition A_sg_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_eq        := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop       := bop_add_ann (A_sg_bop S sgS) c 
   ; A_sg_proofs    := sg_proofs_add_ann S (A_eqv_eq S (A_sg_eq S sgS)) c 
                                         (A_sg_bop S sgS)
                                         (A_eqv_witness S (A_sg_eq S sgS))
                                         (A_eqv_new S (A_sg_eq S sgS))
                                         (A_eqv_not_trivial S (A_sg_eq S sgS)) 
                                         (A_eqv_proofs S (A_sg_eq S sgS))
                                         (A_sg_proofs S sgS)
   ; A_sg_bop_ast   := Ast_bop_add_ann (c, A_sg_bop_ast S sgS) 
   ; A_sg_ast       := Ast_sg_add_ann (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_ann (A_sg_C_bop S sgS) c 
   ; A_sg_C_proofs    := sg_C_proofs_add_ann S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                             (A_sg_C_bop S sgS)
                                             (A_eqv_witness S (A_sg_C_eqv S sgS))
                                             (A_eqv_new S (A_sg_C_eqv S sgS))
                                             (A_eqv_not_trivial S (A_sg_C_eqv S sgS)) 
                                             (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                             (A_sg_C_proofs S sgS)
   ; A_sg_C_bop_ast   := Ast_bop_add_ann (c, A_sg_C_bop_ast S sgS) 
   ; A_sg_C_ast       := Ast_sg_C_add_ann (c, A_sg_C_ast S sgS)
   |}. 

Definition A_sg_CI_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_ann (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_ann S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                               (A_sg_CI_bop S sgS)
                                               (A_eqv_witness S (A_sg_CI_eqv S sgS))                                               
                                               (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                               (A_sg_CI_proofs S sgS)
   ; A_sg_CI_bop_ast   := Ast_bop_add_ann (c, A_sg_CI_bop_ast S sgS) 
   ; A_sg_CI_ast       := Ast_sg_CI_add_ann (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_ann (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_ann S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                               (A_sg_CS_bop S sgS)
                                               (A_eqv_witness S (A_sg_CS_eqv S sgS)) 
                                               (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                               (A_sg_CS_proofs S sgS)
   ; A_sg_CS_bop_ast   := Ast_bop_add_ann (c, A_sg_CS_bop_ast S sgS) 
   ; A_sg_CS_ast       := Ast_sg_CS_add_ann (c, A_sg_CS_ast S sgS)
   |}. 

End ACAS.

Section CAS.


Definition bop_add_ann_commutative_check : 
   ∀ {S : Type},  @check_commutative S → @check_commutative (with_constant S) 
:= λ {S} dS,  
   match dS with 
   | Certify_Commutative            => Certify_Commutative
   | Certify_Not_Commutative (s, t) => Certify_Not_Commutative (inr _ s, inr _ t)
   end. 

Definition bop_add_ann_selective_check : 
   ∀ {S : Type},  @check_selective S → @check_selective (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Selective            => Certify_Selective 
   | Certify_Not_Selective (s, t) => Certify_Not_Selective (inr _ s, inr _ t)
   end. 

Definition bop_add_ann_idempotent_check : 
   ∀ {S : Type},  @check_idempotent S → @check_idempotent (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Idempotent     => Certify_Idempotent 
   | Certify_Not_Idempotent s => Certify_Not_Idempotent (inr _ s) 
   end. 

Definition bop_add_ann_exists_id_check : 
   ∀ {S : Type},  @check_exists_id S → @check_exists_id (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Id i   => Certify_Exists_Id (inr i)
   | Certify_Not_Exists_Id => Certify_Not_Exists_Id
   end. 

Definition sg_certs_add_ann : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> @sg_certificates S -> @sg_certificates (with_constant S)
:= λ {S} c s f sgS,  
{|
  sg_associative      := Assert_Associative  
; sg_congruence       := Assert_Bop_Congruence  
; sg_commutative_d    := bop_add_ann_commutative_check (sg_commutative_d sgS) 
; sg_selective_d      := bop_add_ann_selective_check (sg_selective_d sgS) 
; sg_is_left_d        := Certify_Not_Is_Left (inr _ s, inl _ c)
; sg_is_right_d       := Certify_Not_Is_Right  (inl _ c, inr _ s) 
; sg_idempotent_d     := bop_add_ann_idempotent_check (sg_idempotent_d sgS) 
; sg_exists_id_d      := bop_add_ann_exists_id_check (sg_exists_id_d sgS)
; sg_exists_ann_d     := Certify_Exists_Ann  (inl c) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_right_cancel_d   := Certify_Not_Right_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_left_constant_d  := Certify_Not_Left_Constant  (inr s, (inr s, inl c))
; sg_right_constant_d := Certify_Not_Right_Constant  (inr s, (inr s, inl c))
; sg_anti_left_d      := Certify_Not_Anti_Left  (inl c, inr s) 
; sg_anti_right_d     := Certify_Not_Anti_Right  (inl c, inr s) 
|}. 

Definition sg_C_certs_add_ann : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> sg_C_certificates (S := S) -> sg_C_certificates (S := (with_constant S)) 
:= λ {S} c s f sgS,  
{|
  sg_C_associative   := Assert_Associative  
; sg_C_congruence    := Assert_Bop_Congruence  
; sg_C_commutative   := Assert_Commutative  
; sg_C_selective_d   := bop_add_ann_selective_check (sg_C_selective_d sgS) 
; sg_C_idempotent_d  := bop_add_ann_idempotent_check (sg_C_idempotent_d sgS) 
; sg_C_exists_id_d   := bop_add_ann_exists_id_check (sg_C_exists_id_d sgS)
; sg_C_exists_ann_d  := Certify_Exists_Ann  (inl c) 
; sg_C_left_cancel_d  := Certify_Not_Left_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_C_right_cancel_d := Certify_Not_Right_Cancellative  (inl c, (inr s, inr (f s))) 
; sg_C_left_constant_d  := Certify_Not_Left_Constant  (inr s, (inr s, inl c))
; sg_C_right_constant_d := Certify_Not_Right_Constant  (inr s, (inr s, inl c))
; sg_C_anti_left_d      := Certify_Not_Anti_Left  (inl c, inr s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right  (inl c, inr s) 
|}. 

Definition sg_CI_certs_add_ann : ∀ {S : Type},  cas_constant -> sg_CI_certificates (S := S) -> sg_CI_certificates (S := (with_constant S)) 
:= λ {S} c sgS,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := bop_add_ann_selective_check (sg_CI_selective_d sgS) 
; sg_CI_exists_id_d        := bop_add_ann_exists_id_check (sg_CI_exists_id_d sgS)
; sg_CI_exists_ann_d       := Certify_Exists_Ann  (inl S c) 
|}. 


Definition sg_CS_certs_add_ann : ∀ {S : Type},  cas_constant -> sg_CS_certificates (S := S) -> sg_CS_certificates (S := with_constant S) 
:= λ {S} c sg,  
{|
  sg_CS_associative   := Assert_Associative  
; sg_CS_congruence    := Assert_Bop_Congruence  
; sg_CS_commutative   := Assert_Commutative  
; sg_CS_selective     := Assert_Selective  
; sg_CS_exists_id_d   := bop_add_ann_exists_id_check (sg_CS_exists_id_d sg)
; sg_CS_exists_ann_d  := Certify_Exists_Ann  (inl c) 
|}. 


Definition sg_add_ann:  ∀ {S : Type},  cas_constant -> @sg S -> @sg (with_constant S)
:= λ {S} c sgS, 
   {| 
     sg_eq      := eqv_add_constant (sg_eq sgS) c 
   ; sg_bop     := bop_add_ann (sg_bop sgS) c
   ; sg_certs   := sg_certs_add_ann c (eqv_witness (sg_eq sgS)) (eqv_new (sg_eq sgS)) (sg_certs sgS)
   ; sg_bop_ast := Ast_bop_add_ann (c, sg_bop_ast sgS) 
   ; sg_ast     := Ast_sg_add_ann (c, sg_ast sgS)
   |}. 

Definition sg_C_add_ann : ∀ {S : Type} (c : cas_constant),  sg_C (S := S) -> sg_C (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_C_eqv       := eqv_add_constant (sg_C_eqv sgS) c  
   ; sg_C_bop       := bop_add_ann (sg_C_bop sgS) c 
   ; sg_C_certs     := sg_C_certs_add_ann c (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS)) (sg_C_certs sgS)
   ; sg_C_bop_ast   := Ast_bop_add_ann (c, sg_C_bop_ast sgS) 
   ; sg_C_ast       := Ast_sg_C_add_ann (c, sg_C_ast sgS)
   |}. 

Definition sg_CI_add_ann : ∀ {S : Type} (c : cas_constant),  sg_CI (S := S) -> sg_CI (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CI_eqv       := eqv_add_constant (sg_CI_eqv sgS) c  
   ; sg_CI_bop       := bop_add_ann (sg_CI_bop sgS) c 
   ; sg_CI_certs     := sg_CI_certs_add_ann c (sg_CI_certs sgS)
   ; sg_CI_bop_ast   := Ast_bop_add_ann (c, sg_CI_bop_ast sgS) 
   ; sg_CI_ast       := Ast_sg_CI_add_ann (c, sg_CI_ast sgS)
   |}. 

Definition sg_CS_add_ann : ∀ {S : Type} (c : cas_constant),  sg_CS (S := S) -> sg_CS (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CS_eqv       := eqv_add_constant (sg_CS_eqv sgS) c  
   ; sg_CS_bop       := bop_add_ann (sg_CS_bop sgS) c 
   ; sg_CS_certs     := sg_CS_certs_add_ann c (sg_CS_certs sgS)
   ; sg_CS_bop_ast   := Ast_bop_add_ann (c, sg_CS_bop_ast sgS) 
   ; sg_CS_ast       := Ast_sg_CS_add_ann (c, sg_CS_ast sgS)
   |}. 
 
End CAS.

Section Verify.


Section CertsCorrect. 

  Variable S : Type.
  Variable r : brel S.
  Variable b : binary_op S.
  Variable c : cas_constant. 
  Variable Q : eqv_proofs S r. 
  
Lemma bop_add_ann_commutative_check_correct : ∀ p_d : bop_commutative_decidable S r b, 
     p2c_commutative_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_ann b c)
                         (bop_add_ann_commutative_decide S r c b p_d)
     =                          
     bop_add_ann_commutative_check (p2c_commutative_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 


Lemma bop_add_ann_selective_check_correct : ∀ p_d : bop_selective_decidable S r b, 
     p2c_selective_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_ann b c)
                         (bop_add_ann_selective_decide S r c b p_d)
     =                          
     bop_add_ann_selective_check (p2c_selective_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]]; compute; reflexivity. Qed. 

Lemma bop_add_ann_idempotent_check_correct : ∀ p_d : bop_idempotent_decidable S r b,       
     p2c_idempotent_check (with_constant S)
                         (brel_add_constant r c) 
                         (bop_add_ann b c)
                         (bop_add_ann_idempotent_decide S r c b p_d)
     =                          
     bop_add_ann_idempotent_check (p2c_idempotent_check S r b p_d). 
Proof. intros [p | [s np] ]; compute; reflexivity. Qed. 

Lemma bop_add_ann_exists_id_check_correct : ∀ (s : S) (p_d : bop_exists_id_decidable S r b),
    p2c_exists_id_check (with_constant S)
                        (brel_add_constant r c)
                        (bop_add_ann b c)
                        (bop_add_ann_exists_id_decide S r c b s p_d)
     =                          
     bop_add_ann_exists_id_check (p2c_exists_id_check S r b p_d). 
Proof. intros s [ [a p] | np ]; compute; reflexivity. Qed.


Lemma correct_sg_certs_add_ann : ∀ (s : S) (f : S-> S) (Pf : brel_not_trivial S r f) (P : sg_proofs S r b), 
       sg_certs_add_ann c s f (P2C_sg S r b P) 
       = 
       P2C_sg (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_proofs_add_ann S r c b s f Pf Q P). 
Proof. intros s f Pf P. 
       destruct P. destruct Q. 
       unfold sg_proofs_add_ann, P2C_sg, sg_certs_add_ann; simpl. 
       rewrite bop_add_ann_commutative_check_correct. 
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_idempotent_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 

Lemma correct_sg_C_certs_add_ann : ∀ (s : S) (f : S-> S) (Pf : brel_not_trivial S r f) (P : sg_C_proofs S r b), 
       sg_C_certs_add_ann  c s f (P2C_sg_C S r b P) 
       = 
       P2C_sg_C (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_C_proofs_add_ann S r c b s f Pf Q P). 
Proof. intros s f Pf P. destruct P. destruct Q. 
       unfold sg_C_certs_add_ann, sg_C_proofs_add_ann, P2C_sg_C; simpl.
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_idempotent_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_add_ann : ∀ (s : S) (P : sg_CI_proofs S r b), 
       sg_CI_certs_add_ann c (P2C_sg_CI S r b P) 
       = 
       P2C_sg_CI (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_CI_proofs_add_ann S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CI_certs_add_ann, sg_CI_proofs_add_ann, P2C_sg_CI; simpl.
       rewrite bop_add_ann_selective_check_correct. 
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_add_ann : ∀ (s : S) (P : sg_CS_proofs S r b), 
       sg_CS_certs_add_ann c  (P2C_sg_CS S r b P) 
       = 
       P2C_sg_CS (with_constant S) 
          (brel_add_constant r c) 
          (bop_add_ann b c) 
          (sg_CS_proofs_add_ann S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CS_certs_add_ann, sg_CS_proofs_add_ann, P2C_sg_CS; simpl.
       rewrite bop_add_ann_exists_id_check_correct.
       reflexivity. 
Defined.

End CertsCorrect. 

Section AddAnnCorrect.

  Variable S : Type.
  Variable c : cas_constant. 
  

Theorem correct_sg_add_ann  : ∀ (sgS : A_sg S), 
         sg_add_ann c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_ann S c sgS). 
Proof. intro sgS. unfold A2C_sg, sg_add_ann; simpl.
       rewrite <- correct_sg_certs_add_ann. 
       rewrite correct_eqv_add_constant. 
       reflexivity. 
Qed. 

Theorem correct_sg_C_add_ann  : ∀ (sg_CS : A_sg_C S), 
         sg_C_add_ann c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_ann S c sg_CS). 
Proof. intro sg_CS. unfold sg_C_add_ann, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_C_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_ann  : ∀ (sg_CIS : A_sg_CI S), 
         sg_CI_add_ann c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_ann S c sg_CIS). 
Proof. intro sg_CIS. unfold sg_CI_add_ann, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_ann  : ∀ (sg_CSS : A_sg_CS S), 
         sg_CS_add_ann c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_ann S c sg_CSS). 
Proof. intro sg_CSS. unfold sg_CS_add_ann, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CS_certs_add_ann. 
       reflexivity. 
Qed. 

End AddAnnCorrect.  
 
End Verify.   
  