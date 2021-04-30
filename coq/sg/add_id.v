Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.

Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.theory.facts. 

Section Theory.

Variable S  : Type. 
Variable rS : brel S.
Variable c  : cas_constant.
Variable bS : binary_op S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable congS : bop_congruence S rS bS.
(* Variable assS : bop_associative S rS bS. *) 


Notation "a [+] b"  := (bop_add_id b a)        (at level 15).
  
Lemma bop_add_id_congruence : bop_congruence (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl; intros H1 H2;auto; discriminate. Qed. 

Lemma bop_add_id_associative : bop_associative S rS bS -> bop_associative (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros assS [c1 | s1] [c2 | s2] [c3 | s3]; simpl; auto. Qed. 

Lemma bop_add_id_idempotent : bop_idempotent S rS bS → bop_idempotent (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros idemS [s1 | t1]; simpl; auto. Qed. 

Lemma bop_add_id_not_idempotent : bop_not_idempotent S rS bS → bop_not_idempotent (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros [s P]. exists (inr _ s). simpl. assumption. Defined. 

Lemma bop_add_id_commutative : bop_commutative S rS bS → bop_commutative (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros commS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_id_not_commutative : bop_not_commutative S rS bS → bop_not_commutative (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t); simpl. assumption. Defined. 

Lemma bop_add_id_selective : bop_selective S rS bS → bop_selective (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros selS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_id_not_selective : bop_not_selective S rS bS → bop_not_selective (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. intros [ [s1 s2] P]. exists (inr _ s1, inr _ s2). simpl. assumption. Defined. 

Lemma bop_add_id_not_is_left (s : S) : bop_not_is_left (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. exists (inl _ c, inr _ s). simpl. reflexivity. Defined. 

Lemma bop_add_id_not_is_right (s : S) : bop_not_is_right (with_constant S ) (brel_sum brel_constant rS) (c [+] bS). 
Proof. exists (inr _ s, inl _ c). simpl. reflexivity. Defined. 

Lemma bop_add_id_exists_id : bop_exists_id (with_constant S ) (brel_sum brel_constant rS) (c [+] bS).
Proof. exists (inl S c). intros [a | b]; compute; auto. Defined. 

Lemma bop_add_id_exists_ann : bop_exists_ann S rS bS -> bop_exists_ann (with_constant S ) (brel_sum brel_constant rS) (c [+] bS).
Proof. intros [annS pS]. exists (inr _ annS). intros [s | t]; compute; auto. Defined. 

Lemma bop_add_id_not_exists_ann (s : S) : bop_not_exists_ann S rS bS -> bop_not_exists_ann (with_constant S ) (brel_sum brel_constant rS) (c [+] bS).
Proof. intros naS. intros [x | x]. exists (inr _ s). compute; auto. destruct (naS x) as [y D].  exists (inr _ y). compute. assumption. Defined. 


Lemma bop_add_id_left_cancellative : bop_anti_left S rS bS -> bop_left_cancellative S rS bS -> 
        bop_left_cancellative (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c).
Proof. intros ax lc [c1 | s1] [c2 | s2 ] [c3 | s3]; simpl; auto.  
       rewrite ax. auto. intro H. apply symS in H. rewrite ax in H. assumption. apply lc. 
Defined. 

Lemma bop_add_id_not_left_cancellative : (bop_not_left_cancellative S rS bS) + (bop_not_anti_left S rS bS) -> 
        bop_not_left_cancellative (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. intros [ [ [s [ t u]]  P ]| [ [s t] P ] ].
       exists (inr _ s, (inr _ t, inr _ u)); simpl. assumption. 
       exists (inr _ s, (inr _ t, inl _ c)); simpl. apply symS in P. auto.
Defined. 

Lemma bop_add_id_right_cancellative : (bop_anti_right S rS bS) -> bop_right_cancellative S rS bS -> 
        bop_right_cancellative (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. intros ax lc [c1 | s1] [c2 | s2 ] [c3 | s3]; simpl; auto.  
       rewrite ax. auto. intro H. apply symS in H. rewrite ax in H. assumption. apply lc. 
Defined. 

Lemma bop_add_id_not_right_cancellative : (bop_not_right_cancellative S rS bS) + (bop_not_anti_right S rS bS) -> 
        bop_not_right_cancellative (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. intros [ [ [s [ t  u]] P ] | [ [s  t] P ] ].
       exists (inr _ s, (inr _ t, inr _ u)); simpl. assumption. 
       exists (inr _ s, (inr _ t, inl _ c)); simpl. apply symS in P. auto.
Defined. 

Lemma bop_add_id_not_left_constant : bop_not_left_constant (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))). simpl. destruct (Pf wS) as [L R]. assumption. Defined. 

Lemma bop_add_id_not_right_constant : bop_not_right_constant (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))). simpl. destruct (Pf wS) as [L R]. assumption. Defined. 

Lemma bop_add_id_not_anti_left : bop_not_anti_left (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. unfold bop_not_anti_left. exists (inr wS, inl c); simpl. apply refS. Defined. 

Lemma bop_add_id_not_anti_right : bop_not_anti_right (with_constant S) (brel_sum brel_constant rS) (c [+] bS).
Proof. unfold bop_not_anti_right. exists (inr wS, inl c); simpl. apply refS. Defined. 

(* Decide *) 

Definition bop_add_id_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable (with_constant S ) (brel_sum brel_constant rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_id_selective selS)
   | inr not_selS   => inr _ (bop_add_id_not_selective not_selS)
   end. 

Definition bop_add_id_commutative_decide :
     bop_commutative_decidable S rS bS  → bop_commutative_decidable (with_constant S) (brel_sum brel_constant rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_id_commutative commS)
   | inr not_commS => inr _ (bop_add_id_not_commutative not_commS)
   end. 

Definition bop_add_id_idempotent_decide :
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable (with_constant S ) (brel_sum brel_constant rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_id_idempotent idemS)
   | inr not_idemS => inr _ (bop_add_id_not_idempotent not_idemS)
   end. 

Definition bop_add_id_exists_ann_decide : 
     bop_exists_ann_decidable S rS bS  → bop_exists_ann_decidable (with_constant S ) (brel_sum brel_constant rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl eann  => inl _ (bop_add_id_exists_ann eann)
   | inr neann => inr _ (bop_add_id_not_exists_ann wS neann)
   end. 

Definition bop_add_id_left_cancellative_decide : 
     bop_anti_left_decidable S rS bS -> bop_left_cancellative_decidable S rS bS -> 
        bop_left_cancellative_decidable (with_constant S ) (brel_sum brel_constant rS) (c [+] bS)
:= λ ad lcd,  
   match ad with 
   | inl anti_left     => 
        match lcd with 
        | inl lcanc     => inl _ (bop_add_id_left_cancellative anti_left lcanc)
        | inr not_lcanc => inr _ (bop_add_id_not_left_cancellative (inl _ not_lcanc))
        end 
   | inr not_anti_left => inr _ (bop_add_id_not_left_cancellative (inr _ not_anti_left))
   end. 

Definition bop_add_id_right_cancellative_decide : 
     (bop_anti_right_decidable S rS bS) -> bop_right_cancellative_decidable S rS bS -> 
        bop_right_cancellative_decidable (with_constant S ) (brel_sum brel_constant rS) (c [+] bS)
:= λ ad lcd,  
   match ad with 
   | inl anti_right     => 
        match lcd with 
        | inl lcanc     => inl _ (bop_add_id_right_cancellative anti_right lcanc)
        | inr not_lcanc => inr _ (bop_add_id_not_right_cancellative (inl _ not_lcanc))
        end 
   | inr not_anti_right => inr _ (bop_add_id_not_right_cancellative (inr _ not_anti_right))
   end. 

End Theory.

Section ACAS.

Definition asg_proofs_add_id : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S),
     eqv_proofs S rS -> asg_proofs S rS bS -> 
        asg_proofs (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c)
:= λ S rS c bS s eqvS sgS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in   
{|
  A_asg_associative   := bop_add_id_associative S rS c bS refS (A_asg_associative _ _ _ sgS)
; A_asg_congruence    := bop_add_id_congruence S rS c bS symS (A_asg_congruence _ _ _ sgS) 
; A_asg_commutative   := bop_add_id_commutative S rS c bS refS (A_asg_commutative _ _ _ sgS)
; A_asg_selective_d   := bop_add_id_selective_decide S rS c bS refS (A_asg_selective_d _ _ _ sgS)
; A_asg_idempotent_d  := bop_add_id_idempotent_decide S rS c bS (A_asg_idempotent_d _ _ _ sgS)
|}. 

Definition msg_proofs_add_id : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S) (f : S -> S),
     brel_not_trivial S rS f -> eqv_proofs S rS -> msg_proofs S rS bS -> 
        msg_proofs (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c)
:= λ S rS c bS s f Pf eqvS sgS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in   
{|
  A_msg_associative   := bop_add_id_associative S rS c bS refS (A_msg_associative _ _ _ sgS)
; A_msg_congruence    := bop_add_id_congruence S rS c bS symS (A_msg_congruence _ _ _ sgS) 
; A_msg_commutative_d := bop_add_id_commutative_decide S rS c bS refS (A_msg_commutative_d _ _ _ sgS)
; A_msg_is_left_d     := inr _ (bop_add_id_not_is_left S rS c bS s)
; A_msg_is_right_d    := inr _ (bop_add_id_not_is_right S rS c bS s)
; A_msg_left_cancel_d    :=  bop_add_id_left_cancellative_decide S rS c bS symS 
                               (A_msg_anti_left_d _ _ _ sgS) 
                               (A_msg_left_cancel_d _ _ _ sgS) 
; A_msg_right_cancel_d   := bop_add_id_right_cancellative_decide S rS c bS symS 
                               (A_msg_anti_right_d _ _ _ sgS) 
                               (A_msg_right_cancel_d _ _ _ sgS) 
; A_msg_left_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS s f Pf)
; A_msg_right_constant_d := inr _ (bop_add_id_not_right_constant S rS c bS s f Pf) 
; A_msg_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS s refS)
; A_msg_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS s refS)
|}. 




Definition sg_proofs_add_id : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S) (f : S -> S),
     brel_not_trivial S rS f -> eqv_proofs S rS -> sg_proofs S rS bS -> 
        sg_proofs (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c)
:= λ S rS c bS s f Pf eqvS sgS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in   
{|
  A_sg_associative   := bop_add_id_associative S rS c bS refS (A_sg_associative _ _ _ sgS)
; A_sg_congruence    := bop_add_id_congruence S rS c bS symS (A_sg_congruence _ _ _ sgS) 
; A_sg_commutative_d := bop_add_id_commutative_decide S rS c bS refS (A_sg_commutative_d _ _ _ sgS)
; A_sg_selective_d   := bop_add_id_selective_decide S rS c bS refS (A_sg_selective_d _ _ _ sgS)
; A_sg_is_left_d     := inr _ (bop_add_id_not_is_left S rS c bS s)
; A_sg_is_right_d    := inr _ (bop_add_id_not_is_right S rS c bS s)
; A_sg_idempotent_d  := bop_add_id_idempotent_decide S rS c bS (A_sg_idempotent_d _ _ _ sgS)
; A_sg_left_cancel_d    :=  bop_add_id_left_cancellative_decide S rS c bS symS 
                               (A_sg_anti_left_d _ _ _ sgS) 
                               (A_sg_left_cancel_d _ _ _ sgS) 
; A_sg_right_cancel_d   := bop_add_id_right_cancellative_decide S rS c bS symS 
                               (A_sg_anti_right_d _ _ _ sgS) 
                               (A_sg_right_cancel_d _ _ _ sgS) 
; A_sg_left_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS s f Pf)
; A_sg_right_constant_d := inr _ (bop_add_id_not_right_constant S rS c bS s f Pf) 
; A_sg_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS s refS)
; A_sg_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS s refS)
|}. 



Definition sg_C_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S) (f : S -> S),
     brel_not_trivial S rS f -> eqv_proofs S rS -> sg_C_proofs S rS bS -> 
        sg_C_proofs (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c)
:= λ S rS c bS s f Pf eqvS sgS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in   
{|
  A_sg_C_associative   := bop_add_id_associative S rS c bS refS (A_sg_C_associative _ _ _ sgS)
; A_sg_C_congruence    := bop_add_id_congruence S rS c bS symS (A_sg_C_congruence _ _ _ sgS) 
; A_sg_C_commutative   := bop_add_id_commutative S rS c bS refS (A_sg_C_commutative _ _ _ sgS)
; A_sg_C_selective_d   := bop_add_id_selective_decide S rS c bS refS (A_sg_C_selective_d _ _ _ sgS)
; A_sg_C_idempotent_d  := bop_add_id_idempotent_decide S rS c bS (A_sg_C_idempotent_d _ _ _ sgS)
; A_sg_C_cancel_d    := bop_add_id_left_cancellative_decide  S rS c bS symS 
                              (A_sg_C_anti_left_d _ _ _ sgS) 
                              (A_sg_C_cancel_d _ _ _ sgS) 
; A_sg_C_constant_d  := inr _ (bop_add_id_not_left_constant S rS c bS s f Pf) 
; A_sg_C_anti_left_d      := inr _ (bop_add_id_not_anti_left S rS c bS s refS)
; A_sg_C_anti_right_d     := inr _ (bop_add_id_not_anti_right S rS c bS s refS)
|}. 

Definition sg_CI_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S), 
     eqv_proofs S rS -> sg_CI_proofs S rS bS -> 
        sg_CI_proofs (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c)
:= λ S rS c bS s eqvS sgS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in   
{|
  A_sg_CI_associative        := bop_add_id_associative S rS c bS refS (A_sg_CI_associative _ _ _ sgS)
; A_sg_CI_congruence         := bop_add_id_congruence S rS c bS symS (A_sg_CI_congruence _ _ _ sgS) 
; A_sg_CI_commutative        := bop_add_id_commutative S rS c bS refS (A_sg_CI_commutative _ _ _ sgS)
; A_sg_CI_idempotent         := bop_add_id_idempotent S rS c bS (A_sg_CI_idempotent _ _ _ sgS)
; A_sg_CI_selective_d        := bop_add_id_selective_decide S rS c bS refS (A_sg_CI_selective_d _ _ _ sgS)
|}. 

Definition sg_CS_proofs_add_id : 
   ∀ (S : Type) (rS : brel S) (c : cas_constant) (bS : binary_op S) (s : S), 
     eqv_proofs S rS -> 
     sg_CS_proofs S rS bS -> 
        sg_CS_proofs (with_constant S) (brel_sum brel_constant rS) (bop_add_id bS c)
:= λ S rS c bS s eqvS sgS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in   
{|
  A_sg_CS_associative   := bop_add_id_associative S rS c bS refS (A_sg_CS_associative _ _ _ sgS)
; A_sg_CS_congruence    := bop_add_id_congruence S rS c bS symS (A_sg_CS_congruence _ _ _ sgS) 
; A_sg_CS_commutative   := bop_add_id_commutative S rS c bS refS (A_sg_CS_commutative _ _ _ sgS)
; A_sg_CS_selective     := bop_add_id_selective S rS c bS refS (A_sg_CS_selective _ _ _ sgS)
|}.

Definition A_sg_add_id : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
  let bS := A_sg_bop S sgS in
  let rS := A_eqv_eq S (A_sg_eq S sgS) in
  let s  := A_eqv_witness S (A_sg_eq S sgS) in
  let refS := A_eqv_reflexive _ _(A_eqv_proofs S (A_sg_eq S sgS)) in 
  {| 
     A_sg_eq           := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop          := bop_add_id bS c 
   ; A_sg_exists_id_d  := inl _ (bop_add_id_exists_id S rS c bS refS)
   ; A_sg_exists_ann_d := bop_add_id_exists_ann_decide S rS c bS s refS (A_sg_exists_ann_d _ sgS) 
   ; A_sg_proofs       := sg_proofs_add_id S rS c bS s                                         
                                        (A_eqv_new S (A_sg_eq S sgS))
                                        (A_eqv_not_trivial S (A_sg_eq S sgS))                                        
                                        (A_eqv_proofs S (A_sg_eq S sgS))
                                        (A_sg_proofs S sgS)
   ; A_sg_ast       := Ast_sg_add_id (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
  := λ S c sgS,
  let bS := A_sg_C_bop S sgS in
  let rS := A_eqv_eq S (A_sg_C_eqv S sgS) in
  let s  := A_eqv_witness S (A_sg_C_eqv S sgS) in
  let refS := A_eqv_reflexive _ _(A_eqv_proofs S (A_sg_C_eqv S sgS)) in 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_id (A_sg_C_bop S sgS) c 
   ; A_sg_C_exists_id_d  := inl _ (bop_add_id_exists_id S rS c bS refS)
   ; A_sg_C_exists_ann_d := bop_add_id_exists_ann_decide S rS c bS s refS (A_sg_C_exists_ann_d _ sgS) 
   ; A_sg_C_proofs    := sg_C_proofs_add_id S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                            (A_sg_C_bop S sgS)
                                            (A_eqv_witness S (A_sg_C_eqv S sgS))
                                            (A_eqv_new S (A_sg_C_eqv S sgS))
                                            (A_eqv_not_trivial S (A_sg_C_eqv S sgS))                                        
                                            (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                            (A_sg_C_proofs S sgS)
   ; A_sg_C_ast       := Ast_sg_add_id (c, A_sg_C_ast S sgS)
   |}. 


Definition A_sg_CI_add_id : ∀ (S : Type) (c : cas_constant), A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS,
  let bS := A_sg_CI_bop S sgS in
  let rS := A_eqv_eq S (A_sg_CI_eqv S sgS) in
  let s  := A_eqv_witness S (A_sg_CI_eqv S sgS) in
  let refS := A_eqv_reflexive _ _(A_eqv_proofs S (A_sg_CI_eqv S sgS)) in 
  
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_id (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_exists_id_d  := inl _ (bop_add_id_exists_id S rS c bS refS)
   ; A_sg_CI_exists_ann_d := bop_add_id_exists_ann_decide S rS c bS s refS (A_sg_CI_exists_ann_d _ sgS) 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_id S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                              (A_sg_CI_bop S sgS)
                                              (A_eqv_witness S (A_sg_CI_eqv S sgS))                                              
                                              (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                              (A_sg_CI_proofs S sgS)
   ; A_sg_CI_ast       := Ast_sg_add_id (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
  let bS := A_sg_CS_bop S sgS in
  let rS := A_eqv_eq S (A_sg_CS_eqv S sgS) in
  let s  := A_eqv_witness S (A_sg_CS_eqv S sgS) in
  let refS := A_eqv_reflexive _ _(A_eqv_proofs S (A_sg_CS_eqv S sgS)) in 
  {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_id (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_exists_id_d  := inl _ (bop_add_id_exists_id S rS c bS refS)
   ; A_sg_CS_exists_ann_d := bop_add_id_exists_ann_decide S rS c bS s refS (A_sg_CS_exists_ann_d _ sgS) 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_id S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                              (A_sg_CS_bop S sgS)
                                              (A_eqv_witness S (A_sg_CS_eqv S sgS))                                              
                                              (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                              (A_sg_CS_proofs S sgS)   
   ; A_sg_CS_ast       := Ast_sg_add_id (c, A_sg_CS_ast S sgS)
   |}. 


End ACAS.

Section CAS.


Definition bop_add_id_commutative_check : 
   ∀ {S : Type},  check_commutative (S := S) → check_commutative (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Commutative            => Certify_Commutative (S := (with_constant S)) 
   | Certify_Not_Commutative (s, t) => 
        Certify_Not_Commutative (S := (with_constant S)) (inr _ s, inr _ t)
   end. 

Definition bop_add_id_selective_check : 
   ∀ {S : Type},  check_selective (S := S) → check_selective (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Selective            => Certify_Selective(S := (with_constant S)) 
   | Certify_Not_Selective (s, t) => 
        Certify_Not_Selective (S := (with_constant S)) (inr _ s, inr _ t)
   end. 

Definition bop_add_id_idempotent_check : 
   ∀ {S : Type},  check_idempotent (S := S) → check_idempotent (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Idempotent       => Certify_Idempotent (S := (with_constant S)) 
   | Certify_Not_Idempotent s => Certify_Not_Idempotent (S := (with_constant S)) (inr _ s) 
   end. 


Definition bop_add_id_exists_ann_check : 
   ∀ {S : Type},  check_exists_ann (S := S) → check_exists_ann (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Ann a    => Certify_Exists_Ann (S := (with_constant S)) (inr _ a)
   | Certify_Not_Exists_Ann => Certify_Not_Exists_Ann (S := (with_constant S)) 
   end. 

(*
Definition bop_add_id_not_is_left_check : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → check_is_left (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Left (S := (with_constant S)) (inl _ c, inr _ s)
   end. 

Definition bop_add_id_not_is_left_assert : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → assert_not_is_left (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Left (S := (with_constant S)) (inl _ c, inr _ s)
   end. 


Definition bop_add_id_not_is_right_check : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → check_is_right (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Right (S := (with_constant S)) (inr _ s, inl _ c) 
   end. 

Definition bop_add_id_not_is_right_assert : 
   ∀ {S : Type},  cas_constant -> certify_witness (S := S) → assert_not_is_right (S := (with_constant S)) 
:= λ {S} c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Right (S := (with_constant S)) (inr _ s, inl _ c) 
   end. 
*)

Definition bop_add_id_left_cancellative_check : 
   ∀ {S : Type} (c : cas_constant),
     check_anti_left (S := S) -> 
     check_left_cancellative (S := S) -> 
        check_left_cancellative (S := (with_constant S)) 
:= λ {S} c ad lcd,  
   match ad with 
   | Certify_Anti_Left => 
        match lcd with 
        | Certify_Left_Cancellative     => Certify_Left_Cancellative (S := (with_constant S)) 
        | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
             Certify_Not_Left_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inr s3))
        end 
   | Certify_Not_Anti_Left (s1, s2) => 
        Certify_Not_Left_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inl c)) 
   end. 


Definition bop_add_id_right_cancellative_check : 
   ∀ {S : Type} (c : cas_constant),
     check_anti_right (S := S) -> 
     check_right_cancellative (S := S) -> 
        check_right_cancellative (S := (with_constant S)) 
:= λ {S} c ad lcd,  
   match ad with 
   | Certify_Anti_Right => 
        match lcd with 
        | Certify_Right_Cancellative      => Certify_Right_Cancellative (S := (with_constant S)) 
        | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
             Certify_Not_Right_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inr s3)) 
        end 
   | Certify_Not_Anti_Right (s1, s2) => 
        Certify_Not_Right_Cancellative (S := (with_constant S)) (inr s1, (inr s2, inl c))
   end. 


Definition asg_certs_add_id : ∀ {S : Type},  cas_constant -> S -> @asg_certificates S -> @asg_certificates (with_constant S)
:= λ {S} c s sgS,  
{|
  asg_associative      := Assert_Associative 
; asg_congruence       := Assert_Bop_Congruence  
; asg_commutative      := Assert_Commutative
; asg_selective_d      := bop_add_id_selective_check (asg_selective_d sgS) 
; asg_idempotent_d     := bop_add_id_idempotent_check (asg_idempotent_d sgS)
|}.

Definition msg_certs_add_id : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> @msg_certificates S -> @msg_certificates (with_constant S)
:= λ {S} c s f sgS,  
{|
  msg_associative      := Assert_Associative 
; msg_congruence       := Assert_Bop_Congruence  
; msg_commutative_d    := bop_add_id_commutative_check (msg_commutative_d sgS) 
; msg_is_left_d        := Certify_Not_Is_Left (inl _ c, inr _ s)
; msg_is_right_d       := Certify_Not_Is_Right (inr _ s, inl _ c) 
; msg_left_cancel_d    := bop_add_id_left_cancellative_check c (msg_anti_left_d sgS) (msg_left_cancel_d sgS)
; msg_right_cancel_d   := bop_add_id_right_cancellative_check c (msg_anti_right_d sgS) (msg_right_cancel_d sgS)
; msg_left_constant_d  := Certify_Not_Left_Constant  (inl c, (inr s, inr (f s)))
; msg_right_constant_d := Certify_Not_Right_Constant (inl c, (inr s, inr (f s)))
; msg_anti_left_d      := Certify_Not_Anti_Left  (inr s, inl c)
; msg_anti_right_d     := Certify_Not_Anti_Right  (inr s, inl c)
|}.



Definition sg_certs_add_id : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> @sg_certificates S -> @sg_certificates (with_constant S)
:= λ {S} c s f sgS,  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence  
; sg_commutative_d    := bop_add_id_commutative_check (sg_commutative_d sgS) 
; sg_selective_d      := bop_add_id_selective_check (sg_selective_d sgS) 
; sg_is_left_d        := Certify_Not_Is_Left (inl _ c, inr _ s)
; sg_is_right_d       := Certify_Not_Is_Right (inr _ s, inl _ c) 
; sg_idempotent_d     := bop_add_id_idempotent_check (sg_idempotent_d sgS) 
; sg_left_cancel_d    := bop_add_id_left_cancellative_check c (sg_anti_left_d sgS) (sg_left_cancel_d sgS)
; sg_right_cancel_d   := bop_add_id_right_cancellative_check c (sg_anti_right_d sgS) (sg_right_cancel_d sgS)
; sg_left_constant_d  := Certify_Not_Left_Constant  (inl c, (inr s, inr (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant (inl c, (inr s, inr (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left  (inr s, inl c)
; sg_anti_right_d     := Certify_Not_Anti_Right  (inr s, inl c)
|}.



Definition sg_C_certs_add_id : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> sg_C_certificates (S := S) -> sg_C_certificates (S := (with_constant S))
:= λ {S} c s f sgS,  
{|
  sg_C_associative   := Assert_Associative  
; sg_C_congruence    := Assert_Bop_Congruence  
; sg_C_commutative   := Assert_Commutative  
; sg_C_selective_d   := bop_add_id_selective_check (sg_C_selective_d sgS) 
; sg_C_idempotent_d  := bop_add_id_idempotent_check (sg_C_idempotent_d sgS) 
; sg_C_cancel_d      := bop_add_id_left_cancellative_check c (sg_C_anti_left_d sgS) (sg_C_cancel_d sgS)
; sg_C_constant_d    := Certify_Not_Left_Constant  (inl c, (inr s, inr (f s)))
; sg_C_anti_left_d   := Certify_Not_Anti_Left  (inr s, inl c)
; sg_C_anti_right_d  := Certify_Not_Anti_Right  (inr s, inl c)
|}. 

Definition sg_CI_certs_add_id : ∀ {S : Type},  cas_constant -> sg_CI_certificates (S := S) -> sg_CI_certificates (S := (with_constant S)) 
:= λ {S} c sgS,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := bop_add_id_selective_check (sg_CI_selective_d sgS)
|}. 


Definition sg_CS_certs_add_id : ∀ {S : Type},  cas_constant -> sg_CS_certificates (S := S) -> sg_CS_certificates (S := (with_constant S)) 
:= λ {S} c sg,  
{|
  sg_CS_associative   := Assert_Associative  
; sg_CS_congruence    := Assert_Bop_Congruence  
; sg_CS_commutative   := Assert_Commutative  
; sg_CS_selective     := Assert_Selective
|}. 

Definition sg_add_id: ∀ {S : Type},  cas_constant -> @sg S -> @sg (with_constant S)
:= λ {S} c sgS, 
   {| 
     sg_eq     := eqv_add_constant (sg_eq sgS) c 
   ; sg_bop    := bop_add_id (sg_bop sgS) c
   ; sg_exists_id_d      := Certify_Exists_Id  (inl c) 
   ; sg_exists_ann_d     := bop_add_id_exists_ann_check (sg_exists_ann_d sgS) 
   ; sg_certs  := sg_certs_add_id c (eqv_witness (sg_eq sgS)) (eqv_new (sg_eq sgS)) (sg_certs sgS)
   ; sg_ast    := Ast_sg_add_id (c, sg_ast sgS)
   |}. 

Definition sg_C_add_id : ∀ {S : Type} (c : cas_constant),  sg_C (S := S) -> sg_C (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_C_eqv       := eqv_add_constant (sg_C_eqv sgS) c  
   ; sg_C_bop       := bop_add_id (sg_C_bop sgS) c 
   ; sg_C_exists_id_d  := Certify_Exists_Id  (inl c) 
   ; sg_C_exists_ann_d := bop_add_id_exists_ann_check (sg_C_exists_ann_d sgS) 
   ; sg_C_certs     := sg_C_certs_add_id c (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS)) (sg_C_certs sgS)
   ; sg_C_ast       := Ast_sg_add_id (c, sg_C_ast sgS)
   |}. 

Definition sg_CI_add_id : ∀ {S : Type} (c : cas_constant), sg_CI (S := S) -> sg_CI (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CI_eqv       := eqv_add_constant (sg_CI_eqv sgS) c  
   ; sg_CI_bop       := bop_add_id (sg_CI_bop sgS) c
   ; sg_CI_exists_id_d  := Certify_Exists_Id  (inl c) 
   ; sg_CI_exists_ann_d := bop_add_id_exists_ann_check (sg_CI_exists_ann_d sgS)                                      
   ; sg_CI_certs     := sg_CI_certs_add_id c (sg_CI_certs sgS)
   ; sg_CI_ast       := Ast_sg_add_id (c, sg_CI_ast sgS)
   |}. 


Definition sg_CS_add_id : ∀ {S : Type} (c : cas_constant),  sg_CS (S := S) -> sg_CS (S := (with_constant S)) 
:= λ {S} c sgS, 
   {| 
     sg_CS_eqv       := eqv_add_constant (sg_CS_eqv sgS) c  
   ; sg_CS_bop       := bop_add_id (sg_CS_bop sgS) c
   ; sg_CS_exists_id_d  := Certify_Exists_Id  (inl c) 
   ; sg_CS_exists_ann_d := bop_add_id_exists_ann_check (sg_CS_exists_ann_d sgS)                                      
   ; sg_CS_certs    := sg_CS_certs_add_id c (sg_CS_certs sgS)
   ; sg_CS_ast       := Ast_sg_add_id (c, sg_CS_ast sgS)
   |}. 
  
End CAS.

Section Verify.

Section CertsCorrect.

  Variable S : Type.
  Variable r : brel S.
  Variable b : binary_op S.
  Variable c : cas_constant. 
  Variable Q : eqv_proofs S r. 

  Lemma bop_add_id_commutative_check_correct :  ∀ (p_d : bop_commutative_decidable S r b)     
     (refS : brel_reflexive S r),  
     p2c_commutative_check (with_constant S)
                         (brel_sum brel_constant r) 
                         (bop_add_id b c)
                         (bop_add_id_commutative_decide S r c b refS p_d)
     =                          
     bop_add_id_commutative_check (p2c_commutative_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]] refS; compute; reflexivity. Qed. 


Lemma bop_add_id_selective_check_correct : ∀ (p_d : bop_selective_decidable S r b)
     (refS : brel_reflexive S r) , 
     p2c_selective_check (with_constant S)
                         (brel_sum brel_constant r) 
                         (bop_add_id b c)
                         (bop_add_id_selective_decide S r c b refS p_d)
     =                          
     bop_add_id_selective_check (p2c_selective_check S r b p_d). 
Proof. intros [p | [ [s1 s2] np]] refS; compute; reflexivity. Qed. 

Lemma bop_add_id_idempotent_check_correct : ∀ p_d : bop_idempotent_decidable S r b, 
     p2c_idempotent_check (with_constant S)
                         (brel_sum brel_constant r) 
                         (bop_add_id b c)
                         (bop_add_id_idempotent_decide S r c b p_d)
     =                          
     bop_add_id_idempotent_check (p2c_idempotent_check S r b p_d). 
Proof. intros [p | [s np] ]; compute; reflexivity. Qed. 


Lemma bop_add_id_left_cancellative_check_correct :       
     ∀ (symS : brel_symmetric S r) (q_d : bop_anti_left_decidable S r b) (p_d : bop_left_cancellative_decidable S r b), 

     p2c_left_cancel_check (with_constant S)
                           (brel_sum brel_constant r)
                           (bop_add_id b c)
                           (bop_add_id_left_cancellative_decide S r c b symS q_d p_d)
     =                          
     bop_add_id_left_cancellative_check c (p2c_anti_left_check S r b q_d) 
                                          (p2c_left_cancel_check S r b p_d). 
Proof. intros symS  [ q | [[s1 s2] nq] ] [p | [ [s3 [s4 s5]] np] ]; compute; reflexivity. Qed. 


Lemma bop_add_id_right_cancellative_check_correct : 
      ∀ (symS : brel_symmetric S r) (q_d : bop_anti_right_decidable S r b) (p_d : bop_right_cancellative_decidable S r b), 

     p2c_right_cancel_check (with_constant S)
                            (brel_sum brel_constant r)
                            (bop_add_id b c)
                            (bop_add_id_right_cancellative_decide S r c b symS q_d p_d)
     =                          
     bop_add_id_right_cancellative_check c (p2c_anti_right_check S r b q_d)
                                           (p2c_right_cancel_check S r b p_d). 
Proof. intros symS  [ q | [[s1 s2] nq] ] [p | [ [s3 [s4 s5]] np] ]; compute; reflexivity. Qed. 

Lemma bop_add_id_exists_ann_check_correct : ∀ (s : S) (refS : brel_reflexive S r) (p_d : bop_exists_ann_decidable S r b), 
     p2c_exists_ann_check (with_constant S)
                          (brel_sum brel_constant r)
                          (bop_add_id b c)
        (bop_add_id_exists_ann_decide S r c b s refS p_d)
     =                          
     bop_add_id_exists_ann_check (p2c_exists_ann_check S r b p_d). 
Proof. intros s refS [ [a p] | np ]; compute; reflexivity. Qed.


Lemma correct_asg_certs_add_id : ∀ (s : S) (P : asg_proofs S r b), 
       asg_certs_add_id c s (P2C_asg S r b P) 
       = 
       P2C_asg (with_constant S) 
              (brel_sum brel_constant r) 
              (bop_add_id b c) 
              (asg_proofs_add_id S r c b s Q P). 
Proof. intros s P. 
       destruct P. destruct Q. 
       unfold asg_proofs_add_id, P2C_asg, asg_certs_add_id; simpl. 
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       reflexivity. 
Defined. 


Lemma correct_msg_certs_add_id : ∀ (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : msg_proofs S r b), 
       msg_certs_add_id c s f (P2C_msg S r b P) 
       = 
       P2C_msg (with_constant S) 
              (brel_sum brel_constant r) 
              (bop_add_id b c) 
              (msg_proofs_add_id S r c b s f Pf Q P). 
Proof. intros s f Pf P. 
       destruct P. destruct Q. 
       unfold msg_proofs_add_id, P2C_msg, msg_certs_add_id; simpl. 
       rewrite bop_add_id_commutative_check_correct. 
       rewrite bop_add_id_left_cancellative_check_correct. 
       rewrite bop_add_id_right_cancellative_check_correct. 
       reflexivity. 
Defined. 

Lemma correct_sg_certs_add_id : ∀ (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : sg_proofs S r b), 
       sg_certs_add_id c s f (P2C_sg S r b P) 
       = 
       P2C_sg (with_constant S) 
              (brel_sum brel_constant r) 
              (bop_add_id b c) 
              (sg_proofs_add_id S r c b s f Pf Q P). 
Proof. intros s f Pf P. 
       destruct P. destruct Q. 
       unfold sg_proofs_add_id, P2C_sg, sg_certs_add_id; simpl. 
       rewrite bop_add_id_commutative_check_correct. 
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       rewrite bop_add_id_left_cancellative_check_correct. 
       rewrite bop_add_id_right_cancellative_check_correct. 
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_add_id : ∀ (s : S) (f : S -> S) (Pf : brel_not_trivial S r f) (P : sg_C_proofs S r b),
       sg_C_certs_add_id c s f (P2C_sg_C S r b P) 
       = 
       P2C_sg_C (with_constant S) 
                (brel_sum brel_constant r) 
                (bop_add_id b c) 
                (sg_C_proofs_add_id S r c b s f Pf Q P). 
Proof. intros s f Pf P. destruct P. destruct Q. 
       unfold sg_C_certs_add_id, sg_C_proofs_add_id, P2C_sg_C; simpl.
       rewrite bop_add_id_selective_check_correct. 
       rewrite bop_add_id_idempotent_check_correct. 
       rewrite bop_add_id_left_cancellative_check_correct. 
       reflexivity. 
Defined. 

Lemma correct_sg_CI_certs_add_id : ∀ (s : S) (P : sg_CI_proofs S r b), 
       sg_CI_certs_add_id c (P2C_sg_CI S r b P) 
       = 
       P2C_sg_CI (with_constant S) 
                 (brel_sum brel_constant r) 
                 (bop_add_id b c) 
                 (sg_CI_proofs_add_id S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CI_certs_add_id, sg_CI_proofs_add_id, P2C_sg_CI; simpl.
       rewrite bop_add_id_selective_check_correct. 
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_add_id : ∀ (s : S) (P : sg_CS_proofs S r b),
       sg_CS_certs_add_id c (P2C_sg_CS S r b P) 
       = 
       P2C_sg_CS (with_constant S) 
                 (brel_sum brel_constant r) 
                 (bop_add_id b c) 
                 (sg_CS_proofs_add_id S r c b s Q P). 
Proof. intros s P. destruct P. destruct Q. 
       unfold sg_CS_certs_add_id, sg_CS_proofs_add_id, P2C_sg_CS ; simpl.
       reflexivity. 
Defined. 

End CertsCorrect.

Section AddIdCorrect.

  Variable S : Type.
  Variable c : cas_constant. 

Theorem correct_sg_add_id  : ∀ (sgS : A_sg S), 
         sg_add_id c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_id S c sgS). 
Proof. intro sgS. 
       unfold sg_add_id, A2C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_id.
       rewrite bop_add_id_exists_ann_check_correct.       
       reflexivity. 
Qed. 


Theorem correct_sg_C_add_id  : ∀ (sg_CS : A_sg_C S), 
         sg_C_add_id c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_id S c sg_CS). 
Proof. intro sg_CS. 
       unfold sg_C_add_id, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_C_certs_add_id.
       rewrite bop_add_id_exists_ann_check_correct.       
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_id  : ∀ (sg_CIS : A_sg_CI S), 
         sg_CI_add_id c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_id S c sg_CIS). 
Proof. intro sg_CIS. 
       unfold sg_CI_add_id, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_id.
       rewrite bop_add_id_exists_ann_check_correct.              
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_id  : ∀ (sg_CSS : A_sg_CS S), 
         sg_CS_add_id c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_id S c sg_CSS). 
Proof. intro sg_CSS. 
       unfold sg_CS_add_id, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CS_certs_add_id.
       rewrite bop_add_id_exists_ann_check_correct.              
       reflexivity. 
Qed. 

End AddIdCorrect.  
 
End Verify.   
  