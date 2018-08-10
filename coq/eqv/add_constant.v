Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop.
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.

Section Theory.

Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable wS : S. 
Variable conS : brel_congruence S rS rS.
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

Notation "a <+> b"  := (brel_add_constant b a) (at level 15).

Lemma brel_add_constant_congruence : 
       brel_congruence S rS rS → brel_congruence (with_constant S) (c <+> rS) (c <+> rS). 
Proof. unfold brel_congruence. 
     intros congS [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto. 
     discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
Qed. 

Lemma brel_add_constant_not_trivial : brel_not_trivial (with_constant S) (c <+> rS)
                                                       (λ (d : with_constant S), match d with | inl _ => inr _ wS  | inr _ => inl S c end). 
Proof. intro s. induction s; simpl; auto. Qed. 


Lemma brel_add_constant_reflexive : brel_reflexive (with_constant S) (c <+> rS). 
Proof. intros [a | b]; simpl. reflexivity. apply refS. Qed. 

Lemma brel_add_constant_symmetric : brel_symmetric (with_constant S) (c <+> rS). 
Proof.  intros [c1 | s1] [c2 | s2]; simpl; intro H; auto. Qed. 

Lemma brel_add_constant_transitive : brel_transitive (with_constant S) (c <+> rS). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros H1 H2; auto. discriminate. apply (tranS _ _ _ H1 H2). Qed. 

Lemma brel_add_constant_rep_correct : ∀ (rep : unary_op S), brel_rep_correct S rS rep →
                                       brel_rep_correct (with_constant S) (c <+> rS) (uop_with_constant rep).
Proof. intros rep P [a | b]. simpl. reflexivity. simpl. apply P. Qed. 

Lemma brel_add_constant_rep_idempotent : ∀ (rep : unary_op S), brel_rep_idempotent S rS rep →
                                       brel_rep_idempotent (with_constant S) (c <+> rS) (uop_with_constant rep).
Proof. intros rep P [a | b]; simpl. reflexivity. apply P. Qed. 

End Theory.

Section ACAS.

Require Import CAS.code.ast. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
  
Definition eqv_proofs_add_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
    eqv_proofs S r → eqv_proofs (with_constant S) (brel_add_constant r c) 
:= λ S r c eqv, 
   {| 
     A_eqv_congruence  := brel_add_constant_congruence S r c (A_eqv_congruence S r eqv) (A_eqv_congruence S r eqv)
   ; A_eqv_reflexive   := brel_add_constant_reflexive S r c (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_add_constant_transitive S r c (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_add_constant_symmetric S r c (A_eqv_symmetric S r eqv) 
   |}. 


Definition A_eqv_add_constant : ∀ (S : Type),  A_eqv S -> cas_constant -> A_eqv (with_constant S) 
:= λ S eqvS c, 
   {| 
      A_eqv_eq     := brel_add_constant (A_eqv_eq S eqvS) c
    ; A_eqv_proofs := eqv_proofs_add_constant S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)

    ; A_eqv_witness := inl c
    ; A_eqv_new     := λ (d : with_constant S), match d with | inl _ => inr _ (A_eqv_witness S eqvS)  | inr _ => inl S c end
    ; A_eqv_not_trivial := brel_add_constant_not_trivial S (A_eqv_eq S eqvS) c (A_eqv_witness S eqvS)

    ; A_eqv_data   := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (A_eqv_data S eqvS a) end)
    ; A_eqv_rep    := λ d, (match d with inl s => inl _ s  | inr s => inr _ (A_eqv_rep S eqvS s) end )

    ; A_eqv_ast    := Ast_eqv_add_constant (c, A_eqv_ast S eqvS)
   |}. 
  

End ACAS.

Section CAS.
Require Import CAS.code.ast. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Definition eqv_add_constant : ∀ {S : Type},  eqv (S := S) -> cas_constant -> @eqv (with_constant S)
:= λ {S} eqvS c, 
   {| 
     eqv_eq    := brel_add_constant (eqv_eq eqvS) c
    ; eqv_witness := inl c 
    ; eqv_new := (λ (d : with_constant S), match d with | inl _ => inr (eqv_witness eqvS) | inr _ => inl c end) 
    ; eqv_data  := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (eqv_data eqvS a) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ s  | inr s => inr _ (eqv_rep eqvS s) end )
    ; eqv_ast   := Ast_eqv_add_constant (c, eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.

Require Import CAS.verify.eqv_proofs_to_certs.

Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
    eqv_add_constant (A2C_eqv S E) c = A2C_eqv (with_constant S) (A_eqv_add_constant S E c).
Proof. intros S c E. destruct E, A_eqv_proofs. compute. reflexivity. Qed. 

 
End Verify.   
  