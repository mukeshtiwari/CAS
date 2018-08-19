Require Import Coq.Bool.Bool.    
Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts. 

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

Lemma brel_add_constant_at_least_three (s : S) (f : S -> S) :
  brel_not_trivial S rS f ->
  brel_at_least_three (with_constant S) (c <+> rS).
Proof. intro ntS. 
       exists (inl c, (inr s, inr (f s))).
       destruct (ntS s) as [LS RS].        
       compute. rewrite LS; split; auto. 
Defined. 


Lemma brel_add_constant_not_exactly_two (s : S) (f : S -> S) :
  brel_not_trivial S rS f ->
  brel_not_exactly_two (with_constant S) (c <+> rS).
Proof. intro ntS.
       apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_add_constant_symmetric; auto. 
       apply brel_add_constant_transitive; auto.
       apply (brel_add_constant_at_least_three s f); auto. 
Defined.


End Theory.

Section ACAS.

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
  let eq  := A_eqv_eq S eqvS in
  let eqP := A_eqv_proofs S eqvS in
  let wS  := A_eqv_witness S eqvS in
  let f   := A_eqv_new S eqvS in
  let ntS := A_eqv_not_trivial S eqvS in
  let symS := A_eqv_symmetric S eq eqP in
  let trnS := A_eqv_transitive S eq eqP in   
   {| 
      A_eqv_eq     := brel_add_constant eq c
    ; A_eqv_proofs := eqv_proofs_add_constant S eq c eqP

    ; A_eqv_witness := inl c
    ; A_eqv_new     := λ (d : with_constant S), match d with | inl _ => inr wS  | inr _ => inl c end
    ; A_eqv_not_trivial   := brel_add_constant_not_trivial S eq c wS 
    ; A_eqv_exactly_two_d := inr (brel_add_constant_not_exactly_two S eq c symS trnS wS f ntS)

    ; A_eqv_data   := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (A_eqv_data S eqvS a) end)
    ; A_eqv_rep    := λ d, (match d with inl s => inl _ s  | inr s => inr _ (A_eqv_rep S eqvS s) end )

    ; A_eqv_ast    := Ast_eqv_add_constant (c, A_eqv_ast S eqvS)
   |}. 
  

End ACAS.

Section CAS.

Definition eqv_add_constant : ∀ {S : Type},  eqv (S := S) -> cas_constant -> @eqv (with_constant S)
  := λ {S} eqvS c,
  let s  := eqv_witness eqvS in
  let f  := eqv_new eqvS in
  let r := brel_add_constant (eqv_eq eqvS) c in 
   {| 
     eqv_eq       := r
    ; eqv_witness := inl c 
    ; eqv_new     := (λ (d : with_constant S), match d with | inl _ => inr (eqv_witness eqvS) | inr _ => inl c end) 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 r (inl c) (inr s) (inr (f s)))
    ; eqv_data    := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (eqv_data eqvS a) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ s  | inr s => inr _ (eqv_rep eqvS s) end )
    ; eqv_ast   := Ast_eqv_add_constant (c, eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.

Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
    eqv_add_constant (A2C_eqv S E) c = A2C_eqv (with_constant S) (A_eqv_add_constant S E c).
Proof. intros S c E. destruct E, A_eqv_proofs. compute. reflexivity. Qed. 

 
End Verify.   
  