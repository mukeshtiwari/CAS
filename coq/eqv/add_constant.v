Require Import Coq.Bool.Bool.    
Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.sum.

Section Operations.

Definition brel_constant : brel cas_constant
:= λ  x y, true. (* all constants equal! *) 

End Operations.

Section Theory.

Variable S  : Type. 
Variable rS : brel S.
Variable c : cas_constant.
Variable wS : S. 
Variable conS : brel_congruence S rS rS.
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

(* brel_constant *)

Lemma brel_constant_congruence : brel_congruence cas_constant brel_constant brel_constant.
Proof.   unfold brel_congruence. intros s t u v H1 H2. compute. reflexivity. Qed. 

Lemma brel_constant_reflexive : brel_reflexive cas_constant brel_constant.
Proof. intro a. compute; auto. Qed.

Lemma brel_constant_symmetric : brel_symmetric cas_constant brel_constant.
Proof. intros x y H.  compute; auto. Qed.

Lemma brel_constant_transitive : brel_transitive cas_constant brel_constant.
Proof. intros x y z H1 H2.  compute; auto. Qed.

Lemma brel_constant_is_finite : carrier_is_finite cas_constant brel_constant.
Proof. exists (λ _, c :: nil) .  intro s. compute; auto. Defined. 

(* add constant *) 
Lemma brel_add_constant_congruence : 
  brel_congruence S rS rS → brel_congruence (cas_constant + S) (brel_sum brel_constant rS) (brel_sum brel_constant rS).
Proof. intro H. apply brel_sum_congruence; auto. apply brel_constant_congruence. Qed. 

Lemma brel_add_constant_reflexive : brel_reflexive (cas_constant + S) (brel_sum brel_constant rS). 
Proof. apply brel_sum_reflexive; auto. apply brel_constant_reflexive. Qed. 

Lemma brel_add_constant_symmetric : brel_symmetric (cas_constant + S) (brel_sum brel_constant rS).
Proof. apply brel_sum_symmetric; auto. apply brel_constant_symmetric. Qed. 

Lemma brel_add_constant_transitive : brel_transitive (cas_constant + S) (brel_sum brel_constant rS).
Proof. apply brel_sum_transitive; auto. apply brel_constant_transitive. Qed. 


(* cardinality-related properties *)


Lemma brel_add_constant_not_trivial : brel_not_trivial (cas_constant + S) (brel_sum brel_constant rS)
                                                       (λ (d : cas_constant + S), match d with | inl _ => inr _ wS  | inr _ => inl S c end). 
Proof. intro s. induction s; simpl; auto. Qed. 

Lemma brel_add_constant_at_least_three (s : S) (f : S -> S) :
  brel_not_trivial S rS f ->
  brel_at_least_three (cas_constant + S) (brel_sum brel_constant rS).
Proof. intro ntS. 
       exists (inl c, (inr s, inr (f s))).
       destruct (ntS s) as [LS RS].        
       compute. rewrite LS; split; auto. 
Defined. 

Lemma brel_add_constant_not_exactly_two (s : S) (f : S -> S) :
  brel_not_trivial S rS f ->
  brel_not_exactly_two (cas_constant + S) (brel_sum brel_constant rS).
Proof. intro ntS.
       apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_add_constant_symmetric; auto. 
       apply brel_add_constant_transitive; auto.
       apply (brel_add_constant_at_least_three s f); auto. 
Defined.

Definition eqv_add_constant_is_finite_decidable (dS : carrier_is_finite_decidable S rS) : 
           carrier_is_finite_decidable (cas_constant + S)  (brel_sum brel_constant rS)
  := eqv_sum_finite_decidable cas_constant S brel_constant rS brel_constant_symmetric symS (inl brel_constant_is_finite) dS. 

End Theory.



Section ACAS.

Definition eqv_proofs_add_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
    eqv_proofs S r → eqv_proofs (cas_constant + S) (brel_sum brel_constant r) 
:= λ S r c eqv, 
   {| 
     A_eqv_congruence  := brel_add_constant_congruence S r (A_eqv_congruence S r eqv) 
   ; A_eqv_reflexive   := brel_add_constant_reflexive S r (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_add_constant_transitive S r (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_add_constant_symmetric S r (A_eqv_symmetric S r eqv)
   |}. 

Definition A_eqv_add_constant : ∀ (S : Type),  A_eqv S -> cas_constant -> A_eqv (cas_constant + S) 
  := λ S eqvS c,
  let eq  := A_eqv_eq S eqvS in
  let eqP := A_eqv_proofs S eqvS in
  let wS  := A_eqv_witness S eqvS in
  let f   := A_eqv_new S eqvS in
  let ntS := A_eqv_not_trivial S eqvS in
  let symS := A_eqv_symmetric S eq eqP in
  let trnS := A_eqv_transitive S eq eqP in   
   {| 
      A_eqv_eq     := brel_sum brel_constant eq 
    ; A_eqv_proofs := eqv_proofs_add_constant S eq c eqP
    ; A_eqv_witness := inl c
    ; A_eqv_new     := λ (d : cas_constant + S), match d with | inl _ => inr wS  | inr _ => inl c end
    ; A_eqv_not_trivial   := brel_add_constant_not_trivial S eq c wS 
    ; A_eqv_exactly_two_d := inr (brel_add_constant_not_exactly_two S eq c symS trnS wS f ntS)

    ; A_eqv_data   := λ d, (match d with inl s => DATA_inl(DATA_constant s) | inr a => DATA_inr (A_eqv_data S eqvS a) end)
    ; A_eqv_rep    := λ d, (match d with inl s => inl _ s  | inr s => inr _ (A_eqv_rep S eqvS s) end )
    ; A_eqv_finite_d := eqv_add_constant_is_finite_decidable S eq c symS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast    := Ast_eqv_add_constant (c, A_eqv_ast S eqvS)
   |}. 
  

End ACAS.

Section CAS.


Definition eqv_add_constant : ∀ {S : Type},  @eqv S -> cas_constant -> @eqv (cas_constant + S)
  := λ {S} eqvS c,
  let s  := eqv_witness eqvS in
  let f  := eqv_new eqvS in
  let r  := brel_sum brel_constant (eqv_eq eqvS) in 
   {| 
      eqv_eq       := r 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (cas_constant + S)
     ; eqv_reflexive      := @Assert_Reflexive (cas_constant + S)
     ; eqv_transitive     := @Assert_Transitive (cas_constant + S)
     ; eqv_symmetric      := @Assert_Symmetric (cas_constant + S)
     |}  
    ; eqv_witness := inl c 
    ; eqv_new     := (λ (d : cas_constant + S), match d with | inl _ => inr (eqv_witness eqvS) | inr _ => inl c end) 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 r (inl c) (inr s) (inr (f s)))
    ; eqv_data    := λ d, (match d with inl s => DATA_inl(DATA_constant s) | inr a => DATA_inr (eqv_data eqvS a) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ s  | inr s => inr _ (eqv_rep eqvS s) end )
    ; eqv_finite_d  := eqv_sum_finite_certifiable (Certify_Is_Finite (λ _, c :: nil)) (eqv_finite_d eqvS)                          
    ; eqv_ast   := Ast_eqv_add_constant (c, eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.

Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
    eqv_add_constant (A2C_eqv S E) c = A2C_eqv (cas_constant + S) (A_eqv_add_constant S E c).
Proof. intros S c E. destruct E.
       unfold eqv_add_constant, A_eqv_add_constant, A2C_eqv. simpl. 
       unfold eqv_add_constant_is_finite_decidable.
       destruct A_eqv_finite_d as [ [f Pf] | NF]; simpl; auto.       
Qed.  

End Verify.   
  