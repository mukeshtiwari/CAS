Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Section Theory.
Open Scope list_scope.

Lemma eqb_bool_to_prop  : ∀ s t: bool, eqb s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto. Qed. 


Lemma brel_eq_bool_not_trivial : brel_not_trivial bool brel_eq_bool negb. 
Proof. intro s. induction s; auto. Defined.

Lemma brel_eq_bool_is_finite : carrier_is_finite bool brel_eq_bool. 
Proof. unfold carrier_is_finite. exists (λ _, false :: true :: nil).
       intro s. destruct s; compute; auto. 
Defined.

Lemma brel_eq_bool_reflexive : brel_reflexive bool brel_eq_bool.
Proof. unfold brel_reflexive, brel_eq_bool. induction s; simpl; auto. 
Qed. 

Lemma brel_eq_bool_symmetric : brel_symmetric bool brel_eq_bool. 
Proof. unfold brel_symmetric, brel_eq_bool. 
       induction s; induction t; simpl; intros; auto. 
Qed. 

Lemma brel_eq_bool_transitive : brel_transitive bool brel_eq_bool. 
Proof. unfold brel_transitive, brel_eq_bool. 
       induction s; induction t; simpl; intros u H1 H2; destruct u; auto. 
Qed. 

Lemma brel_eq_bool_congruence : brel_congruence bool brel_eq_bool brel_eq_bool. 
Proof. unfold brel_congruence. 
       induction s; induction t; induction u; induction v; intros H Q; auto. 
Qed.


Lemma brel_eq_bool_exactly_two : brel_exactly_two bool brel_eq_bool.
Proof. exists (true, false). compute. split; auto.
       intro a. destruct a; auto. 
Defined.


End Theory.

Section ACAS.

Definition eqv_proofs_eq_bool : eqv_proofs bool brel_eq_bool  (* (uop_id bool) *) 
:= {| 
   A_eqv_congruence     := brel_eq_bool_congruence 
   ; A_eqv_reflexive      := brel_eq_bool_reflexive 
   ; A_eqv_transitive     := brel_eq_bool_transitive 
   ; A_eqv_symmetric      := brel_eq_bool_symmetric
   |}. 


Definition A_eqv_bool : A_eqv bool 
:= {| 
      A_eqv_eq     := brel_eq_bool
    ; A_eqv_proofs := eqv_proofs_eq_bool
                      
    ; A_eqv_witness     := true
    ; A_eqv_new         := negb                          
    ; A_eqv_not_trivial := brel_eq_bool_not_trivial
    ; A_eqv_exactly_two_d   := inl (brel_eq_bool_exactly_two)                              
    ; A_eqv_data   := λ b, DATA_bool b 
    ; A_eqv_rep    := λ b, b
    ; A_eqv_finite_d  := inl brel_eq_bool_is_finite
    ; A_eqv_ast    := Ast_eqv_bool 
   |}. 


End ACAS.

Section CAS.

Open Scope list_scope.

Definition eqv_bool : @eqv bool 
:= {| 
      eqv_eq    := brel_eq_bool
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence bool
     ; eqv_reflexive      := @Assert_Reflexive bool
     ; eqv_transitive     := @Assert_Transitive bool 
     ; eqv_symmetric      := @Assert_Symmetric bool
     |}  
    ; eqv_witness := true 
    ; eqv_new   := negb
    ; eqv_exactly_two_d := Certify_Exactly_Two (true, false) 
    ; eqv_data  := λ b, DATA_bool b 
    ; eqv_rep   := λ b, b
    ; eqv_finite_d  := Certify_Is_Finite (λ _, false :: true :: nil)
    ; eqv_ast   := Ast_eqv_bool 
|}. 
  
End CAS.

Section Verify.

Theorem correct_eqv_bool : eqv_bool = A2C_eqv bool (A_eqv_bool). 
Proof. compute. reflexivity. Qed. 
 
End Verify.   
  