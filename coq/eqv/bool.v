Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 

Section Theory.


Lemma eqb_bool_to_prop  : ∀ s t: bool, eqb s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto. Qed. 


Lemma brel_eq_bool_not_trivial : brel_not_trivial bool brel_eq_bool negb. 
Proof. intro s. induction s; auto. Defined. 

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

    ; A_eqv_data   := λ b, DATA_bool b 
    ; A_eqv_rep    := λ b, b
    ; A_eqv_ast    := Ast_eqv_bool 
   |}. 


End ACAS.

Section CAS.

Definition eqv_bool : @eqv bool 
:= {| 
      eqv_eq    := brel_eq_bool 
    ; eqv_witness := true 
    ; eqv_new   := negb 
    ; eqv_data  := λ b, DATA_bool b 
    ; eqv_rep   := λ b, b 
    ; eqv_ast   := Ast_eqv_bool 
|}. 
  
End CAS.

Section Verify.

Theorem correct_eqv_bool : eqv_bool = A2C_eqv bool (A_eqv_bool). 
Proof. compute. reflexivity. Qed. 
 
End Verify.   
  