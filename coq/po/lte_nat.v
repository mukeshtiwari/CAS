Require Import Coq.Arith.Arith.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.

Require Import CAS.coq.eqv.nat.

Section Compute.

  Definition brel_lte_nat : brel nat  := Nat.leb.

End Compute.         

Section Theory. 
(*
∀ s t u v : S, brel_eq_nat s u = true → brel_eq_nat t v = true → brel_lte_nat s t = brel_lte_nat u v
*) 
  

Lemma brel_lte_nat_congruence_v1 :
  ∀ (s t u : nat), brel_eq_nat s u = true → brel_lte_nat s t = brel_lte_nat u t. 
Proof. unfold brel_eq_nat. unfold brel_lte_nat.
       intros s t u A. induction s. 
          destruct u. compute; auto. compute in A. discriminate A. 
          unfold Nat.leb. (fold Nat.leb). 
          destruct t. 
Admitted. 

Lemma brel_lte_nat_congruence : brel_congruence nat brel_eq_nat brel_lte_nat. 
Proof. intros s t u v. 
Admitted. 
  

Lemma brel_lte_nat_reflexive : brel_reflexive nat brel_lte_nat. 
Proof. intro s. induction s; auto. Qed. 

Lemma brel_lte_nat_transitive : brel_transitive nat brel_lte_nat. 
Proof. intros s t u A B. induction s. 
         compute. reflexivity.               
         unfold brel_lte_nat. unfold Nat.leb. fold Nat.leb. 
Admitted.

Lemma brel_lte_nat_antisymmetric : brel_antisymmetric nat brel_eq_nat brel_lte_nat. 
Proof. intros s t A B. induction s; induction t. 
          compute; reflexivity.
          compute in B. discriminate B. 
          compute in A. discriminate A. 
Admitted.

Lemma brel_lte_nat_S : ∀ s t : nat, brel_lte_nat (S s) (S t) = brel_lte_nat s t. 
Proof. unfold brel_lte_nat. induction s; induction t; compute; reflexivity. Qed. 

Lemma brel_lte_nat_s_Ss : ∀ s : nat, brel_lte_nat s (S s) = true. 
Proof. induction s. compute; auto. rewrite brel_lte_nat_S; auto. Qed.

Lemma brel_lte_nat_Ss_s : ∀ s : nat, brel_lte_nat (S s) s = false. 
Proof. induction s. compute; auto. rewrite brel_lte_nat_S; auto. Qed. 

Lemma brel_lte_nat_ll : ∀ s t : nat, brel_lte_nat s t = true -> brel_lte_nat s (S t) = true. 
Proof. intros s t A. induction s. compute; auto.
Admitted. 

Lemma brel_lte_nat_lll : ∀ s t : nat, brel_lte_nat s t = true -> brel_eq_nat t s = false -> brel_lte_nat (S s) t = true. 
Admitted. 


Lemma brel_lte_nat_total : brel_total nat brel_lte_nat. 
Proof. intros s t. induction s. left. compute; auto.
       induction t. right. compute; auto.
       destruct IHs as [A | A]. 
          case_eq(brel_eq_nat (S t) s); intro B.           
             right. rewrite (brel_lte_nat_congruence _ _ _ _ B (brel_eq_nat_reflexive (S s))).
             apply brel_lte_nat_s_Ss. 
             left. apply brel_lte_nat_lll; auto. 
             right. apply brel_lte_nat_ll; auto. 
Qed.                  
       
Lemma brel_lte_nat_is_bottom : brel_is_bottom nat brel_lte_nat 0. 
Proof. intro s. compute; auto. Qed. 

Lemma brel_lte_nat_exists_bottom : brel_exists_bottom nat brel_lte_nat.
Proof. exists 0. apply brel_lte_nat_is_bottom. Defined. 


Lemma brel_lte_nat_not_exists_top : brel_not_exists_top nat brel_lte_nat. 
Proof. intro s. exists (S s). induction s.
       compute; auto. rewrite brel_lte_nat_S; auto. 
Defined. 

End Theory.

Section ACAS.

Open Scope nat. 

Definition to_proofs_brel_lte_nat : to_proofs nat brel_eq_nat brel_lte_nat 
:= {| 
     A_to_congruence       := brel_lte_nat_congruence 
   ; A_to_reflexive        := brel_lte_nat_reflexive 
   ; A_to_transitive       := brel_lte_nat_transitive 
   ; A_to_antisymmetric    := brel_lte_nat_antisymmetric
   ; A_to_total            := brel_lte_nat_total
   |}. 

Definition A_lte_nat : A_to nat
:= {|
     A_to_eqv             := A_eqv_nat
   ; A_to_lte             := brel_lte_nat
   ; A_to_exists_top_d    := inr brel_lte_nat_not_exists_top 
   ; A_to_exists_bottom   := brel_lte_nat_exists_bottom
   ; A_to_proofs          := to_proofs_brel_lte_nat
   ; A_to_ast             := Ast_or_nat 
   |}. 


End ACAS.

Section CAS.

  Open Scope nat. 

Definition to_certs_brel_lte_nat : @to_certificates nat 
:= {| 
     to_congruence       := Assert_Brel_Congruence
   ; to_reflexive        := Assert_Reflexive
   ; to_transitive       := Assert_Transitive 
   ; to_antisymmetric    := Assert_Antisymmetric
   ; to_total            := Assert_Total
   |}. 

Definition lte_nat : @to nat
:= {|
     to_eqv             := eqv_eq_nat
   ; to_lte             := brel_lte_nat
   ; to_exists_top_d    := Certify_Not_Exists_Top 
   ; to_exists_bottom   := Assert_Exists_Bottom 0
   ; to_certs           := to_certs_brel_lte_nat
   ; to_ast             := Ast_or_nat 
   |}. 
End CAS.

Section Verify.

Theorem correct_eqv_nat : lte_nat = A2C_to nat (A_lte_nat). 
Proof. unfold lte_nat, A_lte_nat, A2C_to; simpl.
       unfold to_certs_brel_lte_nat, to_proofs_brel_lte_nat, P2C_to; simpl.
       unfold p2c_exists_qo_bottom_assert.
       
       reflexivity.
Qed. 
  
End Verify.   
  
