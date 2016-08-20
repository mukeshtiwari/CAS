Require Import CAS.code.basic_types. 
Require Import CAS.code.cas.
Require Import CAS.a_code.a_cas_records.   
Require Import CAS.a_code.a_cas.           
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.construct_correct. (* break up *)

Theorem correct_to_nat : to_nat = A2C_to nat (A_to_nat). 
Proof. compute. reflexivity. Qed. 

Theorem correct_to_bool : to_bool = A2C_to bool (A_to_bool). 
Proof. compute. reflexivity. Qed. 

Theorem correct_to_dual : ∀ (S : Type) (p : A_to S), 
      to_dual S (A2C_to S p)
      = 
      A2C_to S (A_to_dual S p).
Proof. intros S p. 
       unfold to_dual, A_to_dual, A2C_to; simpl. 
       rewrite correct_certs_to_dual. 
       reflexivity. 
Qed. 


Theorem correct_po_dual : ∀ (S : Type) (p : A_po S), 
      po_dual S (A2C_po S p)
      = 
      A2C_po S (A_po_dual S p).
Proof. intros S p. 
       unfold po_dual, A_po_dual, A2C_po; simpl. 
       rewrite correct_certs_po_dual. 
       reflexivity. 
Qed. 


Theorem correct_to_rlte : ∀ (S : Type) (s : A_sg_CS S), 
      to_rlte S (A2C_sg_CS S s)
      = 
      A2C_to S (A_to_rlte S s).
Proof. intros S s. 
       unfold to_rlte, A_to_rlte, A2C_to, A2C_sg_CS; simpl. 
       rewrite correct_certs_to_rlte. reflexivity. 
Qed. 


Theorem correct_to_llte : ∀ (S : Type) (s : A_sg_CS S), 
      to_llte S (A2C_sg_CS S s)
      = 
      A2C_to S (A_to_llte S s).
Proof. intros S s.        
       unfold to_llte, A_to_llte, A2C_to, A2C_sg_CS; simpl. 
       rewrite correct_certs_to_llte. reflexivity. 
Qed. 

Theorem correct_po_llte : ∀ (S : Type) (s : A_sg_CI S), 
      po_llte S (A2C_sg_CI S s)
      = 
      A2C_po S (A_po_llte S s).
Proof. intros S s.        
       unfold po_llte, A_po_llte, A2C_po, A2C_sg_CI; simpl. 
       rewrite correct_certs_po_llte. reflexivity. 
Qed. 

Theorem correct_po_rlte : ∀ (S : Type) (s : A_sg_CI S), 
      po_rlte S (A2C_sg_CI S s)
      = 
      A2C_po S (A_po_rlte S s).
Proof. intros S s.        
       unfold po_rlte, A_po_rlte, A2C_po, A2C_sg_CI; simpl. 
       rewrite correct_certs_po_rlte. reflexivity. 
Qed. 
