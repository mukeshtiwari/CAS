Require Import CAS.code.basic_types.
Require Import CAS.code.brel. 
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.           
Require Import CAS.code.cas.eqv.sum. 
Require Import CAS.a_code.a_cas.eqv.sum. 
Require Import CAS.verify.eqv_proofs_to_certs.

(*
Lemma correct_eqv_certs_sum : 
      ∀ (S T : Type) (rS : brel S) (rT : brel T) (eS : eqv_proofs S rS) (eT : eqv_proofs T rT), 
       eqv_certs_sum (P2C_eqv S rS eS) (P2C_eqv T rT eT) 
       = 
       P2C_eqv (S + T) (brel_sum rS rT) (eqv_proofs_sum S T rS rT eS eT). 
Proof. intros S T rS rT eS eT. destruct eS; destruct eT. 
       destruct A_eqv_nontrivial. 
       destruct A_eqv_nontrivial0. 
       destruct brel_nontrivial_witness as [s sP]. 
       destruct brel_nontrivial_negate as [f fP]. 
       destruct brel_nontrivial_witness0 as [t tP]. 
       destruct brel_nontrivial_negate0 as [g gP]. 
       compute. reflexivity. 
Defined. 
*)

Theorem correct_eqv_sum :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_sum (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S + T) (A_eqv_sum S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. compute. reflexivity. 
Qed. 

