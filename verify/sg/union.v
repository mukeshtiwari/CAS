Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates. 
Require Import CAS.code.sg_cert_records.
Require Import CAS.a_code.proof_records.           
Require Import CAS.a_code.a_cas_records.

Require Import CAS.theory.bop.union. 
Require Import CAS.code.cas.sg.union.
Require Import CAS.a_code.a_cas.sg.union. 

Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties. 

Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs.

Section UnionCorrect.

Variable S : Type.
Variable c : cas_constant.


Theorem bop_union_certs_correct : 
    ∀ (eqvS : A_eqv S), 
      sg_CI_certs_union c (A_eqv_witness S eqvS) (A_eqv_new S eqvS)
      =                        
      P2C_sg_CI (with_constant (finite_set S))
                (brel_add_constant (brel_set (A_eqv_eq S eqvS)) c)
                (bop_add_ann (combined.bop_union (A_eqv_eq S eqvS)) c)
                (sg_CI_proofs_union S (A_eqv_eq S eqvS) c
                                    (A_eqv_witness S eqvS)
                                    (A_eqv_new S eqvS)
                                    (A_eqv_not_trivial S eqvS)
                                    (A_eqv_proofs S eqvS)).
Proof. intro eqvS.
       destruct eqvS.
       unfold sg_CI_certs_union, sg_CI_proofs_union. unfold P2C_sg_CI. simpl.
       reflexivity. 
Qed. 

    
Theorem bop_union_correct : 
    ∀ (eqvS : A_eqv S), 
         sg_CI_union c (A2C_eqv S eqvS)  
         = 
         A2C_sg_CI (with_constant (finite_set S)) (A_sg_CI_union S c eqvS). 
Proof. intro eqvS. unfold sg_CI_union, A_sg_CI_union. unfold A2C_sg_CI. simpl.
       unfold add_constant.A_eqv_add_constant, add_constant.eqv_add_constant; simpl. unfold A2C_eqv. simpl. 
       rewrite bop_union_certs_correct. 
       reflexivity. 
Qed. 

End UnionCorrect.