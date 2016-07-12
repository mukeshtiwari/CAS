Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.cast.
Require Import CAS.code.construct_certs.
Require Import CAS.code.cas_records.
Require Import CAS.code.cas.
Require Import CAS.a_code.a_cast.
Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.construct_proofs.  (* ~~ construct_certs *)
Require Import CAS.a_code.a_cas_records.     (* ~~ cas_records  *) 
Require Import CAS.a_code.a_cas.             (* ~~ cas          *) 
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.construct_correct. (* ~~ construct_certs <-> construct_proofs *)


Eval compute in sg_CS_llex _ _ sg_CS_min sg_CS_and. 

Eval compute in sg_CS_llex _ _ sg_CS_and sg_CS_or. 

Eval compute in sg_CS_llex _ _ sg_CS_and sg_CS_min. 











