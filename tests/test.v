
Require Import CAS.a_code.a_cas.sg.max. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.bop.
Require Import CAS.code.brel.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
(*
Require Import CAS.code.cas_records. 
Require Import CAS.code.cert_records. 
Require Import CAS.code.certificates. 
*) 

Open Scope string_scope. 
Open Scope nat_scope. 

Print A_sg_CS_max.

Definition t := (A_sg_CS_proofs _ A_sg_CS_max). 

Print t. 


