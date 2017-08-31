Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.nat.

Definition sg_min : sg (S := nat) 
:= {| 
     sg_eq   := eqv_eq_nat 
   ; sg_bop   := bop_min
   ; sg_certs := sg_certs_min
   ; sg_ast   := Ast_sg_min
   |}. 


Definition sg_CS_min : sg_CS (S := nat) 
:= {| 
     sg_CS_eqv   := eqv_eq_nat 
   ; sg_CS_bop   := bop_min 
   ; sg_CS_certs := sg_CS_certs_min 
   ; sg_CS_ast   := Ast_sg_CS_min 
   |}. 
