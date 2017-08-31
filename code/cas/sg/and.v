Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.bool. 

Definition sg_CS_certs_and : @sg_CS_certificates bool
:= {| 
     sg_CS_associative        := Assert_Associative  
   ; sg_CS_congruence         := Assert_Bop_Congruence  
   ; sg_CS_commutative        := Assert_Commutative  
   ; sg_CS_selective          := Assert_Selective  
   ; sg_CS_exists_id_d        := Certify_Exists_Id  true 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann  false 
   |}. 


Definition sg_CS_and : @sg_CS bool
:= {| 
     sg_CS_eqv   := eqv_eq_bool
   ; sg_CS_bop   := bop_and
   ; sg_CS_certs := sg_CS_certs_and
   ; sg_CS_ast   := Ast_sg_CS_and 
   |}. 
