Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.nat.

(* 
  Compute (P2C_sg brel_eq_nat bop_max (sg_proofs_max)). 
*) 
Definition sg_certs_max : sg_certificates (S := nat)
:= {| 
       sg_associative := Assert_Associative;
       sg_congruence := Assert_Bop_Congruence;
       sg_commutative_d := Certify_Commutative;
       sg_selective_d := Certify_Selective;
       sg_idempotent_d := Certify_Idempotent;
       sg_exists_id_d := Certify_Exists_Id 0;
       sg_exists_ann_d := Certify_Not_Exists_Ann;
       sg_is_left_d := Certify_Not_Is_Left (0, 1);
       sg_is_right_d := Certify_Not_Is_Right (1, 0);
       sg_left_cancel_d := Certify_Not_Left_Cancellative (1, (1, 0));
       sg_right_cancel_d := Certify_Not_Right_Cancellative (1, (1, 0));
       sg_left_constant_d := Certify_Not_Left_Constant (0, (1, 0));
       sg_right_constant_d := Certify_Not_Right_Constant (0, (1, 0));
       sg_anti_left_d := Certify_Not_Anti_Left (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right (0, 0) 
  |}.

Definition sg_CS_certs_max : sg_CS_certificates (S := nat) 
:= {| 
     sg_CS_associative        := Assert_Associative 
   ; sg_CS_congruence         := Assert_Bop_Congruence 
   ; sg_CS_commutative        := Assert_Commutative 
   ; sg_CS_selective          := Assert_Selective 
   ; sg_CS_exists_id_d        := Certify_Exists_Id 0
   ; sg_CS_exists_ann_d       := Certify_Not_Exists_Ann 
   |}. 


Definition sg_CS_max : sg_CS (S := nat) 
:= {| 
     sg_CS_eqv   := eqv_eq_nat 
   ; sg_CS_bop   := bop_max
   ; sg_CS_certs := sg_CS_certs_max
   ; sg_CS_ast   := Ast_sg_CS_max
   |}. 


Definition sg_max : sg (S := nat) 
:= {| 
     sg_eq   := eqv_eq_nat 
   ; sg_bop   := bop_max
   ; sg_certs := sg_certs_max
   ; sg_ast   := Ast_sg_max
   |}. 

