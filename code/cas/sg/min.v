Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.nat.

(* 
  Compute (P2C_sg brel_eq_nat bop_min (sg_proofs_min)). 
*) 
Definition sg_certs_min : sg_certificates (S := nat)
:= {| 
       sg_associative := Assert_Associative;
       sg_congruence := Assert_Bop_Congruence;
       sg_commutative_d := Certify_Commutative;
       sg_selective_d := Certify_Selective;
       sg_idempotent_d := Certify_Idempotent;
       sg_exists_id_d := Certify_Not_Exists_Id;
       sg_exists_ann_d := Certify_Exists_Ann 0;
       sg_is_left_d := Certify_Not_Is_Left (1, 0);
       sg_is_right_d := Certify_Not_Is_Right (0, 1);
       sg_left_cancel_d := Certify_Not_Left_Cancellative (0, (0, 1));
       sg_right_cancel_d := Certify_Not_Right_Cancellative (0, (0, 1));
       sg_left_constant_d := Certify_Not_Left_Constant (1, (0, 1));
       sg_right_constant_d := Certify_Not_Right_Constant (1, (0, 1));
       sg_anti_left_d := Certify_Not_Anti_Left (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right (0, 0) 
   |}. 

Definition sg_CS_certs_min : sg_CS_certificates (S := nat) 
:= {|
     sg_CS_associative        := Assert_Associative 
   ; sg_CS_congruence         := Assert_Bop_Congruence 
   ; sg_CS_commutative        := Assert_Commutative 
   ; sg_CS_selective          := Assert_Selective 
   ; sg_CS_exists_id_d        := Certify_Not_Exists_Id 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann 0
   |}. 


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
