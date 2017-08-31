Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.nat.

(* 
  Compute (P2C_sg brel_eq_nat bop_times (sg_proofs_times)). 
*) 
Definition sg_certs_times : sg_certificates (S := nat)
:= {| 
       sg_associative := Assert_Associative;
       sg_congruence := Assert_Bop_Congruence;
       sg_commutative_d := Certify_Commutative;
       sg_selective_d := Certify_Not_Selective (2, 2);
       sg_idempotent_d := Certify_Not_Idempotent 2;
       sg_exists_id_d := Certify_Exists_Id 1;
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


Definition sg_C_certs_times : sg_C_certificates (S := nat) 
:= {|
     sg_C_associative    := Assert_Associative 
   ; sg_C_congruence     := Assert_Bop_Congruence 
   ; sg_C_commutative    := Assert_Commutative 
   ; sg_C_selective_d    := Certify_Not_Selective (2, 2)
   ; sg_C_idempotent_d   := Certify_Not_Idempotent 2
   ; sg_C_exists_id_d    := Certify_Exists_Id 1 
   ; sg_C_exists_ann_d   := Certify_Exists_Ann 0
   ; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative (0, (0, 1))
   ; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative (0, (0, 1))
   ; sg_C_left_constant_d  := Certify_Not_Left_Constant  (1, (0, 1))
   ; sg_C_right_constant_d := Certify_Not_Right_Constant (1, (0, 1))
   ; sg_C_anti_left_d      := Certify_Not_Anti_Left (0, 0)
   ; sg_C_anti_right_d     := Certify_Not_Anti_Right (0, 0)
   |}.



Definition sg_times : sg (S := nat) 
:= {| 
     sg_eq   := eqv_eq_nat 
   ; sg_bop   := bop_times
   ; sg_certs := sg_certs_times
   ; sg_ast   := Ast_sg_times
   |}. 

Definition sg_C_times : sg_C (S := nat) 
:= {| 
     sg_C_eqv   := eqv_eq_nat 
   ; sg_C_bop   := bop_times
   ; sg_C_certs := sg_C_certs_times
   ; sg_C_ast   := Ast_sg_C_times
   |}. 
