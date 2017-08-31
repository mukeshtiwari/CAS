Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.nat.

(* 
  Compute (P2C_sg brel_eq_nat bop_plus (sg_proofs_plus)). 
*) 
Definition sg_certs_plus : sg_certificates (S := nat)
:= {| 
       sg_associative := Assert_Associative;
       sg_congruence := Assert_Bop_Congruence;
       sg_commutative_d := Certify_Commutative;
       sg_selective_d := Certify_Not_Selective (1, 1);
       sg_idempotent_d := Certify_Not_Idempotent 1;
       sg_exists_id_d := Certify_Exists_Id 0;
       sg_exists_ann_d := Certify_Not_Exists_Ann;
       sg_is_left_d := Certify_Not_Is_Left (0, 1);
       sg_is_right_d := Certify_Not_Is_Right (1, 0);
       sg_left_cancel_d := Certify_Left_Cancellative;
       sg_right_cancel_d := Certify_Right_Cancellative;
       sg_left_constant_d := Certify_Not_Left_Constant (0, (0, 1));
       sg_right_constant_d := Certify_Not_Right_Constant (0, (0, 1));
       sg_anti_left_d := Certify_Not_Anti_Left (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right (0, 0)

   |}. 

Definition sg_CK_certs_plus : sg_CK_certificates (S := nat) 
:= {|
     sg_CK_associative    := Assert_Associative 
   ; sg_CK_congruence     := Assert_Bop_Congruence 
   ; sg_CK_commutative    := Assert_Commutative 
   ; sg_CK_left_cancel    := Assert_Left_Cancellative 
   ; sg_CK_exists_id_d    := Certify_Exists_Id 0 
   ; sg_CK_anti_left_d    := Certify_Not_Anti_Left (0, 0) 
   ; sg_CK_anti_right_d   := Certify_Not_Anti_Right (0, 0) 
   |}.


Definition sg_plus : sg (S := nat)
:= {| 
     sg_eq   := eqv_eq_nat 
   ; sg_bop   := bop_plus
   ; sg_certs := sg_certs_plus
   ; sg_ast   := Ast_sg_plus
   |}. 

Definition sg_CK_plus : sg_CK (S := nat) 
:= {| 
     sg_CK_eqv   := eqv_eq_nat 
   ; sg_CK_bop   := bop_plus
   ; sg_CK_certs := sg_CK_certs_plus
   ; sg_CK_ast   := Ast_sg_CK_plus 
   |}. 

