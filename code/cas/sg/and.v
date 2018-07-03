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


(* from Compute (P2C_sg brel_eq_bool bop_and (sg_proofs_and)) *) 
Definition sg_certs_and : sg_certificates (S := bool)
:= {| 
       sg_associative := Assert_Associative ;
       sg_congruence := Assert_Bop_Congruence ;
       sg_commutative_d := Certify_Commutative ;
       sg_selective_d := Certify_Selective ;
       sg_idempotent_d := Certify_Idempotent ;
       sg_exists_id_d := Certify_Exists_Id  true;
       sg_exists_ann_d := Certify_Exists_Ann  false;
       sg_is_left_d := Certify_Not_Is_Left  (true, false);
       sg_is_right_d := Certify_Not_Is_Right  (false, true);
       sg_left_cancel_d := Certify_Not_Left_Cancellative 
                             (false, (false, true));
       sg_right_cancel_d := Certify_Not_Right_Cancellative 
                              (false, (false, true));
       sg_left_constant_d := Certify_Not_Left_Constant 
                               (true, (false, true));
       sg_right_constant_d := Certify_Not_Right_Constant 
                                (true, (false, true));
       sg_anti_left_d := Certify_Not_Anti_Left  (true, true);
       sg_anti_right_d := Certify_Not_Anti_Right  (true, true)
   |}. 



Definition sg_and : sg (S := bool)
:= {| 
     sg_eq   := eqv_eq_bool
   ; sg_bop   := bop_and
   ; sg_certs := sg_certs_and
   ; sg_ast   := Ast_sg_and
   |}. 

Definition sg_CS_and : @sg_CS bool
:= {| 
     sg_CS_eqv   := eqv_eq_bool
   ; sg_CS_bop   := bop_and
   ; sg_CS_certs := sg_CS_certs_and
   ; sg_CS_ast   := Ast_sg_CS_and 
   |}. 
