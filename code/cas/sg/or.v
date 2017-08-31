Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.bool. 


Definition sg_CS_certs_or : sg_CS_certificates (S := bool)
:= {| 
     sg_CS_associative        := Assert_Associative  
   ; sg_CS_congruence         := Assert_Bop_Congruence  
   ; sg_CS_commutative        := Assert_Commutative  
   ; sg_CS_selective          := Assert_Selective  
   ; sg_CS_exists_id_d        := Certify_Exists_Id  false 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann  true
   |}. 




(* from Compute (P2C_sg brel_eq_bool bop_or (sg_proofs_or)) *) 
Definition sg_certs_or : sg_certificates (S := bool)
:= {| 
       sg_associative := Assert_Associative ;
       sg_congruence := Assert_Bop_Congruence ;
       sg_commutative_d := Certify_Commutative ;
       sg_selective_d := Certify_Selective ;
       sg_idempotent_d := Certify_Idempotent ;
       sg_exists_id_d := Certify_Exists_Id  false;
       sg_exists_ann_d := Certify_Exists_Ann  true;
       sg_is_left_d := Certify_Not_Is_Left  (false, true);
       sg_is_right_d := Certify_Not_Is_Right  (true, false);
       sg_left_cancel_d := Certify_Not_Left_Cancellative 
                             (true, (true, false));
       sg_right_cancel_d := Certify_Not_Right_Cancellative 
                              (true, (true, false));
       sg_left_constant_d := Certify_Not_Left_Constant 
                               (false, (true, false));
       sg_right_constant_d := Certify_Not_Right_Constant 
                                (false, (true, false));
       sg_anti_left_d := Certify_Not_Anti_Left  (true, true);
       sg_anti_right_d := Certify_Not_Anti_Right  (true, true)
   |}. 


Definition sg_or : sg (S := bool)
:= {| 
     sg_eq   := eqv_eq_bool
   ; sg_bop   := bop_or
   ; sg_certs := sg_certs_or
   ; sg_ast   := Ast_sg_or
   |}. 

Definition sg_CS_or : sg_CS (S := bool)
:= {| 
     sg_CS_eqv   := eqv_eq_bool
   ; sg_CS_bop   := bop_or
   ; sg_CS_certs := sg_CS_certs_or
   ; sg_CS_ast   := Ast_sg_CS_or 
   |}. 
