Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.  
Require Import CAS.code.cef.  
Require Import CAS.code.ast. 
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.sg_certificates.
Require Import CAS.code.bs_certificates.
Require Import CAS.code.sg_cert_records. 
Require Import CAS.code.sg_records. 


(* DOWNCASTS *) 


Definition sg_C_certs_option_from_sg_certs : ∀ {S : Type}, sg_certificates (S := S) -> option (sg_C_certificates (S := S)) 
:= λ {S} sgS, 
   match sg_commutative_d sgS with 
   | Certify_Commutative => Some
      {|
        sg_C_associative      := Assert_Associative (S := S) 
      ; sg_C_congruence       := Assert_Bop_Congruence (S := S) 
      ; sg_C_commutative      := Assert_Commutative (S := S) 
      ; sg_C_selective_d      := sg_selective_d sgS    
      ; sg_C_idempotent_d     := sg_idempotent_d  sgS    
      ; sg_C_exists_id_d      := sg_exists_id_d  sgS    
      ; sg_C_exists_ann_d     := sg_exists_ann_d  sgS   
      ; sg_C_left_cancel_d    := sg_left_cancel_d  sgS    
      ; sg_C_right_cancel_d   := sg_right_cancel_d  sgS    
      ; sg_C_left_constant_d  := sg_left_constant_d  sgS
      ; sg_C_right_constant_d := sg_right_constant_d  sgS
      ; sg_C_anti_left_d      := sg_anti_left_d   sgS
      ; sg_C_anti_right_d     := sg_anti_right_d  sgS
     |}
   | _ => None
   end . 


Definition sg_C_option_from_sg: ∀ {S : Type},  sg (S := S) -> option (sg_C (S := S)) 
:= λ {S} sgS, 
   match sg_C_certs_option_from_sg_certs (sg_certs sgS) with 
   | None => None
   | Some c => Some
      {| 
        sg_C_eqv   := sg_eq sgS
      ; sg_C_bop   := sg_bop sgS
      ; sg_C_certs := c 
      ; sg_C_ast   := Ast_sg_C_from_sg (sg_ast sgS)
      |}
   end. 



Definition sg_CI_certs_option_from_sg_C_certs : ∀ {S : Type}, sg_C_certificates (S := S) -> option (sg_CI_certificates (S := S)) 
:= λ {S} sg_CS, 
   match sg_C_idempotent_d sg_CS with 
   | Certify_Idempotent => Some
      {|
        sg_CI_associative        := Assert_Associative (S := S) 
      ; sg_CI_congruence         := Assert_Bop_Congruence (S := S) 
      ; sg_CI_commutative        := Assert_Commutative (S := S) 
      ; sg_CI_idempotent         := Assert_Idempotent (S := S) 
      ; sg_CI_selective_d        := sg_C_selective_d sg_CS    
      ; sg_CI_exists_id_d        := sg_C_exists_id_d sg_CS    
      ; sg_CI_exists_ann_d       := sg_C_exists_ann_d sg_CS    
     |}
   | _ => None
   end. 


Definition sg_CI_option_from_sg_C: ∀ {S : Type},  sg_C (S := S) -> option (sg_CI (S := S)) 
:= λ {S} sg_CS, 
   match sg_CI_certs_option_from_sg_C_certs (sg_C_certs sg_CS) with 
   | None => None
   | Some certs => Some
      {| 
        sg_CI_eqv   := sg_C_eqv sg_CS
      ; sg_CI_bop   := sg_C_bop sg_CS
      ; sg_CI_certs := certs 
      ; sg_CI_ast   := Ast_sg_CI_from_sg_C (sg_C_ast sg_CS)
      |}
   end. 


Definition sg_CS_certs_option_from_sg_CI_certs : ∀ {S : Type}, sg_CI_certificates (S := S) -> option (sg_CS_certificates (S := S)) 
:= λ {S} sg_CIS, 
   match sg_CI_selective_d sg_CIS with 
   | Certify_Selective => Some
      {|
        sg_CS_associative        := Assert_Associative (S := S) 
      ; sg_CS_congruence         := Assert_Bop_Congruence (S := S) 
      ; sg_CS_commutative        := Assert_Commutative (S := S) 
      ; sg_CS_selective          := Assert_Selective (S := S) 
      ; sg_CS_exists_id_d        := sg_CI_exists_id_d sg_CIS    
      ; sg_CS_exists_ann_d       := sg_CI_exists_ann_d sg_CIS    
     |}
   | _ => None
   end . 



Definition sg_CS_option_from_sg_CI: ∀ {S : Type},  sg_CI (S := S) -> option (sg_CS (S := S)) 
:= λ {S} sg_CIS, 
   match sg_CS_certs_option_from_sg_CI_certs  (sg_CI_certs sg_CIS) with 
   | None => None
   | Some certs => Some
      {| 
        sg_CS_eqv   := sg_CI_eqv sg_CIS
      ; sg_CS_bop   := sg_CI_bop sg_CIS
      ; sg_CS_certs := certs 
      ; sg_CS_ast   := Ast_sg_CS_from_sg_CI (sg_CI_ast sg_CIS)
      |}
   end. 


Definition sg_CK_certs_option_from_sg_C_certs : ∀ {S : Type}, sg_C_certificates (S := S) -> option (sg_CK_certificates (S := S)) 
:= λ {S} sgS, 
   match sg_C_left_cancel_d sgS with 
   | Certify_Left_Cancellative => Some
      {|
        sg_CK_associative        := sg_C_associative sgS    
      ; sg_CK_congruence         := sg_C_congruence sgS    
      ; sg_CK_commutative        := sg_C_commutative sgS    
      ; sg_CK_left_cancel        := Assert_Left_Cancellative (S := S)
      ; sg_CK_exists_id_d        := sg_C_exists_id_d sgS    
      ; sg_CK_anti_left_d        := sg_C_anti_left_d sgS   
      ; sg_CK_anti_right_d       := sg_C_anti_right_d sgS   
     |}
   |  _ => None
   end . 


Definition sg_CK_option_from_sg_C: ∀ {S : Type},  sg_C (S := S) -> option (sg_CK (S := S)) 
:= λ {S} sgS, 
   match sg_CK_certs_option_from_sg_C_certs (sg_C_certs sgS) with 
   | None => None
   | Some c => Some
      {| 
        sg_CK_eqv         := sg_C_eqv sgS
      ; sg_CK_bop         := sg_C_bop sgS
      ; sg_CK_certs       := c
      ; sg_CK_ast         := Ast_sg_CK_from_sg_C (sg_C_ast sgS)
      |}
   end. 



Definition sg_CS_certs_option_from_sg_certs : ∀ {S : Type},  sg_certificates (S := S) -> option (sg_CS_certificates (S := S)) 
:= λ {S} sgS, 
   match sg_C_certs_option_from_sg_certs sgS with 
   | None => None
   | Some sgC => 
      match sg_CI_certs_option_from_sg_C_certs sgC with 
      | None => None
      | Some sgCI => sg_CS_certs_option_from_sg_CI_certs sgCI 
      end 
   end. 

(* DERIVED DOWNCASTS *) 

Definition sg_CI_option_from_sg: ∀ {S : Type},  sg (S := S) -> option (sg_CI (S := S)) 
:= λ {S} sgS, 
   match sg_C_option_from_sg sgS with 
   | None => None
   | Some sgS => sg_CI_option_from_sg_C sgS 
   end. 


Definition sg_CK_option_from_sg: ∀ {S : Type},  sg (S := S) -> option (sg_CK (S := S)) 
:= λ {S} sgS, 
   match sg_C_option_from_sg sgS with 
   | None => None
   | Some sgS => sg_CK_option_from_sg_C sgS 
   end. 


Definition sg_CS_option_from_sg_C : ∀ {S : Type},  sg_C (S := S) -> option (sg_CS (S := S)) 
:= λ {S} sgS, 
   match sg_CI_option_from_sg_C sgS with 
   | None => None
   | Some sgS => sg_CS_option_from_sg_CI sgS 
   end. 


Definition sg_CS_option_from_sg: ∀ {S : Type},  sg (S := S) -> option (sg_CS (S := S)) 
:= λ {S} sgS, 
   match sg_CI_option_from_sg sgS with 
   | None => None
   | Some sgS => sg_CS_option_from_sg_CI sgS 
   end. 



