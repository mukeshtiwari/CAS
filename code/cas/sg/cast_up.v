Require Import CAS.code.basic_types. 

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.
Require Import CAS.code.ast.

Require Import CAS.code.cef. 

Definition sg_certs_from_sg_C_certs : ∀ {S : Type}, brel S -> binary_op S -> eqv_certificates (S := S) -> sg_C_certificates (S := S) -> sg_certificates (S := S)  
:= λ {S} r b eqvS sgS, 
let ntS := eqv_nontrivial eqvS in 
match certify_nontrivial_witness ntS, certify_nontrivial_negate ntS with 
| Certify_Witness s, Certify_Negate f => 
{|
  sg_associative      := Assert_Associative (S := S) 
; sg_congruence       := Assert_Bop_Congruence (S := S) 
; sg_commutative_d    := Certify_Commutative (S := S)  
; sg_selective_d      := sg_C_selective_d sgS    
; sg_is_left_d        := Certify_Not_Is_Left (cef_commutative_implies_not_is_left r b s f)
; sg_is_right_d       := Certify_Not_Is_Right (cef_commutative_implies_not_is_right r b s f)
; sg_idempotent_d     := sg_C_idempotent_d sgS    
; sg_exists_id_d      := sg_C_exists_id_d sgS    
; sg_exists_ann_d     := sg_C_exists_ann_d sgS    
; sg_left_cancel_d    := sg_C_left_cancel_d sgS    
; sg_right_cancel_d   := sg_C_right_cancel_d sgS    
; sg_left_constant_d  := sg_C_left_constant_d sgS
; sg_right_constant_d := sg_C_right_constant_d sgS
; sg_anti_left_d      := sg_C_anti_left_d sgS
; sg_anti_right_d     := sg_C_anti_right_d sgS
|}
end. 


Definition sg_from_sg_C: ∀ {S : Type},  sg_C (S := S) -> sg (S := S)  
:= λ {S} sg_C, 
   {| 
     sg_eq    := sg_C_eqv sg_C
   ; sg_bop   := sg_C_bop sg_C
   ; sg_certs := sg_certs_from_sg_C_certs 
                    (eqv_eq (sg_C_eqv sg_C)) 
                    (sg_C_bop sg_C) 
                    (eqv_certs (sg_C_eqv sg_C))
                    (sg_C_certs sg_C) 
   ; sg_ast   := Ast_sg_from_sg_C (sg_C_ast sg_C)
   |}. 



(*CC*)
Definition sg_C_certs_from_sg_CI_certs : ∀ {S : Type}, brel S -> binary_op S -> eqv_certificates (S := S) -> sg_CI_certificates (S := S) -> sg_C_certificates (S := S)  
:= λ {S} r b eqvS sgS, 
let ntS := eqv_nontrivial eqvS in 
match certify_nontrivial_witness ntS, certify_nontrivial_negate ntS with 
| Certify_Witness s, Certify_Negate f => 
{|
  sg_C_associative      := Assert_Associative (S := S) 
; sg_C_congruence       := Assert_Bop_Congruence (S := S) 
; sg_C_commutative      := Assert_Commutative (S := S) 
; sg_C_selective_d      := sg_CI_selective_d sgS    
; sg_C_idempotent_d     := Certify_Idempotent (S := S)  
; sg_C_exists_id_d      := sg_CI_exists_id_d sgS    
; sg_C_exists_ann_d     := sg_CI_exists_ann_d sgS    
; sg_C_left_cancel_d    := 
     Certify_Not_Left_Cancellative 
        (match sg_CI_selective_d sgS with 
        | Certify_Selective => 
             cef_selective_and_commutative_imply_not_left_cancellative r b s f
        | Certify_Not_Selective (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative b s1 s2
        end) 
; sg_C_right_cancel_d   := 
     Certify_Not_Right_Cancellative 
        (match sg_CI_selective_d sgS with 
        | Certify_Selective => 
             cef_selective_and_commutative_imply_not_right_cancellative r b s f
        | Certify_Not_Selective (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative b s1 s2
        end) 
; sg_C_left_constant_d  := 
     Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b s f)
; sg_C_right_constant_d := 
     Certify_Not_Right_Constant (cef_idempotent_and_commutative_imply_not_right_constant r b s f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left s)
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s)
|}
end. 

(*CC*)
Definition sg_C_from_sg_CI: ∀ {S : Type},  sg_CI (S := S) -> sg_C (S := S)  
:= λ {S} sgS, 
   {| 
     sg_C_eqv   := sg_CI_eqv sgS
   ; sg_C_bop   := sg_CI_bop sgS
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs  
                      (eqv_eq  (sg_CI_eqv  sgS)) 
                      (sg_CI_bop sgS) 
                      (eqv_certs (sg_CI_eqv sgS))
                      (sg_CI_certs sgS) 
   ; sg_C_ast   := Ast_sg_C_from_sg_CI (sg_CI_ast sgS)
   |}. 




(*CC*)
Definition sg_CI_certs_from_sg_CS_certs : ∀ {S : Type}, sg_CS_certificates (S := S) -> sg_CI_certificates (S := S) 
:= λ {S} sgS, 
{|
  sg_CI_associative        := Assert_Associative (S := S) 
; sg_CI_congruence         := Assert_Bop_Congruence (S := S) 
; sg_CI_commutative        := Assert_Commutative (S := S) 
; sg_CI_idempotent         := Assert_Idempotent (S := S) 
; sg_CI_selective_d        := Certify_Selective (S := S) 
; sg_CI_exists_id_d        := sg_CS_exists_id_d sgS    
; sg_CI_exists_ann_d       := sg_CS_exists_ann_d sgS    
|}. 

(*CC*)
Definition sg_CI_from_sg_CS: ∀ {S : Type},  sg_CS (S := S) -> sg_CI (S := S) 
:= λ {S} sgS, 
   {| 
     sg_CI_eqv   := sg_CS_eqv sgS
   ; sg_CI_bop   := sg_CS_bop sgS
   ; sg_CI_certs := sg_CI_certs_from_sg_CS_certs (sg_CS_certs sgS) 
   ; sg_CI_ast   := Ast_sg_CI_from_sg_CS (sg_CS_ast sgS)
   |}. 

(*CC*)
Definition sg_C_certs_from_sg_CK_certs : ∀ {S : Type}, brel S -> binary_op S -> eqv_certificates (S := S) -> sg_CK_certificates (S := S) -> sg_C_certificates (S := S) 
:= λ {S} r b eqvS sgS, 
let ntS := eqv_nontrivial eqvS in 
match certify_nontrivial_witness (S := S) ntS, certify_nontrivial_negate (S := S) ntS with 
| Certify_Witness s, Certify_Negate f => 
let ni := match sg_CK_exists_id_d sgS with 
          | Certify_Exists_Id i => cef_cancellative_and_exists_id_imply_not_idempotent r s i f
          | Certify_Not_Exists_Id => s 
          end 
in 
{|
  sg_C_associative      := Assert_Associative (S := S) 
; sg_C_congruence       := Assert_Bop_Congruence (S := S) 
; sg_C_commutative      := Assert_Commutative (S := S) 

; sg_C_idempotent_d     := Certify_Not_Idempotent (S := S) ni 
; sg_C_selective_d      := Certify_Not_Selective (S := S) 
                              (cef_not_idempotent_implies_not_selective ni) 

; sg_C_exists_id_d      := sg_CK_exists_id_d sgS
; sg_C_exists_ann_d     := Certify_Not_Exists_Ann (S := S) 

; sg_C_left_constant_d  := Certify_Not_Left_Constant (S := S) 
                              (cef_left_cancellative_implies_not_left_constant s f) 
; sg_C_right_constant_d := Certify_Not_Right_Constant (S := S) 
                              (cef_right_cancellative_implies_not_right_constant  s f) 

; sg_C_left_cancel_d    := Certify_Left_Cancellative (S := S) 
; sg_C_right_cancel_d   := Certify_Right_Cancellative (S := S) 
; sg_C_anti_left_d      := sg_CK_anti_left_d sgS 
; sg_C_anti_right_d     := sg_CK_anti_right_d sgS 
|}
end. 


(*CC*)
Definition sg_C_from_sg_CK: ∀ {S : Type},  sg_CK (S := S) -> sg_C (S := S)  
:= λ {S} sg, 
   {| 
     sg_C_eqv   := sg_CK_eqv sg
   ; sg_C_bop   := sg_CK_bop sg
   ; sg_C_certs := sg_C_certs_from_sg_CK_certs 
                      (eqv_eq (sg_CK_eqv sg))
                      (sg_CK_bop sg)
                      (eqv_certs (sg_CK_eqv sg)) 
                      (sg_CK_certs sg) 
   ; sg_C_ast   := Ast_sg_C_from_sg_CK (sg_CK_ast sg)
   |}. 




(* DERIVED UPCASTS *) 

Definition sg_from_sg_CI: ∀ {S : Type},  sg_CI (S := S) -> sg (S := S)  
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CI sgS).  

Definition sg_from_sg_CK: ∀ {S : Type},  sg_CK (S := S) -> sg (S := S)
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CK sgS).  

Definition sg_C_from_sg_CS: ∀ {S : Type},  sg_CS (S := S) -> sg_C (S := S)
:= λ {S} sgS, sg_C_from_sg_CI (sg_CI_from_sg_CS sgS ). 

Definition sg_from_sg_CS: ∀ {S : Type},  sg_CS (S := S) -> sg (S := S)
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CS sgS).  


Definition sg_certs_from_sg_CI_certs : ∀ {S : Type} (r : brel S) (eqv : eqv_certificates (S := S)) (b : binary_op S),
            sg_CI_certificates (S := S) -> sg_certificates (S := S)
:= λ {S} r eqv b sg_CI, sg_certs_from_sg_C_certs r b eqv (sg_C_certs_from_sg_CI_certs r b eqv sg_CI).

Definition sg_certs_from_sg_CS_certs : ∀ {S : Type} (r : brel S) (eqv : eqv_certificates (S := S)) (b : binary_op S),
            sg_CS_certificates (S := S) -> sg_certificates (S := S)
:= λ {S} r eqv b sg_CI, sg_certs_from_sg_CI_certs r eqv b (sg_CI_certs_from_sg_CS_certs sg_CI).

