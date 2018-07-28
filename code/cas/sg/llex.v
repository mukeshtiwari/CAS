Require Import CAS.code.basic_types. 
Require Import CAS.code.combined.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.

Require Import CAS.code.cef. 
Require Import CAS.code.cas.eqv.product.

Definition check_commutative_llex : ∀ {S T : Type},  S -> @check_commutative T -> @check_commutative (S * T)
:= λ {S T} s cT,  
      match cT with 
      | Certify_Commutative              => Certify_Commutative 
      | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative ((s, t1), (s, t2))
      end. 


Definition check_idempotent_llex : ∀ {S T : Type}, S -> @check_idempotent T -> @check_idempotent (S * T)
:= λ {S T} s cT,  
      match cT with 
      | Certify_Idempotent        => Certify_Idempotent 
      | Certify_Not_Idempotent t1 => Certify_Not_Idempotent (s, t1) 
      end.

Definition check_selective_llex : ∀ {S T : Type}, S -> @check_selective T -> @check_selective (S * T)
:= λ {S T} s dT,  
     match dT with 
     | Certify_Selective              => Certify_Selective 
     | Certify_Not_Selective (t1, t2) => Certify_Not_Selective ((s, t1), (s, t2)) 
     end.


Definition check_exists_id_llex : ∀ {S T : Type}, 
             (check_exists_id (S := S)) -> (check_exists_id (S := T)) -> (check_exists_id (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t => Certify_Exists_Id  (s, t) 
      | Certify_Not_Exists_Id, _                 => Certify_Not_Exists_Id 
      | _, Certify_Not_Exists_Id                 => Certify_Not_Exists_Id 
      end. 

Definition check_exists_ann_llex : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := T)) -> (check_exists_ann (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann  (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann 
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann 
      end. 


Definition sg_certs_llex : ∀ {S T : Type},  
        brel S -> binary_op S -> 
        S -> (S -> S) -> 
        T -> (T -> T) -> 
        sg_CS_certificates (S := S) -> 
        sg_certificates (S := T) -> sg_certificates (S := (S * T))
:= λ {S T} rS bS s f t g cS cT,  
{|
  sg_associative      := Assert_Associative   
; sg_congruence       := Assert_Bop_Congruence   
; sg_commutative_d    := check_commutative_llex s (sg_commutative_d cT)
; sg_selective_d      := check_selective_llex s (sg_selective_d cT)
; sg_idempotent_d     := check_idempotent_llex s (sg_idempotent_d cT)
; sg_exists_id_d      := check_exists_id_llex (sg_CS_exists_id_d cS) (sg_exists_id_d cT)
; sg_exists_ann_d     := check_exists_ann_llex (sg_CS_exists_ann_d cS) (sg_exists_ann_d cT)

; sg_is_left_d        := Certify_Not_Is_Left (cef_bop_llex_not_is_left rS bS s f t)
; sg_is_right_d       := Certify_Not_Is_Right (cef_bop_llex_not_is_right rS bS s f t)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (cef_bop_llex_not_cancellative rS bS s f t g)
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (cef_bop_llex_not_cancellative rS bS s f t g)
; sg_left_constant_d  := Certify_Not_Left_Constant (cef_bop_llex_not_constant rS bS s f t g)
; sg_right_constant_d := Certify_Not_Right_Constant (cef_bop_llex_not_constant rS bS s f t g)
; sg_anti_left_d      := Certify_Not_Anti_Left (cef_bop_llex_not_anti_left rS bS s f t)
; sg_anti_right_d     := Certify_Not_Anti_Right (cef_bop_llex_not_anti_right rS bS s f t)
|}. 

Definition sg_C_certs_llex : ∀ {S T : Type} (rS : brel S) (bS : binary_op S), 
        S -> (S -> S) -> T -> (T -> T) -> sg_CS_certificates (S := S) -> sg_C_certificates (S := T) -> sg_C_certificates (S := (S * T)) 
:= λ {S T} rS bS s f t g cS cT,  
{|
  sg_C_associative   := Assert_Associative 
; sg_C_congruence    := Assert_Bop_Congruence   
; sg_C_commutative   := Assert_Commutative   
; sg_C_selective_d   := check_selective_llex s (sg_C_selective_d cT)
; sg_C_idempotent_d  := check_idempotent_llex s (sg_C_idempotent_d cT)
; sg_C_exists_id_d   := check_exists_id_llex (sg_CS_exists_id_d cS) (sg_C_exists_id_d cT)
; sg_C_exists_ann_d  := check_exists_ann_llex (sg_CS_exists_ann_d cS) (sg_C_exists_ann_d cT)
; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative (cef_bop_llex_not_cancellative rS bS s f t g)
; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative (cef_bop_llex_not_cancellative rS bS s f t g)
; sg_C_left_constant_d  := Certify_Not_Left_Constant (cef_bop_llex_not_constant rS bS s f t g)
; sg_C_right_constant_d := Certify_Not_Right_Constant (cef_bop_llex_not_constant rS bS s f t g)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_bop_llex_not_anti_left rS bS s f t)                            
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_bop_llex_not_anti_right rS bS s f t)
|}.

Definition sg_CI_certs_llex : ∀ {S T : Type} (rS : brel S) (bS : binary_op S), 
        S -> sg_CS_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S * T)) 
:= λ {S T} rS bS s cS cT,  
{|
  sg_CI_associative   := Assert_Associative   
; sg_CI_congruence    := Assert_Bop_Congruence   
; sg_CI_commutative   := Assert_Commutative   
; sg_CI_idempotent    := Assert_Idempotent   
; sg_CI_selective_d   := check_selective_llex s (sg_CI_selective_d cT)
; sg_CI_exists_id_d   := check_exists_id_llex (sg_CS_exists_id_d cS) (sg_CI_exists_id_d cT)
; sg_CI_exists_ann_d  := check_exists_ann_llex (sg_CS_exists_ann_d cS) (sg_CI_exists_ann_d cT)
|}.

Definition sg_CS_certs_llex : ∀ {S T : Type} (rS : brel S) (bS : binary_op S), 
        sg_CS_certificates (S := S) -> sg_CS_certificates (S := T) -> sg_CS_certificates (S := (S * T)) 
:= λ {S T} rS bS cS cT,  
{|
  sg_CS_associative   := Assert_Associative   
; sg_CS_congruence    := Assert_Bop_Congruence   
; sg_CS_commutative   := Assert_Commutative   
; sg_CS_selective     := Assert_Selective   
; sg_CS_exists_id_d   := check_exists_id_llex (sg_CS_exists_id_d cS) (sg_CS_exists_id_d cT)
; sg_CS_exists_ann_d  := check_exists_ann_llex (sg_CS_exists_ann_d cS) (sg_CS_exists_ann_d cT)
|}.

Definition sg_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg (S := T) -> sg (S := (S * T))
:= λ {S T} sgS sgT, 
   {| 
     sg_eq    := eqv_product (sg_CS_eqv sgS) (sg_eq sgT) 
   ; sg_bop   := bop_llex (eqv_eq (sg_CS_eqv sgS)) (sg_CS_bop sgS) (sg_bop sgT) 
   ; sg_certs := sg_certs_llex 
                   (eqv_eq (sg_CS_eqv sgS)) 
                   (sg_CS_bop sgS) 
                   (eqv_witness (sg_CS_eqv sgS)) (eqv_new (sg_CS_eqv sgS)) 
                   (eqv_witness (sg_eq sgT)) (eqv_new (sg_eq sgT)) 
                   (sg_CS_certs sgS) 
                   (sg_certs sgT) 
   ; sg_ast   := Ast_sg_llex (sg_CS_ast sgS, sg_ast sgT)
   |}. 

Definition sg_C_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg_C (S := T) -> sg_C (S := (S * T))
:= λ {S T} sgS sgT, 
      {| 
        sg_C_eqv     := eqv_product (sg_CS_eqv sgS) (sg_C_eqv sgT) 
      ; sg_C_bop    := bop_llex 
                          (eqv_eq (sg_CS_eqv sgS)) 
                          (sg_CS_bop sgS) 
                          (sg_C_bop sgT) 
      ; sg_C_certs := sg_C_certs_llex 
                          (eqv_eq (sg_CS_eqv sgS))
                          (sg_CS_bop sgS) 
                          (eqv_witness (sg_CS_eqv sgS)) (eqv_new (sg_CS_eqv sgS)) 
                          (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT))
                          (sg_CS_certs sgS) 
                          (sg_C_certs sgT) 
      ; sg_C_ast    := Ast_sg_C_llex (sg_CS_ast sgS, sg_C_ast sgT)  
      |}. 

Definition sg_CI_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg_CI (S := T) -> sg_CI (S := (S * T))
:= λ {S T} sgS sgT, 
      {| 
        sg_CI_eqv     := eqv_product (sg_CS_eqv sgS) (sg_CI_eqv sgT) 
      ; sg_CI_bop    := bop_llex 
                          (eqv_eq (sg_CS_eqv sgS)) 
                          (sg_CS_bop sgS) 
                          (sg_CI_bop sgT) 
      ; sg_CI_certs := sg_CI_certs_llex 
                          (eqv_eq (sg_CS_eqv sgS))
                          (sg_CS_bop sgS)
                          (eqv_witness (sg_CS_eqv sgS)) 
                          (sg_CS_certs sgS) 
                          (sg_CI_certs sgT) 
      ; sg_CI_ast    := Ast_sg_CI_llex (sg_CS_ast sgS, sg_CI_ast sgT)  
      |}. 

Definition sg_CS_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg_CS (S := T) -> sg_CS (S := (S * T))
:= λ {S T} sgS sgT, 
      {| 
        sg_CS_eqv    := eqv_product (sg_CS_eqv sgS) (sg_CS_eqv sgT) 
      ; sg_CS_bop    := bop_llex 
                          (eqv_eq (sg_CS_eqv sgS)) 
                          (sg_CS_bop sgS) 
                          (sg_CS_bop sgT) 
      ; sg_CS_certs := sg_CS_certs_llex 
                          (eqv_eq (sg_CS_eqv sgS))
                          (sg_CS_bop sgS) 
                          (sg_CS_certs sgS) 
                          (sg_CS_certs sgT) 
      ; sg_CS_ast    := Ast_sg_CS_llex (sg_CS_ast sgS, sg_CS_ast sgT)  
      |}. 

