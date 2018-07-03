Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.sum.

Definition check_exists_id_left_sum : ∀ {S T : Type}, @check_exists_id T -> @check_exists_id (S + T)
:= λ {S T} cT,  
      match cT with 
      | Certify_Exists_Id t    => Certify_Exists_Id (inr S t) 
      | Certify_Not_Exists_Id  => Certify_Not_Exists_Id
      end. 

Definition check_exists_ann_left_sum : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := (S + T)))
:= λ {S T} cS,  
      match cS with 
      | Certify_Exists_Ann s    => Certify_Exists_Ann (inl T s)
      | Certify_Not_Exists_Ann => Certify_Not_Exists_Ann 
      end.

Definition check_idempotent_left_sum : ∀ {S T : Type}, 
             (check_idempotent (S := S)) -> 
             (check_idempotent (S := T)) -> 
                (check_idempotent (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent (inl _ s1)
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent (inr _ t1)
      end. 


Definition check_selective_left_sum : ∀ {S T : Type}, 
             (check_selective (S := S)) -> 
             (check_selective (S := T)) -> 
                (check_selective (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Selective, Certify_Selective => Certify_Selective 
      | Certify_Not_Selective (s1, s2), _    => Certify_Not_Selective ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Selective (t1, t2)    => Certify_Not_Selective ((inr _ t1), (inr _ t2))
      end. 

Definition check_commutative_left_sum : ∀ {S T : Type}, 
             (check_commutative (S := S)) -> 
             (check_commutative (S := T)) -> 
                (check_commutative (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative 
      | Certify_Not_Commutative (s1, s2), _  => Certify_Not_Commutative ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Commutative (t1, t2)  => Certify_Not_Commutative ((inr _ t1), (inr _ t2))
      end. 




Definition sg_certs_left_sum : ∀ {S T : Type},  S -> (S -> S) -> T -> (T -> T) -> @sg_certificates S -> @sg_certificates T -> @sg_certificates (S + T) 
:= λ {S T} s f t g cS cT,  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := check_commutative_left_sum 
                            (sg_commutative_d cS) 
                            (sg_commutative_d cT)
; sg_idempotent_d     := check_idempotent_left_sum 
                            (sg_idempotent_d cS) 
                            (sg_idempotent_d cT)
; sg_selective_d      := check_selective_left_sum 
                            (sg_selective_d cS) 
                            (sg_selective_d cT)
; sg_is_left_d        := Certify_Not_Is_Left (inr t, inl s) 
; sg_is_right_d       := Certify_Not_Is_Right (inl s, inr t) 
; sg_exists_id_d      := check_exists_id_left_sum (sg_exists_id_d  cT)
; sg_exists_ann_d     := check_exists_ann_left_sum (sg_exists_ann_d cS)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (inl s, (inr t, inr (g t)))
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (inl s, (inr t, inr (g t)))
; sg_left_constant_d  := Certify_Not_Left_Constant (inr t, (inl s, inl (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant (inr t, (inl s, inl (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left (inl s, inr t) 
; sg_anti_right_d     := Certify_Not_Anti_Right (inl s, inr t) 
|}.

Definition sg_C_certs_left_sum : ∀ {S T : Type}, S -> (S -> S) -> T -> (T -> T) -> @sg_C_certificates S -> @sg_C_certificates T -> @sg_C_certificates (S + T) 
:= λ {S T} s f t g cS cT,  
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence  
; sg_C_commutative      := Assert_Commutative  
; sg_C_idempotent_d     := check_idempotent_left_sum 
                            (sg_C_idempotent_d cS) 
                            (sg_C_idempotent_d cT)
; sg_C_selective_d      := check_selective_left_sum 
                            (sg_C_selective_d cS) 
                            (sg_C_selective_d cT)
; sg_C_exists_id_d      := check_exists_id_left_sum (sg_C_exists_id_d cT)
; sg_C_exists_ann_d     := check_exists_ann_left_sum (sg_C_exists_ann_d cS)
; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative (inl s, (inr t, inr (g t)))
; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative (inl s, (inr t, inr (g t)))
; sg_C_left_constant_d  := Certify_Not_Left_Constant (inr t, (inl s, inl (f s)))
; sg_C_right_constant_d := Certify_Not_Right_Constant (inr t, (inl s, inl (f s)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left (inl s, inr t) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (inl s, inr t) 
|}.


Definition sg_CI_certs_left_sum : ∀ {S T : Type},  sg_CI_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S + T)) 
:= λ {S T} cS cT,  
{|
  sg_CI_associative  := Assert_Associative   
; sg_CI_congruence   := Assert_Bop_Congruence  
; sg_CI_commutative  := Assert_Commutative  
; sg_CI_idempotent   := Assert_Idempotent  
; sg_CI_selective_d  := check_selective_left_sum (sg_CI_selective_d cS) (sg_CI_selective_d cT)
; sg_CI_exists_id_d  := check_exists_id_left_sum (sg_CI_exists_id_d cT)
; sg_CI_exists_ann_d := check_exists_ann_left_sum (sg_CI_exists_ann_d cS)
|}.

Definition sg_CS_certs_left_sum : ∀ {S T : Type},  sg_CS_certificates (S := S) -> sg_CS_certificates (S := T) -> sg_CS_certificates (S := (S + T)) 
:= λ {S T} cS cT,  
{|
  sg_CS_associative  := Assert_Associative   
; sg_CS_congruence   := Assert_Bop_Congruence  
; sg_CS_commutative  := Assert_Commutative  
; sg_CS_selective    := Assert_Selective  
; sg_CS_exists_id_d  := check_exists_id_left_sum (sg_CS_exists_id_d cT)
; sg_CS_exists_ann_d := check_exists_ann_left_sum (sg_CS_exists_ann_d cS)
|}.

Definition sg_left_sum : ∀ {S T : Type},  sg (S := S) -> sg (S := T) -> sg (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_eq     := eqv_sum (sg_eq sgS) (sg_eq sgT) 
   ; sg_bop    := bop_left_sum (sg_bop sgS) (sg_bop sgT) 
   ; sg_certs := sg_certs_left_sum 
                    (eqv_witness (sg_eq sgS)) (eqv_new (sg_eq sgS))
                    (eqv_witness (sg_eq sgT)) (eqv_new (sg_eq sgT)) 
                    (sg_certs sgS) 
                    (sg_certs sgT) 
   ; sg_ast    := Ast_sg_left_sum (sg_ast sgS, sg_ast sgT)
   |}. 


Definition sg_C_left_sum : ∀ {S T : Type},  sg_C (S := S) -> sg_C (S := T) -> sg_C (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_C_eqv       := eqv_sum (sg_C_eqv sgS) (sg_C_eqv sgT) 
   ; sg_C_bop       := bop_left_sum (sg_C_bop sgS) (sg_C_bop sgT) 
   ; sg_C_certs    := sg_C_certs_left_sum 
                           (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS)) 
                           (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT)) 
                           (sg_C_certs sgS) 
                           (sg_C_certs sgT) 
   ; sg_C_ast       := Ast_sg_C_left_sum (sg_C_ast sgS, sg_C_ast sgT)
   |}. 

Definition sg_CI_left_sum : ∀ {S T : Type},  sg_CI (S := S) -> sg_CI (S := T) -> sg_CI (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CI_eqv       := eqv_sum (sg_CI_eqv sgS) (sg_CI_eqv sgT) 
   ; sg_CI_bop       := bop_left_sum (sg_CI_bop sgS) (sg_CI_bop sgT) 
   ; sg_CI_certs    := sg_CI_certs_left_sum (sg_CI_certs sgS) (sg_CI_certs sgT) 
   ; sg_CI_ast       := Ast_sg_CI_left_sum (sg_CI_ast sgS, sg_CI_ast sgT)
   |}. 

Definition sg_CS_left_sum : ∀ {S T : Type},  sg_CS (S := S) -> sg_CS (S := T) -> sg_CS (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CS_eqv       := eqv_sum (sg_CS_eqv sgS) (sg_CS_eqv sgT) 
   ; sg_CS_bop       := bop_left_sum (sg_CS_bop sgS) (sg_CS_bop sgT) 
   ; sg_CS_certs     := sg_CS_certs_left_sum (sg_CS_certs sgS) (sg_CS_certs sgT) 
   ; sg_CS_ast       := Ast_sg_CS_left_sum (sg_CS_ast sgS, sg_CS_ast sgT)
   |}. 
