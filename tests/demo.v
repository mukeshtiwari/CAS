
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.construct_proofs. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cast.
Require Import CAS.a_code.decide.
Require Import CAS.a_code.a_cas.


Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.cast.
Require Import CAS.code.cas.
Require Import CAS.code.cas_records. 
Require Import CAS.code.cert_records. 
Require Import CAS.code.certificates. 

Require Import CAS.verify.proofs_to_certs. 


Open Scope string_scope. 
Open Scope nat_scope. 

Compute A2C_sg _ (A_sg_from_sg_CS _ A_sg_CS_and). 

Compute A2C_sg _ (A_sg_from_sg_CS _ A_sg_CS_or). 

Compute A2C_sg _ (A_sg_from_sg_CS _ A_sg_CS_min). 

Compute A2C_sg _ (A_sg_from_sg_CS _ A_sg_CS_max). 

Compute A2C_sg _ (A_sg_from_sg_C _ A_sg_C_times). 

Compute A2C_sg _ (A_sg_from_sg_CK _ A_sg_CK_plus). 

Compute A2C_sg _ (A_sg_concat _ A_eqv_eq_nat). 

Compute A2C_sg _ (A_sg_left _ A_eqv_eq_nat). 

Compute A2C_sg _ (A_sg_right _ A_eqv_eq_nat). 

Compute A2C_sg _ (A_sg_from_sg_CS _ (A_sg_CS_left_sum _ _ A_sg_CS_and A_sg_CS_or)). 

Compute A2C_sg _ (A_sg_product _ _ (A_sg_left _ A_eqv_eq_nat) (A_sg_right _ A_eqv_eq_nat)).

Compute A2C_sg _ (A_sg_llex _ _ A_sg_CS_and (A_sg_right _ A_eqv_eq_nat)).

Compute A2C_sg_CI _ (A_sg_CI_union_with_ann _ "N" A_eqv_eq_nat). 

Compute A2C_sg_CI _ (A_sg_CI_intersect_with_id _ "{}" A_eqv_eq_nat). 

Compute A2C_sg_sg_from_sg_CS_sg_CS_AD bool A_sg_CS_sg_CS_AD_and_or. 

Compute A2C_sg_sg_from_sg_CS_sg_CS_AD bool A_sg_CS_sg_CS_AD_or_and. 

Compute A2C_sg_sg_from_sg_CS_sg_CS_AD nat A_sg_CS_sg_CS_AD_max_min. 

Compute A2C_sg_sg_from_sg_CS_sg_CS_AD nat A_sg_CS_sg_CS_AD_min_max. 

Compute A2C_sg_sg_from_sg_CS_sg_CK_AD nat A_sg_CS_sg_CK_AD_min_plus. 

(* 
   A_sg_sg_product : ∀ (S T : Type),  A_sg_sg S -> A_sg_sg T -> A_sg_sg (S * T) 
*) 

(* 
   A_sg_C_sg_llex : ∀ S T : Type, A_sg_CS_sg S → A_sg_C_sg T → A_sg_C_sg (S * T)
*) 

(* 
   (min, +) lex (max, min) 
*) 
Compute A2C_sg_sg  (nat * nat) 
           (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex nat nat 
                (A_sg_CS_sg_from_sg_CS_sg_CK_AD nat (A_sg_CS_sg_CK_AD_min_plus))
                (A_sg_C_sg_from_sg_CS_sg_CS_AD nat (A_sg_CS_sg_CS_AD_max_min)))). 

(* 
   add_zero "infinity" (add_one "id" (min, +) lex (max, min)) 
*) 
Compute A2C_sg_sg  (with_constant (with_constant (nat * nat)))
         (A_sg_sg_add_zero  _ 
           (A_sg_sg_from_sg_C_sg _ 
             (A_sg_C_sg_add_one _   
                 (A_sg_C_sg_llex nat nat 
                   (A_sg_CS_sg_from_sg_CS_sg_CK_AD nat (A_sg_CS_sg_CK_AD_min_plus))
                   (A_sg_C_sg_from_sg_CS_sg_CS_AD nat (A_sg_CS_sg_CS_AD_max_min)))
                 "id"))
            "infinity"). 


(* 
   add_one "id" ((min, +) lex (add_zero "infinity" (max, min)))
*) 
Compute A2C_sg_sg  _ 
         (A_sg_sg_add_zero  _ 
           (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex _ _ 
                (A_sg_CS_sg_from_sg_CS_sg_CK_AD nat (A_sg_CS_sg_CK_AD_min_plus))
                (A_sg_C_sg_add_one _ (A_sg_C_sg_from_sg_CS_sg_CS_AD nat (A_sg_CS_sg_CS_AD_max_min))
                                     "id")))
            "infinity"). 

(* 
   ( (add_one "id" (min, +)) lex (add_zero "infinity" (max, min))
*) 
Compute A2C_sg_sg  _ 
           (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex _ _ 
                (A_sg_CS_sg_add_zero  _   
                     (A_sg_CS_sg_from_sg_CS_sg_CK_AD nat (A_sg_CS_sg_CK_AD_min_plus))
                     "infinity")
                (A_sg_C_sg_add_one _ 
                     (A_sg_C_sg_from_sg_CS_sg_CS_AD nat (A_sg_CS_sg_CS_AD_max_min))
                     "id"))). 
            





(* 
   (max, min) lex (min, +)
*) 
Compute A2C_sg_sg  (nat * nat) 
           (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex nat nat 
                (A_sg_CS_sg_from_sg_CS_sg_CS_AD nat (A_sg_CS_sg_CS_AD_max_min))
                (A_sg_C_sg_from_sg_CS_sg _ 
                  (A_sg_CS_sg_from_sg_CS_sg_CK_AD nat (A_sg_CS_sg_CK_AD_min_plus))))). 


(* 
   add_zero "infinity" (add_one "id"  (max, min) lex (min, +))
*) 
Compute A2C_sg_sg  _ 
         (A_sg_sg_add_zero  _  
           (A_sg_sg_from_sg_C_sg _ 
             (A_sg_C_sg_add_one _   
                (A_sg_C_sg_llex nat nat 
                  (A_sg_CS_sg_from_sg_CS_sg_CS_AD nat (A_sg_CS_sg_CS_AD_max_min))
                  (A_sg_C_sg_from_sg_CS_sg _ 
                    (A_sg_CS_sg_from_sg_CS_sg_CK_AD nat (A_sg_CS_sg_CK_AD_min_plus))))
                 "id"))
             "infinity"). 


(* 
   (max, min) lex add_zero(infinity, (min, +)) 
*) 
Compute A2C_sg_sg  _ 
           (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex _ _ 
                (A_sg_CS_sg_from_sg_CS_sg_CS_AD _ (A_sg_CS_sg_CS_AD_max_min))
                (A_sg_C_sg_from_sg_CS_sg _
                  (A_sg_CS_sg_add_zero  _    
                    (A_sg_CS_sg_from_sg_CS_sg_CK_AD _ (A_sg_CS_sg_CK_AD_min_plus))
                    "infinity")))). 

(*
Compute (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex _ _ 
                (A_sg_CS_sg_from_sg_CS_sg_CS_AD _ (A_sg_CS_sg_CS_AD_max_min))
                (A_sg_C_sg_from_sg_CS_sg _
                  (A_sg_CS_sg_add_zero  _    
                    (A_sg_CS_sg_from_sg_CS_sg_CK_AD _ (A_sg_CS_sg_CK_AD_min_plus))
                    "infinity")))). 
*) 

(* 
   (add_one infty_2 (max, min)) lex (add_zero(infty_1, (min, +)))
*) 
Compute A2C_sg_sg  _ 
           (A_sg_sg_from_sg_C_sg _ 
              (A_sg_C_sg_llex _ _ 
                  (A_sg_CS_sg_add_one  _    
                     (A_sg_CS_sg_from_sg_CS_sg_CS_AD _ (A_sg_CS_sg_CS_AD_max_min))
                    "infinity2")
                (A_sg_C_sg_from_sg_CS_sg _
                  (A_sg_CS_sg_add_zero  _    
                    (A_sg_CS_sg_from_sg_CS_sg_CK_AD _ (A_sg_CS_sg_CK_AD_min_plus))
                    "infinity1")))). 

             
