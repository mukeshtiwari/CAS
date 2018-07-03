
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.bool.
Require Import CAS.a_code.a_cas.eqv.nat. 
Require Import CAS.a_code.a_cas.eqv.add_constant.
Require Import CAS.a_code.a_cas.eqv.list.
Require Import CAS.a_code.a_cas.eqv.product.
Require Import CAS.a_code.a_cas.eqv.sum.

Require Import CAS.a_code.a_cas.sg.add_ann.
Require Import CAS.a_code.a_cas.sg.add_id.        
Require Import CAS.a_code.a_cas.sg.and.
Require Import CAS.a_code.a_cas.sg.cast_up.
Require Import CAS.a_code.a_cas.sg.concat.
Require Import CAS.a_code.a_cas.sg.left_sum.
Require Import CAS.a_code.a_cas.sg.left.
Require Import CAS.a_code.a_cas.sg.llex.
Require Import CAS.a_code.a_cas.sg.max.
Require Import CAS.a_code.a_cas.sg.min.
Require Import CAS.a_code.a_cas.sg.or.
Require Import CAS.a_code.a_cas.sg.plus.
Require Import CAS.a_code.a_cas.sg.product.
Require Import CAS.a_code.a_cas.sg.right_sum.
Require Import CAS.a_code.a_cas.sg.right.
Require Import CAS.a_code.a_cas.sg.times.

Require Import CAS.a_code.a_cas.bs.add_one.
Require Import CAS.a_code.a_cas.bs.add_zero.
Require Import CAS.a_code.a_cas.bs.and_or.
Require Import CAS.a_code.a_cas.bs.dual. 
Require Import CAS.a_code.a_cas.bs.left_sum. 
Require Import CAS.a_code.a_cas.bs.llex_product. 
Require Import CAS.a_code.a_cas.bs.max_min. 
Require Import CAS.a_code.a_cas.bs.max_plus.
Require Import CAS.a_code.a_cas.bs.min_max.
Require Import CAS.a_code.a_cas.bs.min_plus.
Require Import CAS.a_code.a_cas.bs.or_and.
Require Import CAS.a_code.a_cas.bs.product. 
Require Import CAS.a_code.a_cas.bs.right_sum. 

Require Import CAS.verify.eqv_proofs_to_certs.
Require Import CAS.verify.sg_proofs_to_certs. 
Require Import CAS.verify.bs_proofs_to_certs. 

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records. 


Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records. 

Require Import CAS.code.bs_certificates.
Require Import CAS.code.bs_cert_records.
Require Import CAS.code.bs_records. 

Open Scope string_scope.


Check A_distributive_lattice_add_one.
Check A_distributive_lattice_add_zero.

Check A_lattice_add_one.
Check A_lattice_add_zero.

Check A_dioid_add_zero.

Check A_semiring_add_zero.

Check A_bs_add_one.
Check A_bs_add_zero.


Check A_distributive_lattice_and_or.
Check A_distributive_lattice_or_and. 
Check A_distributive_lattice_min_max. 
Check A_distributive_lattice_max_min. 
Check A_dioid_max_plus.
Check A_dioid_min_plus. 

Check A_lattice_dual.

Check A_bs_left_sum.
Check A_lattice_left_sum. 
Check A_distributive_lattice_left_sum. 

Check A_bs_product.
Check A_semiring_product.
Check A_dioid_product.
Check A_distributive_lattice_product.
Check A_lattice_product. 

Check A_bs_C_llex_product.
Check A_bs_CS_llex_product.


Compute A2C_dioid _ (A_dioid_min_plus).

Compute A2C_distributive_lattice _ (A_distributive_lattice_max_min). 







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
