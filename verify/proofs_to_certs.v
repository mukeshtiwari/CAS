Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.cas_records.
Require Import CAS.theory.properties.    (* ~~ certificates *) 
Require Import CAS.a_code.proof_records. (* ~~ cert_records *) 
Require Import CAS.a_code.a_cas_records. (* ~~ cas_records  *) 
Require Import CAS.a_code.a_cast. 
(*
 *  PROOFS to CERTS 
 *
 *
 *
 *
 *
*) 

Definition p2c_witness : ∀ (S : Type) (r : brel S),
           brel_witness S r → certify_witness S 
:= λ S r nt, Certify_Witness S (projT1 nt). 
(* 
   match nt with 
   | existT s _ => Certify_Witness S s
   end. 
*) 
Definition p2c_negate : ∀ (S : Type) (r : brel S),
           brel_negate S r → certify_negate S 
:= λ S r nt, Certify_Negate S (projT1 nt). 
(* 
   match nt with 
   | existT f _ => Certify_Negate S f
   end. 
*) 

Definition p2c_nontrivial : ∀ (S : Type) (r : brel S),
           brel_nontrivial S r → assert_nontrivial S 
:= λ S r nt, 
{|
  certify_nontrivial_witness  := p2c_witness S r (brel_nontrivial_witness S r nt)
; certify_nontrivial_negate := p2c_negate S r (brel_nontrivial_negate S r nt)
|}.  


Definition P2C_eqv : ∀ (S : Type) (r : brel S), eqv_proofs S r -> eqv_certificates S 
:= λ S r P,
  {| 
     eqv_nontrivial     := p2c_nontrivial S r (A_eqv_nontrivial S r P)
    ; eqv_congruence    := Assert_Brel_Congruence S
    ; eqv_reflexive     := Assert_Reflexive S
    ; eqv_symmetric     := Assert_Symmetric S
    ; eqv_transitive    := Assert_Transitive S
  |}.


Definition A2C_eqv : ∀ (S : Type), A_eqv S -> eqv S 
:= λ S E,
{| 
  eqv_eq      := A_eqv_eq S E
; eqv_certs   := P2C_eqv S (A_eqv_eq S E) (A_eqv_proofs S E)
; eqv_data    := A_eqv_data S E
; eqv_rep     := A_eqv_rep S E
; eqv_ast     := A_eqv_ast S E
|}. 


Definition p2c_total_check : ∀ (S : Type) (lte : brel S), 
       brel_total_decidable S lte -> check_total S 
:= λ S lte d, 
   match d with 
   | inl _             => Certify_Total S
(*
   | inr (existT (s, t) _ ) => Certify_Not_Total S (s, t)
*) 
   | inr p => Certify_Not_Total S (projT1 p)   
   end. 


Definition p2c_exists_id_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_id_decidable S r b -> check_exists_id S 
:= λ S eq b d, 
   match d with 
(*   | inl (existT s _) => Certify_Exists_Id S s *) 
   | inl p => Certify_Exists_Id S (projT1 p)
   | inr _ => Certify_Not_Exists_Id S 
   end. 

Definition p2c_exists_ann_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_ann_decidable S r b -> check_exists_ann S 
:= λ S eq b d, 
   match d with 
(*   | inl (existT s _) => Certify_Exists_Ann S s *) 
   | inl p => Certify_Exists_Ann S (projT1 p)
   | inr _ => Certify_Not_Exists_Ann S 
   end. 


Definition p2c_commutative_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_commutative_decidable S r b -> check_commutative S 
:= λ S eq b d, 
   match d with 
   | inl _             => Certify_Commutative S
(* 
   | inr (existT (s, t) _) => Certify_Not_Commutative S (s, t)
*) 
   | inr p => Certify_Not_Commutative S (projT1 p) 
   end. 

Definition p2c_idempotent_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_idempotent_decidable S r b -> check_idempotent S 
:= λ S eq b d, 
   match d with 
   | inl _             => Certify_Idempotent S
(* 
   | inr (existT s _ ) => Certify_Not_Idempotent S s
*) 
   | inr p  => Certify_Not_Idempotent S (projT1 p) 
   end. 

Definition p2c_selective_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_selective_decidable S r b -> check_selective S 
:= λ S eq b d, 
   match d with 
   | inl _                        => Certify_Selective S
(*   | inr (existT (s, t) _ ) => Certify_Not_Selective S (s, t) *) 
   | inr p => Certify_Not_Selective S (projT1 p)
   end. 

Definition p2c_is_left_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_is_left_decidable S r b -> check_is_left S 
:= λ S eq b d, 
   match d with 
   | inl _                        => Certify_Is_Left S
(*   | inr (existT (s, t) _ ) => Certify_Not_Is_Left S (s, t) *) 
   | inr p => Certify_Not_Is_Left S (projT1 p) 
   end. 

Definition p2c_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_is_left S r b -> assert_not_is_left S 
:= λ S eq b d, Assert_Not_Is_Left S (projT1 d). 
(*
   match d with 
   | (existT (s, t) _ ) => Assert_Not_Is_Left S (s, t)
   end. 
*) 

Definition p2c_is_right_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_is_right_decidable S r b -> check_is_right S 
:= λ S eq b d, 
   match d with 
   | inl _                  => Certify_Is_Right S
(*   | inr (existT (s, t) _ ) => Certify_Not_Is_Right S (s, t) *) 
   | inr p => Certify_Not_Is_Right S (projT1 p) 
   end. 

Definition p2c_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_is_right S r b -> assert_not_is_right S 
:= λ S eq b d, Assert_Not_Is_Right S (projT1 d). 
(* 
   match d with 
   | existT (s, t) _  => Assert_Not_Is_Right S (s, t)
   end. 
*) 

Definition p2c_left_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b1 b2 -> check_left_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive S 
(*   | inr (existT (s, (t, u)) _) => Certify_Not_Left_Distributive S (s, (t, u)) *) 
   | inr p => Certify_Not_Left_Distributive S (projT1 p) 
   end. 

Definition p2c_right_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_right_distributive_decidable S r b1 b2 -> check_right_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Distributive S 
(*   | inr (existT (s, (t, u)) _) => Certify_Not_Right_Distributive S (s, (t, u)) *) 
   | inr p => Certify_Not_Right_Distributive S (projT1 p)
   end. 

Definition p2c_plus_id_equals_times_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann_decidable S r b1 b2 -> check_plus_id_equals_times_ann S 
:= λ S r b1 b2 d, 
   match d with 
   | inl _ => Certify_Plus_Id_Equals_Times_Ann S 
   | inr _ => Certify_Not_Plus_Id_Equals_Times_Ann S 
   end. 

Definition p2c_times_id_equals_plus_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann_decidable S r b2 b1 -> check_times_id_equals_plus_ann S
:= λ S r b1 b2 d, 
   match d with 
   | inl _ => Certify_Times_Id_Equals_Plus_Ann S 
   | inr _ => Certify_Not_Times_Id_Equals_Plus_Ann S 
   end. 



Definition p2c_anti_left_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_anti_left_decidable S r b -> check_anti_left S 
:= λ S eq b d, 
   match d with 
   | inl _                  => Certify_Anti_Left S 
(*   | inr (existT (s, t) _ ) => Certify_Not_Anti_Left S (s, t) *) 
   | inr p => Certify_Not_Anti_Left S (projT1 p)
   end. 


Definition p2c_anti_right_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_anti_right_decidable S r b -> check_anti_right S 
:= λ S eq b d, 
   match d with 
   | inl _                  => Certify_Anti_Right S 
(*   | inr (existT (s, t) _ ) => Certify_Not_Anti_Right S (s, t) *) 
   | inr p => Certify_Not_Anti_Right S (projT1 p) 
   end. 


Definition p2c_left_constant_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_left_constant_decidable S r b -> check_left_constant S 
:= λ S eq b d, 
   match d with 
   | inl _                  => Certify_Left_Constant S 
(*   | inr (existT (s, t) _ ) => Certify_Not_Left_Constant S (s, t) *) 
   | inr p => Certify_Not_Left_Constant S (projT1 p)
   end. 


Definition p2c_right_constant_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_right_constant_decidable S r b -> check_right_constant S 
:= λ S eq b d, 
   match d with 
   | inl _                  => Certify_Right_Constant S 
(*   | inr (existT (s, t) _ ) => Certify_Not_Right_Constant S (s, t) *) 
   | inr p => Certify_Not_Right_Constant S (projT1 p)
   end. 

Definition p2c_left_cancel_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_left_cancellative_decidable S r b -> check_left_cancellative S 
:= λ S eq b d, 
   match d with 
   | inl _             => Certify_Left_Cancellative S 
(*   | inr (existT x _ ) => Certify_Not_Left_Cancellative S x *) 
   | inr p => Certify_Not_Left_Cancellative S (projT1 p)
   end. 


Definition p2c_right_cancel_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_right_cancellative_decidable S r b -> check_right_cancellative S 
:= λ S eq b d, 
   match d with 
   | inl _             => Certify_Right_Cancellative S 
(*   | inr (existT x _ ) => Certify_Not_Right_Cancellative S x *) 
   | inr p => Certify_Not_Right_Cancellative S (projT1 p) 
   end. 



Definition P2C_sg : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_proofs S r b -> sg_certificates S 
:= λ S r b P,
{|
  sg_associative      := Assert_Associative S 
; sg_congruence       := Assert_Bop_Congruence S 
; sg_commutative_d    := p2c_commutative_check S r b (A_sg_commutative_d S r b P)
; sg_selective_d      := p2c_selective_check S r b (A_sg_selective_d S r b P)
; sg_idempotent_d     := p2c_idempotent_check S r b (A_sg_idempotent_d S r b P)
; sg_exists_id_d      := p2c_exists_id_check S r b (A_sg_exists_id_d S r b P)
; sg_exists_ann_d     := p2c_exists_ann_check S r b (A_sg_exists_ann_d S r b P)
; sg_is_left_d        := p2c_is_left_check S r b (A_sg_is_left_d S r b P)
; sg_is_right_d       := p2c_is_right_check S r b (A_sg_is_right_d S r b P)
; sg_left_cancel_d    := p2c_left_cancel_check S r b (A_sg_left_cancel_d S r b P)
; sg_right_cancel_d   := p2c_right_cancel_check S r b (A_sg_right_cancel_d S r b P)
; sg_left_constant_d  := p2c_left_constant_check S r b (A_sg_left_constant_d S r b P)
; sg_right_constant_d := p2c_right_constant_check S r b (A_sg_right_constant_d S r b P)
; sg_anti_left_d      := p2c_anti_left_check S r b (A_sg_anti_left_d S r b P)
; sg_anti_right_d     := p2c_anti_right_check S r b (A_sg_anti_right_d S r b P)
|}. 

Definition A2C_sg : ∀ (S : Type), A_sg S -> sg S 
:= λ S R,
{| 
  sg_eq     := A2C_eqv S (A_sg_eq S R) 
; sg_bop    := A_sg_bop S R 
; sg_certs  := P2C_sg S (A_eqv_eq S (A_sg_eq S R)) (A_sg_bop S R) (A_sg_proofs S R)  
; sg_ast    := A_sg_ast S R
|}. 

Definition P2C_sg_new : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_proofs_new S r b -> sg_certificates_new S 
:= λ S r b P,
{|
  sgn_commutative_d    := projT1 (A_sgn_commutative_d S r b P)
; sgn_selective_d      := projT1 (A_sgn_selective_d S r b P)
; sgn_idempotent_d     := projT1 (A_sgn_idempotent_d S r b P)
; sgn_exists_id_d      := projT1 (A_sgn_exists_id_d S r b P)
; sgn_exists_ann_d     := projT1 (A_sgn_exists_ann_d S r b P)
; sgn_is_left_d        := projT1 (A_sgn_is_left_d S r b P)
; sgn_is_right_d       := projT1 (A_sgn_is_right_d S r b P)
; sgn_left_cancel_d    := projT1 (A_sgn_left_cancel_d S r b P)
; sgn_right_cancel_d   := projT1 (A_sgn_right_cancel_d S r b P)
; sgn_left_constant_d  := projT1 (A_sgn_left_constant_d S r b P)
; sgn_right_constant_d := projT1 (A_sgn_right_constant_d S r b P)
; sgn_anti_left_d      := projT1 (A_sgn_anti_left_d S r b P)
; sgn_anti_right_d     := projT1 (A_sgn_anti_right_d S r b P)
|}. 

Definition A2C_sg_new : ∀ (S : Type), A_sg_new S -> sg_new S 
:= λ S R,
{| 
  sgn_eq     := A2C_eqv S (A_sgn_eq S R) 
; sgn_bop    := A_sgn_bop S R 
; sgn_certs  := P2C_sg_new S (A_eqv_eq S (A_sgn_eq S R)) (A_sgn_bop S R) (A_sgn_proofs S R)  
; sgn_ast    := A_sgn_ast S R
|}. 


Definition P2C_sg_C : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_C_proofs S r b -> sg_C_certificates S 
:= λ S r b P,
{|
  sg_C_associative   := Assert_Associative S 
; sg_C_congruence    := Assert_Bop_Congruence S 
; sg_C_commutative   := Assert_Commutative S 
; sg_C_selective_d   := p2c_selective_check S r b (A_sg_C_selective_d S r b P)
; sg_C_idempotent_d  := p2c_idempotent_check S r b (A_sg_C_idempotent_d S r b P)
; sg_C_exists_id_d   := p2c_exists_id_check S r b (A_sg_C_exists_id_d S r b P)
; sg_C_exists_ann_d  := p2c_exists_ann_check S r b (A_sg_C_exists_ann_d S r b P)
; sg_C_left_cancel_d    := p2c_left_cancel_check S r b (A_sg_C_left_cancel_d S r b P)
; sg_C_right_cancel_d   := p2c_right_cancel_check S r b (A_sg_C_right_cancel_d S r b P)
; sg_C_left_constant_d  := p2c_left_constant_check S r b (A_sg_C_left_constant_d S r b P)
; sg_C_right_constant_d := p2c_right_constant_check S r b (A_sg_C_right_constant_d S r b P)
; sg_C_anti_left_d      := p2c_anti_left_check S r b (A_sg_C_anti_left_d S r b P)
; sg_C_anti_right_d     := p2c_anti_right_check S r b (A_sg_C_anti_right_d S r b P)
|}. 

Definition A2C_sg_C : ∀ (S : Type), A_sg_C S -> sg_C S 
:= λ S R,
{| 
  sg_C_eqv   := A2C_eqv S (A_sg_C_eqv S R) 
; sg_C_bop   := A_sg_C_bop S R 
; sg_C_certs := P2C_sg_C S 
                   (A_eqv_eq S (A_sg_C_eqv S R)) 
                   (A_sg_C_bop S R) 
                   (A_sg_C_proofs S R)  
; sg_C_ast   := A_sg_C_ast S R
|}.


Definition P2C_sg_CI : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CI_proofs S r b -> sg_CI_certificates S 
:= λ S r b P,
{|
  sg_CI_associative   := Assert_Associative S 
; sg_CI_congruence    := Assert_Bop_Congruence S 
; sg_CI_commutative   := Assert_Commutative S 
; sg_CI_idempotent    := Assert_Idempotent S 
; sg_CI_selective_d   := p2c_selective_check S r b (A_sg_CI_selective_d S r b P)
; sg_CI_exists_id_d   := p2c_exists_id_check S r b (A_sg_CI_exists_id_d S r b P)
; sg_CI_exists_ann_d  := p2c_exists_ann_check S r b (A_sg_CI_exists_ann_d S r b P)
|}. 

Definition A2C_sg_CI : ∀ (S : Type), A_sg_CI S -> sg_CI S 
:= λ S R,
{| 
  sg_CI_eqv   := A2C_eqv S (A_sg_CI_eqv S R)
; sg_CI_bop   := A_sg_CI_bop S R 
; sg_CI_certs := P2C_sg_CI S (A_eqv_eq S (A_sg_CI_eqv S R)) (A_sg_CI_bop S R) (A_sg_CI_proofs S R)  
; sg_CI_ast   := A_sg_CI_ast S R
|}. 



Definition P2C_sg_CS : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CS_proofs S r b -> sg_CS_certificates S 
:= λ S r b P,
{|
  sg_CS_associative   := Assert_Associative S 
; sg_CS_congruence    := Assert_Bop_Congruence S 
; sg_CS_commutative   := Assert_Commutative S 
; sg_CS_selective     := Assert_Selective S 
; sg_CS_exists_id_d   := p2c_exists_id_check S r b (A_sg_CS_exists_id_d S r b P)
; sg_CS_exists_ann_d  := p2c_exists_ann_check S r b (A_sg_CS_exists_ann_d S r b P)
|}. 

Definition A2C_sg_CS : ∀ (S : Type), A_sg_CS S -> sg_CS S 
:= λ S R,
{| 
  sg_CS_eqv   := A2C_eqv S (A_sg_CS_eqv S R)
; sg_CS_bop   := A_sg_CS_bop S R 
; sg_CS_certs := P2C_sg_CS S (A_eqv_eq S (A_sg_CS_eqv S R)) (A_sg_CS_bop S R) (A_sg_CS_proofs S R)  
; sg_CS_ast   := A_sg_CS_ast S R
|}. 


Definition P2C_sg_CK : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CK_proofs S r b -> sg_CK_certificates S 
:= λ S r b P,
{|
  sg_CK_associative      := Assert_Associative S 
; sg_CK_congruence       := Assert_Bop_Congruence S 
; sg_CK_commutative      := Assert_Commutative S 
; sg_CK_left_cancel      := Assert_Left_Cancellative S 
; sg_CK_exists_id_d      := p2c_exists_id_check S r b (A_sg_CK_exists_id_d S r b P)
; sg_CK_anti_left_d      := p2c_anti_left_check S r b (A_sg_CK_anti_left_d S r b P)
; sg_CK_anti_right_d     := p2c_anti_right_check S r b (A_sg_CK_anti_right_d S r b P)
|}. 

Definition A2C_sg_CK : ∀ (S : Type), A_sg_CK S -> sg_CK S 
:= λ S R,
{| 
  sg_CK_eqv   := A2C_eqv S (A_sg_CK_eqv S R)
; sg_CK_bop   := A_sg_CK_bop S R 
; sg_CK_certs := P2C_sg_CK S (A_eqv_eq S (A_sg_CK_eqv S R)) (A_sg_CK_bop S R) (A_sg_CK_proofs S R)  
; sg_CK_ast   := A_sg_CK_ast S R
|}. 




Definition p2c_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_absorption_decidable S r b1 b2 -> check_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Absorptive S 
   | inr p => Certify_Not_Left_Absorptive S (projT1 p) 
   end. 

Definition p2c_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_absorption_decidable S r b1 b2 -> check_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Absorptive S 
   | inr p => Certify_Not_Right_Absorptive S (projT1 p)
   end. 



Definition P2C_sg_sg : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             sg_sg_proofs S r b1 b2 -> sg_sg_certificates S 
:= λ S r b1 b2 R,
{|
  sg_sg_left_distributive_d    := p2c_left_distributive S r b1 b2 (A_sg_sg_left_distributive_d S r b1 b2 R)
; sg_sg_right_distributive_d   := p2c_right_distributive S r b1 b2 (A_sg_sg_right_distributive_d S r b1 b2 R)
; sg_sg_left_absorptive_d      := p2c_left_absorptive S r b1 b2 (A_sg_sg_left_absorption_d S r b1 b2 R)
; sg_sg_right_absorptive_d     := p2c_right_absorptive S r b1 b2 (A_sg_sg_right_absorption_d S r b1 b2 R)
; sg_sg_plus_id_is_times_ann_d := p2c_plus_id_equals_times_ann S r b1 b2 (A_sg_sg_plus_id_is_times_ann_d S r b1 b2 R)
; sg_sg_times_id_is_plus_ann_d := p2c_times_id_equals_plus_ann S r b1 b2  (A_sg_sg_times_id_is_plus_ann_d S r b1 b2 R)
   
|}. 

Definition A2C_sg_sg : ∀ (S : Type), A_sg_sg S -> sg_sg S 
:= λ S R,
{|
  sg_sg_eqv         := A2C_eqv S (A_sg_sg_eqv S R)
; sg_sg_plus        := A_sg_sg_plus S R 
; sg_sg_times       := A_sg_sg_times S R 
; sg_sg_plus_certs  := P2C_sg S (A_eqv_eq S (A_sg_sg_eqv S R)) 
                                (A_sg_sg_plus S R) 
                                (A_sg_sg_plus_proofs S R)
; sg_sg_times_certs := P2C_sg S (A_eqv_eq S (A_sg_sg_eqv S R)) 
                                (A_sg_sg_times S R) 
                                (A_sg_sg_times_proofs S R)
; sg_sg_certs       := P2C_sg_sg S (A_eqv_eq S (A_sg_sg_eqv S R)) 
                                   (A_sg_sg_plus S R) 
                                   (A_sg_sg_times S R) 
                                   (A_sg_sg_proofs S R)
; sg_sg_ast        := A_sg_sg_ast S R
|}.


(* for testing/demos .... *) 
Definition A2C_sg_sg_from_sg_C_sg : ∀ (S : Type), A_sg_C_sg S -> sg_sg S 
:= λ S s, A2C_sg_sg S (A_sg_sg_from_sg_C_sg S s). 

Definition A2C_sg_sg_from_sg_CS_sg : ∀ (S : Type), A_sg_CS_sg S -> sg_sg S 
:= λ S s, A2C_sg_sg S (A_sg_sg_from_sg_CS_sg S s). 


Definition A2C_sg_sg_from_sg_CS_sg_CK_AD : ∀ (S : Type), A_sg_CS_sg_CK_AD S -> sg_sg S 
:= λ S s, A2C_sg_sg_from_sg_CS_sg S (A_sg_CS_sg_from_sg_CS_sg_CK_AD S s) . 

Definition A2C_sg_sg_from_sg_CS_sg_CS_AD : ∀ (S : Type), A_sg_CS_sg_CS_AD S -> sg_sg S 
:= λ S s, A2C_sg_sg_from_sg_C_sg S (A_sg_C_sg_from_sg_CS_sg_CS_AD S s) . 



(* 
Definition p2c_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_anti_left S r b -> assert_not_anti_left S 
:= λ S eq b d, 
   match d with 
   | (existT (s, t) _ ) => Assert_Not_Anti_Left S (s, t)
   end. 

Definition p2c_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_anti_right S r b -> assert_not_anti_right S 
:= λ S eq b d, 
   match d with 
   | (existT (s, t) _ ) => Assert_Not_Anti_Right S (s, t)
   end. 


Definition p2c_not_left_constant : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_left_constant S r b -> assert_not_left_constant S 
:= λ S eq b d, 
   match d with 
   | (existT (s, t) _ ) => Assert_Not_Left_Constant S (s, t)
   end. 


Definition p2c_not_right_constant : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_right_constant S r b -> assert_not_right_constant S 
:= λ S eq b d, 
   match d with 
   | (existT (s, t) _ ) => Assert_Not_Right_Constant S (s, t)
   end. 
 
Definition p2c_not_left_cancel : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_left_cancellative S r b -> assert_not_left_cancellative S 
:= λ S eq b d, 
   match d with 
   | (existT (s, (t, u)) _ ) => Assert_Not_Left_Cancellative S (s, (t, u))
   end. 

Definition p2c_not_right_cancel : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_right_cancellative S r b -> assert_not_right_cancellative S 
:= λ S eq b d, 
   match d with 
   | (existT (s, (t, u)) _ ) => Assert_Not_Right_Cancellative S (s, (t, u))
   end. 





Definition P2C_po : ∀ (S : Type) (eq lte : brel S), po_proofs S eq lte -> po_certs S 
:= λ S eq lte P,
{|
(*  po_not_trivial   := p2c_not_trivial S lte (A_po_not_trivial S eq lte P) *) 
  po_congruence    := Assert_Brel_Congruence S 
; po_reflexive     := Assert_Reflexive S 
; po_transitive    := Assert_Transitive S
; po_antisymmetric := Assert_Antisymmetric S 
; po_total_d       := p2c_total_check S lte (A_po_total_d S eq lte P)
|}. 

Definition A2C_po : ∀ (S : Type), A_po S -> po S 
:= λ S R,
{| 
  po_eq         := A_po_eq S R 
; po_lte        := A_po_lte S R 
; po_eqv_certs  := P2C_eqv S (A_po_eq S R) (A_po_eqv_proofs S R)  
; po_po_certs   := P2C_po S (A_po_eq S R) (A_po_lte S R) (A_po_po_proofs S R)  
; po_ast        := A_po_ast S R
|}. 


Definition P2C_to : ∀ (S : Type) (eq lte : brel S), to_proofs S eq lte -> to_certs S 
:= λ S eq lte P,
{|
(*  to_not_trivial   := p2c_not_trivial S lte (A_to_not_trivial S eq lte P) *) 
 to_congruence    := Assert_Brel_Congruence S 
; to_reflexive     := Assert_Reflexive S 
; to_transitive    := Assert_Transitive S
; to_antisymmetric := Assert_Antisymmetric S 
; to_total         := Assert_Total S 
|}. 

Definition A2C_to : ∀ (S : Type), A_to S -> to S 
:= λ S R,
{| 
  to_eq         := A_to_eq S R 
; to_lte        := A_to_lte S R 
; to_eqv_certs  := P2C_eqv S (A_to_eq S R) (A_to_eqv_proofs S R)  
; to_po_certs   := P2C_to S (A_to_eq S R) (A_to_lte S R) (A_to_to_proofs S R)  
; to_ast        := A_to_ast S R
|}. 

*)

(*

*) 

(*
Definition A2C_sg_C_sg : ∀ (S : Type), A_sg_C_sg S -> sg_C_sg S 
:= λ S R,
{|
  sg_C_sg_eqv         := A2C_eqv S (A_sg_C_sg_eqv S R)
; sg_C_sg_plus        := A_sg_C_sg_plus S R 
; sg_C_sg_times       := A_sg_C_sg_times S R 
; sg_C_sg_plus_certs  := P2C_sg_C S (A_eqv_eq S (A_sg_C_sg_eqv S R)) 
                                (A_sg_C_sg_plus S R) 
                                (A_sg_C_sg_plus_proofs S R)
; sg_C_sg_times_certs := P2C_sg S (A_eqv_eq S (A_sg_C_sg_eqv S R)) 
                                (A_sg_C_sg_times S R) 
                                (A_sg_C_sg_times_proofs S R)
; sg_C_sg_certs       := P2C_sg_sg S (A_eqv_eq S (A_sg_C_sg_eqv S R)) 
                                   (A_sg_C_sg_plus S R) 
                                   (A_sg_C_sg_times S R) 
                                   (A_sg_C_sg_proofs S R)
; sg_C_sg_ast        := A_sg_C_sg_ast S R
|}.


Definition A2C_sg_CS_sg : ∀ (S : Type), A_sg_CS_sg S -> sg_CS_sg S 
:= λ S R,
{|
  sg_CS_sg_eqv         := A2C_eqv S (A_sg_CS_sg_eqv S R)
; sg_CS_sg_plus        := A_sg_CS_sg_plus S R 
; sg_CS_sg_times       := A_sg_CS_sg_times S R 
; sg_CS_sg_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_sg_CS_sg_eqv S R)) 
                                (A_sg_CS_sg_plus S R) 
                                (A_sg_CS_sg_plus_proofs S R)
; sg_CS_sg_times_certs := P2C_sg S (A_eqv_eq S (A_sg_CS_sg_eqv S R)) 
                                (A_sg_CS_sg_times S R) 
                                (A_sg_CS_sg_times_proofs S R)
; sg_CS_sg_certs       := P2C_sg_sg S (A_eqv_eq S (A_sg_CS_sg_eqv S R)) 
                                   (A_sg_CS_sg_plus S R) 
                                   (A_sg_CS_sg_times S R) 
                                   (A_sg_CS_sg_proofs S R)
; sg_CS_sg_ast        := A_sg_CS_sg_ast S R
|}.

*) 
(* 

Definition P2C_sr : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),  sr_proofs S r b1 b2 -> sr_certs S 
:= λ S r b1 b2 R,
{|
  sr_left_distributive      := Assert_Left_Distributive S 
; sr_right_distributive     := Assert_Right_Distributive S 
; sr_plus_id_is_times_ann   := Assert_Plus_Id_Equals_Times_Ann S 
; sr_times_id_is_plus_ann_d := p2c_times_id_equals_plus_ann S r b1 b2 (A_sr_times_id_is_plus_ann_d S r b1 b2 R)
|}. 

Definition A2C_sr : ∀ (S : Type), A_sr S -> sr S 
:= λ S R,
{|
  sr_eq          := A_sr_eq S R 
; sr_plus        := A_sr_plus S R 
; sr_times       := A_sr_times S R 
; sr_eqv_certs   := P2C_eqv S (A_sr_eq S R) (A_sr_eqv_proofs S R)  
; sr_plus_certs  := P2C_sg_C S (A_sr_eq S R) (A_sr_plus S R) (A_sr_plus_proofs S R)
; sr_times_certs := P2C_sg S (A_sr_eq S R) (A_sr_times S R) (A_sr_times_proofs S R)
; sr_sr_certs    := P2C_sr S (A_sr_eq S R) (A_sr_plus S R) (A_sr_times S R) (A_sr_sr_proofs S R)
; sr_ast         := A_sr_ast S R
|}. 

Definition P2C_csr : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
               csr_proofs S r b1 b2 -> csr_certs S 
:= λ S r b1 b2 R,
{|
  csr_left_distributive    := Assert_Left_Distributive S 
; csr_right_distributive   := Assert_Right_Distributive S 
; csr_plus_id_is_times_ann := Assert_Plus_Id_Equals_Times_Ann S 
; csr_times_id_is_plus_ann := Assert_Times_Id_Equals_Plus_Ann S 
|}. 

Definition A2C_csr : ∀ (S : Type), A_csr S -> csr S 
:= λ S R,
{|
  csr_eq          := A_csr_eq S R 
; csr_plus        := A_csr_plus S R 
; csr_times       := A_csr_times S R 
; csr_eqv_certs   := P2C_eqv S (A_csr_eq S R) (A_csr_eqv_proofs S R)  
; csr_plus_certs  := P2C_sg_C S (A_csr_eq S R) (A_csr_plus S R) (A_csr_plus_proofs S R)
; csr_times_certs := P2C_sg S (A_csr_eq S R) (A_csr_times S R) (A_csr_times_proofs S R)
; csr_csr_certs   := P2C_csr S (A_csr_eq S R) (A_csr_plus S R) (A_csr_times S R) (A_csr_csr_proofs S R)
; csr_ast         := A_csr_ast S R
|}. 

Definition A2C_pa : ∀ (S : Type), A_pa S -> pa S 
:= λ S R,
{|
  pa_eq          := A_pa_eq S R 
; pa_plus        := A_pa_plus S R 
; pa_times       := A_pa_times S R 
; pa_eqv_certs   := P2C_eqv S (A_pa_eq S R) (A_pa_eqv_proofs S R)  
; pa_plus_certs  := P2C_sg_CI S (A_pa_eq S R) (A_pa_plus S R) (A_pa_plus_proofs S R)
; pa_times_certs := P2C_sg S (A_pa_eq S R) (A_pa_times S R) (A_pa_times_proofs S R)
; pa_pa_certs    := P2C_csr S (A_pa_eq S R) (A_pa_plus S R) (A_pa_times S R) (A_pa_pa_proofs S R)
; pa_ast         := A_pa_ast S R
|}. 

*) 


(* for downcasting *) 

Definition P2C_sg_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_proofs S r b) -> option(sg_certificates S)
  := λ S r b, option_map (P2C_sg S r b). 


Definition A2C_sg_option : ∀ (S : Type), option(A_sg S) -> option(sg S)
  := λ S, option_map (A2C_sg S). 

Definition P2C_sg_C_option : ∀ (S : Type) (r : brel S) (b : binary_op S),  option(sg_C_proofs S r b) -> option(sg_C_certificates S)       
  := λ S r b, option_map (P2C_sg_C S r b). 

Definition A2C_sg_C_option : ∀ (S : Type), option(A_sg_C S) -> option(sg_C S) 
  := λ S, option_map (A2C_sg_C S). 

Definition P2C_sg_CI_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CI_proofs S r b) -> option(sg_CI_certificates S)  
  := λ S r b, option_map (P2C_sg_CI S r b).          

Definition A2C_sg_CI_option : ∀ (S : Type), option(A_sg_CI S) -> option(sg_CI S) 
  := λ S, option_map (A2C_sg_CI S). 

Definition P2C_sg_CS_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CS_proofs S r b) -> option(sg_CS_certificates S)   
  := λ S r b, option_map (P2C_sg_CS S r b). 
         
Definition A2C_sg_CS_option : ∀ (S : Type), option(A_sg_CS S) -> option(sg_CS S)
  := λ S, option_map (A2C_sg_CS S). 


Definition P2C_sg_CK_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CK_proofs S r b) -> option(sg_CK_certificates S)   
  := λ S r b, option_map (P2C_sg_CK S r b). 
         
Definition A2C_sg_CK_option : ∀ (S : Type), option(A_sg_CK S) -> option(sg_CK S)
  := λ S, option_map (A2C_sg_CK S). 



(* 
Definition P2C_po_option : ∀ (S : Type) (eq lte : brel S), option(po_proofs S eq lte) -> option(po_certs S) 
  := λ S r b, option_map (P2C_po S r b). 

Definition A2C_po_option : ∀ (S : Type), option(A_po S) -> option(po S) 
  := λ S, option_map (A2C_po S). 

Definition P2C_to_option : ∀ (S : Type) (eq lte : brel S), option(to_proofs S eq lte) -> option(to_certs S)
  := λ S eq lte, option_map (P2C_to S eq lte). 

Definition A2C_to_option : ∀ (S : Type), option(A_to S) -> option(to S) 
  := λ S, option_map (A2C_to S). 



Definition P2C_sg_sg_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), option(sg_sg_proofs S r b1 b2) -> option(sg_sg_certs S)
  := λ S r b1 b2, option_map (P2C_sg_sg S r b1 b2). 

Definition A2C_sg_sg_option : ∀ (S : Type), option(A_sg_sg S) -> option(sg_sg S) 
  := λ S, option_map (A2C_sg_sg S). 

Definition P2C_sr_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),  option(sr_proofs S r b1 b2) -> option(sr_certs S) 
  := λ S r b1 b2, option_map (P2C_sr S r b1 b2). 

Definition A2C_sr_option : ∀ (S : Type), option(A_sr S) -> option(sr S) 
  := λ S, option_map (A2C_sr S). 

Definition P2C_csr_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), option(csr_proofs S r b1 b2) -> option(csr_certs S)
  := λ S r b1 b2, option_map (P2C_csr S r b1 b2). 
               
Definition A2C_csr_option : ∀ (S : Type), option(A_csr S) -> option(csr S) 
  := λ S, option_map (A2C_csr S). 

Definition A2C_pa_option : ∀ (S : Type), option (A_pa S) -> option (pa S)
  := λ S, option_map (A2C_pa S). 


*)