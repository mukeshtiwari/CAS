Require Import CAS.coq.common.compute. 

Require Import CAS.coq.common.eqv_certificates.
Require Import CAS.coq.common.eqv_cert_records.
Require Import CAS.coq.common.eqv_records.

Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.sg_cert_records.
Require Import CAS.coq.common.sg_records.

Require Import CAS.coq.common.bs_certificates.
Require Import CAS.coq.common.bs_cert_records.
Require Import CAS.coq.common.bs_records.

Require Import CAS.coq.common.brel_properties. 
Require Import CAS.coq.common.bop_properties. 
Require Import CAS.coq.common.bs_properties. 

Require Import CAS.coq.common.proof_records. 
Require Import CAS.coq.common.a_cas_records.

Require Import CAS.coq.common.eqv_proofs_to_certs.
Require Import CAS.coq.common.sg_proofs_to_certs.

Definition p2c_left_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_left_absorptive_decidable S r b1 b2 -> @check_left_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Left_Absorptive 
   | inr p => Certify_Not_Left_Left_Absorptive (projT1 p)                                             
   end. 


Definition p2c_left_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_right_absorptive_decidable S r b1 b2 -> @check_left_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Right_Absorptive
   | inr p => Certify_Not_Left_Right_Absorptive (projT1 p)
   end. 


Definition p2c_right_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_left_absorptive_decidable S r b1 b2 -> @check_right_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Left_Absorptive
   | inr p => Certify_Not_Right_Left_Absorptive (projT1 p)
   end. 


Definition p2c_right_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_right_absorptive_decidable S r b1 b2 -> @check_right_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Right_Absorptive 
   | inr p => Certify_Not_Right_Right_Absorptive (projT1 p)
   end. 

Definition p2c_left_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b1 b2 -> @check_left_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive 
   | inr p => Certify_Not_Left_Distributive (projT1 p) 
   end. 

Definition p2c_right_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_right_distributive_decidable S r b1 b2 -> @check_right_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Distributive
   | inr p => Certify_Not_Right_Distributive (projT1 p)
   end. 

Definition p2c_left_distributive_dual : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b2 b1 -> @check_left_distributive_dual S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive_Dual 
   | inr p => Certify_Not_Left_Distributive_Dual (projT1 p) 
   end. 

Definition p2c_plus_id_equals_times_ann_assert : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann S r b1 b2 -> @assert_plus_id_equals_times_ann S 
:= λ S r b1 b2 p, Assert_Plus_Id_Equals_Times_Ann (projT1 p).


Definition p2c_plus_id_equals_times_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann_decidable S r b1 b2 -> @check_plus_id_equals_times_ann S 
:= λ S r b1 b2 d, 
   match d with 
   | inl p => Certify_Plus_Id_Equals_Times_Ann (projT1 p)
   | inr _ => Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 


Definition p2c_times_id_equals_plus_ann_assert : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann S r b2 b1 -> @assert_times_id_equals_plus_ann S
:= λ S r b1 b2 p, Assert_Times_Id_Equals_Plus_Ann (projT1 p). 

Definition p2c_times_id_equals_plus_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_id_equals_ann_decidable S r b2 b1 -> @check_times_id_equals_plus_ann S
:= λ S r b1 b2 d, 
   match d with 
   | inl p => Certify_Times_Id_Equals_Plus_Ann (projT1 p)
   | inr _ => Certify_Not_Times_Id_Equals_Plus_Ann 
   end. 

Definition P2C_id_ann : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             id_ann_proofs S r b1 b2 -> @id_ann_certificates S 
:= λ S r b1 b2 R,
{|
  id_ann_exists_plus_id_d       := p2c_exists_id_check S r b1  (A_id_ann_exists_plus_id_d S r b1 b2 R)
; id_ann_exists_plus_ann_d      := p2c_exists_ann_check S r b1  (A_id_ann_exists_plus_ann_d S r b1 b2 R)
; id_ann_exists_times_id_d      := p2c_exists_id_check S r b2  (A_id_ann_exists_times_id_d S r b1 b2 R)
; id_ann_exists_times_ann_d     := p2c_exists_ann_check S r b2  (A_id_ann_exists_times_ann_d S r b1 b2 R)
; id_ann_plus_id_is_times_ann_d := p2c_plus_id_equals_times_ann S r b1 b2 (A_id_ann_plus_id_is_times_ann_d S r b1 b2 R)
; id_ann_times_id_is_plus_ann_d := p2c_times_id_equals_plus_ann S r b1 b2  (A_id_ann_times_id_is_plus_ann_d S r b1 b2 R)
|}.


Definition P2C_zero_one : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             zero_one_proofs S r b1 b2 -> @zero_one_certificates S 
:= λ S r b1 b2 R,
{|
  zero_one_exists_plus_ann_d      := p2c_exists_ann_check S r b1  (A_zero_one_exists_plus_ann_d S r b1 b2 R)
; zero_one_exists_times_id        := p2c_exists_id_assert S r b2  (A_zero_one_exists_times_id S r b1 b2 R)
; zero_one_plus_id_is_times_ann   := p2c_plus_id_equals_times_ann_assert S r b1 b2 (A_zero_one_plus_id_is_times_ann S r b1 b2 R)
; zero_one_times_id_is_plus_ann_d := p2c_times_id_equals_plus_ann S r b1 b2  (A_zero_one_times_id_is_plus_ann_d S r b1 b2 R)
|}.


Definition P2C_bounded : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             bounded_proofs S r b1 b2 -> @bounded_certificates S 
:= λ S r b1 b2 R,
{|
  bounded_plus_id_is_times_ann  := p2c_plus_id_equals_times_ann_assert S r b1 b2 (A_bounded_plus_id_is_times_ann S r b1 b2 R)
; bounded_times_id_is_plus_ann := p2c_times_id_equals_plus_ann_assert S r b1 b2  (A_bounded_times_id_is_plus_ann S r b1 b2 R)
|}.



Definition P2C_bs : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             bs_proofs S r b1 b2 -> @bs_certificates S 
:= λ S r b1 b2 R,
{|
  bs_left_distributive_d      := p2c_left_distributive S r b1 b2 (A_bs_left_distributive_d S r b1 b2 R)
; bs_right_distributive_d     := p2c_right_distributive S r b1 b2 (A_bs_right_distributive_d S r b1 b2 R)

; bs_left_left_absorptive_d   := p2c_left_left_absorptive S r b1 b2 (A_bs_left_left_absorptive_d S r b1 b2 R)
; bs_left_right_absorptive_d  := p2c_left_right_absorptive S r b1 b2 (A_bs_left_right_absorptive_d S r b1 b2 R)
; bs_right_left_absorptive_d  := p2c_right_left_absorptive S r b1 b2 (A_bs_right_left_absorptive_d S r b1 b2 R)
; bs_right_right_absorptive_d := p2c_right_right_absorptive S r b1 b2 (A_bs_right_right_absorptive_d S r b1 b2 R)
|}. 

Definition A2C_bs : ∀ (S : Type), A_bs S -> @bs S 
:= λ S R,
{|
 bs_eqv         := A2C_eqv S (A_bs_eqv S R)
; bs_plus        := A_bs_plus S R 
; bs_times       := A_bs_times S R 
; bs_plus_certs  := P2C_asg S (A_eqv_eq S (A_bs_eqv S R)) 
                                (A_bs_plus S R) 
                                (A_bs_plus_proofs S R)
; bs_times_certs := P2C_msg S (A_eqv_eq S (A_bs_eqv S R)) 
                                (A_bs_times S R) 
                                (A_bs_times_proofs S R)
; bs_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_bs_eqv S R)) 
                                   (A_bs_plus S R) 
                                   (A_bs_times S R) 
                                   (A_bs_id_ann_proofs S R)
; bs_certs       := P2C_bs S (A_eqv_eq S (A_bs_eqv S R)) 
                                   (A_bs_plus S R) 
                                   (A_bs_times S R) 
                                   (A_bs_proofs S R)
; bs_ast        := A_bs_ast S R
|}.



Definition A2C_bs_CS : ∀ (S : Type), A_bs_CS S -> @bs_CS S 
:= λ S R,
{|
  bs_CS_eqv         := A2C_eqv S (A_bs_CS_eqv S R)
; bs_CS_plus        := A_bs_CS_plus S R 
; bs_CS_times       := A_bs_CS_times S R 
; bs_CS_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                (A_bs_CS_plus S R) 
                                (A_bs_CS_plus_proofs S R)
; bs_CS_times_certs := P2C_msg S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                (A_bs_CS_times S R) 
                                (A_bs_CS_times_proofs S R)
; bs_CS_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                   (A_bs_CS_plus S R) 
                                   (A_bs_CS_times S R) 
                                   (A_bs_CS_id_ann_proofs S R)
; bs_CS_certs       := P2C_bs S (A_eqv_eq S (A_bs_CS_eqv S R)) 
                                   (A_bs_CS_plus S R) 
                                   (A_bs_CS_times S R) 
                                   (A_bs_CS_proofs S R)
; bs_CS_ast        := A_bs_CS_ast S R
|}.


Definition A2C_bs_CI : ∀ (S : Type), A_bs_CI S -> @bs_CI S 
:= λ S R,
{|
  bs_CI_eqv         := A2C_eqv S (A_bs_CI_eqv S R)
; bs_CI_plus        := A_bs_CI_plus S R 
; bs_CI_times       := A_bs_CI_times S R 
; bs_CI_plus_certs  := P2C_sg_CI S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                (A_bs_CI_plus S R) 
                                (A_bs_CI_plus_proofs S R)
; bs_CI_times_certs := P2C_msg S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                (A_bs_CI_times S R) 
                                (A_bs_CI_times_proofs S R)
; bs_CI_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                   (A_bs_CI_plus S R) 
                                   (A_bs_CI_times S R) 
                                   (A_bs_CI_id_ann_proofs S R)
; bs_CI_certs       := P2C_bs S (A_eqv_eq S (A_bs_CI_eqv S R)) 
                                   (A_bs_CI_plus S R) 
                                   (A_bs_CI_times S R) 
                                   (A_bs_CI_proofs S R)
; bs_CI_ast        := A_bs_CI_ast S R
|}.


(* for downcasting *) 

Definition P2C_sg_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_proofs S r b) -> option(@sg_certificates S)
  := λ S r b, option_map (P2C_sg S r b). 


Definition A2C_sg_option : ∀ (S : Type), option(A_sg S) -> option(@sg S)
  := λ S, option_map (A2C_sg S). 

Definition P2C_sg_C_option : ∀ (S : Type) (r : brel S) (b : binary_op S),  option(sg_C_proofs S r b) -> option(@sg_C_certificates S)       
  := λ S r b, option_map (P2C_sg_C S r b). 

Definition A2C_sg_C_option : ∀ (S : Type), option(A_sg_C S) -> option(@sg_C S) 
  := λ S, option_map (A2C_sg_C S). 

Definition P2C_sg_CI_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CI_proofs S r b) -> option(@sg_CI_certificates S)  
  := λ S r b, option_map (P2C_sg_CI S r b).          

Definition A2C_sg_CI_option : ∀ (S : Type), option(A_sg_CI S) -> option(@sg_CI S) 
  := λ S, option_map (A2C_sg_CI S). 

Definition P2C_sg_CS_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CS_proofs S r b) -> option(@sg_CS_certificates S)   
  := λ S r b, option_map (P2C_sg_CS S r b). 
         
Definition A2C_sg_CS_option : ∀ (S : Type), option(A_sg_CS S) -> option(@sg_CS S)
  := λ S, option_map (A2C_sg_CS S). 


Definition P2C_sg_CK_option : ∀ (S : Type) (r : brel S) (b : binary_op S), option(sg_CK_proofs S r b) -> option(@sg_CK_certificates S)   
  := λ S r b, option_map (P2C_sg_CK S r b). 
         
Definition A2C_sg_CK_option : ∀ (S : Type), option(A_sg_CK S) -> option(@sg_CK S)
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



Definition P2C_bs_option : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), option(bs_proofs S r b1 b2) -> option(bs_certs S)
  := λ S r b1 b2, option_map (P2C_bs S r b1 b2). 

Definition A2C_bs_option : ∀ (S : Type), option(A_bs S) -> option(bs S) 
  := λ S, option_map (A2C_bs S). 

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



Definition P2C_semiring : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             semiring_proofs S r b1 b2 -> @semiring_certificates S 
:= λ S r b1 b2 R,
{|
  semiring_left_distributive      := Assert_Left_Distributive
; semiring_right_distributive     := Assert_Right_Distributive

; semiring_left_left_absorptive_d   := p2c_left_left_absorptive S r b1 b2 (A_semiring_left_left_absorptive_d S r b1 b2 R)
; semiring_left_right_absorptive_d  := p2c_left_right_absorptive S r b1 b2 (A_semiring_left_right_absorptive_d S r b1 b2 R)

|}.



Definition A2C_presemiring : ∀ (S : Type), A_presemiring S -> @presemiring S 
:= λ S R,
{|
  presemiring_eqv         := A2C_eqv S (A_presemiring_eqv S R)
; presemiring_plus        := A_presemiring_plus S R 
; presemiring_times       := A_presemiring_times S R 
; presemiring_plus_certs  := P2C_sg_C S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                (A_presemiring_plus S R) 
                                (A_presemiring_plus_proofs S R)
; presemiring_times_certs := P2C_msg S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                (A_presemiring_times S R) 
                                (A_presemiring_times_proofs S R)
; presemiring_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                   (A_presemiring_plus S R) 
                                   (A_presemiring_times S R) 
                                   (A_presemiring_id_ann_proofs S R)        
; presemiring_certs       := P2C_semiring S (A_eqv_eq S (A_presemiring_eqv S R)) 
                                   (A_presemiring_plus S R) 
                                   (A_presemiring_times S R) 
                                   (A_presemiring_proofs S R)
; presemiring_ast        := A_presemiring_ast S R
|}.

Definition A2C_selective_presemiring : ∀ (S : Type), A_selective_presemiring S -> @selective_presemiring S 
:= λ S R,
{|
  selective_presemiring_eqv         := A2C_eqv S (A_selective_presemiring_eqv S R)
; selective_presemiring_plus        := A_selective_presemiring_plus S R 
; selective_presemiring_times       := A_selective_presemiring_times S R 
; selective_presemiring_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                (A_selective_presemiring_plus S R) 
                                (A_selective_presemiring_plus_proofs S R)
; selective_presemiring_times_certs := P2C_msg S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                (A_selective_presemiring_times S R) 
                                (A_selective_presemiring_times_proofs S R)
; selective_presemiring_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                   (A_selective_presemiring_plus S R) 
                                   (A_selective_presemiring_times S R) 
                                   (A_selective_presemiring_id_ann_proofs S R)        
; selective_presemiring_certs       := P2C_semiring S (A_eqv_eq S (A_selective_presemiring_eqv S R)) 
                                   (A_selective_presemiring_plus S R) 
                                   (A_selective_presemiring_times S R) 
                                   (A_selective_presemiring_proofs S R)
; selective_presemiring_ast        := A_selective_presemiring_ast S R
|}.




Definition A2C_semiring : ∀ (S : Type), A_semiring S -> @semiring S 
:= λ S R,
{|
  semiring_eqv         := A2C_eqv S (A_semiring_eqv S R)
; semiring_plus        := A_semiring_plus S R 
; semiring_times       := A_semiring_times S R 
; semiring_plus_certs  := P2C_sg_C S (A_eqv_eq S (A_semiring_eqv S R)) 
                                (A_semiring_plus S R) 
                                (A_semiring_plus_proofs S R)
; semiring_times_certs := P2C_msg S (A_eqv_eq S (A_semiring_eqv S R)) 
                                (A_semiring_times S R) 
                                (A_semiring_times_proofs S R)
; semiring_id_ann_certs := P2C_zero_one S (A_eqv_eq S (A_semiring_eqv S R)) 
                                   (A_semiring_plus S R) 
                                   (A_semiring_times S R) 
                                   (A_semiring_id_ann_proofs S R)         
; semiring_certs       := P2C_semiring S (A_eqv_eq S (A_semiring_eqv S R)) 
                                   (A_semiring_plus S R) 
                                   (A_semiring_times S R) 
                                   (A_semiring_proofs S R)
; semiring_ast        := A_semiring_ast S R
|}.

Definition A2C_selective_semiring : ∀ (S : Type), A_selective_semiring S -> @selective_semiring S 
:= λ S R,
{|
  selective_semiring_eqv         := A2C_eqv S (A_selective_semiring_eqv S R)
; selective_semiring_plus        := A_selective_semiring_plus S R 
; selective_semiring_times       := A_selective_semiring_times S R 
; selective_semiring_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                (A_selective_semiring_plus S R) 
                                (A_selective_semiring_plus_proofs S R)
; selective_semiring_times_certs := P2C_msg S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                (A_selective_semiring_times S R) 
                                (A_selective_semiring_times_proofs S R)
; selective_semiring_id_ann_certs := P2C_zero_one S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                   (A_selective_semiring_plus S R) 
                                   (A_selective_semiring_times S R) 
                                   (A_selective_semiring_id_ann_proofs S R)         
; selective_semiring_certs       := P2C_semiring S (A_eqv_eq S (A_selective_semiring_eqv S R)) 
                                   (A_selective_semiring_plus S R) 
                                   (A_selective_semiring_times S R) 
                                   (A_selective_semiring_proofs S R)
; selective_semiring_ast        := A_selective_semiring_ast S R
|}.


Definition A2C_dioid : ∀ (S : Type), A_dioid S -> @dioid S 
:= λ S R,
{|
  dioid_eqv         := A2C_eqv S (A_dioid_eqv S R)
; dioid_plus        := A_dioid_plus S R 
; dioid_times       := A_dioid_times S R 
; dioid_plus_certs  := P2C_sg_CI S (A_eqv_eq S (A_dioid_eqv S R)) 
                                (A_dioid_plus S R) 
                                (A_dioid_plus_proofs S R)
; dioid_times_certs := P2C_msg S (A_eqv_eq S (A_dioid_eqv S R)) 
                                (A_dioid_times S R) 
                                (A_dioid_times_proofs S R)
; dioid_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_dioid_eqv S R)) 
                                   (A_dioid_plus S R) 
                                   (A_dioid_times S R) 
                                   (A_dioid_id_ann_proofs S R)
; dioid_certs       := P2C_semiring S (A_eqv_eq S (A_dioid_eqv S R)) 
                                   (A_dioid_plus S R) 
                                   (A_dioid_times S R) 
                                   (A_dioid_proofs S R)
; dioid_ast        := A_dioid_ast S R
|}.


Definition A2C_selective_dioid : ∀ (S : Type), A_selective_dioid S -> @selective_dioid S 
:= λ S R,
{|
  selective_dioid_eqv         := A2C_eqv S (A_selective_dioid_eqv S R)
; selective_dioid_plus        := A_selective_dioid_plus S R 
; selective_dioid_times       := A_selective_dioid_times S R 
; selective_dioid_plus_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                (A_selective_dioid_plus S R) 
                                (A_selective_dioid_plus_proofs S R)
; selective_dioid_times_certs := P2C_msg S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                (A_selective_dioid_times S R) 
                                (A_selective_dioid_times_proofs S R)
; selective_dioid_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                   (A_selective_dioid_plus S R) 
                                   (A_selective_dioid_times S R) 
                                   (A_selective_dioid_id_ann_proofs S R)              
; selective_dioid_certs       := P2C_semiring S (A_eqv_eq S (A_selective_dioid_eqv S R)) 
                                   (A_selective_dioid_plus S R) 
                                   (A_selective_dioid_times S R) 
                                   (A_selective_dioid_proofs S R)  
; selective_dioid_ast        := A_selective_dioid_ast S R
|}.




Definition P2C_lattice : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
             lattice_proofs S r b1 b2 -> @lattice_certificates S 
:= λ S r b1 b2 R,
{|

  lattice_absorptive             := Assert_Left_Left_Absorptive
; lattice_absorptive_dual        := Assert_Left_Left_Absorptive_Dual 

; lattice_distributive_d         := p2c_left_distributive S r b1 b2 (A_lattice_distributive_d S r b1 b2 R)
; lattice_distributive_dual_d    := p2c_left_distributive_dual S r b1 b2 (A_lattice_distributive_dual_d S r b1 b2 R)

|}. 

Definition A2C_lattice : ∀ (S : Type), A_lattice S -> @lattice S 
:= λ S R,
{|
  lattice_eqv         := A2C_eqv S (A_lattice_eqv S R)
; lattice_join        := A_lattice_join S R 
; lattice_meet        := A_lattice_meet S R 
; lattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_lattice_eqv S R)) 
                                (A_lattice_join S R) 
                                (A_lattice_join_proofs S R)
; lattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_lattice_eqv S R)) 
                                (A_lattice_meet S R) 
                                (A_lattice_meet_proofs S R)
; lattice_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_lattice_eqv S R)) 
                                   (A_lattice_join S R) 
                                   (A_lattice_meet S R) 
                                   (A_lattice_id_ann_proofs S R)                                              
; lattice_certs       := P2C_lattice S (A_eqv_eq S (A_lattice_eqv S R)) 
                                   (A_lattice_join S R) 
                                   (A_lattice_meet S R) 
                                   (A_lattice_proofs S R)
; lattice_ast        := A_lattice_ast S R
|}.


Definition P2C_distributive_lattice : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
    distributive_lattice_proofs S r b1 b2 -> @distributive_lattice_certificates S 
:= λ S r b1 b2 p,
{|

  distributive_lattice_absorptive             := Assert_Left_Left_Absorptive
; distributive_lattice_absorptive_dual        := Assert_Left_Left_Absorptive_Dual 
; distributive_lattice_distributive           := Assert_Left_Distributive
|}. 

Definition A2C_distributive_lattice : ∀ (S : Type), A_distributive_lattice S -> @distributive_lattice S 
:= λ S R,
{|
  distributive_lattice_eqv         := A2C_eqv S (A_distributive_lattice_eqv S R)
; distributive_lattice_join        := A_distributive_lattice_join S R 
; distributive_lattice_meet        := A_distributive_lattice_meet S R 
; distributive_lattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                (A_distributive_lattice_join S R) 
                                (A_distributive_lattice_join_proofs S R)
; distributive_lattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                (A_distributive_lattice_meet S R) 
                                (A_distributive_lattice_meet_proofs S R)
; distributive_lattice_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                   (A_distributive_lattice_join S R) 
                                   (A_distributive_lattice_meet S R) 
                                   (A_distributive_lattice_id_ann_proofs S R)         
; distributive_lattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_distributive_lattice_eqv S R)) 
                                        (A_distributive_lattice_join S R)
                                        (A_distributive_lattice_meet S R)                   
                                        (A_distributive_lattice_proofs S R)
; distributive_lattice_ast        := A_distributive_lattice_ast S R
|}.



Definition A2C_selective_distributive_lattice : ∀ (S : Type), A_selective_distributive_lattice S -> @selective_distributive_lattice S 
:= λ S R,
{|
  selective_distributive_lattice_eqv         := A2C_eqv S (A_selective_distributive_lattice_eqv S R)
; selective_distributive_lattice_join        := A_selective_distributive_lattice_join S R 
; selective_distributive_lattice_meet        := A_selective_distributive_lattice_meet S R 
; selective_distributive_lattice_join_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                (A_selective_distributive_lattice_join S R) 
                                (A_selective_distributive_lattice_join_proofs S R)
; selective_distributive_lattice_meet_certs := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                (A_selective_distributive_lattice_meet S R) 
                                (A_selective_distributive_lattice_meet_proofs S R)
; selective_distributive_lattice_id_ann_certs := P2C_bounded S (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                   (A_selective_distributive_lattice_join S R) 
                                   (A_selective_distributive_lattice_meet S R) 
                                   (A_selective_distributive_lattice_id_ann_proofs S R)         

; selective_distributive_lattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_selective_distributive_lattice_eqv S R)) 
                                        (A_selective_distributive_lattice_join S R)
                                        (A_selective_distributive_lattice_meet S R)                   
                                        (A_selective_distributive_lattice_proofs S R)
; selective_distributive_lattice_ast        := A_selective_distributive_lattice_ast S R
|}.



Definition A2C_selective_distributive_prelattice : ∀ (S : Type), A_selective_distributive_prelattice S -> @selective_distributive_prelattice S 
:= λ S R,
{|
  selective_distributive_prelattice_eqv         := A2C_eqv S (A_selective_distributive_prelattice_eqv S R)
; selective_distributive_prelattice_join        := A_selective_distributive_prelattice_join S R 
; selective_distributive_prelattice_meet        := A_selective_distributive_prelattice_meet S R 
; selective_distributive_prelattice_join_certs  := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                (A_selective_distributive_prelattice_join S R) 
                                (A_selective_distributive_prelattice_join_proofs S R)
; selective_distributive_prelattice_meet_certs := P2C_sg_CS S (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                (A_selective_distributive_prelattice_meet S R) 
                                (A_selective_distributive_prelattice_meet_proofs S R)
; selective_distributive_prelattice_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                   (A_selective_distributive_prelattice_join S R) 
                                   (A_selective_distributive_prelattice_meet S R) 
                                   (A_selective_distributive_prelattice_id_ann_proofs S R)         

; selective_distributive_prelattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_selective_distributive_prelattice_eqv S R)) 
                                        (A_selective_distributive_prelattice_join S R)
                                        (A_selective_distributive_prelattice_meet S R)                   
                                        (A_selective_distributive_prelattice_proofs S R)
; selective_distributive_prelattice_ast        := A_selective_distributive_prelattice_ast S R
|}.



Definition A2C_distributive_prelattice : ∀ (S : Type), A_distributive_prelattice S -> @distributive_prelattice S 
:= λ S R,
{|
  distributive_prelattice_eqv         := A2C_eqv S (A_distributive_prelattice_eqv S R)
; distributive_prelattice_join        := A_distributive_prelattice_join S R 
; distributive_prelattice_meet        := A_distributive_prelattice_meet S R 
; distributive_prelattice_join_certs  := P2C_sg_CI S (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                (A_distributive_prelattice_join S R) 
                                (A_distributive_prelattice_join_proofs S R)
; distributive_prelattice_meet_certs := P2C_sg_CI S (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                (A_distributive_prelattice_meet S R) 
                                (A_distributive_prelattice_meet_proofs S R)
; distributive_prelattice_id_ann_certs := P2C_id_ann S (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                   (A_distributive_prelattice_join S R) 
                                   (A_distributive_prelattice_meet S R) 
                                   (A_distributive_prelattice_id_ann_proofs S R)         
; distributive_prelattice_certs       := P2C_distributive_lattice S 
                                        (A_eqv_eq S (A_distributive_prelattice_eqv S R)) 
                                        (A_distributive_prelattice_join S R)
                                        (A_distributive_prelattice_meet S R)                   
                                        (A_distributive_prelattice_proofs S R)
; distributive_prelattice_ast        := A_distributive_prelattice_ast S R
|}.

