Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.sg_cert_records.
Require Import CAS.coq.common.sg_records.
Require Import CAS.coq.common.brel_properties. 
Require Import CAS.coq.common.bop_properties. 
Require Import CAS.coq.common.bs_properties. 
Require Import CAS.coq.common.proof_records. 
Require Import CAS.coq.common.a_cas_records. 
Require Import CAS.coq.common.eqv_proofs_to_certs. 

Definition p2c_exists_id_assert : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_id S r b -> @assert_exists_id S 
:= λ S eq b p, Assert_Exists_Id (projT1 p). 

Definition p2c_exists_id_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_id_decidable S r b -> @check_exists_id S 
:= λ S eq b d, 
   match d with 
   | inl p => Certify_Exists_Id (projT1 p)
   | inr _ => @Certify_Not_Exists_Id S 
   end. 


Definition p2c_exists_ann_assert : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_ann S r b -> @assert_exists_ann S 
:= λ S eq b p, Assert_Exists_Ann (projT1 p).  

Definition p2c_exists_ann_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_ann_decidable S r b -> @check_exists_ann S 
:= λ S eq b d, 
   match d with 
   | inl p => Certify_Exists_Ann (projT1 p)
   | inr _ => @Certify_Not_Exists_Ann S 
   end. 


Definition p2c_commutative_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_commutative_decidable S r b -> @check_commutative S 
:= λ S eq b d, 
   match d with 
   | inl _             => @Certify_Commutative S
   | inr p => Certify_Not_Commutative (projT1 p) 
   end. 

Definition p2c_idempotent_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_idempotent_decidable S r b -> @check_idempotent S 
:= λ S eq b d, 
   match d with 
   | inl _  => @Certify_Idempotent S
   | inr p  => Certify_Not_Idempotent (projT1 p) 
   end. 

Definition p2c_selective_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_selective_decidable S r b -> @check_selective S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Selective S
   | inr p => Certify_Not_Selective (projT1 p)
   end. 

Definition p2c_is_left_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_is_left_decidable S r b -> @check_is_left S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Is_Left S
   | inr p => Certify_Not_Is_Left (projT1 p) 
   end. 

Definition p2c_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_is_left S r b -> @assert_not_is_left S 
:= λ S eq b d, Assert_Not_Is_Left (projT1 d). 

Definition p2c_is_right_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_is_right_decidable S r b -> @check_is_right S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Is_Right S
   | inr p => Certify_Not_Is_Right (projT1 p) 
   end. 

Definition p2c_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_is_right S r b -> @assert_not_is_right S 
:= λ S eq b d, Assert_Not_Is_Right (projT1 d). 



Definition p2c_anti_left_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_anti_left_decidable S r b -> @check_anti_left S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Anti_Left S 
   | inr p => Certify_Not_Anti_Left (projT1 p)
   end. 


Definition p2c_anti_right_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_anti_right_decidable S r b -> @check_anti_right S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Anti_Right S 
   | inr p => Certify_Not_Anti_Right (projT1 p) 
   end. 


Definition p2c_left_constant_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_left_constant_decidable S r b -> @check_left_constant S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Left_Constant S 
   | inr p => Certify_Not_Left_Constant (projT1 p)
   end. 


Definition p2c_right_constant_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_right_constant_decidable S r b -> @check_right_constant S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Right_Constant S 
   | inr p => Certify_Not_Right_Constant (projT1 p)
   end. 

Definition p2c_left_cancel_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_left_cancellative_decidable S r b -> @check_left_cancellative S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Left_Cancellative S 
   | inr p => Certify_Not_Left_Cancellative (projT1 p)
   end. 

Definition p2c_right_cancel_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_right_cancellative_decidable S r b -> @check_right_cancellative S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Right_Cancellative S 
   | inr p => Certify_Not_Right_Cancellative (projT1 p) 
   end. 

(*************************************************************************) 

Definition P2C_sg : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_proofs S r b -> @sg_certificates S 
:= λ S r b P,
{|
  sg_associative      := @Assert_Associative S 
; sg_congruence       := @Assert_Bop_Congruence S 
; sg_commutative_d    := p2c_commutative_check S r b (A_sg_commutative_d S r b P)
; sg_selective_d      := p2c_selective_check S r b (A_sg_selective_d S r b P)
; sg_idempotent_d     := p2c_idempotent_check S r b (A_sg_idempotent_d S r b P)
; sg_is_left_d        := p2c_is_left_check S r b (A_sg_is_left_d S r b P)
; sg_is_right_d       := p2c_is_right_check S r b (A_sg_is_right_d S r b P)
; sg_left_cancel_d    := p2c_left_cancel_check S r b (A_sg_left_cancel_d S r b P)
; sg_right_cancel_d   := p2c_right_cancel_check S r b (A_sg_right_cancel_d S r b P)
; sg_left_constant_d  := p2c_left_constant_check S r b (A_sg_left_constant_d S r b P)
; sg_right_constant_d := p2c_right_constant_check S r b (A_sg_right_constant_d S r b P)
; sg_anti_left_d      := p2c_anti_left_check S r b (A_sg_anti_left_d S r b P)
; sg_anti_right_d     := p2c_anti_right_check S r b (A_sg_anti_right_d S r b P)

; sg_bop_ast          := A_sg_bop_ast S r b P
|}. 


Definition P2C_sg_C : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_C_proofs S r b -> @sg_C_certificates S 
:= λ S r b P,
{|
  sg_C_associative   := @Assert_Associative S 
; sg_C_congruence    := @Assert_Bop_Congruence S 
; sg_C_commutative   := @Assert_Commutative S 
; sg_C_selective_d   := p2c_selective_check S r b (A_sg_C_selective_d S r b P)
; sg_C_idempotent_d  := p2c_idempotent_check S r b (A_sg_C_idempotent_d S r b P)
; sg_C_cancel_d      := p2c_left_cancel_check S r b (A_sg_C_cancel_d S r b P)
; sg_C_constant_d    := p2c_left_constant_check S r b (A_sg_C_constant_d S r b P)
; sg_C_anti_left_d   := p2c_anti_left_check S r b (A_sg_C_anti_left_d S r b P)
; sg_C_anti_right_d  := p2c_anti_right_check S r b (A_sg_C_anti_right_d S r b P)

; sg_C_bop_ast       := A_sg_C_bop_ast S r b P
|}. 


Definition P2C_sg_CI : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CI_proofs S r b -> @sg_CI_certificates S 
:= λ S r b P,
{|
  sg_CI_associative   := @Assert_Associative S 
; sg_CI_congruence    := @Assert_Bop_Congruence S 
; sg_CI_commutative   := @Assert_Commutative S 
; sg_CI_idempotent    := @Assert_Idempotent S 
; sg_CI_selective_d   := p2c_selective_check S r b (A_sg_CI_selective_d S r b P)

; sg_CI_bop_ast       := A_sg_CI_bop_ast S r b P                                             
|}. 


Definition P2C_sg_CS : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CS_proofs S r b -> @sg_CS_certificates S 
:= λ S r b P,
{|
  sg_CS_associative   := @Assert_Associative S 
; sg_CS_congruence    := @Assert_Bop_Congruence S 
; sg_CS_commutative   := @Assert_Commutative S 
; sg_CS_selective     := @Assert_Selective S

; sg_CS_bop_ast       := A_sg_CS_bop_ast S r b P                                                 
|}. 


Definition P2C_sg_CK : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CK_proofs S r b -> @sg_CK_certificates S 
:= λ S r b P,
{|
  sg_CK_associative      := @Assert_Associative S 
; sg_CK_congruence       := @Assert_Bop_Congruence S 
; sg_CK_commutative      := @Assert_Commutative S 
; sg_CK_left_cancel      := @Assert_Left_Cancellative S 
; sg_CK_anti_left_d      := p2c_anti_left_check S r b (A_sg_CK_anti_left_d S r b P)
; sg_CK_anti_right_d     := p2c_anti_right_check S r b (A_sg_CK_anti_right_d S r b P)

; sg_CK_bop_ast          := A_sg_CK_bop_ast S r b P                                                 
|}. 

Definition P2C_asg : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         asg_proofs S r b -> @asg_certificates S 
:= λ S r b P,
{|
  asg_associative      := @Assert_Associative S
; asg_congruence       := @Assert_Bop_Congruence S 
; asg_commutative      := @Assert_Commutative S 
; asg_selective_d      := p2c_selective_check S r b (A_asg_selective_d S r b P)
; asg_idempotent_d     := p2c_idempotent_check S r b (A_asg_idempotent_d S r b P)

; asg_bop_ast          := A_asg_bop_ast S r b P
|}. 


Definition P2C_msg : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         msg_proofs S r b -> @msg_certificates S 
:= λ S r b P,
{|
  msg_associative      := @Assert_Associative S 
; msg_congruence       := @Assert_Bop_Congruence S 
; msg_commutative_d    := p2c_commutative_check S r b (A_msg_commutative_d S r b P)
; msg_is_left_d        := p2c_is_left_check S r b (A_msg_is_left_d S r b P)
; msg_is_right_d       := p2c_is_right_check S r b (A_msg_is_right_d S r b P)
; msg_left_cancel_d    := p2c_left_cancel_check S r b (A_msg_left_cancel_d S r b P)
; msg_right_cancel_d   := p2c_right_cancel_check S r b (A_msg_right_cancel_d S r b P)
; msg_left_constant_d  := p2c_left_constant_check S r b (A_msg_left_constant_d S r b P)
; msg_right_constant_d := p2c_right_constant_check S r b (A_msg_right_constant_d S r b P)
; msg_anti_left_d      := p2c_anti_left_check S r b (A_msg_anti_left_d S r b P)
; msg_anti_right_d     := p2c_anti_right_check S r b (A_msg_anti_right_d S r b P)

; msg_bop_ast          := A_msg_bop_ast S r b P                                                                     
|}. 


(*************************************************************************) 


Definition A2C_sg : ∀ (S : Type), A_sg S -> @sg S 
:= λ S R,
let b  := A_sg_bop S R in
let eq := A_eqv_eq S (A_sg_eq S R) in 
{| 
  sg_eq           := A2C_eqv S (A_sg_eq S R) 
; sg_bop          := b 
; sg_exists_id_d  := p2c_exists_id_check S eq b (A_sg_exists_id_d S R)
; sg_exists_ann_d := p2c_exists_ann_check S eq b (A_sg_exists_ann_d S R)
; sg_certs        := P2C_sg S eq b (A_sg_proofs S R)
; sg_ast          := A_sg_ast S R
|}. 


Definition A2C_sg_C : ∀ (S : Type), A_sg_C S -> @sg_C S 
:= λ S R,
let b  := A_sg_C_bop S R in 
let eq := A_eqv_eq S (A_sg_C_eqv S R) in 
{| 
  sg_C_eqv          := A2C_eqv S (A_sg_C_eqv S R) 
; sg_C_bop          := b 
; sg_C_exists_id_d  := p2c_exists_id_check S eq b (A_sg_C_exists_id_d S R)
; sg_C_exists_ann_d := p2c_exists_ann_check S eq b (A_sg_C_exists_ann_d S R)
; sg_C_certs        := P2C_sg_C S eq b (A_sg_C_proofs S R)
; sg_C_ast          := A_sg_C_ast S R
|}.

Definition A2C_sg_CI : ∀ (S : Type), A_sg_CI S -> @sg_CI S 
:= λ S R,
let b  := A_sg_CI_bop S R in
let eq := A_eqv_eq S (A_sg_CI_eqv S R) in 
{| 
  sg_CI_eqv          := A2C_eqv S (A_sg_CI_eqv S R)
; sg_CI_bop          := b 
; sg_CI_exists_id_d  := p2c_exists_id_check S eq b (A_sg_CI_exists_id_d S R)
; sg_CI_exists_ann_d := p2c_exists_ann_check S eq b (A_sg_CI_exists_ann_d S R)
; sg_CI_certs        := P2C_sg_CI S eq b (A_sg_CI_proofs S R)
; sg_CI_ast          := A_sg_CI_ast S R
|}. 


Definition A2C_sg_CS : ∀ (S : Type), A_sg_CS S -> @sg_CS S 
:= λ S R,
let b := A_sg_CS_bop S R in
let eq := A_eqv_eq S (A_sg_CS_eqv S R) in   
{| 
  sg_CS_eqv          := A2C_eqv S (A_sg_CS_eqv S R)
; sg_CS_bop          := b 
; sg_CS_exists_id_d  := p2c_exists_id_check S eq b (A_sg_CS_exists_id_d S R)
; sg_CS_exists_ann_d := p2c_exists_ann_check S eq b (A_sg_CS_exists_ann_d S R)
; sg_CS_certs        := P2C_sg_CS S eq b (A_sg_CS_proofs S R)
; sg_CS_ast          := A_sg_CS_ast S R
|}. 


Definition A2C_sg_CK : ∀ (S : Type), A_sg_CK S -> @sg_CK S 
:= λ S R,
let b  := A_sg_CK_bop S R  in 
let eq := A_eqv_eq S (A_sg_CK_eqv S R) in
{| 
  sg_CK_eqv         := A2C_eqv S (A_sg_CK_eqv S R)
; sg_CK_bop         := b
; sg_CK_exists_id_d := p2c_exists_id_check S eq b (A_sg_CK_exists_id_d S R)
; sg_CK_certs       := P2C_sg_CK S eq b (A_sg_CK_proofs S R)
; sg_CK_ast         := A_sg_CK_ast S R
|}.

Definition A2C_asg : ∀ (S : Type), A_asg S -> @asg S 
:= λ S R,
let b  := A_asg_bop S R in 
let eq := A_eqv_eq S (A_asg_eq S R) in
{| 
  asg_eq           := A2C_eqv S (A_asg_eq S R) 
; asg_bop          := b
; asg_exists_id_d  := p2c_exists_id_check S eq b (A_asg_exists_id_d S R)
; asg_exists_ann_d := p2c_exists_ann_check S eq b (A_asg_exists_ann_d S R)
; asg_certs        := P2C_asg S eq b (A_asg_proofs S R)
; asg_ast          := A_asg_ast S R
|}. 


Definition A2C_msg : ∀ (S : Type), A_msg S -> @msg S 
:= λ S R,
let b  := A_msg_bop S R in 
let eq := A_eqv_eq S (A_msg_eq S R) in
{| 
  msg_eq           := A2C_eqv S (A_msg_eq S R) 
; msg_bop          := b 
; msg_exists_id_d  := p2c_exists_id_check S eq b (A_msg_exists_id_d S R)
; msg_exists_ann_d := p2c_exists_ann_check S eq b (A_msg_exists_ann_d S R)
; msg_certs        := P2C_msg S eq b (A_msg_proofs S R)

; msg_ast          := A_msg_ast S R
|}. 


(*************************** for downcasting ********************************************) 

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

