Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.


Section ACAS. 

Record sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required                          *) 
  A_sg_associative      : bop_associative S eq bop 
; A_sg_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sg_commutative_d    : bop_commutative_decidable S eq bop  
; A_sg_selective_d      : bop_selective_decidable S eq bop  
; A_sg_idempotent_d     : bop_idempotent_decidable S eq bop  

(* needed to decide selectivity of sg product    *) 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  

(* needed to decide distributivity of (lex, product). For multiplicative operator *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

(* needed to decide distributivity of (lex, product). For multiplicative operator *) 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

(* needed to decide absorptivity of (lex, product). For multiplicative operator *) 
; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop

}.


(* semigroups 

sg    = semigroup 
asg   = additive semigroup (is either selective or idempotent, ignores "multiplicative" properties) 
msg   = multiplicative semigroup (ignores "additive" properties) 
sg_C  = commutative semigroup 
sg_CI = commutative idempotent semigroup, not selective 
sg_CS = commutative selective semigroup 
sg_CK = commutative cancellative semigroup 

           sg
         / | \
       asg | msg
         \ | 
          sg_C 
         / |  \
        /  |   \ 
       /   |    \
  sg_CI sg_CS  sg_CK

Note, if cancellative, 

    LK: a * b = a * c -> b = c      

suppose c is any idempotent : c * c = c, then c = id 

    c * a = (c * c) * a = c * (c * a) 
    -LK-> a = c * a 

     LK -> idem(c) -> left_id(c), etc 

So any cancellative idempotent commutative semigroup will be trivial {id}. 
Since all carriers are non-trivial, sg_CI, sg_CS, and sg_CK are distinct. 
*) 


Record sg_C_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_C_associative      : bop_associative S eq bop 
; A_sg_C_congruence       : bop_congruence S eq bop   
; A_sg_C_commutative      : bop_commutative S eq bop

; A_sg_C_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_C_anti_right_d     : bop_anti_right_decidable S eq bop 

(***)
; A_sg_C_selective_d      : bop_selective_decidable S eq bop  
; A_sg_C_idempotent_d     : bop_idempotent_decidable S eq bop  

; A_sg_C_cancel_d         : bop_left_cancellative_decidable S eq bop 
; A_sg_C_constant_d       : bop_left_constant_decidable S eq bop 

}. 


Record sg_CS_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CS_associative        : bop_associative S eq bop 
; A_sg_CS_congruence         : bop_congruence S eq bop   
; A_sg_CS_commutative        : bop_commutative S eq bop  
; A_sg_CS_selective          : bop_selective S eq bop

}. 

Record sg_CI_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CI_associative        : bop_associative S eq bop 
; A_sg_CI_congruence         : bop_congruence S eq bop   
; A_sg_CI_commutative        : bop_commutative S eq bop  
; A_sg_CI_idempotent         : bop_idempotent S eq bop  
; A_sg_CI_not_selective      : bop_not_selective S eq bop
}. 


Record sg_CK_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CK_associative        : bop_associative S eq bop 
; A_sg_CK_congruence         : bop_congruence S eq bop   
; A_sg_CK_commutative        : bop_commutative S eq bop  
; A_sg_CK_cancel             : bop_left_cancellative S eq bop
                                                     
; A_sg_CK_anti_left_d        : bop_anti_left_decidable S eq bop 
; A_sg_CK_anti_right_d       : bop_anti_right_decidable S eq bop

}.




(* additive semigroup 
   idea : don't worry about "multiplicative properties". 
   why? 
*) 
Record asg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_asg_associative      : bop_associative S eq bop 
; A_asg_congruence       : bop_congruence S eq bop   
; A_asg_commutative      : bop_commutative S eq bop  

(** should this be ((bop_selective S eq bop) + ((bop_idempotent S eq bop) * (bop_not_selective S eq bop))) ? **) 
; A_asg_selective_d      : bop_selective_decidable S eq bop  
; A_asg_idempotent_d     : bop_idempotent_decidable S eq bop
}.


(* multiplicative semigroup 
   idea: don't worry about selectivity/idempotence. 
   Why? 

*) 
Record msg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_msg_associative      : bop_associative S eq bop 
; A_msg_congruence       : bop_congruence S eq bop   
; A_msg_commutative_d    : bop_commutative_decidable S eq bop  

(* needed?*)                                                    
; A_msg_is_left_d        : bop_is_left_decidable S eq bop  
; A_msg_is_right_d       : bop_is_right_decidable S eq bop  

(***)                                                   
; A_msg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_msg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

; A_msg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_msg_right_constant_d : bop_right_constant_decidable S eq bop 

; A_msg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_msg_anti_right_d     : bop_anti_right_decidable S eq bop
}. 


Record A_sg (S : Type) := {
  A_sg_eq           : A_eqv S 
; A_sg_bop          : binary_op S
; A_sg_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_eq) A_sg_bop 
; A_sg_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_eq) A_sg_bop 
; A_sg_proofs       : sg_proofs S (A_eqv_eq S A_sg_eq) A_sg_bop 
; A_sg_ast          : cas_ast
}.

(* sg_C = commutative semigroup *) 
Record A_sg_C (S : Type) := {
  A_sg_C_eqv          : A_eqv S 
; A_sg_C_bop          : binary_op S
; A_sg_C_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_proofs       : sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_ast          : cas_ast
}.

(* sg_CI = commutative idempotent semigroup *) 
Record A_sg_CI (S : Type) := {
  A_sg_CI_eqv          : A_eqv S
; A_sg_CI_bop          : binary_op S
; A_sg_CI_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_proofs       : sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_ast          : cas_ast
}.

Record A_sg_CI_with_ann (S : Type) := {
  A_sg_CI_wa_eqv          : A_eqv S
; A_sg_CI_wa_bop          : binary_op S
; A_sg_CI_wa_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_CI_wa_eqv) A_sg_CI_wa_bop
; A_sg_CI_wa_exists_ann   : bop_exists_ann S (A_eqv_eq S A_sg_CI_wa_eqv) A_sg_CI_wa_bop
; A_sg_CI_wa_proofs       : sg_CI_proofs S (A_eqv_eq S A_sg_CI_wa_eqv) A_sg_CI_wa_bop
; A_sg_CI_wa_ast          : cas_ast
}.

Record A_sg_CI_with_id (S : Type) := {
  A_sg_CI_wi_eqv          : A_eqv S
; A_sg_CI_wi_bop          : binary_op S
; A_sg_CI_wi_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_CI_wi_eqv) A_sg_CI_wi_bop
; A_sg_CI_wi_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_CI_wi_eqv) A_sg_CI_wi_bop
; A_sg_CI_wi_proofs       : sg_CI_proofs S (A_eqv_eq S A_sg_CI_wi_eqv) A_sg_CI_wi_bop
; A_sg_CI_wi_ast          : cas_ast
}.


(* sg_CS = commutative selective semigroup *) 
Record A_sg_CS (S : Type) := {
  A_sg_CS_eqv          : A_eqv S 
; A_sg_CS_bop          : binary_op S
; A_sg_CS_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_proofs       : sg_CS_proofs S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_ast          : cas_ast
}.

Record A_sg_CK (S : Type) := {
  A_sg_CK_eqv         : A_eqv S 
; A_sg_CK_bop         : binary_op S
; A_sg_CK_exists_id_d : bop_exists_id_decidable S (A_eqv_eq S A_sg_CK_eqv) A_sg_CK_bop
; A_sg_CK_proofs      : sg_CK_proofs S (A_eqv_eq S A_sg_CK_eqv) A_sg_CK_bop
; A_sg_CK_ast         : cas_ast
}.

(* additive semigroups *) 
Record A_asg (S : Type) := {
  A_asg_eq           : A_eqv S 
; A_asg_bop          : binary_op S
; A_asg_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_asg_eq) A_asg_bop
; A_asg_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_asg_eq) A_asg_bop
; A_asg_proofs       : asg_proofs S (A_eqv_eq S A_asg_eq) A_asg_bop 
; A_asg_ast          : cas_ast
}.

(* multiplicitive semigroups *) 
Record A_msg (S : Type) := {
  A_msg_eq           : A_eqv S 
; A_msg_bop          : binary_op S
; A_msg_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_msg_eq) A_msg_bop 
; A_msg_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_msg_eq) A_msg_bop 
; A_msg_proofs       : msg_proofs S (A_eqv_eq S A_msg_eq) A_msg_bop 
; A_msg_ast          : cas_ast
}.

End ACAS.

Section CAS. 

Record sg_certificates {S: Type}  := 
{
  sg_associative      : assert_associative (S := S) 
; sg_congruence       : assert_bop_congruence (S := S) 

; sg_commutative_d    : check_commutative (S := S) 
; sg_selective_d      : check_selective (S := S) 
; sg_idempotent_d     : check_idempotent (S := S) 

; sg_is_left_d        : check_is_left (S := S) 
; sg_is_right_d       : check_is_right (S := S) 

; sg_left_cancel_d    : check_left_cancellative (S := S) 
; sg_right_cancel_d   : check_right_cancellative (S := S) 
; sg_left_constant_d  : check_left_constant (S := S) 
; sg_right_constant_d : check_right_constant (S := S) 
; sg_anti_left_d      : check_anti_left (S := S) 
; sg_anti_right_d     : check_anti_right (S := S)

}. 

Record sg_C_certificates {S: Type}  := 
{
  sg_C_associative      : assert_associative (S := S) 
; sg_C_congruence       : assert_bop_congruence (S := S) 
; sg_C_commutative      : assert_commutative (S := S) 
; sg_C_selective_d      : check_selective (S := S) 
; sg_C_idempotent_d     : check_idempotent (S := S)
; sg_C_cancel_d         : check_left_cancellative (S := S) 
; sg_C_constant_d       : check_left_constant (S := S) 
; sg_C_anti_left_d      : check_anti_left (S := S) 
; sg_C_anti_right_d     : check_anti_right (S := S)
}. 

Record sg_CS_certificates {S: Type}  := 
{
  sg_CS_associative        : assert_associative (S := S) 
; sg_CS_congruence         : assert_bop_congruence (S := S) 
; sg_CS_commutative        : assert_commutative (S := S)
; sg_CS_selective          : assert_selective (S := S)
}. 

Record sg_CI_certificates {S: Type}  := 
{
  sg_CI_associative        : assert_associative (S := S) 
; sg_CI_congruence         : assert_bop_congruence (S := S) 
; sg_CI_commutative        : assert_commutative (S := S) 
; sg_CI_idempotent         : assert_idempotent (S := S) 
; sg_CI_not_selective        : assert_not_selective (S := S)                                             
}. 


Record sg_CK_certificates {S: Type}  := 
{
  sg_CK_associative      : assert_associative (S := S) 
; sg_CK_congruence       : assert_bop_congruence (S := S) 
; sg_CK_commutative      : assert_commutative (S := S) 
; sg_CK_left_cancel      : assert_left_cancellative (S := S) 
; sg_CK_anti_left_d      : check_anti_left (S := S) 
; sg_CK_anti_right_d     : check_anti_right (S := S)
}. 


Record asg_certificates {S: Type}  := 
{
  asg_associative      : assert_associative (S := S) 
; asg_congruence       : assert_bop_congruence (S := S) 
; asg_commutative      : assert_commutative (S := S) 
; asg_selective_d      : check_selective (S := S) 
; asg_idempotent_d     : check_idempotent (S := S)
}. 

Record msg_certificates {S: Type}  := 
{
  msg_associative      : assert_associative (S := S) 
; msg_congruence       : assert_bop_congruence (S := S) 

; msg_commutative_d    : check_commutative (S := S) 
; msg_is_left_d        : check_is_left (S := S) 
; msg_is_right_d       : check_is_right (S := S) 
; msg_left_cancel_d    : check_left_cancellative (S := S) 
; msg_right_cancel_d   : check_right_cancellative (S := S) 
; msg_left_constant_d  : check_left_constant (S := S) 
; msg_right_constant_d : check_right_constant (S := S) 
; msg_anti_left_d      : check_anti_left (S := S) 
; msg_anti_right_d     : check_anti_right (S := S)
}. 

Record sg {S : Type} := {
  sg_eq           : @eqv S 
; sg_bop          : binary_op S
; sg_exists_id_d  : @check_exists_id S
; sg_exists_ann_d : @check_exists_ann S
; sg_certs        : @sg_certificates S
; sg_ast          : cas_ast
}.


Record sg_C {S : Type} := {
  sg_C_eqv          : @eqv S 
; sg_C_bop          : binary_op S
; sg_C_exists_id_d  : @check_exists_id S
; sg_C_exists_ann_d : @check_exists_ann S
; sg_C_certs        : @sg_C_certificates S
; sg_C_ast          : cas_ast
}.

Record sg_CI {S : Type} := {
  sg_CI_eqv          : @eqv S 
; sg_CI_bop          : binary_op S
; sg_CI_exists_id_d  : @check_exists_id S
; sg_CI_exists_ann_d : @check_exists_ann S
; sg_CI_certs        : @sg_CI_certificates S
; sg_CI_ast          : cas_ast
}.

Record sg_CI_with_ann {S : Type} := {
  sg_CI_wa_eqv          : @eqv S 
; sg_CI_wa_bop          : binary_op S
; sg_CI_wa_exists_id_d  : @check_exists_id S
; sg_CI_wa_exists_ann   : @assert_exists_ann S
; sg_CI_wa_certs        : @sg_CI_certificates S
; sg_CI_wa_ast          : cas_ast
}.

Record sg_CI_with_id {S : Type} := {
  sg_CI_wi_eqv          : @eqv S 
; sg_CI_wi_bop          : binary_op S
; sg_CI_wi_exists_id    : @assert_exists_id S
; sg_CI_wi_exists_ann_d : @check_exists_ann S
; sg_CI_wi_certs        : @sg_CI_certificates S
; sg_CI_wi_ast          : cas_ast
}.

Record sg_CS {S : Type} := {
  sg_CS_eqv          : @eqv S 
; sg_CS_bop          : binary_op S
; sg_CS_exists_id_d  : @check_exists_id S
; sg_CS_exists_ann_d : @check_exists_ann S
; sg_CS_certs        : @sg_CS_certificates S
; sg_CS_ast          : cas_ast
}.

Record sg_CK {S : Type} := {
  sg_CK_eqv         : @eqv S
; sg_CK_bop         : binary_op S
; sg_CK_exists_id_d : @check_exists_id S
; sg_CK_certs       : @sg_CK_certificates S
; sg_CK_ast         : cas_ast
}.

Record asg {S : Type} := {
  asg_eq           : @eqv S 
; asg_bop          : binary_op S
; asg_exists_id_d  : @check_exists_id S
; asg_exists_ann_d : @check_exists_ann S
; asg_certs        : @asg_certificates S
; asg_ast          : cas_ast
}.

Record msg {S : Type} := {
  msg_eq           : @eqv S 
; msg_bop          : binary_op S
; msg_exists_id_d  : @check_exists_id S
; msg_exists_ann_d : @check_exists_ann S
; msg_certs        : @msg_certificates S
; msg_ast          : cas_ast
}.

End CAS.


Section Translation.

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
|}. 


Definition P2C_sg_CI : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CI_proofs S r b -> @sg_CI_certificates S 
:= λ S r b P,
{|
  sg_CI_associative   := @Assert_Associative S 
; sg_CI_congruence    := @Assert_Bop_Congruence S 
; sg_CI_commutative   := @Assert_Commutative S 
; sg_CI_idempotent    := @Assert_Idempotent S 
; sg_CI_not_selective   := p2c_not_selective_assert S r b (A_sg_CI_not_selective S r b P)
|}. 



Definition P2C_sg_CS : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CS_proofs S r b -> @sg_CS_certificates S 
:= λ S r b P,
{|
  sg_CS_associative   := @Assert_Associative S 
; sg_CS_congruence    := @Assert_Bop_Congruence S 
; sg_CS_commutative   := @Assert_Commutative S 
; sg_CS_selective     := @Assert_Selective S
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


Definition A2C_sg_CI_with_ann : ∀ (S : Type), A_sg_CI_with_ann S -> @sg_CI_with_ann S 
:= λ S R,
let b  := A_sg_CI_wa_bop S R in
let eq := A_eqv_eq S (A_sg_CI_wa_eqv S R) in 
{| 
  sg_CI_wa_eqv          := A2C_eqv S (A_sg_CI_wa_eqv S R)
; sg_CI_wa_bop          := b 
; sg_CI_wa_exists_id_d  := p2c_exists_id_check S eq b (A_sg_CI_wa_exists_id_d S R)
; sg_CI_wa_exists_ann   := Assert_Exists_Ann (projT1 (A_sg_CI_wa_exists_ann S R))
; sg_CI_wa_certs        := P2C_sg_CI S eq b (A_sg_CI_wa_proofs S R)
; sg_CI_wa_ast          := A_sg_CI_wa_ast S R
|}. 


Definition A2C_sg_CI_with_id : ∀ (S : Type), A_sg_CI_with_id S -> @sg_CI_with_id S 
:= λ S R,
let b  := A_sg_CI_wi_bop S R in
let eq := A_eqv_eq S (A_sg_CI_wi_eqv S R) in 
{| 
  sg_CI_wi_eqv          := A2C_eqv S (A_sg_CI_wi_eqv S R)
; sg_CI_wi_bop          := b 
; sg_CI_wi_exists_id    := Assert_Exists_Id (projT1 (A_sg_CI_wi_exists_id S R))
; sg_CI_wi_exists_ann_d := p2c_exists_ann_check S eq b (A_sg_CI_wi_exists_ann_d S R)
; sg_CI_wi_certs        := P2C_sg_CI S eq b (A_sg_CI_wi_proofs S R)
; sg_CI_wi_ast          := A_sg_CI_wi_ast S R
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
  asg_eq           := A2C_eqv  S (A_asg_eq S R) 
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


  
End Translation.   


Section Verify.
(* Do we really need to prove things like this? 

    ∀ (S : Type) (sgS : A_sg S),
    sg_certs (A2C_sg (sgS)) = P2C_sg _ _ _ (A_sg_proofs sgS). 

Hmm. Seems such things are true by construction.  
For example, 

Definition A2C_sg : ∀ (S : Type), A_sg S -> @sg S := 
 ... 
; sg_certs        := P2C_sg S eq b (A_sg_proofs S R)
 ... 

In addition, it seems that these facts are never 
actually needed in verification proofs. 
*) 
End Verify.   
