Require Import CAS.code.basic_types.
Require Import CAS.code.bop.
Require Import CAS.code.combined. 

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.add_constant.
Require Import CAS.code.cas.eqv.set.


Definition sg_CI_certs_union : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> @sg_CI_certificates (with_constant (finite_set S))
:= λ {S} c s f,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := Certify_Not_Selective (inr (s :: nil), inr ((f s) :: nil))
; sg_CI_exists_id_d        := Certify_Exists_Id (inr nil) 
; sg_CI_exists_ann_d       := Certify_Exists_Ann (inl c) 
|}. 



Definition sg_CI_union : ∀ {S : Type} (c : cas_constant), @eqv S -> @sg_CI (with_constant (finite_set S)) 
:= λ {S} c eqvS,
  let eqS := eqv_eq eqvS in
  let s   := eqv_witness eqvS in
  let f   := eqv_new eqvS in
   {| 
     sg_CI_eqv       := eqv_add_constant (eqv_set eqvS) c  
   ; sg_CI_bop       := bop_add_ann (bop_union eqS) c
   ; sg_CI_certs     := sg_CI_certs_union c s f
   ; sg_CI_ast       := Ast_sg_CI_union_with_ann (c, eqv_ast eqvS)
   |}. 

