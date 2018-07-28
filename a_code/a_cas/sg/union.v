Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cas.eqv.add_constant.
Require Import CAS.a_code.a_cas.eqv.set.
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bop.add_ann.
Require Import CAS.theory.bop.union.
Require Import CAS.theory.facts.


Definition sg_CI_proofs_union : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS ->
        sg_CI_proofs (with_constant (finite_set S)) (brel_add_constant (brel_set rS) c) (bop_add_ann (bop_union rS) c)
:= λ S rS c s f ntS eqvS,
   let refS := A_eqv_reflexive S rS eqvS in
   let symS := A_eqv_symmetric S rS eqvS in
   let tranS := A_eqv_transitive S rS eqvS in                                                            
{|
  A_sg_CI_associative        := bop_union_associative S rS c refS symS tranS 
; A_sg_CI_congruence         := bop_union_congruence S rS c refS symS tranS 
; A_sg_CI_commutative        := bop_union_commutative S rS c refS symS tranS 
; A_sg_CI_idempotent         := bop_union_idempotent S rS c refS symS tranS 
; A_sg_CI_selective_d        := inr _ (bop_union_not_selective S rS c s f ntS refS symS)
; A_sg_CI_exists_id_d        := inl _ (bop_union_exists_id S rS c refS symS tranS)
; A_sg_CI_exists_ann_d       := inl _ (bop_union_exists_ann S rS c)
|}. 


Definition A_sg_CI_union : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_sg_CI (with_constant (finite_set S)) 
  := λ S c eqv,
  let eqS := A_eqv_eq S eqv in
  let s   := A_eqv_witness S eqv in
  let f   := A_eqv_new S eqv in
  let ntS := A_eqv_not_trivial S eqv in       
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant (finite_set S) (A_eqv_set S eqv) c  
   ; A_sg_CI_bop       := bop_add_ann (bop_union eqS) c
   ; A_sg_CI_proofs    := sg_CI_proofs_union S eqS c s f ntS (A_eqv_proofs S eqv)
   ; A_sg_CI_ast       := Ast_sg_CI_union_with_ann (c, A_eqv_ast S eqv)
                                                                   
   |}. 