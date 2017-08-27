Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bop.right.
Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.



Definition A_sg_right : ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq         := eqvS
   ; A_sg_bop        := bop_right S 
   ; A_sg_proofs     := sg_proofs_right S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_right (A_eqv_ast _ eqvS)
   |}. 

