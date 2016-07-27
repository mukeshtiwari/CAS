Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.data.
Require Import CAS.a_code.proof_records.

(* eqv *) 
Record A_eqv (S : Type) := {
  A_eqv_eq      : brel S 
; A_eqv_proofs  : eqv_proofs S A_eqv_eq
; A_eqv_data    : S -> data (* for printing in ocaml-land *) 
; A_eqv_rep     : S -> S    (* for reductions.  Should this be an option? *) 
; A_eqv_ast     : ast_eqv 
}.

Record A_sg (S : Type) := {
  A_sg_eq         : A_eqv S 
; A_sg_bop        : binary_op S 
; A_sg_proofs     : sg_proofs S (A_eqv_eq S A_sg_eq) A_sg_bop 
; A_sg_ast        : ast_sg
}.


(* sg_C = commutative semigroup *) 
Record A_sg_C (S : Type) := {
  A_sg_C_eqv         : A_eqv S 
; A_sg_C_bop         : binary_op S 
; A_sg_C_proofs      : sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop 
; A_sg_C_ast         : ast_sg_C
}.


(* sg_CI = commutative idempotent semigroup *) 
Record A_sg_CI (S : Type) := {
  A_sg_CI_eqv          : A_eqv S
; A_sg_CI_bop          : binary_op S 
; A_sg_CI_proofs       : sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop 
; A_sg_CI_ast          : ast_sg_CI
}.


(* sg_CS = commutative selective semigroup *) 
Record A_sg_CS (S : Type) := {
  A_sg_CS_eqv          : A_eqv S 
; A_sg_CS_bop          : binary_op S 
; A_sg_CS_proofs       : sg_CS_proofs S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop 
; A_sg_CS_ast          : ast_sg_CS 
}.


(* sg_CK = commutative cancellative semigroup 

LK: a * b = a * c -> b = c      

suppose c is any idempotent : c * c = c, then c = id 

    c * a = (c * c) * a = c * (c * a) 
    -LK-> a = c * a 

LK -> idem(c) -> left_id(c) 

So any cancellative idempotent commutative semigroup will be trivial {id}. 

           sg
           | 
           | 
           sg_C --
           |      \ 
           |       \ 
           sg_CI    sg_CK
           | 
           | 
           sg_CS 
*) 




Record A_sg_CK (S : Type) := {
  A_sg_CK_eqv         : A_eqv S 
; A_sg_CK_bop         : binary_op S 
; A_sg_CK_proofs      : sg_CK_proofs S (A_eqv_eq S A_sg_CK_eqv) A_sg_CK_bop 
; A_sg_CK_ast         : ast_sg_CK
}.


(* bi-semigroups *) 

Record A_bs (S : Type) := {
  A_bs_eqv          : A_eqv S 
; A_bs_plus         : binary_op S 
; A_bs_times        : binary_op S 
; A_bs_plus_proofs  : sg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus
; A_bs_times_proofs : sg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_times 
; A_bs_proofs       : bs_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times 
; A_bs_ast          : ast_bs
}.


Record A_bs_CS (S : Type) := {
  A_bs_CS_eqv          : A_eqv S 
; A_bs_CS_plus         : binary_op S 
; A_bs_CS_times        : binary_op S 
; A_bs_CS_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus
; A_bs_CS_times_proofs : sg_proofs S    (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times 
; A_bs_CS_proofs       : bs_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times 
; A_bs_CS_ast          : ast_bs_CS
}.


Record A_bs_C (S : Type) := {
  A_bs_C_eqv          : A_eqv S 
; A_bs_C_plus         : binary_op S 
; A_bs_C_times        : binary_op S 
; A_bs_C_plus_proofs  : sg_C_proofs S (A_eqv_eq S A_bs_C_eqv) A_bs_C_plus
; A_bs_C_times_proofs : sg_proofs S   (A_eqv_eq S A_bs_C_eqv) A_bs_C_times 
; A_bs_C_proofs       : bs_proofs S (A_eqv_eq S A_bs_C_eqv) A_bs_C_plus A_bs_C_times 
; A_bs_C_ast          : ast_bs_C
}.






