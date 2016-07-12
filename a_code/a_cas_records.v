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

Record A_sg_new (S : Type) := {
  A_sgn_eq         : A_eqv S 
; A_sgn_bop        : binary_op S 
; A_sgn_proofs     : sg_proofs_new S (A_eqv_eq S A_sgn_eq) A_sgn_bop 
; A_sgn_ast        : ast_sg
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



(* 
Definition A_eqv_eq_bool : A_eqv bool 
Definition A_eqv_eq_nat : A_eqv nat
Definition A_eqv_add_constant : ∀ (S : Type),  A_eqv S -> cas_constant -> A_eqv (with_constant S) 
Definition A_eqv_list : ∀ (S : Type),  A_eqv S -> A_eqv (list S) 
Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S) 
Definition A_eqv_product : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S * T) 
Definition A_eqv_sum : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S + T) 

    A_sg 
    A_sg_C  
    A_sg_CI  A_sg_CK
    A_sg_CS  

Definition A_sg_CS_and  : A_sg_CS bool
Definition A_sg_CS_or   : A_sg_CS bool
Definition A_sg_CS_min  : A_sg_CS nat 
Definition A_sg_CS_max  : A_sg_CS nat 
Definition A_sg_C_times : A_sg_C nat 
Definition A_sg_CK_plus : A_sg_CK nat 

Definition A_sg_concat : ∀ (S : Type),  A_eqv S -> A_sg (list S) 
Definition A_sg_left   : ∀ (S : Type),  A_eqv S -> A_sg S 
Definition A_sg_right  : ∀ (S : Type),  A_eqv S -> A_sg S 

Definition A_sg_add_id     : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
Definition A_sg_C_add_id   : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
Definition A_sg_CI_add_id  : ∀ (S : Type) (c : cas_constant),  A_sg_CI S -> A_sg_CI (with_constant S) 
Definition A_sg_CS_add_id  : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 

Definition A_sg_add_ann    : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
Definition A_sg_C_add_ann  : ∀ (S : Type) (c : cas_constant),  A_s g_C S -> A_sg_C (with_constant S) 
Definition A_sg_CI_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CI S -> A_sg_CI (with_constant S) 
Definition A_sg_CS_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 

Definition A_sg_left_sum     : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
Definition A_sg_right_sum    : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
Definition A_sg_C_left_sum   : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
Definition A_sg_C_right_sum  : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
Definition A_sg_CI_left_sum  : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
Definition A_sg_CI_right_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
Definition A_sg_CS_left_sum  : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
Definition A_sg_CS_right_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 

Definition A_sg_product    : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S * T) 
Definition A_sg_C_product  : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S * T) 
Definition A_sg_CI_product : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S * T) 
Definition A_sg_CK_product : ∀ (S T : Type),  A_sg_CK S -> A_sg_CK T -> A_sg_CK (S * T) 

Definition A_sg_llex    : ∀ (S T : Type),  A_sg_CS S -> A_sg T -> A_sg (S * T)
Definition A_sg_C_llex  : ∀ (S T : Type),  A_sg_CS S -> A_sg_C T -> A_sg_C (S * T)
Definition A_sg_CI_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CI T -> A_sg_CI (S * T)
Definition A_sg_CS_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S * T)

    A_sg_sg
    A_sg_C_sg
    A_sg_CI_sg
    A_sg_CS_sg

Definition A_sg_sg_product    : ∀ (S T : Type),  A_sg_sg S -> A_sg_sg T -> A_sg_sg (S * T) 
Definition A_sg_CS_sg_product : ∀ (S T : Type),  A_sg_CS_sg S -> A_sg_CS_sg T -> A_sg_CS_sg (S * T) 
Definition A_sg_C_sg_llex : ∀ (S T : Type),  A_sg_CS_sg S -> A_sg_C_sg T -> A_sg_C_sg (S * T) 

    A_sg_CS_min  : A_sg_CS nat 
    A_sg_CK_plus : A_sg_CK nat
    A_sg_CS_sg_CK_D_min_plus     ?? 

    A_sg_CS_max : A_sg_CS nat 
    A_sg_CS_min : A_sg_CS nat 
    A_sg_CS_sg_CS_D_max_min      ?? 

*) 
Record A_sg_sg (S : Type) := {
  A_sg_sg_eqv          : A_eqv S 
; A_sg_sg_plus         : binary_op S 
; A_sg_sg_times        : binary_op S 
; A_sg_sg_plus_proofs  : sg_proofs S (A_eqv_eq S A_sg_sg_eqv) A_sg_sg_plus
; A_sg_sg_times_proofs : sg_proofs S (A_eqv_eq S A_sg_sg_eqv) A_sg_sg_times 
; A_sg_sg_proofs       : sg_sg_proofs S (A_eqv_eq S A_sg_sg_eqv) A_sg_sg_plus A_sg_sg_times 
; A_sg_sg_ast          : ast_sg_sg
}.

Record A_sg_C_sg (S : Type) := {
  A_sg_C_sg_eqv          : A_eqv S 
; A_sg_C_sg_plus         : binary_op S 
; A_sg_C_sg_times        : binary_op S 
; A_sg_C_sg_plus_proofs  : sg_C_proofs S (A_eqv_eq S A_sg_C_sg_eqv) A_sg_C_sg_plus
; A_sg_C_sg_times_proofs : sg_proofs S    (A_eqv_eq S A_sg_C_sg_eqv) A_sg_C_sg_times 
; A_sg_C_sg_proofs       : sg_sg_proofs S (A_eqv_eq S A_sg_C_sg_eqv) 
                                            A_sg_C_sg_plus A_sg_C_sg_times 
; A_sg_C_sg_ast          : ast_sg_C_sg
}.


Record A_sg_CS_sg (S : Type) := {
  A_sg_CS_sg_eqv          : A_eqv S 
; A_sg_CS_sg_plus         : binary_op S 
; A_sg_CS_sg_times        : binary_op S 
; A_sg_CS_sg_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_eqv) A_sg_CS_sg_plus
; A_sg_CS_sg_times_proofs : sg_proofs S    (A_eqv_eq S A_sg_CS_sg_eqv) A_sg_CS_sg_times 
; A_sg_CS_sg_proofs       : sg_sg_proofs S (A_eqv_eq S A_sg_CS_sg_eqv) 
                                            A_sg_CS_sg_plus A_sg_CS_sg_times 
; A_sg_CS_sg_ast          : ast_sg_CS_sg
}.



(* a lattice *) 
Record A_sg_CI_sg_CI_A (S : Type) := {
  A_sg_CI_sg_CI_A_eqv          : A_eqv S 
; A_sg_CI_sg_CI_A_plus         : binary_op S 
; A_sg_CI_sg_CI_A_times        : binary_op S 

; A_sg_CI_sg_CI_A_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_sg_CI_sg_CI_A_eqv) 
                                                  A_sg_CI_sg_CI_A_plus
; A_sg_CI_sg_CI_A_times_proofs : sg_CI_proofs S (A_eqv_eq S A_sg_CI_sg_CI_A_eqv) 
                                                  A_sg_CI_sg_CI_A_times
; A_sg_CI_sg_CI_A_proofs       : sg_sg_LA_proofs S (A_eqv_eq S A_sg_CI_sg_CI_A_eqv) 
                                                       A_sg_CI_sg_CI_A_plus
                                                       A_sg_CI_sg_CI_A_times
; A_sg_CI_sg_CI_A_ast          : ast_sg_CI_sg_CI_A
}.




(* a distributive lattice *) 
Record A_sg_CI_sg_CI_AD (S : Type) := {
  A_sg_CI_sg_CI_AD_eqv          : A_eqv S 
; A_sg_CI_sg_CI_AD_plus         : binary_op S 
; A_sg_CI_sg_CI_AD_times        : binary_op S 

; A_sg_CI_sg_CI_AD_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_sg_CI_sg_CI_AD_eqv) 
                                                  A_sg_CI_sg_CI_AD_plus
; A_sg_CI_sg_CI_AD_times_proofs : sg_CI_proofs S (A_eqv_eq S A_sg_CI_sg_CI_AD_eqv) 
                                                  A_sg_CI_sg_CI_AD_times
; A_sg_CI_sg_CI_AD_proofs       : sg_sg_LALD_proofs S (A_eqv_eq S A_sg_CI_sg_CI_AD_eqv) 
                                                       A_sg_CI_sg_CI_AD_plus
                                                       A_sg_CI_sg_CI_AD_times
; A_sg_CI_sg_CI_AD_ast          : ast_sg_CI_sg_CI_AD
}.



(* totally ordered lattice *) 
Record A_sg_CS_sg_CS_A (S : Type) := {
  A_sg_CS_sg_CS_A_eqv          : A_eqv S 
; A_sg_CS_sg_CS_A_plus         : binary_op S 
; A_sg_CS_sg_CS_A_times        : binary_op S 

; A_sg_CS_sg_CS_A_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_CS_A_eqv) 
                                                  A_sg_CS_sg_CS_A_plus
; A_sg_CS_sg_CS_A_times_proofs : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_CS_A_eqv) 
                                                  A_sg_CS_sg_CS_A_times
; A_sg_CS_sg_CS_A_proofs       : sg_sg_LA_proofs S (A_eqv_eq S A_sg_CS_sg_CS_A_eqv) 
                                                       A_sg_CS_sg_CS_A_plus
                                                       A_sg_CS_sg_CS_A_times
; A_sg_CS_sg_CS_A_ast          : ast_sg_CS_sg_CS_A 
}.




(* totally ordered distributive lattice *) 
Record A_sg_CS_sg_CS_AD (S : Type) := {
  A_sg_CS_sg_CS_AD_eqv          : A_eqv S 
; A_sg_CS_sg_CS_AD_plus         : binary_op S 
; A_sg_CS_sg_CS_AD_times        : binary_op S 

; A_sg_CS_sg_CS_AD_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_CS_AD_eqv) 
                                                  A_sg_CS_sg_CS_AD_plus
; A_sg_CS_sg_CS_AD_times_proofs : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_CS_AD_eqv) 
                                                  A_sg_CS_sg_CS_AD_times
; A_sg_CS_sg_CS_AD_proofs       : sg_sg_LALD_proofs S (A_eqv_eq S A_sg_CS_sg_CS_AD_eqv) 
                                                       A_sg_CS_sg_CS_AD_plus
                                                       A_sg_CS_sg_CS_AD_times
; A_sg_CS_sg_CS_AD_ast          : ast_sg_CS_sg_CS_AD
}.


(* think max-plus ... *) 
Record A_sg_CS_sg_CK_D (S : Type) := {
  A_sg_CS_sg_CK_D_eqv          : A_eqv S 
; A_sg_CS_sg_CK_D_plus         : binary_op S 
; A_sg_CS_sg_CK_D_times        : binary_op S 
; A_sg_CS_sg_CK_D_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_CK_D_eqv) 
                                                 A_sg_CS_sg_CK_D_plus
; A_sg_CS_sg_CK_D_times_proofs : sg_CK_proofs S (A_eqv_eq S A_sg_CS_sg_CK_D_eqv) 
                                                  A_sg_CS_sg_CK_D_times
; A_sg_CS_sg_CK_D_proofs       : sg_sg_LD_proofs S (A_eqv_eq S A_sg_CS_sg_CK_D_eqv) 
                                                       A_sg_CS_sg_CK_D_plus
                                                       A_sg_CS_sg_CK_D_times
; A_sg_CS_sg_CK_D_ast          : ast_sg_CS_sg_CK_D
}.

(* think min-plus ... *) 
Record A_sg_CS_sg_CK_AD (S : Type) := {
  A_sg_CS_sg_CK_AD_eqv          : A_eqv S 
; A_sg_CS_sg_CK_AD_plus         : binary_op S 
; A_sg_CS_sg_CK_AD_times        : binary_op S 
; A_sg_CS_sg_CK_AD_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sg_CS_sg_CK_AD_eqv) 
                                                  A_sg_CS_sg_CK_AD_plus
; A_sg_CS_sg_CK_AD_times_proofs : sg_CK_proofs S (A_eqv_eq S A_sg_CS_sg_CK_AD_eqv) 
                                                  A_sg_CS_sg_CK_AD_times
; A_sg_CS_sg_CK_AD_proofs       : sg_sg_LALD_proofs S (A_eqv_eq S A_sg_CS_sg_CK_AD_eqv) 
                                                       A_sg_CS_sg_CK_AD_plus
                                                       A_sg_CS_sg_CK_AD_times
; A_sg_CS_sg_CK_AD_ast          : ast_sg_CS_sg_CK_AD
}.




(*

*) 



(* 
Record A_sg_sg_D (S : Type) := {
  A_sg_sg_D_eq           : brel S 
; A_sg_sg_D_plus         : binary_op S 
; A_sg_sg_D_times        : binary_op S 
; A_sg_sg_D_eqv_proofs   : eqv_proofs S     A_sg_sg_D_eq
; A_sg_sg_D_plus_proofs  : sg_proofs S      A_sg_sg_D_eq A_sg_sg_D_plus
; A_sg_sg_D_times_proofs : sg_proofs S      A_sg_sg_D_eq A_sg_sg_D_times 
; A_sg_sg_D_proofs       : sg_sg_D_proofs S A_sg_sg_D_eq A_sg_sg_D_plus A_sg_sg_D_times 
; A_sg_sg_D_ast          : ast_sg_sg_D 
}.

Record A_sg_CS_sg_D (S : Type) := {
  A_sg_CS_sg_D_eq           : brel S 
; A_sg_CS_sg_D_plus         : binary_op S 
; A_sg_CS_sg_D_times        : binary_op S 
; A_sg_CS_sg_D_eqv_proofs   : eqv_proofs S     A_sg_CS_sg_D_eq
; A_sg_CS_sg_D_plus_proofs  : sg_CS_proofs S   A_sg_CS_sg_D_eq A_sg_CS_sg_D_plus
; A_sg_CS_sg_D_times_proofs : sg_proofs S      A_sg_CS_sg_D_eq A_sg_CS_sg_D_times 
; A_sg_CS_sg_D_proofs       : sg_sg_D_proofs S A_sg_CS_sg_D_eq A_sg_CS_sg_D_plus A_sg_CS_sg_D_times 
; A_sg_CS_sg_D_ast          : ast_sg_CS_sg_D
}.

Record A_sg_CS_sg_BD (S : Type) := {
  A_sg_CS_sg_BD_eq           : brel S 
; A_sg_CS_sg_BD_plus         : binary_op S 
; A_sg_CS_sg_BD_times        : binary_op S 
; A_sg_CS_sg_BD_eqv_proofs   : eqv_proofs S      A_sg_CS_sg_BD_eq
; A_sg_CS_sg_BD_plus_proofs  : sg_CS_proofs S    A_sg_CS_sg_BD_eq A_sg_CS_sg_BD_plus
; A_sg_CS_sg_BD_times_proofs : sg_proofs S       A_sg_CS_sg_BD_eq A_sg_CS_sg_BD_times 
; A_sg_CS_sg_BD_proofs       : sg_sg_BD_proofs S A_sg_CS_sg_BD_eq A_sg_CS_sg_BD_plus 
                                                 A_sg_CS_sg_BD_times 
; A_sg_CS_sg_BD_ast          : ast_sg_CS_sg_BD
}.

Record A_sg_CS_sg_D (S : Type) := {
  A_sg_CS_sg_D_eq           : brel S 
; A_sg_CS_sg_D_plus         : binary_op S 
; A_sg_CS_sg_D_times        : binary_op S 
; A_sg_CS_sg_D_eqv_proofs   : eqv_proofs S     A_sg_CS_sg_D_eq
; A_sg_CS_sg_D_plus_proofs  : sg_CS_proofs S   A_sg_CS_sg_D_eq A_sg_CS_sg_D_plus
; A_sg_CS_sg_D_times_proofs : sg_proofs S      A_sg_CS_sg_D_eq A_sg_CS_sg_D_times 
; A_sg_CS_sg_D_proofs       : sg_sg_D_proofs S A_sg_CS_sg_D_eq A_sg_CS_sg_D_plus A_sg_CS_sg_D_times 
; A_sg_CS_sg_D_ast          : ast_sg_CS_sg_D
}.

Record A_sg_CS_sg_BD (S : Type) := {
  A_sg_CS_sg_BD_eq           : brel S 
; A_sg_CS_sg_BD_plus         : binary_op S 
; A_sg_CS_sg_BD_times        : binary_op S 
; A_sg_CS_sg_BD_eqv_proofs   : eqv_proofs S      A_sg_CS_sg_BD_eq
; A_sg_CS_sg_BD_plus_proofs  : sg_CS_proofs S    A_sg_CS_sg_BD_eq A_sg_CS_sg_BD_plus
; A_sg_CS_sg_BD_times_proofs : sg_proofs S       A_sg_CS_sg_BD_eq A_sg_CS_sg_BD_times 
; A_sg_CS_sg_BD_proofs       : sg_sg_BD_proofs S A_sg_CS_sg_BD_eq A_sg_CS_sg_BD_plus 
                                                 A_sg_CS_sg_BD_times 
; A_sg_CS_sg_BD_ast          : ast_sg_CS_sg_BD
}.




(* po *) 
Record A_po (S : Type) := {
  A_po_eq           : brel S 
; A_po_lte          : brel S 
; A_po_eqv_proofs   : eqv_proofs S A_po_eq
; A_po_po_proofs    : po_proofs S A_po_eq A_po_lte
; A_po_ast          : ast_po
}.

(* to *) 
Record A_to (S : Type) := {
  A_to_eq           : brel S 
; A_to_lte          : brel S 
; A_to_eqv_proofs   : eqv_proofs S A_to_eq
; A_to_to_proofs    : to_proofs S A_to_eq A_to_lte
; A_to_ast          : ast_to
}.
*) 