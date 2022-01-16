Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.

(* semigroups 

Current classification. 

sg     = semigroup 
sg_C   = commutative semigroup 
sg_NC  = noncommutative semigroup 
sg_CS  = commutative selective semigroup (is idempotent, of course) 
sg_CI  = commutative idempotent semigroup, not selective 
sg_CNI = commutative non-idempotent semigroup, not selective 
sg_CK  = commutative cancellative semigroup (can't be idempotent, see below)

           sg ------------------------
           |                         |
           |                         |
          sg_C                     sg_NC 
         / |  \ 
        /  |   \                (deplicate hierarchy here? but with K, LK, and RK) 
       /   |    \  
  sg_CI sg_CNI  sg_CS 
           | 
           |
         sg_CK

Note, if cancellative, 

    LK: a * b = a * c -> b = c      

suppose c is any idempotent : c * c = c, then c = id 

    c * a = (c * c) * a = c * (c * a) 
    -LK-> a = c * a 
    so, LK -> idem(c) -> left_id(c), etc 

So any cancellative idempotent commutative semigroup will be trivial {id}. 
Since all carriers are non-trivial, sg_CI, sg_CS, and sg_CK are distinct. 

Note : each class contains just enough info so that 
we can always "cast up" in this hierarchy using the 
implications in sg/theory.v.  (see sg/cast_up.v) 
*) 


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

(* currently plays no role *) 
Record sg_NC_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_NC_associative      : bop_associative S eq bop 
; A_sg_NC_congruence       : bop_congruence S eq bop   
; A_sg_NC_not_commutative  : bop_not_commutative S eq bop  
; A_sg_NC_selective_d      : bop_selective_decidable S eq bop  
; A_sg_NC_idempotent_d     : bop_idempotent_decidable S eq bop  
; A_sg_NC_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_NC_is_right_d       : bop_is_right_decidable S eq bop  
; A_sg_NC_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_NC_right_cancel_d   : bop_right_cancellative_decidable S eq bop 
; A_sg_NC_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_NC_right_constant_d : bop_right_constant_decidable S eq bop 
; A_sg_NC_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_NC_anti_right_d     : bop_anti_right_decidable S eq bop

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

Record sg_CNI_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CNI_associative     : bop_associative S eq bop 
; A_sg_CNI_congruence     : bop_congruence S eq bop   
; A_sg_CNI_commutative     : bop_commutative S eq bop  
; A_sg_CNI_not_idempotent : bop_not_idempotent S eq bop

; A_sg_CNI_cancel_d         : bop_left_cancellative_decidable S eq bop 
; A_sg_CNI_constant_d       : bop_left_constant_decidable S eq bop
; A_sg_CNI_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_CNI_anti_right_d     : bop_anti_right_decidable S eq bop                                                         
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


(*********************************** sg = semigroup ******************************)

Record A_sg (S : Type) := {
  A_sg_eqv          : A_eqv S
; A_sg_bop          : binary_op S
; A_sg_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_eqv) A_sg_bop
; A_sg_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_eqv) A_sg_bop
; A_sg_proofs       : sg_proofs S (A_eqv_eq S A_sg_eqv) A_sg_bop
; A_sg_ast          : cas_ast
}.


(*********************************** sg_C = commutative semigroup ******************************) 
Record A_sg_C (S : Type) := {
  A_sg_C_eqv            : A_eqv S
; A_sg_C_bop            : binary_op S
; A_sg_C_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_proofs         : sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_ast            : cas_ast
}.

Record A_sg_C_with_ann (S : Type) := {
  A_sg_C_wa_eqv           : A_eqv S
; A_sg_C_wa_bop           : binary_op S
; A_sg_C_wa_not_exists_id : bop_not_exists_id S (A_eqv_eq S A_sg_C_wa_eqv) A_sg_C_wa_bop
; A_sg_C_wa_exists_ann    : bop_exists_ann S (A_eqv_eq S A_sg_C_wa_eqv) A_sg_C_wa_bop
; A_sg_C_wa_proofs        : sg_C_proofs S (A_eqv_eq S A_sg_C_wa_eqv) A_sg_C_wa_bop
; A_sg_C_wa_ast           : cas_ast
}.

Record A_sg_C_with_id (S : Type) := {
  A_sg_C_wi_eqv            : A_eqv S
; A_sg_C_wi_bop            : binary_op S
; A_sg_C_wi_exists_id      : bop_exists_id S (A_eqv_eq S A_sg_C_wi_eqv) A_sg_C_wi_bop
; A_sg_C_wi_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_C_wi_eqv) A_sg_C_wi_bop
; A_sg_C_wi_proofs         : sg_C_proofs S (A_eqv_eq S A_sg_C_wi_eqv) A_sg_C_wi_bop
; A_sg_C_wi_ast            : cas_ast
}.

(* bounded sg_C *) 
Record A_sg_BC (S : Type) := {
  A_sg_BC_eqv          : A_eqv S
; A_sg_BC_bop          : binary_op S
; A_sg_BC_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_BC_eqv) A_sg_BC_bop
; A_sg_BC_exists_ann   : bop_exists_ann S (A_eqv_eq S A_sg_BC_eqv) A_sg_BC_bop
; A_sg_BC_proofs       : sg_C_proofs S (A_eqv_eq S A_sg_BC_eqv) A_sg_BC_bop
; A_sg_BC_ast          : cas_ast
}.

(*********************************** sg_NC = non-commutative semigroup ******************************) 
Record A_sg_NC (S : Type) := {
  A_sg_NC_eqv            : A_eqv S
; A_sg_NC_bop            : binary_op S
; A_sg_NC_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_NC_eqv) A_sg_NC_bop
; A_sg_NC_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_NC_eqv) A_sg_NC_bop
; A_sg_NC_proofs         : sg_NC_proofs S (A_eqv_eq S A_sg_NC_eqv) A_sg_NC_bop
; A_sg_NC_ast            : cas_ast
}.

Record A_sg_NC_with_ann (S : Type) := {
  A_sg_NC_wa_eqv           : A_eqv S
; A_sg_NC_wa_bop           : binary_op S
; A_sg_NC_wa_not_exists_id : bop_not_exists_id S (A_eqv_eq S A_sg_NC_wa_eqv) A_sg_NC_wa_bop
; A_sg_NC_wa_exists_ann    : bop_exists_ann S (A_eqv_eq S A_sg_NC_wa_eqv) A_sg_NC_wa_bop
; A_sg_NC_wa_proofs        : sg_NC_proofs S (A_eqv_eq S A_sg_NC_wa_eqv) A_sg_NC_wa_bop
; A_sg_NC_wa_ast           : cas_ast
}.

Record A_sg_NC_with_id (S : Type) := {
  A_sg_NC_wi_eqv            : A_eqv S
; A_sg_NC_wi_bop            : binary_op S
; A_sg_NC_wi_exists_id      : bop_exists_id S (A_eqv_eq S A_sg_NC_wi_eqv) A_sg_NC_wi_bop
; A_sg_NC_wi_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_NC_wi_eqv) A_sg_NC_wi_bop
; A_sg_NC_wi_proofs         : sg_NC_proofs S (A_eqv_eq S A_sg_NC_wi_eqv) A_sg_NC_wi_bop
; A_sg_NC_wi_ast            : cas_ast
}.

(* bounded sg_NC *) 
Record A_sg_BNC (S : Type) := {
  A_sg_BNC_eqv          : A_eqv S
; A_sg_BNC_bop          : binary_op S
; A_sg_BNC_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_BNC_eqv) A_sg_BNC_bop
; A_sg_BNC_exists_ann   : bop_exists_ann S (A_eqv_eq S A_sg_BNC_eqv) A_sg_BNC_bop
; A_sg_BNC_proofs       : sg_NC_proofs S (A_eqv_eq S A_sg_BNC_eqv) A_sg_BNC_bop
; A_sg_BNC_ast          : cas_ast
}.

(*********************** sg_CI = commutative idempotent semigroup ****************************) 
Record A_sg_CI (S : Type) := {
  A_sg_CI_eqv            : A_eqv S
; A_sg_CI_bop            : binary_op S
; A_sg_CI_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_proofs         : sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_ast            : cas_ast
}.

Record A_sg_CI_with_ann (S : Type) := {
  A_sg_CI_wa_eqv            : A_eqv S
; A_sg_CI_wa_bop            : binary_op S
; A_sg_CI_wa_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_CI_wa_eqv) A_sg_CI_wa_bop
; A_sg_CI_wa_exists_ann     : bop_exists_ann S (A_eqv_eq S A_sg_CI_wa_eqv) A_sg_CI_wa_bop
; A_sg_CI_wa_proofs         : sg_CI_proofs S (A_eqv_eq S A_sg_CI_wa_eqv) A_sg_CI_wa_bop
; A_sg_CI_wa_ast            : cas_ast
}.

Record A_sg_CI_with_id (S : Type) := {
  A_sg_CI_wi_eqv            : A_eqv S
; A_sg_CI_wi_bop            : binary_op S
; A_sg_CI_wi_exists_id      : bop_exists_id S (A_eqv_eq S A_sg_CI_wi_eqv) A_sg_CI_wi_bop
; A_sg_CI_wi_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_CI_wi_eqv) A_sg_CI_wi_bop
; A_sg_CI_wi_proofs         : sg_CI_proofs S (A_eqv_eq S A_sg_CI_wi_eqv) A_sg_CI_wi_bop
; A_sg_CI_wi_ast            : cas_ast
}.

(* bounded sg_CI *) 
Record A_sg_BCI (S : Type) := {
  A_sg_BCI_eqv          : A_eqv S
; A_sg_BCI_bop          : binary_op S
; A_sg_BCI_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_BCI_eqv) A_sg_BCI_bop
; A_sg_BCI_exists_ann   : bop_exists_ann S (A_eqv_eq S A_sg_BCI_eqv) A_sg_BCI_bop
; A_sg_BCI_proofs       : sg_CI_proofs S (A_eqv_eq S A_sg_BCI_eqv) A_sg_BCI_bop
; A_sg_BCI_ast          : cas_ast
}.

(*********************** sg_CNI = commutative not-idempotent semigroup ****************************) 
Record A_sg_CNI (S : Type) := {
  A_sg_CNI_eqv            : A_eqv S
; A_sg_CNI_bop            : binary_op S
; A_sg_CNI_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_CNI_eqv) A_sg_CNI_bop
; A_sg_CNI_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_CNI_eqv) A_sg_CNI_bop
; A_sg_CNI_proofs         : sg_CNI_proofs S (A_eqv_eq S A_sg_CNI_eqv) A_sg_CNI_bop
; A_sg_CNI_ast            : cas_ast
}.

Record A_sg_CNI_with_ann (S : Type) := {
  A_sg_CNI_wa_eqv            : A_eqv S
; A_sg_CNI_wa_bop            : binary_op S
; A_sg_CNI_wa_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_CNI_wa_eqv) A_sg_CNI_wa_bop
; A_sg_CNI_wa_exists_ann     : bop_exists_ann S (A_eqv_eq S A_sg_CNI_wa_eqv) A_sg_CNI_wa_bop
; A_sg_CNI_wa_proofs         : sg_CNI_proofs S (A_eqv_eq S A_sg_CNI_wa_eqv) A_sg_CNI_wa_bop
; A_sg_CNI_wa_ast            : cas_ast
}.

Record A_sg_CNI_with_id (S : Type) := {
  A_sg_CNI_wi_eqv            : A_eqv S
; A_sg_CNI_wi_bop            : binary_op S
; A_sg_CNI_wi_exists_id      : bop_exists_id S (A_eqv_eq S A_sg_CNI_wi_eqv) A_sg_CNI_wi_bop
; A_sg_CNI_wi_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_CNI_wi_eqv) A_sg_CNI_wi_bop
; A_sg_CNI_wi_proofs         : sg_CNI_proofs S (A_eqv_eq S A_sg_CNI_wi_eqv) A_sg_CNI_wi_bop
; A_sg_CNI_wi_ast            : cas_ast
}.

(* bounded sg_CNI *) 
Record A_sg_BCNI (S : Type) := {
  A_sg_BCNI_eqv          : A_eqv S
; A_sg_BCNI_bop          : binary_op S
; A_sg_BCNI_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_BCNI_eqv) A_sg_BCNI_bop
; A_sg_BCNI_exists_ann   : bop_exists_ann S (A_eqv_eq S A_sg_BCNI_eqv) A_sg_BCNI_bop
; A_sg_BCNI_proofs       : sg_CNI_proofs S (A_eqv_eq S A_sg_BCNI_eqv) A_sg_BCNI_bop
; A_sg_BCNI_ast          : cas_ast
}.

(************************ sg_CS = commutative selective semigroup *************************) 

Record A_sg_CS (S : Type) := {
  A_sg_CS_eqv            : A_eqv S
; A_sg_CS_bop            : binary_op S
; A_sg_CS_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_not_exists_ann : bop_not_exists_ann  S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_proofs         : sg_CS_proofs S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_ast            : cas_ast
}.

Record A_sg_CS_with_ann (S : Type) := {
  A_sg_CS_wa_eqv            : A_eqv S
; A_sg_CS_wa_bop            : binary_op S
; A_sg_CS_wa_not_exists_id  : bop_not_exists_id S (A_eqv_eq S A_sg_CS_wa_eqv) A_sg_CS_wa_bop
; A_sg_CS_wa_exists_ann     : bop_exists_ann S (A_eqv_eq S A_sg_CS_wa_eqv) A_sg_CS_wa_bop
; A_sg_CS_wa_proofs         : sg_CS_proofs S (A_eqv_eq S A_sg_CS_wa_eqv) A_sg_CS_wa_bop
; A_sg_CS_wa_ast            : cas_ast
}.

Record A_sg_CS_with_id (S : Type) := {
  A_sg_CS_wi_eqv            : A_eqv S
; A_sg_CS_wi_bop            : binary_op S
; A_sg_CS_wi_exists_id      : bop_exists_id S (A_eqv_eq S A_sg_CS_wi_eqv) A_sg_CS_wi_bop
; A_sg_CS_wi_not_exists_ann : bop_not_exists_ann S (A_eqv_eq S A_sg_CS_wi_eqv) A_sg_CS_wi_bop
; A_sg_CS_wi_proofs         : sg_CS_proofs S (A_eqv_eq S A_sg_CS_wi_eqv) A_sg_CS_wi_bop
; A_sg_CS_wi_ast            : cas_ast
}.

(* bounded sg_CS *) 
Record A_sg_BCS (S : Type) := {
  A_sg_BCS_eqv          : A_eqv S
; A_sg_BCS_bop          : binary_op S
; A_sg_BCS_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_BCS_eqv) A_sg_BCS_bop
; A_sg_BCS_exists_ann   : bop_exists_ann S (A_eqv_eq S A_sg_BCS_eqv) A_sg_BCS_bop
; A_sg_BCS_proofs       : sg_CS_proofs S (A_eqv_eq S A_sg_BCS_eqv) A_sg_BCS_bop
; A_sg_BCS_ast          : cas_ast
}.


(************************ sg_CK = commutative cancellative semigroup *************************) 

Record A_sg_CK (S : Type) := {
  A_sg_CK_eqv           : A_eqv S
; A_sg_CK_bop           : binary_op S
; A_sg_CK_not_exists_id : bop_not_exists_id S (A_eqv_eq S A_sg_CK_eqv) A_sg_CK_bop
; A_sg_CK_proofs        : sg_CK_proofs S (A_eqv_eq S A_sg_CK_eqv) A_sg_CK_bop
; A_sg_CK_ast           : cas_ast
}.

Record A_sg_CK_with_id (S : Type) := {
  A_sg_CK_wi_eqv          : A_eqv S
; A_sg_CK_wi_bop          : binary_op S
; A_sg_CK_wi_exists_id    : bop_exists_id S (A_eqv_eq S A_sg_CK_wi_eqv) A_sg_CK_wi_bop
; A_sg_CK_wi_proofs       : sg_CK_proofs S (A_eqv_eq S A_sg_CK_wi_eqv) A_sg_CK_wi_bop
; A_sg_CK_wi_ast          : cas_ast
}.

End ACAS.


Section AMCAS.

Inductive sg_proofs_mcas (S: Type) (eq : brel S) (bop : binary_op S) := 
| A_MCAS_Proof_sg_Error : list string             -> sg_proofs_mcas S eq bop
| A_MCAS_Proof_sg       : sg_proofs S eq bop     -> sg_proofs_mcas S eq bop
| A_MCAS_Proof_sg_C     : sg_C_proofs S eq bop   -> sg_proofs_mcas S eq bop
| A_MCAS_Proof_sg_NC    : sg_NC_proofs S eq bop  -> sg_proofs_mcas S eq bop
| A_MCAS_Proof_sg_CS    : sg_CS_proofs S eq bop  -> sg_proofs_mcas S eq bop    
| A_MCAS_Proof_sg_CI    : sg_CI_proofs S eq bop  -> sg_proofs_mcas S eq bop
| A_MCAS_Proof_sg_CNI   : sg_CNI_proofs S eq bop -> sg_proofs_mcas S eq bop
| A_MCAS_Proof_sg_CK    : sg_CK_proofs S eq bop  -> sg_proofs_mcas S eq bop                                                                 
.

Inductive A_sg_mcas (S : Type) := 
| A_MCAS_sg_Error        : list string             -> A_sg_mcas S
| A_MCAS_sg              : A_sg S             -> A_sg_mcas S
| A_MCAS_sg_C            : A_sg_C S           -> A_sg_mcas S
| A_MCAS_sg_C_with_id    : A_sg_C_with_id S   -> A_sg_mcas S
| A_MCAS_sg_C_with_ann   : A_sg_C_with_ann S  -> A_sg_mcas S
| A_MCAS_sg_BC           : A_sg_BC S          -> A_sg_mcas S
| A_MCAS_sg_NC           : A_sg_NC S          -> A_sg_mcas S
| A_MCAS_sg_NC_with_id   : A_sg_NC_with_id S  -> A_sg_mcas S
| A_MCAS_sg_NC_with_ann  : A_sg_NC_with_ann S -> A_sg_mcas S
| A_MCAS_sg_BNC          : A_sg_BNC S         -> A_sg_mcas S
| A_MCAS_sg_CS           : A_sg_CS S          -> A_sg_mcas S
| A_MCAS_sg_CS_with_id   : A_sg_CS_with_id S  -> A_sg_mcas S
| A_MCAS_sg_CS_with_ann  : A_sg_CS_with_ann S -> A_sg_mcas S
| A_MCAS_sg_BCS          : A_sg_BCS S         -> A_sg_mcas S
| A_MCAS_sg_CI           : A_sg_CI S          -> A_sg_mcas S
| A_MCAS_sg_CI_with_id   : A_sg_CI_with_id S  -> A_sg_mcas S
| A_MCAS_sg_CI_with_ann  : A_sg_CI_with_ann S -> A_sg_mcas S
| A_MCAS_sg_BCI          : A_sg_BCI S         -> A_sg_mcas S
| A_MCAS_sg_CNI          : A_sg_CNI S         -> A_sg_mcas S
| A_MCAS_sg_CNI_with_id  : A_sg_CNI_with_id S -> A_sg_mcas S
| A_MCAS_sg_CNI_with_ann : A_sg_CNI_with_ann S -> A_sg_mcas S
| A_MCAS_sg_BCNI         : A_sg_BCNI S        -> A_sg_mcas S
| A_MCAS_sg_CK           : A_sg_CK S          -> A_sg_mcas S
| A_MCAS_sg_CK_with_id   : A_sg_CK_with_id S  -> A_sg_mcas S                                             
.




Definition A_sg_proofs_classify_sg_CNI
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (A : sg_CNI_proofs S eq bop) : sg_proofs_mcas S eq bop :=
match A_sg_CNI_cancel_d _ _ _ A with 
| inl cancel => A_MCAS_Proof_sg_CK _ _ _ 
                     {|
                         A_sg_CK_associative   := A_sg_CNI_associative _ _ _ A
                       ; A_sg_CK_congruence    := A_sg_CNI_congruence _ _ _ A
                       ; A_sg_CK_commutative   := A_sg_CNI_commutative _ _ _ A
                       ; A_sg_CK_cancel        := cancel  
                       ; A_sg_CK_anti_left_d   := A_sg_CNI_anti_left_d _ _ _ A
                       ; A_sg_CK_anti_right_d  := A_sg_CNI_anti_right_d _ _ _ A

                     |}
| inr _      => A_MCAS_Proof_sg_CNI _ _ _ A 
end.


Definition A_sg_proofs_classify_sg_C
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (A : sg_C_proofs S eq bop) : sg_proofs_mcas S eq bop :=
match A_sg_C_idempotent_d _ _ _ A with 
| inl idem =>
  match A_sg_C_selective_d _ _ _ A with
  | inl sel => A_MCAS_Proof_sg_CS _ _ _
                {|    
                    A_sg_CS_associative        := A_sg_C_associative _ _ _ A 
                  ; A_sg_CS_congruence         := A_sg_C_congruence  _ _ _ A 
                  ; A_sg_CS_commutative        := A_sg_C_commutative  _ _ _ A 
                  ; A_sg_CS_selective          := sel 
                |}
  | inr nsel => A_MCAS_Proof_sg_CI _ _ _
                {|    
                    A_sg_CI_associative        := A_sg_C_associative _ _ _ A 
                  ; A_sg_CI_congruence         := A_sg_C_congruence  _ _ _ A 
                  ; A_sg_CI_commutative        := A_sg_C_commutative  _ _ _ A
                  ; A_sg_CI_idempotent         := idem 
                  ; A_sg_CI_not_selective      := nsel 
                |}
  end 
| inr nidem  => A_MCAS_Proof_sg_CNI _ _ _
                {|
                    A_sg_CNI_associative     := A_sg_C_associative _ _ _ A 
                  ; A_sg_CNI_congruence      := A_sg_C_congruence  _ _ _ A 
                  ; A_sg_CNI_commutative     := A_sg_C_commutative  _ _ _ A 
                  ; A_sg_CNI_not_idempotent  := nidem 
                  ; A_sg_CNI_cancel_d        := A_sg_C_cancel_d  _ _ _ A 
                  ; A_sg_CNI_constant_d      := A_sg_C_constant_d  _ _ _ A 
                  ; A_sg_CNI_anti_left_d     := A_sg_C_anti_left_d  _ _ _ A 
                  ; A_sg_CNI_anti_right_d    := A_sg_C_anti_right_d  _ _ _ A 
                |}
end.


Definition A_sg_proofs_classify_sg
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (P : sg_proofs S eq bop) : sg_proofs_mcas S eq bop :=
match A_sg_commutative_d _ _ _ P with 
| inl comm => A_sg_proofs_classify_sg_C _ _ _
   {| 
       A_sg_C_associative      := A_sg_associative _ _ _ P
     ; A_sg_C_congruence       := A_sg_congruence _ _ _ P
     ; A_sg_C_commutative      := comm 
     ; A_sg_C_anti_left_d      := A_sg_anti_left_d _ _ _ P
     ; A_sg_C_anti_right_d     := A_sg_anti_right_d _ _ _ P
     ; A_sg_C_selective_d      := A_sg_selective_d _ _ _ P
     ; A_sg_C_idempotent_d     := A_sg_idempotent_d _ _ _ P
     ; A_sg_C_cancel_d         := A_sg_left_cancel_d _ _ _ P
     ; A_sg_C_constant_d       := A_sg_left_constant_d _ _ _ P
   |}                                        
| inr ncomm  => A_MCAS_Proof_sg_NC _ _ _
   {| 
       A_sg_NC_associative      := A_sg_associative _ _ _ P
     ; A_sg_NC_congruence       := A_sg_congruence _ _ _ P
     ; A_sg_NC_not_commutative  := ncomm 
     ; A_sg_NC_selective_d      := A_sg_selective_d _ _ _ P
     ; A_sg_NC_idempotent_d     := A_sg_idempotent_d _ _ _ P
     ; A_sg_NC_is_left_d        := A_sg_is_left_d _ _ _ P
     ; A_sg_NC_is_right_d       := A_sg_is_right_d _ _ _ P    
     ; A_sg_NC_left_cancel_d    := A_sg_left_cancel_d _ _ _ P
     ; A_sg_NC_right_cancel_d   := A_sg_right_cancel_d _ _ _ P
     ; A_sg_NC_left_constant_d  := A_sg_left_constant_d _ _ _ P
     ; A_sg_NC_right_constant_d := A_sg_right_constant_d _ _ _ P
     ; A_sg_NC_anti_left_d      := A_sg_anti_left_d _ _ _ P
     ; A_sg_NC_anti_right_d     := A_sg_anti_right_d _ _ _ P
     |}                                     
end.

Definition sg_proof_classify
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (A : sg_proofs_mcas S eq bop) : sg_proofs_mcas S eq bop :=
match A with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A 
| A_MCAS_Proof_sg _ _ _ B       => A_sg_proofs_classify_sg _ _ _ B
| A_MCAS_Proof_sg_C  _ _ _ B    => A_sg_proofs_classify_sg_C _ _ _ B
| A_MCAS_Proof_sg_NC _ _ _ B    => A
| A_MCAS_Proof_sg_CS _ _ _ B    => A
| A_MCAS_Proof_sg_CI _ _ _ B    => A
| A_MCAS_Proof_sg_CNI _ _ _ B   => A_sg_proofs_classify_sg_CNI _ _ _ B
| A_MCAS_Proof_sg_CK _ _ _ B    => A
end                                   
.

Local Open Scope string_scope.


Definition A_sg_classify_sg_CNI (S : Type) (A : A_sg_CNI S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg_CNI _ _ _ (A_sg_CNI_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg_CNI" :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg_CNI" :: nil) 
| A_MCAS_Proof_sg_NC _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (3) : sg_classify_sg_CNI" :: nil) 
| A_MCAS_Proof_sg_CS _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (4) : sg_classify_sg_CNI" :: nil) 
| A_MCAS_Proof_sg_CI _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (5) : sg_classify_sg_CNI" :: nil) 
| A_MCAS_Proof_sg_CNI _ _ _ P   => A_MCAS_sg_CNI _ A 
| A_MCAS_Proof_sg_CK _ _ _ P    => A_MCAS_sg_CK _
                {|
                    A_sg_CK_eqv            := A_sg_CNI_eqv _ A 
                  ; A_sg_CK_bop            := A_sg_CNI_bop _ A 
                  ; A_sg_CK_not_exists_id  := A_sg_CNI_not_exists_id _ A
                  ; A_sg_CK_proofs         := P 
                  ; A_sg_CK_ast            := A_sg_CNI_ast _ A 
                |}
end.


Definition A_sg_classify_sg_CNI_with_id (S : Type) (A : A_sg_CNI_with_id S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg_CNI _ _ _ (A_sg_CNI_wi_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg_CNI_with_id"  :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg_CNI_with_id" :: nil) 
| A_MCAS_Proof_sg_NC _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (3) : sg_classify_sg_CNI_with_id" :: nil) 
| A_MCAS_Proof_sg_CS _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (4) : sg_classify_sg_CNI_with_id" :: nil) 
| A_MCAS_Proof_sg_CI _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (5) : sg_classify_sg_CNI_with_id" :: nil) 
| A_MCAS_Proof_sg_CNI _ _ _ P   => A_MCAS_sg_CNI_with_id _ A 
| A_MCAS_Proof_sg_CK _ _ _ P    => A_MCAS_sg_CK_with_id _
                {|
                    A_sg_CK_wi_eqv            := A_sg_CNI_wi_eqv _ A 
                  ; A_sg_CK_wi_bop            := A_sg_CNI_wi_bop _ A 
                  ; A_sg_CK_wi_exists_id      := A_sg_CNI_wi_exists_id _ A
                  ; A_sg_CK_wi_proofs         := P 
                  ; A_sg_CK_wi_ast            := A_sg_CNI_wi_ast _ A 
                |}
end.


Definition A_sg_classify_sg_C (S : Type) (A : A_sg_C S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg_C _ _ _ (A_sg_C_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg_C"  :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    => A_MCAS_sg_C _ A 
| A_MCAS_Proof_sg_NC _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg_C"  :: nil) 
| A_MCAS_Proof_sg_CS _ _ _ P    => A_MCAS_sg_CS _
                {|
                    A_sg_CS_eqv            := A_sg_C_eqv _ A 
                  ; A_sg_CS_bop            := A_sg_C_bop _ A 
                  ; A_sg_CS_not_exists_id  := A_sg_C_not_exists_id _ A
                  ; A_sg_CS_not_exists_ann := A_sg_C_not_exists_ann _ A 
                  ; A_sg_CS_proofs         := P 
                  ; A_sg_CS_ast            := A_sg_C_ast _ A 
                |}       
| A_MCAS_Proof_sg_CI _ _ _ P    => A_MCAS_sg_CI _
                {|
                    A_sg_CI_eqv            := A_sg_C_eqv _ A 
                  ; A_sg_CI_bop            := A_sg_C_bop _ A 
                  ; A_sg_CI_not_exists_id  := A_sg_C_not_exists_id _ A
                  ; A_sg_CI_not_exists_ann := A_sg_C_not_exists_ann _ A 
                  ; A_sg_CI_proofs         := P 
                  ; A_sg_CI_ast            := A_sg_C_ast _ A 
                |}       
| A_MCAS_Proof_sg_CNI _ _ _ P   => A_MCAS_sg_CNI _
                {|
                    A_sg_CNI_eqv            := A_sg_C_eqv _ A 
                  ; A_sg_CNI_bop            := A_sg_C_bop _ A 
                  ; A_sg_CNI_not_exists_id  := A_sg_C_not_exists_id _ A
                  ; A_sg_CNI_not_exists_ann := A_sg_C_not_exists_ann _ A 
                  ; A_sg_CNI_proofs         := P 
                  ; A_sg_CNI_ast            := A_sg_C_ast _ A 
                |}       
| A_MCAS_Proof_sg_CK _ _ _ P    => A_MCAS_sg_CK _
                {|
                    A_sg_CK_eqv            := A_sg_C_eqv _ A 
                  ; A_sg_CK_bop            := A_sg_C_bop _ A 
                  ; A_sg_CK_not_exists_id  := A_sg_C_not_exists_id _ A
                  ; A_sg_CK_proofs         := P 
                  ; A_sg_CK_ast            := A_sg_C_ast _ A 
                |}
end.




Definition A_sg_classify_sg_C_with_id (S : Type) (A : A_sg_C_with_id S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg_C _ _ _ (A_sg_C_wi_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg_C_with_id"  :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    => A_MCAS_sg_C_with_id _ A 
| A_MCAS_Proof_sg_NC _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg_C_with_id"     :: nil) 
| A_MCAS_Proof_sg_CS _ _ _ P    => A_MCAS_sg_CS_with_id _
                {|
                    A_sg_CS_wi_eqv            := A_sg_C_wi_eqv _ A 
                  ; A_sg_CS_wi_bop            := A_sg_C_wi_bop _ A 
                  ; A_sg_CS_wi_exists_id      := A_sg_C_wi_exists_id _ A
                  ; A_sg_CS_wi_not_exists_ann := A_sg_C_wi_not_exists_ann _ A 
                  ; A_sg_CS_wi_proofs         := P 
                  ; A_sg_CS_wi_ast            := A_sg_C_wi_ast _ A 
                |}       
| A_MCAS_Proof_sg_CI _ _ _ P    => A_MCAS_sg_CI_with_id _
                {|
                    A_sg_CI_wi_eqv            := A_sg_C_wi_eqv _ A 
                  ; A_sg_CI_wi_bop            := A_sg_C_wi_bop _ A 
                  ; A_sg_CI_wi_exists_id      := A_sg_C_wi_exists_id _ A
                  ; A_sg_CI_wi_not_exists_ann := A_sg_C_wi_not_exists_ann _ A 
                  ; A_sg_CI_wi_proofs         := P 
                  ; A_sg_CI_wi_ast            := A_sg_C_wi_ast _ A 
                |}       
| A_MCAS_Proof_sg_CNI _ _ _ P   => A_MCAS_sg_CNI_with_id _
                {|
                    A_sg_CNI_wi_eqv            := A_sg_C_wi_eqv _ A 
                  ; A_sg_CNI_wi_bop            := A_sg_C_wi_bop _ A 
                  ; A_sg_CNI_wi_exists_id      := A_sg_C_wi_exists_id _ A
                  ; A_sg_CNI_wi_not_exists_ann := A_sg_C_wi_not_exists_ann _ A 
                  ; A_sg_CNI_wi_proofs         := P 
                  ; A_sg_CNI_wi_ast            := A_sg_C_wi_ast _ A 
                |}       
| A_MCAS_Proof_sg_CK _ _ _ P    => A_MCAS_sg_CK_with_id _
                {|
                    A_sg_CK_wi_eqv            := A_sg_C_wi_eqv _ A 
                  ; A_sg_CK_wi_bop            := A_sg_C_wi_bop _ A 
                  ; A_sg_CK_wi_exists_id      := A_sg_C_wi_exists_id _ A
                  ; A_sg_CK_wi_proofs         := P 
                  ; A_sg_CK_wi_ast            := A_sg_C_wi_ast _ A 
                |}
end.

Definition A_sg_classify_sg_C_with_ann (S : Type) (A : A_sg_C_with_ann S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg_C _ _ _ (A_sg_C_wa_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg_C_with_ann"  :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    => A_MCAS_sg_C_with_ann _ A 
| A_MCAS_Proof_sg_NC _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg_C_with_ann"  :: nil) 
| A_MCAS_Proof_sg_CS _ _ _ P    => A_MCAS_sg_CS_with_ann _
                {|
                    A_sg_CS_wa_eqv            := A_sg_C_wa_eqv _ A 
                  ; A_sg_CS_wa_bop            := A_sg_C_wa_bop _ A 
                  ; A_sg_CS_wa_not_exists_id  := A_sg_C_wa_not_exists_id _ A
                  ; A_sg_CS_wa_exists_ann     := A_sg_C_wa_exists_ann _ A 
                  ; A_sg_CS_wa_proofs         := P 
                  ; A_sg_CS_wa_ast            := A_sg_C_wa_ast _ A 
                |}       
| A_MCAS_Proof_sg_CI _ _ _ P    => A_MCAS_sg_CI_with_ann _
                {|
                    A_sg_CI_wa_eqv            := A_sg_C_wa_eqv _ A 
                  ; A_sg_CI_wa_bop            := A_sg_C_wa_bop _ A 
                  ; A_sg_CI_wa_not_exists_id  := A_sg_C_wa_not_exists_id _ A
                  ; A_sg_CI_wa_exists_ann     := A_sg_C_wa_exists_ann _ A 
                  ; A_sg_CI_wa_proofs         := P 
                  ; A_sg_CI_wa_ast            := A_sg_C_wa_ast _ A 
                |}       
| A_MCAS_Proof_sg_CNI _ _ _ P   => A_MCAS_sg_CNI_with_ann _
                {|
                    A_sg_CNI_wa_eqv            := A_sg_C_wa_eqv _ A 
                  ; A_sg_CNI_wa_bop            := A_sg_C_wa_bop _ A 
                  ; A_sg_CNI_wa_not_exists_id  := A_sg_C_wa_not_exists_id _ A
                  ; A_sg_CNI_wa_exists_ann     := A_sg_C_wa_exists_ann _ A 
                  ; A_sg_CNI_wa_proofs         := P 
                  ; A_sg_CNI_wa_ast            := A_sg_C_wa_ast _ A 
                |}       
| A_MCAS_Proof_sg_CK _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (3) : sg_classify_sg_C_with_ann"  :: nil) 
end.

Definition A_sg_classify_sg_BC (S : Type) (A : A_sg_BC S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg_C _ _ _ (A_sg_BC_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg_BC"  :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    => A_MCAS_sg_BC _ A 
| A_MCAS_Proof_sg_NC _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg_BC"  :: nil) 
| A_MCAS_Proof_sg_CS _ _ _ P    => A_MCAS_sg_BCS _
                {|
                    A_sg_BCS_eqv            := A_sg_BC_eqv _ A 
                  ; A_sg_BCS_bop            := A_sg_BC_bop _ A 
                  ; A_sg_BCS_exists_id      := A_sg_BC_exists_id _ A
                  ; A_sg_BCS_exists_ann     := A_sg_BC_exists_ann _ A 
                  ; A_sg_BCS_proofs         := P 
                  ; A_sg_BCS_ast            := A_sg_BC_ast _ A 
                |}       
| A_MCAS_Proof_sg_CI _ _ _ P    => A_MCAS_sg_BCI _
                {|
                    A_sg_BCI_eqv            := A_sg_BC_eqv _ A 
                  ; A_sg_BCI_bop            := A_sg_BC_bop _ A 
                  ; A_sg_BCI_exists_id      := A_sg_BC_exists_id _ A
                  ; A_sg_BCI_exists_ann     := A_sg_BC_exists_ann _ A 
                  ; A_sg_BCI_proofs         := P 
                  ; A_sg_BCI_ast            := A_sg_BC_ast _ A 
                |}       
| A_MCAS_Proof_sg_CNI _ _ _ P   => A_MCAS_sg_BCNI _
                {|
                    A_sg_BCNI_eqv            := A_sg_BC_eqv _ A 
                  ; A_sg_BCNI_bop            := A_sg_BC_bop _ A 
                  ; A_sg_BCNI_exists_id      := A_sg_BC_exists_id _ A
                  ; A_sg_BCNI_exists_ann     := A_sg_BC_exists_ann _ A 
                  ; A_sg_BCNI_proofs         := P 
                  ; A_sg_BCNI_ast            := A_sg_BC_ast _ A 
                |}       
| A_MCAS_Proof_sg_CK _ _ _ P    => A_MCAS_sg_Error _ ("Internal Error (3) : sg_classify_sg_BC"  :: nil) 
end.



Definition A_sg_classify_sg (S : Type) (A : A_sg S) : A_sg_mcas S :=
match A_sg_proofs_classify_sg _ _ _ (A_sg_proofs _ A) with
| A_MCAS_Proof_sg_Error _ _ _ s =>  A_MCAS_sg_Error _ s 
| A_MCAS_Proof_sg _ _ _ _       => A_MCAS_sg_Error _ ("Internal Error (1) : sg_classify_sg" :: nil) 
| A_MCAS_Proof_sg_C  _ _ _ P    =>
  match A_sg_exists_id_d _ A, A_sg_exists_ann_d _ A with
  | inl idP, inl annP => A_MCAS_sg_BC _
                {|
                    A_sg_BC_eqv        := A_sg_eqv _ A 
                  ; A_sg_BC_bop        := A_sg_bop _ A 
                  ; A_sg_BC_exists_id  := idP
                  ; A_sg_BC_exists_ann := annP 
                  ; A_sg_BC_proofs     := P
                  ; A_sg_BC_ast        := A_sg_ast _ A 
                |}                                        
  | inl idP, inr nannP => A_MCAS_sg_C_with_id _
                {|
                    A_sg_C_wi_eqv            := A_sg_eqv _ A 
                  ; A_sg_C_wi_bop            := A_sg_bop _ A 
                  ; A_sg_C_wi_exists_id      := idP
                  ; A_sg_C_wi_not_exists_ann := nannP 
                  ; A_sg_C_wi_proofs         := P
                  ; A_sg_C_wi_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inl annP => A_MCAS_sg_C_with_ann _
                {|
                    A_sg_C_wa_eqv            := A_sg_eqv _ A 
                  ; A_sg_C_wa_bop            := A_sg_bop _ A 
                  ; A_sg_C_wa_not_exists_id  := nidP
                  ; A_sg_C_wa_exists_ann     := annP 
                  ; A_sg_C_wa_proofs         := P
                  ; A_sg_C_wa_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inr nannP => A_MCAS_sg_C _
                {|
                    A_sg_C_eqv            := A_sg_eqv _ A 
                  ; A_sg_C_bop            := A_sg_bop _ A 
                  ; A_sg_C_not_exists_id  := nidP
                  ; A_sg_C_not_exists_ann := nannP 
                  ; A_sg_C_proofs         := P
                  ; A_sg_C_ast            := A_sg_ast _ A 
                |}       
  end 
| A_MCAS_Proof_sg_NC _ _ _ P    => 
  match A_sg_exists_id_d _ A, A_sg_exists_ann_d _ A with
  | inl idP, inl annP => A_MCAS_sg_BNC _
                {|
                    A_sg_BNC_eqv        := A_sg_eqv _ A 
                  ; A_sg_BNC_bop        := A_sg_bop _ A 
                  ; A_sg_BNC_exists_id  := idP
                  ; A_sg_BNC_exists_ann := annP 
                  ; A_sg_BNC_proofs     := P 
                  ; A_sg_BNC_ast        := A_sg_ast _ A 
                |}                                        
  | inl idP, inr nannP => A_MCAS_sg_NC_with_id _
                {|
                    A_sg_NC_wi_eqv            := A_sg_eqv _ A 
                  ; A_sg_NC_wi_bop            := A_sg_bop _ A 
                  ; A_sg_NC_wi_exists_id      := idP
                  ; A_sg_NC_wi_not_exists_ann := nannP 
                  ; A_sg_NC_wi_proofs         := P 
                  ; A_sg_NC_wi_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inl annP => A_MCAS_sg_NC_with_ann _
                {|
                    A_sg_NC_wa_eqv            := A_sg_eqv _ A 
                  ; A_sg_NC_wa_bop            := A_sg_bop _ A 
                  ; A_sg_NC_wa_not_exists_id  := nidP
                  ; A_sg_NC_wa_exists_ann     := annP 
                  ; A_sg_NC_wa_proofs         := P 
                  ; A_sg_NC_wa_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inr nannP => A_MCAS_sg_NC _
                {|
                    A_sg_NC_eqv            := A_sg_eqv _ A 
                  ; A_sg_NC_bop            := A_sg_bop _ A 
                  ; A_sg_NC_not_exists_id  := nidP
                  ; A_sg_NC_not_exists_ann := nannP 
                  ; A_sg_NC_proofs         := P 
                  ; A_sg_NC_ast            := A_sg_ast _ A 
                |}       
  end 
| A_MCAS_Proof_sg_CS _ _ _ P    => 
  match A_sg_exists_id_d _ A, A_sg_exists_ann_d _ A with
  | inl idP, inl annP => A_MCAS_sg_BCS _
                {|
                    A_sg_BCS_eqv        := A_sg_eqv _ A 
                  ; A_sg_BCS_bop        := A_sg_bop _ A 
                  ; A_sg_BCS_exists_id  := idP
                  ; A_sg_BCS_exists_ann := annP 
                  ; A_sg_BCS_proofs     := P 
                  ; A_sg_BCS_ast        := A_sg_ast _ A 
                |}                                        
  | inl idP, inr nannP => A_MCAS_sg_CS_with_id _
                {|
                    A_sg_CS_wi_eqv            := A_sg_eqv _ A 
                  ; A_sg_CS_wi_bop            := A_sg_bop _ A 
                  ; A_sg_CS_wi_exists_id      := idP
                  ; A_sg_CS_wi_not_exists_ann := nannP 
                  ; A_sg_CS_wi_proofs         := P 
                  ; A_sg_CS_wi_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inl annP => A_MCAS_sg_CS_with_ann _
                {|
                    A_sg_CS_wa_eqv            := A_sg_eqv _ A 
                  ; A_sg_CS_wa_bop            := A_sg_bop _ A 
                  ; A_sg_CS_wa_not_exists_id  := nidP
                  ; A_sg_CS_wa_exists_ann     := annP 
                  ; A_sg_CS_wa_proofs         := P 
                  ; A_sg_CS_wa_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inr nannP => A_MCAS_sg_CS _
                {|
                    A_sg_CS_eqv            := A_sg_eqv _ A 
                  ; A_sg_CS_bop            := A_sg_bop _ A 
                  ; A_sg_CS_not_exists_id  := nidP
                  ; A_sg_CS_not_exists_ann := nannP 
                  ; A_sg_CS_proofs         := P 
                  ; A_sg_CS_ast            := A_sg_ast _ A 
                |}       
  end 
| A_MCAS_Proof_sg_CI _ _ _ P    => 
  match A_sg_exists_id_d _ A, A_sg_exists_ann_d _ A with
  | inl idP, inl annP => A_MCAS_sg_BCI _
                {|
                    A_sg_BCI_eqv        := A_sg_eqv _ A 
                  ; A_sg_BCI_bop        := A_sg_bop _ A 
                  ; A_sg_BCI_exists_id  := idP
                  ; A_sg_BCI_exists_ann := annP 
                  ; A_sg_BCI_proofs     := P 
                  ; A_sg_BCI_ast        := A_sg_ast _ A 
                |}                                        
  | inl idP, inr nannP => A_MCAS_sg_CI_with_id _
                {|
                    A_sg_CI_wi_eqv            := A_sg_eqv _ A 
                  ; A_sg_CI_wi_bop            := A_sg_bop _ A 
                  ; A_sg_CI_wi_exists_id      := idP
                  ; A_sg_CI_wi_not_exists_ann := nannP 
                  ; A_sg_CI_wi_proofs         := P 
                  ; A_sg_CI_wi_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inl annP => A_MCAS_sg_CI_with_ann _
                {|
                    A_sg_CI_wa_eqv            := A_sg_eqv _ A 
                  ; A_sg_CI_wa_bop            := A_sg_bop _ A 
                  ; A_sg_CI_wa_not_exists_id  := nidP
                  ; A_sg_CI_wa_exists_ann     := annP 
                  ; A_sg_CI_wa_proofs         := P 
                  ; A_sg_CI_wa_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inr nannP => A_MCAS_sg_CI _
                {|
                    A_sg_CI_eqv            := A_sg_eqv _ A 
                  ; A_sg_CI_bop            := A_sg_bop _ A 
                  ; A_sg_CI_not_exists_id  := nidP
                  ; A_sg_CI_not_exists_ann := nannP 
                  ; A_sg_CI_proofs         := P 
                  ; A_sg_CI_ast            := A_sg_ast _ A 
                |}       
  end 
| A_MCAS_Proof_sg_CNI _ _ _ P   => 
  match A_sg_exists_id_d _ A, A_sg_exists_ann_d _ A with
  | inl idP, inl annP => A_MCAS_sg_BCNI _
                {|
                    A_sg_BCNI_eqv        := A_sg_eqv _ A 
                  ; A_sg_BCNI_bop        := A_sg_bop _ A 
                  ; A_sg_BCNI_exists_id  := idP
                  ; A_sg_BCNI_exists_ann := annP 
                  ; A_sg_BCNI_proofs     := P 
                  ; A_sg_BCNI_ast        := A_sg_ast _ A 
                |}                                        
  | inl idP, inr nannP => A_MCAS_sg_CNI_with_id _
                {|
                    A_sg_CNI_wi_eqv            := A_sg_eqv _ A 
                  ; A_sg_CNI_wi_bop            := A_sg_bop _ A 
                  ; A_sg_CNI_wi_exists_id      := idP
                  ; A_sg_CNI_wi_not_exists_ann := nannP 
                  ; A_sg_CNI_wi_proofs         := P 
                  ; A_sg_CNI_wi_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inl annP => A_MCAS_sg_CNI_with_ann _
                {|
                    A_sg_CNI_wa_eqv            := A_sg_eqv _ A 
                  ; A_sg_CNI_wa_bop            := A_sg_bop _ A 
                  ; A_sg_CNI_wa_not_exists_id  := nidP
                  ; A_sg_CNI_wa_exists_ann     := annP 
                  ; A_sg_CNI_wa_proofs         := P 
                  ; A_sg_CNI_wa_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inr nannP => A_MCAS_sg_CNI _
                {|
                    A_sg_CNI_eqv            := A_sg_eqv _ A 
                  ; A_sg_CNI_bop            := A_sg_bop _ A 
                  ; A_sg_CNI_not_exists_id  := nidP
                  ; A_sg_CNI_not_exists_ann := nannP 
                  ; A_sg_CNI_proofs         := P 
                  ; A_sg_CNI_ast            := A_sg_ast _ A 
                |}       
  end 
| A_MCAS_Proof_sg_CK _ _ _ P    =>
  match A_sg_exists_id_d _ A, A_sg_exists_ann_d _ A with
  | inl idP, inr nannP => A_MCAS_sg_CK_with_id _
                {|
                    A_sg_CK_wi_eqv            := A_sg_eqv _ A 
                  ; A_sg_CK_wi_bop            := A_sg_bop _ A 
                  ; A_sg_CK_wi_exists_id      := idP
                  ; A_sg_CK_wi_proofs         := P 
                  ; A_sg_CK_wi_ast            := A_sg_ast _ A 
                |}       
  | inr nidP, inr nannP => A_MCAS_sg_CK _
                {|
                    A_sg_CK_eqv            := A_sg_eqv _ A 
                  ; A_sg_CK_bop            := A_sg_bop _ A 
                  ; A_sg_CK_not_exists_id  := nidP
                  ; A_sg_CK_proofs         := P 
                  ; A_sg_CK_ast            := A_sg_ast _ A 
                |}
  | _, inl annP => A_MCAS_sg_Error _ ("Internal Error (2) : sg_classify_sg" :: nil) 
  end   
end.



Definition A_sg_classify (S : Type) (A : A_sg_mcas S) : A_sg_mcas S :=
match A with
| A_MCAS_sg_Error _ _        => A 
| A_MCAS_sg _ B              => A_sg_classify_sg _ B 

| A_MCAS_sg_C _ B            => A_sg_classify_sg_C _ B  
| A_MCAS_sg_C_with_id _ B    => A_sg_classify_sg_C_with_id _ B   
| A_MCAS_sg_C_with_ann _ B   => A_sg_classify_sg_C_with_ann _ B   
| A_MCAS_sg_BC _ B           => A_sg_classify_sg_BC _ B   

| A_MCAS_sg_NC _ B           => A
| A_MCAS_sg_NC_with_id _ B   => A
| A_MCAS_sg_NC_with_ann _ B  => A 
| A_MCAS_sg_BNC _ B          => A 

| A_MCAS_sg_CS _ B           => A
| A_MCAS_sg_CS_with_id _ B   => A
| A_MCAS_sg_CS_with_ann _ B  => A
| A_MCAS_sg_BCS _ B          => A

| A_MCAS_sg_CI _ B           => A 
| A_MCAS_sg_CI_with_id _ B   => A
| A_MCAS_sg_CI_with_ann _ B  => A 
| A_MCAS_sg_BCI _ B          => A 

| A_MCAS_sg_CNI _ B          => A_sg_classify_sg_CNI _ B   
| A_MCAS_sg_CNI_with_id _ B  => A_sg_classify_sg_CNI_with_id _ B  
| A_MCAS_sg_CNI_with_ann _ B => A 
| A_MCAS_sg_BCNI _ B         => A 

| A_MCAS_sg_CK _ _           => A 
| A_MCAS_sg_CK_with_id _ _   => A 
end. 

End AMCAS.                                                                                            

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

Record sg_NC_certificates {S: Type}  := 
{
  sg_NC_associative      : assert_associative (S := S) 
; sg_NC_congruence       : assert_bop_congruence (S := S) 
; sg_NC_not_commutative  : assert_not_commutative (S := S) 
; sg_NC_selective_d      : check_selective (S := S) 
; sg_NC_idempotent_d     : check_idempotent (S := S) 
; sg_NC_is_left_d        : check_is_left (S := S) 
; sg_NC_is_right_d       : check_is_right (S := S) 
; sg_NC_left_cancel_d    : check_left_cancellative (S := S) 
; sg_NC_right_cancel_d   : check_right_cancellative (S := S) 
; sg_NC_left_constant_d  : check_left_constant (S := S) 
; sg_NC_right_constant_d : check_right_constant (S := S) 
; sg_NC_anti_left_d      : check_anti_left (S := S) 
; sg_NC_anti_right_d     : check_anti_right (S := S)

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


Record sg_CNI_certificates {S: Type}  := 
{
  sg_CNI_associative     : assert_associative (S := S) 
; sg_CNI_congruence      : assert_bop_congruence (S := S) 
; sg_CNI_commutative     : assert_commutative (S := S) 
; sg_CNI_not_idempotent  : assert_not_idempotent (S := S) 

; sg_CNI_cancel_d         : check_left_cancellative (S := S) 
; sg_CNI_constant_d       : check_left_constant (S := S) 
; sg_CNI_anti_left_d      : check_anti_left (S := S) 
; sg_CNI_anti_right_d     : check_anti_right (S := S)
}. 


Record sg_CK_certificates {S: Type}  := 
{
  sg_CK_associative      : assert_associative (S := S) 
; sg_CK_congruence       : assert_bop_congruence (S := S) 
; sg_CK_commutative      : assert_commutative (S := S) 
; sg_CK_cancel           : assert_left_cancellative (S := S) 
; sg_CK_anti_left_d      : check_anti_left (S := S) 
; sg_CK_anti_right_d     : check_anti_right (S := S)
}. 

Record sg {S : Type} := {
  sg_eqv          : @eqv S 
; sg_bop          : binary_op S
; sg_exists_id_d  : @check_exists_id S
; sg_exists_ann_d : @check_exists_ann S
; sg_certs        : @sg_certificates S
; sg_ast          : cas_ast
}.

Record sg_C {S : Type} := {
  sg_C_eqv            : @eqv S 
; sg_C_bop            : binary_op S
; sg_C_not_exists_id  : @assert_not_exists_id S
; sg_C_not_exists_ann : @assert_not_exists_ann S
; sg_C_certs          : @sg_C_certificates S
; sg_C_ast            : cas_ast
}.

Record sg_C_with_id {S : Type} := {
  sg_C_wi_eqv            : @eqv S 
; sg_C_wi_bop            : binary_op S
; sg_C_wi_exists_id      : @assert_exists_id S
; sg_C_wi_not_exists_ann : @assert_not_exists_ann S
; sg_C_wi_certs          : @sg_C_certificates S
; sg_C_wi_ast            : cas_ast
}.

Record sg_C_with_ann {S : Type} := {
  sg_C_wa_eqv            : @eqv S 
; sg_C_wa_bop            : binary_op S
; sg_C_wa_not_exists_id   : @assert_not_exists_id S
; sg_C_wa_exists_ann     : @assert_exists_ann S
; sg_C_wa_certs          : @sg_C_certificates S
; sg_C_wa_ast            : cas_ast
}.

Record sg_BC {S : Type} := {
  sg_BC_eqv            : @eqv S 
; sg_BC_bop            : binary_op S
; sg_BC_exists_id      : @assert_exists_id S
; sg_BC_exists_ann     : @assert_exists_ann S
; sg_BC_certs          : @sg_C_certificates S
; sg_BC_ast            : cas_ast
}.


Record sg_NC {S : Type} := {
  sg_NC_eqv            : @eqv S 
; sg_NC_bop            : binary_op S
; sg_NC_not_exists_id  : @assert_not_exists_id S
; sg_NC_not_exists_ann : @assert_not_exists_ann S
; sg_NC_certs          : @sg_NC_certificates S
; sg_NC_ast            : cas_ast
}.

Record sg_NC_with_id {S : Type} := {
  sg_NC_wi_eqv            : @eqv S 
; sg_NC_wi_bop            : binary_op S
; sg_NC_wi_exists_id      : @assert_exists_id S
; sg_NC_wi_not_exists_ann : @assert_not_exists_ann S
; sg_NC_wi_certs          : @sg_NC_certificates S
; sg_NC_wi_ast            : cas_ast
}.

Record sg_NC_with_ann {S : Type} := {
  sg_NC_wa_eqv            : @eqv S 
; sg_NC_wa_bop            : binary_op S
; sg_NC_wa_not_exists_id  : @assert_not_exists_id S
; sg_NC_wa_exists_ann     : @assert_exists_ann S
; sg_NC_wa_certs          : @sg_NC_certificates S
; sg_NC_wa_ast            : cas_ast
}.

Record sg_BNC {S : Type} := {
  sg_BNC_eqv            : @eqv S 
; sg_BNC_bop            : binary_op S
; sg_BNC_exists_id      : @assert_exists_id S
; sg_BNC_exists_ann     : @assert_exists_ann S
; sg_BNC_certs          : @sg_NC_certificates S
; sg_BNC_ast            : cas_ast
}.



Record sg_CI {S : Type} := {
  sg_CI_eqv              : @eqv S 
; sg_CI_bop              : binary_op S
; sg_CI_not_exists_id  : @assert_not_exists_id S
; sg_CI_not_exists_ann : @assert_not_exists_ann S
; sg_CI_certs            : @sg_CI_certificates S
; sg_CI_ast              : cas_ast
}.

Record sg_CI_with_ann {S : Type} := {
  sg_CI_wa_eqv           : @eqv S 
; sg_CI_wa_bop           : binary_op S
; sg_CI_wa_not_exists_id : @assert_not_exists_id S
; sg_CI_wa_exists_ann    : @assert_exists_ann S
; sg_CI_wa_certs         : @sg_CI_certificates S
; sg_CI_wa_ast           : cas_ast
}.

Record sg_CI_with_id {S : Type} := {
  sg_CI_wi_eqv            : @eqv S 
; sg_CI_wi_bop            : binary_op S
; sg_CI_wi_exists_id      : @assert_exists_id S
; sg_CI_wi_not_exists_ann : @assert_not_exists_ann S
; sg_CI_wi_certs          : @sg_CI_certificates S
; sg_CI_wi_ast            : cas_ast
                                  }.
(* bounded sg_CI *) 
Record sg_BCI {S : Type} := {
  sg_BCI_eqv          : @eqv S
; sg_BCI_bop          : binary_op S
; sg_BCI_exists_id    : @assert_exists_id S 
; sg_BCI_exists_ann   : @assert_exists_ann S 
; sg_BCI_certs        : @sg_CI_certificates S 
; sg_BCI_ast          : cas_ast
}.



Record sg_CNI {S : Type} := {
  sg_CNI_eqv              : @eqv S 
; sg_CNI_bop              : binary_op S
; sg_CNI_not_exists_id    : @assert_not_exists_id S
; sg_CNI_not_exists_ann   : @assert_not_exists_ann S
; sg_CNI_certs            : @sg_CNI_certificates S
; sg_CNI_ast              : cas_ast
}.

Record sg_CNI_with_ann {S : Type} := {
  sg_CNI_wa_eqv           : @eqv S 
; sg_CNI_wa_bop           : binary_op S
; sg_CNI_wa_not_exists_id : @assert_not_exists_id S
; sg_CNI_wa_exists_ann    : @assert_exists_ann S
; sg_CNI_wa_certs         : @sg_CNI_certificates S
; sg_CNI_wa_ast           : cas_ast
}.

Record sg_CNI_with_id {S : Type} := {
  sg_CNI_wi_eqv            : @eqv S 
; sg_CNI_wi_bop            : binary_op S
; sg_CNI_wi_exists_id      : @assert_exists_id S
; sg_CNI_wi_not_exists_ann : @assert_not_exists_ann S
; sg_CNI_wi_certs          : @sg_CNI_certificates S
; sg_CNI_wi_ast            : cas_ast
                                  }.
(* bounded sg_CNI *) 
Record sg_BCNI {S : Type} := {
  sg_BCNI_eqv          : @eqv S
; sg_BCNI_bop          : binary_op S
; sg_BCNI_exists_id    : @assert_exists_id S 
; sg_BCNI_exists_ann   : @assert_exists_ann S 
; sg_BCNI_certs        : @sg_CNI_certificates S 
; sg_BCNI_ast          : cas_ast
}.




Record sg_CS {S : Type} := {
  sg_CS_eqv            : @eqv S 
; sg_CS_bop            : binary_op S
; sg_CS_not_exists_id  : @assert_not_exists_id S
; sg_CS_not_exists_ann : @assert_not_exists_ann S
; sg_CS_certs          : @sg_CS_certificates S
; sg_CS_ast            : cas_ast
}.

Record sg_CS_with_ann {S : Type} := {
  sg_CS_wa_eqv           : @eqv S 
; sg_CS_wa_bop           : binary_op S
; sg_CS_wa_not_exists_id : @assert_not_exists_id S
; sg_CS_wa_exists_ann    : @assert_exists_ann S
; sg_CS_wa_certs         : @sg_CS_certificates S
; sg_CS_wa_ast           : cas_ast
}.

Record sg_CS_with_id {S : Type} := {
  sg_CS_wi_eqv            : @eqv S 
; sg_CS_wi_bop            : binary_op S
; sg_CS_wi_exists_id      : @assert_exists_id S
; sg_CS_wi_not_exists_ann : @assert_not_exists_ann S
; sg_CS_wi_certs          : @sg_CS_certificates S
; sg_CS_wi_ast            : cas_ast
                                  }.
(* bounded sg_CS *) 
Record sg_BCS {S : Type} := {
  sg_BCS_eqv          : @eqv S
; sg_BCS_bop          : binary_op S
; sg_BCS_exists_id    : @assert_exists_id S 
; sg_BCS_exists_ann   : @assert_exists_ann S 
; sg_BCS_certs        : @sg_CS_certificates S 
; sg_BCS_ast          : cas_ast
}.

Record sg_CK {S : Type} := {
  sg_CK_eqv           : @eqv S
; sg_CK_bop           : binary_op S
; sg_CK_not_exists_id : @assert_not_exists_id S
; sg_CK_certs         : @sg_CK_certificates S
; sg_CK_ast           : cas_ast
}.

Record sg_CK_with_id {S : Type} := {
  sg_CK_wi_eqv           : @eqv S
; sg_CK_wi_bop           : binary_op S
; sg_CK_wi_exists_id     : @assert_exists_id S
; sg_CK_wi_certs         : @sg_CK_certificates S
; sg_CK_wi_ast           : cas_ast
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



Definition P2C_sg_NC : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_NC_proofs S r b -> @sg_NC_certificates S 
:= λ S r b P,
{|
  sg_NC_associative      := @Assert_Associative S 
; sg_NC_congruence       := @Assert_Bop_Congruence S 
; sg_NC_not_commutative  := Assert_Not_Commutative (projT1 (A_sg_NC_not_commutative _ _ _ P))
; sg_NC_selective_d      := p2c_selective_check S r b (A_sg_NC_selective_d S r b P)
; sg_NC_idempotent_d     := p2c_idempotent_check S r b (A_sg_NC_idempotent_d S r b P)
; sg_NC_is_left_d        := p2c_is_left_check S r b (A_sg_NC_is_left_d S r b P)
; sg_NC_is_right_d       := p2c_is_right_check S r b (A_sg_NC_is_right_d S r b P)
; sg_NC_left_cancel_d    := p2c_left_cancel_check S r b (A_sg_NC_left_cancel_d S r b P)
; sg_NC_right_cancel_d   := p2c_right_cancel_check S r b (A_sg_NC_right_cancel_d S r b P)
; sg_NC_left_constant_d  := p2c_left_constant_check S r b (A_sg_NC_left_constant_d S r b P)
; sg_NC_right_constant_d := p2c_right_constant_check S r b (A_sg_NC_right_constant_d S r b P)
; sg_NC_anti_left_d      := p2c_anti_left_check S r b (A_sg_NC_anti_left_d S r b P)
; sg_NC_anti_right_d     := p2c_anti_right_check S r b (A_sg_NC_anti_right_d S r b P)
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



Definition P2C_sg_CNI : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CNI_proofs S r b -> @sg_CNI_certificates S 
:= λ S r b P,
{|
  sg_CNI_associative     := @Assert_Associative S 
; sg_CNI_congruence      := @Assert_Bop_Congruence S 
; sg_CNI_commutative     := @Assert_Commutative S 
; sg_CNI_not_idempotent  := Assert_Not_Idempotent (projT1 (A_sg_CNI_not_idempotent _ _ _ P))

; sg_CNI_cancel_d         := p2c_left_cancel_check S r b (A_sg_CNI_cancel_d S r b P)
; sg_CNI_constant_d       := p2c_left_constant_check S r b (A_sg_CNI_constant_d S r b P)
; sg_CNI_anti_left_d      := p2c_anti_left_check S r b (A_sg_CNI_anti_left_d S r b P)
; sg_CNI_anti_right_d     := p2c_anti_right_check S r b (A_sg_CNI_anti_right_d S r b P)
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
; sg_CK_cancel           := @Assert_Left_Cancellative S 
; sg_CK_anti_left_d      := p2c_anti_left_check S r b (A_sg_CK_anti_left_d S r b P)
; sg_CK_anti_right_d     := p2c_anti_right_check S r b (A_sg_CK_anti_right_d S r b P)
|}. 
(*************************************************************************) 


Definition A2C_sg (S : Type) (R : A_sg S) : @sg S := 
{| 
  sg_eqv           := A2C_eqv _ (A_sg_eqv _ R) 
; sg_bop          := A_sg_bop _ R 
; sg_exists_id_d  := p2c_exists_id_check _ _ _ (A_sg_exists_id_d _ R)
; sg_exists_ann_d := p2c_exists_ann_check _ _ _ (A_sg_exists_ann_d _ R)
; sg_certs        := P2C_sg _ _ _ (A_sg_proofs _ R)
; sg_ast          := A_sg_ast _ R
|}. 


Definition A2C_sg_C (S : Type) (R : A_sg_C S) : @sg_C S :=
{| 
  sg_C_eqv            := A2C_eqv _ (A_sg_C_eqv _ R) 
; sg_C_bop            := A_sg_C_bop _ R 
; sg_C_not_exists_id  := Assert_Not_Exists_Id
; sg_C_not_exists_ann := Assert_Not_Exists_Ann
; sg_C_certs          := P2C_sg_C _ _ _ (A_sg_C_proofs _ R)
; sg_C_ast            := A_sg_C_ast _ R
|}.


Definition A2C_sg_C_with_id (S : Type) (R : A_sg_C_with_id S) : @sg_C_with_id S := 
{| 
  sg_C_wi_eqv            := A2C_eqv S (A_sg_C_wi_eqv _ R) 
; sg_C_wi_bop            := A_sg_C_wi_bop _ R 
; sg_C_wi_exists_id      := Assert_Exists_Id (projT1 (A_sg_C_wi_exists_id _ R))
; sg_C_wi_not_exists_ann := Assert_Not_Exists_Ann
; sg_C_wi_certs          := P2C_sg_C _ _ _  (A_sg_C_wi_proofs _ R)
; sg_C_wi_ast            := A_sg_C_wi_ast _ R
|}.


Definition A2C_sg_C_with_ann (S : Type) (R : A_sg_C_with_ann S) : @sg_C_with_ann S := 
{| 
  sg_C_wa_eqv            := A2C_eqv S (A_sg_C_wa_eqv _ R) 
; sg_C_wa_bop            := A_sg_C_wa_bop _ R 
; sg_C_wa_not_exists_id  := Assert_Not_Exists_Id
; sg_C_wa_exists_ann     := Assert_Exists_Ann (projT1 (A_sg_C_wa_exists_ann _ R))
; sg_C_wa_certs          := P2C_sg_C _ _ _  (A_sg_C_wa_proofs _ R)
; sg_C_wa_ast            := A_sg_C_wa_ast _ R
|}.

Definition A2C_sg_BC (S : Type) (R : A_sg_BC S) : @sg_BC S :=
{| 
  sg_BC_eqv            := A2C_eqv _ (A_sg_BC_eqv _ R) 
; sg_BC_bop            := A_sg_BC_bop _ R 
; sg_BC_exists_id      := Assert_Exists_Id (projT1 (A_sg_BC_exists_id _ R))
; sg_BC_exists_ann     := Assert_Exists_Ann (projT1 (A_sg_BC_exists_ann _ R))
; sg_BC_certs          := P2C_sg_C _ _ _ (A_sg_BC_proofs _ R)
; sg_BC_ast            := A_sg_BC_ast _ R
|}.


Definition A2C_sg_NC (S : Type) (R : A_sg_NC S) : @sg_NC S :=
{| 
  sg_NC_eqv            := A2C_eqv _ (A_sg_NC_eqv _ R) 
; sg_NC_bop            := A_sg_NC_bop _ R 
; sg_NC_not_exists_id  := Assert_Not_Exists_Id
; sg_NC_not_exists_ann := Assert_Not_Exists_Ann
; sg_NC_certs          := P2C_sg_NC _ _ _ (A_sg_NC_proofs _ R)
; sg_NC_ast            := A_sg_NC_ast _ R
|}.


Definition A2C_sg_NC_with_id (S : Type) (R : A_sg_NC_with_id S) : @sg_NC_with_id S := 
{| 
  sg_NC_wi_eqv            := A2C_eqv S (A_sg_NC_wi_eqv _ R) 
; sg_NC_wi_bop            := A_sg_NC_wi_bop _ R 
; sg_NC_wi_exists_id      := Assert_Exists_Id (projT1 (A_sg_NC_wi_exists_id _ R))
; sg_NC_wi_not_exists_ann := Assert_Not_Exists_Ann
; sg_NC_wi_certs          := P2C_sg_NC _ _ _  (A_sg_NC_wi_proofs _ R)
; sg_NC_wi_ast            := A_sg_NC_wi_ast _ R
|}.


Definition A2C_sg_NC_with_ann (S : Type) (R : A_sg_NC_with_ann S) : @sg_NC_with_ann S := 
{| 
  sg_NC_wa_eqv            := A2C_eqv S (A_sg_NC_wa_eqv _ R) 
; sg_NC_wa_bop            := A_sg_NC_wa_bop _ R 
; sg_NC_wa_not_exists_id  := Assert_Not_Exists_Id
; sg_NC_wa_exists_ann     := Assert_Exists_Ann (projT1 (A_sg_NC_wa_exists_ann _ R))
; sg_NC_wa_certs          := P2C_sg_NC _ _ _  (A_sg_NC_wa_proofs _ R)
; sg_NC_wa_ast            := A_sg_NC_wa_ast _ R
|}.

Definition A2C_sg_BNC (S : Type) (R : A_sg_BNC S) : @sg_BNC S :=
{| 
  sg_BNC_eqv            := A2C_eqv _ (A_sg_BNC_eqv _ R) 
; sg_BNC_bop            := A_sg_BNC_bop _ R 
; sg_BNC_exists_id      := Assert_Exists_Id (projT1 (A_sg_BNC_exists_id _ R))
; sg_BNC_exists_ann     := Assert_Exists_Ann (projT1 (A_sg_BNC_exists_ann _ R))
; sg_BNC_certs          := P2C_sg_NC _ _ _ (A_sg_BNC_proofs _ R)
; sg_BNC_ast            := A_sg_BNC_ast _ R
|}.


Definition A2C_sg_CI (S : Type) (R : A_sg_CI S) : @sg_CI S := 
{| 
  sg_CI_eqv              := A2C_eqv _ (A_sg_CI_eqv _ R)
; sg_CI_bop              := A_sg_CI_bop S R 
; sg_CI_not_exists_id  := Assert_Not_Exists_Id
; sg_CI_not_exists_ann := Assert_Not_Exists_Ann
; sg_CI_certs            := P2C_sg_CI _ _ _ (A_sg_CI_proofs _ R)
; sg_CI_ast              := A_sg_CI_ast _ R
|}. 
 

Definition A2C_sg_CI_with_ann (S : Type) (R : A_sg_CI_with_ann S) : @sg_CI_with_ann S := 
{| 
  sg_CI_wa_eqv              := A2C_eqv _ (A_sg_CI_wa_eqv _ R)
; sg_CI_wa_bop              := A_sg_CI_wa_bop _ R 
; sg_CI_wa_not_exists_id    := Assert_Not_Exists_Id
; sg_CI_wa_exists_ann       := Assert_Exists_Ann (projT1 (A_sg_CI_wa_exists_ann _ R))
; sg_CI_wa_certs            := P2C_sg_CI _ _ _  (A_sg_CI_wa_proofs _ R)
; sg_CI_wa_ast              := A_sg_CI_wa_ast _ R
|}. 


Definition A2C_sg_CI_with_id (S : Type) (R : A_sg_CI_with_id S) : @sg_CI_with_id S :=
{| 
  sg_CI_wi_eqv            := A2C_eqv _ (A_sg_CI_wi_eqv _ R)
; sg_CI_wi_bop            := A_sg_CI_wi_bop _ R 
; sg_CI_wi_exists_id      := Assert_Exists_Id (projT1 (A_sg_CI_wi_exists_id _ R))
; sg_CI_wi_not_exists_ann := Assert_Not_Exists_Ann
; sg_CI_wi_certs          := P2C_sg_CI _ _ _  (A_sg_CI_wi_proofs _ R)
; sg_CI_wi_ast            := A_sg_CI_wi_ast _ R
|}. 

Definition A2C_sg_BCI (S : Type) (R: A_sg_BCI S) : @sg_BCI S := 
{| 
  sg_BCI_eqv          := A2C_eqv _ (A_sg_BCI_eqv _ R)
; sg_BCI_bop          := A_sg_BCI_bop _ R 
; sg_BCI_exists_id    := Assert_Exists_Id (projT1 (A_sg_BCI_exists_id _ R))
; sg_BCI_exists_ann   := Assert_Exists_Ann (projT1 (A_sg_BCI_exists_ann _ R))
; sg_BCI_certs        := P2C_sg_CI _ _ _  (A_sg_BCI_proofs _ R)
; sg_BCI_ast          := A_sg_BCI_ast _ R
|}. 



Definition A2C_sg_CNI (S : Type) (R : A_sg_CNI S) : @sg_CNI S := 
{| 
  sg_CNI_eqv              := A2C_eqv _ (A_sg_CNI_eqv _ R)
; sg_CNI_bop              := A_sg_CNI_bop S R 
; sg_CNI_not_exists_id    := Assert_Not_Exists_Id
; sg_CNI_not_exists_ann  := Assert_Not_Exists_Ann
; sg_CNI_certs            := P2C_sg_CNI _ _ _ (A_sg_CNI_proofs _ R)
; sg_CNI_ast              := A_sg_CNI_ast _ R
|}. 
 

Definition A2C_sg_CNI_with_ann (S : Type) (R : A_sg_CNI_with_ann S) : @sg_CNI_with_ann S := 
{| 
  sg_CNI_wa_eqv              := A2C_eqv _ (A_sg_CNI_wa_eqv _ R)
; sg_CNI_wa_bop              := A_sg_CNI_wa_bop _ R 
; sg_CNI_wa_not_exists_id    := Assert_Not_Exists_Id
; sg_CNI_wa_exists_ann       := Assert_Exists_Ann (projT1 (A_sg_CNI_wa_exists_ann _ R))
; sg_CNI_wa_certs            := P2C_sg_CNI _ _ _  (A_sg_CNI_wa_proofs _ R)
; sg_CNI_wa_ast              := A_sg_CNI_wa_ast _ R
|}. 


Definition A2C_sg_CNI_with_id (S : Type) (R : A_sg_CNI_with_id S) : @sg_CNI_with_id S :=
{| 
  sg_CNI_wi_eqv            := A2C_eqv _ (A_sg_CNI_wi_eqv _ R)
; sg_CNI_wi_bop            := A_sg_CNI_wi_bop _ R 
; sg_CNI_wi_exists_id      := Assert_Exists_Id (projT1 (A_sg_CNI_wi_exists_id _ R))
; sg_CNI_wi_not_exists_ann := Assert_Not_Exists_Ann
; sg_CNI_wi_certs          := P2C_sg_CNI _ _ _  (A_sg_CNI_wi_proofs _ R)
; sg_CNI_wi_ast            := A_sg_CNI_wi_ast _ R
|}. 

Definition A2C_sg_BCNI (S : Type) (R: A_sg_BCNI S) : @sg_BCNI S := 
{| 
  sg_BCNI_eqv          := A2C_eqv _ (A_sg_BCNI_eqv _ R)
; sg_BCNI_bop          := A_sg_BCNI_bop _ R 
; sg_BCNI_exists_id    := Assert_Exists_Id (projT1 (A_sg_BCNI_exists_id _ R))
; sg_BCNI_exists_ann   := Assert_Exists_Ann (projT1 (A_sg_BCNI_exists_ann _ R))
; sg_BCNI_certs        := P2C_sg_CNI _ _ _  (A_sg_BCNI_proofs _ R)
; sg_BCNI_ast          := A_sg_BCNI_ast _ R
|}. 


Definition A2C_sg_CS (S : Type) (R : A_sg_CS S) : @sg_CS S := 
{| 
  sg_CS_eqv            := A2C_eqv _ (A_sg_CS_eqv _ R)
; sg_CS_bop            := A_sg_CS_bop _ R 
; sg_CS_not_exists_id  := Assert_Not_Exists_Id
; sg_CS_not_exists_ann := Assert_Not_Exists_Ann
; sg_CS_certs          := P2C_sg_CS _ _ _ (A_sg_CS_proofs _ R)
; sg_CS_ast            := A_sg_CS_ast _ R
|}. 


Definition A2C_sg_CS_with_ann (S : Type) (R : A_sg_CS_with_ann S) : @sg_CS_with_ann S := 
{| 
  sg_CS_wa_eqv              := A2C_eqv _ (A_sg_CS_wa_eqv _ R)
; sg_CS_wa_bop              := A_sg_CS_wa_bop _ R 
; sg_CS_wa_not_exists_id    := Assert_Not_Exists_Id
; sg_CS_wa_exists_ann       := Assert_Exists_Ann (projT1 (A_sg_CS_wa_exists_ann _ R))
; sg_CS_wa_certs            := P2C_sg_CS _ _ _  (A_sg_CS_wa_proofs _ R)
; sg_CS_wa_ast              := A_sg_CS_wa_ast _ R
|}. 


Definition A2C_sg_CS_with_id (S : Type) (R : A_sg_CS_with_id S) : @sg_CS_with_id S :=
{| 
  sg_CS_wi_eqv            := A2C_eqv _ (A_sg_CS_wi_eqv _ R)
; sg_CS_wi_bop            := A_sg_CS_wi_bop _ R 
; sg_CS_wi_exists_id      := Assert_Exists_Id (projT1 (A_sg_CS_wi_exists_id _ R))
; sg_CS_wi_not_exists_ann := Assert_Not_Exists_Ann
; sg_CS_wi_certs          := P2C_sg_CS _ _ _  (A_sg_CS_wi_proofs _ R)
; sg_CS_wi_ast            := A_sg_CS_wi_ast _ R
|}. 

Definition A2C_sg_BCS (S : Type) (R: A_sg_BCS S) : @sg_BCS S := 
{| 
  sg_BCS_eqv          := A2C_eqv _ (A_sg_BCS_eqv _ R)
; sg_BCS_bop          := A_sg_BCS_bop _ R 
; sg_BCS_exists_id    := Assert_Exists_Id (projT1 (A_sg_BCS_exists_id _ R))
; sg_BCS_exists_ann   := Assert_Exists_Ann (projT1 (A_sg_BCS_exists_ann _ R))
; sg_BCS_certs        := P2C_sg_CS _ _ _  (A_sg_BCS_proofs _ R)
; sg_BCS_ast          := A_sg_BCS_ast _ R
|}. 


Definition A2C_sg_CK (S : Type) (R : A_sg_CK S) : @sg_CK S := 
{| 
  sg_CK_eqv           := A2C_eqv _ (A_sg_CK_eqv _ R)
; sg_CK_bop           := A_sg_CK_bop _ R  
; sg_CK_not_exists_id := Assert_Not_Exists_Id
; sg_CK_certs         := P2C_sg_CK _ _ _ (A_sg_CK_proofs _ R)
; sg_CK_ast           := A_sg_CK_ast _ R
|}.


Definition A2C_sg_CK_with_id (S : Type) (R : A_sg_CK_with_id S) : @sg_CK_with_id S := 
{| 
  sg_CK_wi_eqv         := A2C_eqv _ (A_sg_CK_wi_eqv _ R)
; sg_CK_wi_bop         := A_sg_CK_wi_bop _ R  
; sg_CK_wi_exists_id   := Assert_Exists_Id (projT1 (A_sg_CK_wi_exists_id _ R))
; sg_CK_wi_certs       := P2C_sg_CK _ _ _ (A_sg_CK_wi_proofs _ R)
; sg_CK_wi_ast         := A_sg_CK_wi_ast _ R
|}.


  
End Translation.


Section MCAS.

Inductive sg_certs_mcas {S: Type} := 
| MCAS_Cert_sg_Error : list string              -> @sg_certs_mcas S 
| MCAS_Cert_sg       : @sg_certificates S      -> @sg_certs_mcas S 
| MCAS_Cert_sg_C     : @sg_C_certificates S    -> @sg_certs_mcas S 
| MCAS_Cert_sg_NC    : @sg_NC_certificates S   -> @sg_certs_mcas S 
| MCAS_Cert_sg_CS    : @sg_CS_certificates S   -> @sg_certs_mcas S     
| MCAS_Cert_sg_CI    : @sg_CI_certificates S   -> @sg_certs_mcas S 
| MCAS_Cert_sg_CNI   : @sg_CNI_certificates S  -> @sg_certs_mcas S 
| MCAS_Cert_sg_CK    : @sg_CK_certificates S   -> @sg_certs_mcas S                                                                  
.

Inductive sg_mcas {S : Type} := 
| MCAS_sg_Error        : list string       -> @sg_mcas S
| MCAS_sg              : @sg S             -> @sg_mcas S
| MCAS_sg_C            : @sg_C S           -> @sg_mcas S
| MCAS_sg_C_with_id    : @sg_C_with_id S   -> @sg_mcas S
| MCAS_sg_C_with_ann   : @sg_C_with_ann S  -> @sg_mcas S
| MCAS_sg_BC           : @sg_BC S          -> @sg_mcas S
| MCAS_sg_NC           : @sg_NC S          -> @sg_mcas S
| MCAS_sg_NC_with_id   : @sg_NC_with_id S  -> @sg_mcas S
| MCAS_sg_NC_with_ann  : @sg_NC_with_ann S -> @sg_mcas S
| MCAS_sg_BNC          : @sg_BNC S         -> @sg_mcas S
| MCAS_sg_CS           : @sg_CS S          -> @sg_mcas S
| MCAS_sg_CS_with_id   : @sg_CS_with_id S  -> @sg_mcas S
| MCAS_sg_CS_with_ann  : @sg_CS_with_ann S -> @sg_mcas S
| MCAS_sg_BCS          : @sg_BCS S         -> @sg_mcas S
| MCAS_sg_CI           : @sg_CI S          -> @sg_mcas S
| MCAS_sg_CI_with_id   : @sg_CI_with_id S  -> @sg_mcas S
| MCAS_sg_CI_with_ann  : @sg_CI_with_ann S -> @sg_mcas S
| MCAS_sg_BCI          : @sg_BCI S         -> @sg_mcas S
| MCAS_sg_CNI          : @sg_CNI S         -> @sg_mcas S
| MCAS_sg_CNI_with_id  : @sg_CNI_with_id S -> @sg_mcas S
| MCAS_sg_CNI_with_ann : @sg_CNI_with_ann S -> @sg_mcas S
| MCAS_sg_BCNI         : @sg_BCNI S        -> @sg_mcas S
| MCAS_sg_CK           : @sg_CK S          -> @sg_mcas S
| MCAS_sg_CK_with_id   : @sg_CK_with_id S  -> @sg_mcas S                                             
.

Definition P2C_proofs_mcas_sg
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (A : sg_proofs_mcas S eq bop) : @sg_certs_mcas S :=
match A with 
| A_MCAS_Proof_sg_Error _ _ _ s => MCAS_Cert_sg_Error s
| A_MCAS_Proof_sg _ _ _ B       => MCAS_Cert_sg (P2C_sg _ _ _ B)
| A_MCAS_Proof_sg_C _ _ _ B     => MCAS_Cert_sg_C (P2C_sg_C _ _ _ B)
| A_MCAS_Proof_sg_NC _ _ _ B    => MCAS_Cert_sg_NC (P2C_sg_NC _ _ _ B)   
| A_MCAS_Proof_sg_CS _ _ _ B    => MCAS_Cert_sg_CS (P2C_sg_CS _ _ _ B)      
| A_MCAS_Proof_sg_CI _ _ _ B    => MCAS_Cert_sg_CI (P2C_sg_CI _ _ _ B)      
| A_MCAS_Proof_sg_CNI _ _ _ B   => MCAS_Cert_sg_CNI (P2C_sg_CNI _ _ _ B)      
| A_MCAS_Proof_sg_CK _ _ _ B    => MCAS_Cert_sg_CK (P2C_sg_CK _ _ _ B)      
end.

Definition A2C_mcas_sg (S : Type) (A : A_sg_mcas S) : @sg_mcas S :=
match A with
| A_MCAS_sg_Error _ s        => MCAS_sg_Error s
| A_MCAS_sg _ B              => MCAS_sg (A2C_sg _ B)

| A_MCAS_sg_C _ B            => MCAS_sg_C (A2C_sg_C _ B)
| A_MCAS_sg_C_with_id _ B    => MCAS_sg_C_with_id (A2C_sg_C_with_id _ B)
| A_MCAS_sg_C_with_ann _ B   => MCAS_sg_C_with_ann (A2C_sg_C_with_ann _ B)
| A_MCAS_sg_BC _ B           => MCAS_sg_BC (A2C_sg_BC _ B)

| A_MCAS_sg_NC _ B           => MCAS_sg_NC (A2C_sg_NC _ B)
| A_MCAS_sg_NC_with_id _ B   => MCAS_sg_NC_with_id (A2C_sg_NC_with_id _ B)
| A_MCAS_sg_NC_with_ann _ B  => MCAS_sg_NC_with_ann (A2C_sg_NC_with_ann _ B)
| A_MCAS_sg_BNC _ B          => MCAS_sg_BNC (A2C_sg_BNC _ B)

| A_MCAS_sg_CS _ B           => MCAS_sg_CS (A2C_sg_CS _ B)
| A_MCAS_sg_CS_with_id _ B   => MCAS_sg_CS_with_id (A2C_sg_CS_with_id _ B)
| A_MCAS_sg_CS_with_ann _ B  => MCAS_sg_CS_with_ann (A2C_sg_CS_with_ann _ B)
| A_MCAS_sg_BCS _ B          => MCAS_sg_BCS (A2C_sg_BCS _ B)

| A_MCAS_sg_CI _ B           => MCAS_sg_CI (A2C_sg_CI _ B)
| A_MCAS_sg_CI_with_id _ B   => MCAS_sg_CI_with_id (A2C_sg_CI_with_id _ B)
| A_MCAS_sg_CI_with_ann _ B  => MCAS_sg_CI_with_ann (A2C_sg_CI_with_ann _ B)
| A_MCAS_sg_BCI _ B          => MCAS_sg_BCI (A2C_sg_BCI _ B)

| A_MCAS_sg_CNI _ B          => MCAS_sg_CNI (A2C_sg_CNI _ B)
| A_MCAS_sg_CNI_with_id _ B  => MCAS_sg_CNI_with_id (A2C_sg_CNI_with_id _ B)
| A_MCAS_sg_CNI_with_ann _ B => MCAS_sg_CNI_with_ann (A2C_sg_CNI_with_ann _ B)
| A_MCAS_sg_BCNI _ B         => MCAS_sg_BCNI (A2C_sg_BCNI _ B)

| A_MCAS_sg_CK _ B           => MCAS_sg_CK (A2C_sg_CK _ B)
| A_MCAS_sg_CK_with_id _ B   => MCAS_sg_CK_with_id (A2C_sg_CK_with_id _ B)
end. 
  





Definition sg_certificates_classify_sg_CNI {S : Type} 
           (A : @sg_CNI_certificates S) : @sg_certs_mcas S  :=
match sg_CNI_cancel_d A with 
| Certify_Left_Cancellative => MCAS_Cert_sg_CK
                     {|
                         sg_CK_associative   := sg_CNI_associative A
                       ; sg_CK_congruence    := sg_CNI_congruence A
                       ; sg_CK_commutative   := sg_CNI_commutative A
                       ; sg_CK_cancel        := Assert_Left_Cancellative
                       ; sg_CK_anti_left_d   := sg_CNI_anti_left_d A
                       ; sg_CK_anti_right_d  := sg_CNI_anti_right_d A

                     |}
| _      => MCAS_Cert_sg_CNI A 
end.


Definition sg_certificates_classify_sg_C {S : Type} 
           (A : @sg_C_certificates S) : @sg_certs_mcas S  :=
match sg_C_idempotent_d A with 
| Certify_Idempotent =>
  match sg_C_selective_d A with
  | Certify_Selective => MCAS_Cert_sg_CS 
                {|    
                    sg_CS_associative        := sg_C_associative A 
                  ; sg_CS_congruence         := sg_C_congruence  A 
                  ; sg_CS_commutative        := sg_C_commutative  A 
                  ; sg_CS_selective          := Assert_Selective 
                |}
  | Certify_Not_Selective p => MCAS_Cert_sg_CI 
                {|    
                    sg_CI_associative        := sg_C_associative A 
                  ; sg_CI_congruence         := sg_C_congruence  A 
                  ; sg_CI_commutative        := sg_C_commutative  A
                  ; sg_CI_idempotent         := Assert_Idempotent
                  ; sg_CI_not_selective      := Assert_Not_Selective p
                |}
  end 
| Certify_Not_Idempotent s  => MCAS_Cert_sg_CNI 
                {|
                    sg_CNI_associative     := sg_C_associative A 
                  ; sg_CNI_congruence      := sg_C_congruence  A 
                  ; sg_CNI_commutative     := sg_C_commutative  A 
                  ; sg_CNI_not_idempotent  := Assert_Not_Idempotent s
                  ; sg_CNI_cancel_d        := sg_C_cancel_d  A 
                  ; sg_CNI_constant_d      := sg_C_constant_d  A 
                  ; sg_CNI_anti_left_d     := sg_C_anti_left_d  A 
                  ; sg_CNI_anti_right_d    := sg_C_anti_right_d  A 
                |}
end.


Definition sg_certificates_classify_sg {S : Type}
           (P : @sg_certificates S) : @sg_certs_mcas S  :=
match sg_commutative_d P with 
| Certify_Commutative => sg_certificates_classify_sg_C 
   {| 
       sg_C_associative      := sg_associative P
     ; sg_C_congruence       := sg_congruence P
     ; sg_C_commutative      := Assert_Commutative 
     ; sg_C_anti_left_d      := sg_anti_left_d P
     ; sg_C_anti_right_d     := sg_anti_right_d P
     ; sg_C_selective_d      := sg_selective_d P
     ; sg_C_idempotent_d     := sg_idempotent_d P
     ; sg_C_cancel_d         := sg_left_cancel_d P
     ; sg_C_constant_d       := sg_left_constant_d P
   |}                                        
| Certify_Not_Commutative p  => MCAS_Cert_sg_NC 
   {| 
       sg_NC_associative      := sg_associative P
     ; sg_NC_congruence       := sg_congruence P
     ; sg_NC_not_commutative  := Assert_Not_Commutative p
     ; sg_NC_selective_d      := sg_selective_d P
     ; sg_NC_idempotent_d     := sg_idempotent_d P
     ; sg_NC_is_left_d        := sg_is_left_d P
     ; sg_NC_is_right_d       := sg_is_right_d P    
     ; sg_NC_left_cancel_d    := sg_left_cancel_d P
     ; sg_NC_right_cancel_d   := sg_right_cancel_d P
     ; sg_NC_left_constant_d  := sg_left_constant_d P
     ; sg_NC_right_constant_d := sg_right_constant_d P
     ; sg_NC_anti_left_d      := sg_anti_left_d P
     ; sg_NC_anti_right_d     := sg_anti_right_d P
     |}                                     
end.

Definition sg_certificates_classify {S : Type}
           (A : @sg_certs_mcas S ) : @sg_certs_mcas S  :=
match A with
| MCAS_Cert_sg_Error s =>  A 
| MCAS_Cert_sg B       => sg_certificates_classify_sg B
| MCAS_Cert_sg_C  B    => sg_certificates_classify_sg_C B
| MCAS_Cert_sg_NC B    => A
| MCAS_Cert_sg_CS B    => A
| MCAS_Cert_sg_CI B    => A
| MCAS_Cert_sg_CNI B   => sg_certificates_classify_sg_CNI B
| MCAS_Cert_sg_CK B    => A
end                                   
.


Local Open Scope string_scope.

Definition sg_classify_sg_CNI {S : Type} (A : @sg_CNI S) : @sg_mcas S :=
match sg_certificates_classify_sg_CNI (sg_CNI_certs A) with
| MCAS_Cert_sg_Error s => MCAS_sg_Error s 
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg_CNI"  :: nil) 
| MCAS_Cert_sg_C  P    => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg_CNI"  :: nil) 
| MCAS_Cert_sg_NC P    => MCAS_sg_Error ("Internal Error (3) : sg_classify_sg_CNI" :: nil) 
| MCAS_Cert_sg_CS P    => MCAS_sg_Error ("Internal Error (4) : sg_classify_sg_CNI" :: nil) 
| MCAS_Cert_sg_CI P    => MCAS_sg_Error ("Internal Error (5) : sg_classify_sg_CNI" :: nil) 
| MCAS_Cert_sg_CNI P   => MCAS_sg_CNI A 
| MCAS_Cert_sg_CK P    => MCAS_sg_CK 
                {|
                    sg_CK_eqv            := sg_CNI_eqv A 
                  ; sg_CK_bop            := sg_CNI_bop A 
                  ; sg_CK_not_exists_id  := sg_CNI_not_exists_id A
                  ; sg_CK_certs          := P 
                  ; sg_CK_ast            := sg_CNI_ast A 
                |}
end.


Definition sg_classify_sg_CNI_with_id {S : Type} (A : @sg_CNI_with_id S) : @sg_mcas S :=
match sg_certificates_classify_sg_CNI (sg_CNI_wi_certs A) with
| MCAS_Cert_sg_Error s =>  MCAS_sg_Error s
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg_CNI_with_id" :: nil)
| MCAS_Cert_sg_C  P    => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg_CNI_with_id" :: nil)
| MCAS_Cert_sg_NC P    => MCAS_sg_Error ("Internal Error (3) : sg_classify_sg_CNI_with_id" :: nil)
| MCAS_Cert_sg_CS P    => MCAS_sg_Error ("Internal Error (4) : sg_classify_sg_CNI_with_id" :: nil)
| MCAS_Cert_sg_CI P    => MCAS_sg_Error ("Internal Error (5) : sg_classify_sg_CNI_with_id" :: nil)
| MCAS_Cert_sg_CNI P   => MCAS_sg_CNI_with_id A 
| MCAS_Cert_sg_CK P    => MCAS_sg_CK_with_id 
                {|
                    sg_CK_wi_eqv            := sg_CNI_wi_eqv A 
                  ; sg_CK_wi_bop            := sg_CNI_wi_bop A 
                  ; sg_CK_wi_exists_id      := sg_CNI_wi_exists_id A
                  ; sg_CK_wi_certs         := P 
                  ; sg_CK_wi_ast            := sg_CNI_wi_ast A 
                |}
end.


Definition sg_classify_sg_C {S : Type} (A : @sg_C S) : @sg_mcas S :=
match sg_certificates_classify_sg_C (sg_C_certs A) with
| MCAS_Cert_sg_Error s =>  MCAS_sg_Error s 
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg_C"  :: nil)
| MCAS_Cert_sg_C  P    => MCAS_sg_C A 
| MCAS_Cert_sg_NC P    => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg_C" :: nil)
| MCAS_Cert_sg_CS P    => MCAS_sg_CS
                {|
                    sg_CS_eqv            := sg_C_eqv A 
                  ; sg_CS_bop            := sg_C_bop A 
                  ; sg_CS_not_exists_id  := sg_C_not_exists_id A
                  ; sg_CS_not_exists_ann := sg_C_not_exists_ann A 
                  ; sg_CS_certs          := P 
                  ; sg_CS_ast            := sg_C_ast A 
                |}       
| MCAS_Cert_sg_CI P    => MCAS_sg_CI 
                {|
                    sg_CI_eqv            := sg_C_eqv A 
                  ; sg_CI_bop            := sg_C_bop A 
                  ; sg_CI_not_exists_id  := sg_C_not_exists_id A
                  ; sg_CI_not_exists_ann := sg_C_not_exists_ann A 
                  ; sg_CI_certs         := P 
                  ; sg_CI_ast            := sg_C_ast A 
                |}       
| MCAS_Cert_sg_CNI P   => MCAS_sg_CNI 
                {|
                    sg_CNI_eqv            := sg_C_eqv A 
                  ; sg_CNI_bop            := sg_C_bop A 
                  ; sg_CNI_not_exists_id  := sg_C_not_exists_id A
                  ; sg_CNI_not_exists_ann := sg_C_not_exists_ann A 
                  ; sg_CNI_certs         := P 
                  ; sg_CNI_ast            := sg_C_ast A 
                |}       
| MCAS_Cert_sg_CK P    => MCAS_sg_CK 
                {|
                    sg_CK_eqv            := sg_C_eqv A 
                  ; sg_CK_bop            := sg_C_bop A 
                  ; sg_CK_not_exists_id  := sg_C_not_exists_id A
                  ; sg_CK_certs         := P 
                  ; sg_CK_ast            := sg_C_ast A 
                |}
end.


Definition sg_classify_sg_C_with_id {S : Type} (A : @sg_C_with_id S) : @sg_mcas S :=
match sg_certificates_classify_sg_C (sg_C_wi_certs A) with
| MCAS_Cert_sg_Error s =>  MCAS_sg_Error s 
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg_C_with_id"  :: nil)
| MCAS_Cert_sg_C  P    => MCAS_sg_C_with_id A 
| MCAS_Cert_sg_NC P    => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg_C_with_id"  :: nil)
| MCAS_Cert_sg_CS P    => MCAS_sg_CS_with_id 
                {|
                    sg_CS_wi_eqv            := sg_C_wi_eqv A 
                  ; sg_CS_wi_bop            := sg_C_wi_bop A 
                  ; sg_CS_wi_exists_id      := sg_C_wi_exists_id A
                  ; sg_CS_wi_not_exists_ann := sg_C_wi_not_exists_ann A 
                  ; sg_CS_wi_certs         := P 
                  ; sg_CS_wi_ast            := sg_C_wi_ast A 
                |}       
| MCAS_Cert_sg_CI P    => MCAS_sg_CI_with_id 
                {|
                    sg_CI_wi_eqv            := sg_C_wi_eqv A 
                  ; sg_CI_wi_bop            := sg_C_wi_bop A 
                  ; sg_CI_wi_exists_id      := sg_C_wi_exists_id A
                  ; sg_CI_wi_not_exists_ann := sg_C_wi_not_exists_ann A 
                  ; sg_CI_wi_certs         := P 
                  ; sg_CI_wi_ast            := sg_C_wi_ast A 
                |}       
| MCAS_Cert_sg_CNI P   => MCAS_sg_CNI_with_id 
                {|
                    sg_CNI_wi_eqv            := sg_C_wi_eqv A 
                  ; sg_CNI_wi_bop            := sg_C_wi_bop A 
                  ; sg_CNI_wi_exists_id      := sg_C_wi_exists_id A
                  ; sg_CNI_wi_not_exists_ann := sg_C_wi_not_exists_ann A 
                  ; sg_CNI_wi_certs         := P 
                  ; sg_CNI_wi_ast            := sg_C_wi_ast A 
                |}       
| MCAS_Cert_sg_CK P    => MCAS_sg_CK_with_id 
                {|
                    sg_CK_wi_eqv            := sg_C_wi_eqv A 
                  ; sg_CK_wi_bop            := sg_C_wi_bop A 
                  ; sg_CK_wi_exists_id      := sg_C_wi_exists_id A
                  ; sg_CK_wi_certs         := P 
                  ; sg_CK_wi_ast            := sg_C_wi_ast A 
                |}
end.

Definition sg_classify_sg_C_with_ann {S : Type} (A : @sg_C_with_ann S) : @sg_mcas S :=
match sg_certificates_classify_sg_C (sg_C_wa_certs A) with
| MCAS_Cert_sg_Error s =>  MCAS_sg_Error s 
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg_C_with_ann"  :: nil)
| MCAS_Cert_sg_C  P    => MCAS_sg_C_with_ann A 
| MCAS_Cert_sg_NC P    => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg_C_with_ann"  :: nil)
| MCAS_Cert_sg_CS P    => MCAS_sg_CS_with_ann
                {|
                    sg_CS_wa_eqv            := sg_C_wa_eqv A 
                  ; sg_CS_wa_bop            := sg_C_wa_bop A 
                  ; sg_CS_wa_not_exists_id  := sg_C_wa_not_exists_id A
                  ; sg_CS_wa_exists_ann     := sg_C_wa_exists_ann A 
                  ; sg_CS_wa_certs         := P 
                  ; sg_CS_wa_ast            := sg_C_wa_ast A 
                |}       
| MCAS_Cert_sg_CI P    => MCAS_sg_CI_with_ann
                {|
                    sg_CI_wa_eqv            := sg_C_wa_eqv A 
                  ; sg_CI_wa_bop            := sg_C_wa_bop A 
                  ; sg_CI_wa_not_exists_id  := sg_C_wa_not_exists_id A
                  ; sg_CI_wa_exists_ann     := sg_C_wa_exists_ann A 
                  ; sg_CI_wa_certs         := P 
                  ; sg_CI_wa_ast            := sg_C_wa_ast A 
                |}       
| MCAS_Cert_sg_CNI P   => MCAS_sg_CNI_with_ann 
                {|
                    sg_CNI_wa_eqv            := sg_C_wa_eqv A 
                  ; sg_CNI_wa_bop            := sg_C_wa_bop A 
                  ; sg_CNI_wa_not_exists_id  := sg_C_wa_not_exists_id A
                  ; sg_CNI_wa_exists_ann     := sg_C_wa_exists_ann A 
                  ; sg_CNI_wa_certs         := P 
                  ; sg_CNI_wa_ast            := sg_C_wa_ast A 
                |}       
| MCAS_Cert_sg_CK P    => MCAS_sg_Error ("Internal Error (3) : sg_classify_sg_C_with_ann"  :: nil)
end.

Definition sg_classify_sg_BC {S : Type} (A : @sg_BC S) : @sg_mcas S :=
match sg_certificates_classify_sg_C (sg_BC_certs A) with
| MCAS_Cert_sg_Error s =>  MCAS_sg_Error s 
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg_BC"  :: nil)
| MCAS_Cert_sg_C  P    => MCAS_sg_BC A 
| MCAS_Cert_sg_NC P    => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg_BC" :: nil)
| MCAS_Cert_sg_CS P    => MCAS_sg_BCS 
                {|
                    sg_BCS_eqv            := sg_BC_eqv A 
                  ; sg_BCS_bop            := sg_BC_bop A 
                  ; sg_BCS_exists_id      := sg_BC_exists_id A
                  ; sg_BCS_exists_ann     := sg_BC_exists_ann A 
                  ; sg_BCS_certs         := P 
                  ; sg_BCS_ast            := sg_BC_ast A 
                |}       
| MCAS_Cert_sg_CI P    => MCAS_sg_BCI 
                {|
                    sg_BCI_eqv            := sg_BC_eqv A 
                  ; sg_BCI_bop            := sg_BC_bop A 
                  ; sg_BCI_exists_id      := sg_BC_exists_id A
                  ; sg_BCI_exists_ann     := sg_BC_exists_ann A 
                  ; sg_BCI_certs         := P 
                  ; sg_BCI_ast            := sg_BC_ast A 
                |}       
| MCAS_Cert_sg_CNI P   => MCAS_sg_BCNI
                {|
                    sg_BCNI_eqv            := sg_BC_eqv A 
                  ; sg_BCNI_bop            := sg_BC_bop A 
                  ; sg_BCNI_exists_id      := sg_BC_exists_id A
                  ; sg_BCNI_exists_ann     := sg_BC_exists_ann A 
                  ; sg_BCNI_certs         := P 
                  ; sg_BCNI_ast            := sg_BC_ast A 
                |}       
| MCAS_Cert_sg_CK P    => MCAS_sg_Error ("Internal Error (3) : sg_classify_sg_BC"  :: nil)
end.



Definition sg_classify_sg {S : Type} (A : @sg S) : @sg_mcas S :=
match sg_certificates_classify_sg (sg_certs A) with
| MCAS_Cert_sg_Error s =>  MCAS_sg_Error s 
| MCAS_Cert_sg _       => MCAS_sg_Error ("Internal Error (1) : sg_classify_sg"  :: nil)
| MCAS_Cert_sg_C  P    =>
  match sg_exists_id_d A, sg_exists_ann_d A with
  | Certify_Exists_Id id, Certify_Exists_Ann ann => MCAS_sg_BC 
                {|
                    sg_BC_eqv        := sg_eqv A 
                  ; sg_BC_bop        := sg_bop A 
                  ; sg_BC_exists_id  := Assert_Exists_Id id
                  ; sg_BC_exists_ann := Assert_Exists_Ann ann 
                  ; sg_BC_certs     := P
                  ; sg_BC_ast        := sg_ast A 
                |}                                        
  | Certify_Exists_Id id, Certify_Not_Exists_Ann => MCAS_sg_C_with_id 
                {|
                    sg_C_wi_eqv            := sg_eqv A 
                  ; sg_C_wi_bop            := sg_bop A 
                  ; sg_C_wi_exists_id      := Assert_Exists_Id id
                  ; sg_C_wi_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_C_wi_certs         := P
                  ; sg_C_wi_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Exists_Ann ann => MCAS_sg_C_with_ann 
                {|
                    sg_C_wa_eqv            := sg_eqv A 
                  ; sg_C_wa_bop            := sg_bop A 
                  ; sg_C_wa_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_C_wa_exists_ann     := Assert_Exists_Ann ann 
                  ; sg_C_wa_certs         := P
                  ; sg_C_wa_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Not_Exists_Ann => MCAS_sg_C 
                {|
                    sg_C_eqv            := sg_eqv A 
                  ; sg_C_bop            := sg_bop A 
                  ; sg_C_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_C_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_C_certs         := P
                  ; sg_C_ast            := sg_ast A 
                |}       
  end 
| MCAS_Cert_sg_NC P    => 
  match sg_exists_id_d A, sg_exists_ann_d A with
  | Certify_Exists_Id id, Certify_Exists_Ann ann => MCAS_sg_BNC 
                {|
                    sg_BNC_eqv        := sg_eqv A 
                  ; sg_BNC_bop        := sg_bop A 
                  ; sg_BNC_exists_id  := Assert_Exists_Id id
                  ; sg_BNC_exists_ann := Assert_Exists_Ann ann 
                  ; sg_BNC_certs     := P 
                  ; sg_BNC_ast        := sg_ast A 
                |}                                        
  | Certify_Exists_Id id, Certify_Not_Exists_Ann => MCAS_sg_NC_with_id 
                {|
                    sg_NC_wi_eqv            := sg_eqv A 
                  ; sg_NC_wi_bop            := sg_bop A 
                  ; sg_NC_wi_exists_id      := Assert_Exists_Id id
                  ; sg_NC_wi_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_NC_wi_certs         := P 
                  ; sg_NC_wi_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Exists_Ann ann => MCAS_sg_NC_with_ann
                {|
                    sg_NC_wa_eqv            := sg_eqv A 
                  ; sg_NC_wa_bop            := sg_bop A 
                  ; sg_NC_wa_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_NC_wa_exists_ann     := Assert_Exists_Ann ann 
                  ; sg_NC_wa_certs         := P 
                  ; sg_NC_wa_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Not_Exists_Ann => MCAS_sg_NC
                {|
                    sg_NC_eqv            := sg_eqv A 
                  ; sg_NC_bop            := sg_bop A 
                  ; sg_NC_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_NC_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_NC_certs         := P 
                  ; sg_NC_ast            := sg_ast A 
                |}       
  end 
| MCAS_Cert_sg_CS P    => 
  match sg_exists_id_d A, sg_exists_ann_d A with
  | Certify_Exists_Id id, Certify_Exists_Ann ann => MCAS_sg_BCS
                {|
                    sg_BCS_eqv        := sg_eqv A 
                  ; sg_BCS_bop        := sg_bop A 
                  ; sg_BCS_exists_id  := Assert_Exists_Id id
                  ; sg_BCS_exists_ann := Assert_Exists_Ann ann 
                  ; sg_BCS_certs     := P 
                  ; sg_BCS_ast        := sg_ast A 
                |}                                        
  | Certify_Exists_Id id, Certify_Not_Exists_Ann => MCAS_sg_CS_with_id 
                {|
                    sg_CS_wi_eqv            := sg_eqv A 
                  ; sg_CS_wi_bop            := sg_bop A 
                  ; sg_CS_wi_exists_id      := Assert_Exists_Id id
                  ; sg_CS_wi_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_CS_wi_certs         := P 
                  ; sg_CS_wi_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Exists_Ann ann => MCAS_sg_CS_with_ann 
                {|
                    sg_CS_wa_eqv            := sg_eqv A 
                  ; sg_CS_wa_bop            := sg_bop A 
                  ; sg_CS_wa_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CS_wa_exists_ann     := Assert_Exists_Ann ann 
                  ; sg_CS_wa_certs         := P 
                  ; sg_CS_wa_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Not_Exists_Ann => MCAS_sg_CS 
                {|
                    sg_CS_eqv            := sg_eqv A 
                  ; sg_CS_bop            := sg_bop A 
                  ; sg_CS_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CS_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_CS_certs         := P 
                  ; sg_CS_ast            := sg_ast A 
                |}       
  end 
| MCAS_Cert_sg_CI P    => 
  match sg_exists_id_d A, sg_exists_ann_d A with
  | Certify_Exists_Id id, Certify_Exists_Ann ann => MCAS_sg_BCI 
                {|
                    sg_BCI_eqv        := sg_eqv A 
                  ; sg_BCI_bop        := sg_bop A 
                  ; sg_BCI_exists_id  := Assert_Exists_Id id
                  ; sg_BCI_exists_ann := Assert_Exists_Ann ann 
                  ; sg_BCI_certs     := P 
                  ; sg_BCI_ast        := sg_ast A 
                |}                                        
  | Certify_Exists_Id id, Certify_Not_Exists_Ann => MCAS_sg_CI_with_id 
                {|
                    sg_CI_wi_eqv            := sg_eqv A 
                  ; sg_CI_wi_bop            := sg_bop A 
                  ; sg_CI_wi_exists_id      := Assert_Exists_Id id
                  ; sg_CI_wi_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_CI_wi_certs         := P 
                  ; sg_CI_wi_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Exists_Ann ann => MCAS_sg_CI_with_ann 
                {|
                    sg_CI_wa_eqv            := sg_eqv A 
                  ; sg_CI_wa_bop            := sg_bop A 
                  ; sg_CI_wa_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CI_wa_exists_ann     := Assert_Exists_Ann ann 
                  ; sg_CI_wa_certs         := P 
                  ; sg_CI_wa_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Not_Exists_Ann => MCAS_sg_CI 
                {|
                    sg_CI_eqv            := sg_eqv A 
                  ; sg_CI_bop            := sg_bop A 
                  ; sg_CI_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CI_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_CI_certs         := P 
                  ; sg_CI_ast            := sg_ast A 
                |}       
  end 
| MCAS_Cert_sg_CNI P   => 
  match sg_exists_id_d A, sg_exists_ann_d A with
  | Certify_Exists_Id id, Certify_Exists_Ann ann => MCAS_sg_BCNI 
                {|
                    sg_BCNI_eqv        := sg_eqv A 
                  ; sg_BCNI_bop        := sg_bop A 
                  ; sg_BCNI_exists_id  := Assert_Exists_Id id
                  ; sg_BCNI_exists_ann := Assert_Exists_Ann ann 
                  ; sg_BCNI_certs     := P 
                  ; sg_BCNI_ast        := sg_ast A 
                |}                                        
  | Certify_Exists_Id id, Certify_Not_Exists_Ann => MCAS_sg_CNI_with_id 
                {|
                    sg_CNI_wi_eqv            := sg_eqv A 
                  ; sg_CNI_wi_bop            := sg_bop A 
                  ; sg_CNI_wi_exists_id      := Assert_Exists_Id id
                  ; sg_CNI_wi_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_CNI_wi_certs         := P 
                  ; sg_CNI_wi_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Exists_Ann ann => MCAS_sg_CNI_with_ann 
                {|
                    sg_CNI_wa_eqv            := sg_eqv A 
                  ; sg_CNI_wa_bop            := sg_bop A 
                  ; sg_CNI_wa_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CNI_wa_exists_ann     := Assert_Exists_Ann ann 
                  ; sg_CNI_wa_certs         := P 
                  ; sg_CNI_wa_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Not_Exists_Ann => MCAS_sg_CNI 
                {|
                    sg_CNI_eqv            := sg_eqv A 
                  ; sg_CNI_bop            := sg_bop A 
                  ; sg_CNI_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CNI_not_exists_ann := Assert_Not_Exists_Ann 
                  ; sg_CNI_certs         := P 
                  ; sg_CNI_ast            := sg_ast A 
                |}       
  end 
| MCAS_Cert_sg_CK P    =>
  match sg_exists_id_d A, sg_exists_ann_d A with
  | Certify_Exists_Id id, Certify_Not_Exists_Ann => MCAS_sg_CK_with_id 
                {|
                    sg_CK_wi_eqv            := sg_eqv A 
                  ; sg_CK_wi_bop            := sg_bop A 
                  ; sg_CK_wi_exists_id      := Assert_Exists_Id id
                  ; sg_CK_wi_certs         := P 
                  ; sg_CK_wi_ast            := sg_ast A 
                |}       
  | Certify_Not_Exists_Id, Certify_Not_Exists_Ann => MCAS_sg_CK 
                {|
                    sg_CK_eqv            := sg_eqv A 
                  ; sg_CK_bop            := sg_bop A 
                  ; sg_CK_not_exists_id  := Assert_Not_Exists_Id
                  ; sg_CK_certs         := P 
                  ; sg_CK_ast            := sg_ast A 
                |}
  | _, Certify_Exists_Ann ann => MCAS_sg_Error ("Internal Error (2) : sg_classify_sg"  :: nil)
  end   
end.



Definition sg_classify (S : Type) (A : @sg_mcas S) : @sg_mcas S :=
match A with
| MCAS_sg_Error _        => A 
| MCAS_sg B              => sg_classify_sg B 

| MCAS_sg_C B            => sg_classify_sg_C B  
| MCAS_sg_C_with_id B    => sg_classify_sg_C_with_id B   
| MCAS_sg_C_with_ann B   => sg_classify_sg_C_with_ann B   
| MCAS_sg_BC B           => sg_classify_sg_BC B   

| MCAS_sg_NC B           => A
| MCAS_sg_NC_with_id B   => A
| MCAS_sg_NC_with_ann B  => A 
| MCAS_sg_BNC B          => A 

| MCAS_sg_CS B           => A
| MCAS_sg_CS_with_id B   => A
| MCAS_sg_CS_with_ann B  => A
| MCAS_sg_BCS B          => A

| MCAS_sg_CI B           => A 
| MCAS_sg_CI_with_id B   => A
| MCAS_sg_CI_with_ann B  => A 
| MCAS_sg_BCI B          => A 

| MCAS_sg_CNI B          => sg_classify_sg_CNI B   
| MCAS_sg_CNI_with_id B  => sg_classify_sg_CNI_with_id B  
| MCAS_sg_CNI_with_ann B => A 
| MCAS_sg_BCNI B         => A 

| MCAS_sg_CK _           => A 
| MCAS_sg_CK_with_id _   => A 
end.

Print sg_certs_mcas. 

Definition mcas_sg_certs {S : Type} (A : @sg_mcas S) : @sg_certs_mcas S :=
match A with
| MCAS_sg_Error sl       => MCAS_Cert_sg_Error sl 
| MCAS_sg B              => MCAS_Cert_sg (sg_certs B)

| MCAS_sg_C B            => MCAS_Cert_sg_C (sg_C_certs B)
| MCAS_sg_C_with_id B    => MCAS_Cert_sg_C (sg_C_wi_certs B)
| MCAS_sg_C_with_ann B   => MCAS_Cert_sg_C (sg_C_wa_certs B)
| MCAS_sg_BC B           => MCAS_Cert_sg_C (sg_BC_certs B)

| MCAS_sg_NC B           => MCAS_Cert_sg_NC (sg_NC_certs B)
| MCAS_sg_NC_with_id B   => MCAS_Cert_sg_NC (sg_NC_wi_certs B)
| MCAS_sg_NC_with_ann B  => MCAS_Cert_sg_NC (sg_NC_wa_certs B)
| MCAS_sg_BNC B          => MCAS_Cert_sg_NC (sg_BNC_certs B)

| MCAS_sg_CS B           => MCAS_Cert_sg_CS (sg_CS_certs B)
| MCAS_sg_CS_with_id B   => MCAS_Cert_sg_CS (sg_CS_wi_certs B)
| MCAS_sg_CS_with_ann B  => MCAS_Cert_sg_CS (sg_CS_wa_certs B)
| MCAS_sg_BCS B          => MCAS_Cert_sg_CS (sg_BCS_certs B)

| MCAS_sg_CI B           => MCAS_Cert_sg_CI (sg_CI_certs B)
| MCAS_sg_CI_with_id B   => MCAS_Cert_sg_CI (sg_CI_wi_certs B)
| MCAS_sg_CI_with_ann B  => MCAS_Cert_sg_CI (sg_CI_wa_certs B)
| MCAS_sg_BCI B          => MCAS_Cert_sg_CI (sg_BCI_certs B)

| MCAS_sg_CNI B          => MCAS_Cert_sg_CNI (sg_CNI_certs B)
| MCAS_sg_CNI_with_id B  => MCAS_Cert_sg_CNI (sg_CNI_wi_certs B)
| MCAS_sg_CNI_with_ann B => MCAS_Cert_sg_CNI (sg_CNI_wa_certs B)
| MCAS_sg_BCNI B         => MCAS_Cert_sg_CNI (sg_BCNI_certs B)

| MCAS_sg_CK B           => MCAS_Cert_sg_CK (sg_CK_certs B)
| MCAS_sg_CK_with_id B   => MCAS_Cert_sg_CK (sg_CK_wi_certs B)
end.


End MCAS.                                                                                            



Section Verify.

Section Proofs.   
Variables (S : Type)
          (eq : brel S)
          (bop : binary_op S).

(* some lemmas are just stubs in case of future extensions.... *) 

Lemma correct_sg_certificates_classify_sg_CK (s : sg_CK_proofs S eq bop) : 
  MCAS_Cert_sg_CK (P2C_sg_CK S eq bop s) =
  MCAS_Cert_sg_CK (P2C_sg_CK S eq bop s).
Proof. reflexivity. Qed. 

Lemma correct_sg_certificates_classify_sg_CNI (s : sg_CNI_proofs S eq bop) : 
  sg_certificates_classify_sg_CNI (P2C_sg_CNI S eq bop s) =
  P2C_proofs_mcas_sg S eq bop (A_sg_proofs_classify_sg_CNI S eq bop s).
Proof. destruct s.
       unfold sg_certificates_classify_sg_CNI, A_sg_proofs_classify_sg_CNI.
       unfold P2C_sg_CNI, P2C_proofs_mcas_sg; simpl.
       destruct A_sg_CNI_cancel_d0 as [A | [trip A]]; simpl.
          unfold P2C_sg_CK; simpl. reflexivity. 
          unfold P2C_sg_CNI; simpl. reflexivity. 
Qed.

Lemma correct_sg_certificates_classify_sg_CS (s : sg_CS_proofs S eq bop) : 
  MCAS_Cert_sg_CS (P2C_sg_CS S eq bop s) =
  MCAS_Cert_sg_CS (P2C_sg_CS S eq bop s).
Proof. reflexivity. Qed. 

Lemma correct_sg_certificates_classify_sg_CI (s : sg_CI_proofs S eq bop) : 
  MCAS_Cert_sg_CI (P2C_sg_CI S eq bop s) =
  MCAS_Cert_sg_CI (P2C_sg_CI S eq bop s).
Proof. reflexivity. Qed. 

Lemma correct_sg_certificates_classify_sg_NC (s : sg_NC_proofs S eq bop) : 
  MCAS_Cert_sg_NC (P2C_sg_NC S eq bop s) =
  MCAS_Cert_sg_NC (P2C_sg_NC S eq bop s).
Proof. reflexivity. Qed. 

Lemma correct_sg_certificates_classify_sg_C (s : sg_C_proofs S eq bop) : 
  sg_certificates_classify_sg_C (P2C_sg_C S eq bop s) =
  P2C_proofs_mcas_sg S eq bop (A_sg_proofs_classify_sg_C S eq bop s).
Proof. destruct s.
       unfold sg_certificates_classify_sg_C, A_sg_proofs_classify_sg_C.
       unfold P2C_sg_C, P2C_proofs_mcas_sg; simpl.
       destruct A_sg_C_idempotent_d0 as [A | [i A]];
       destruct A_sg_C_selective_d0 as [B | [[a b] B]]; simpl. 
          unfold P2C_sg_CS; simpl. reflexivity. 
          unfold P2C_sg_CI; simpl. unfold p2c_not_selective_assert; simpl. reflexivity.
          unfold P2C_sg_CNI; simpl.  reflexivity.
          unfold P2C_sg_CNI; simpl.  reflexivity.                    
Qed.


Lemma correct_sg_certificates_classify_sg (s : sg_proofs S eq bop): 
  sg_certificates_classify_sg (P2C_sg S eq bop s) =
  P2C_proofs_mcas_sg S eq bop (A_sg_proofs_classify_sg S eq bop s). 
Proof. unfold sg_certificates_classify_sg, A_sg_proofs_classify_sg.
       case_eq (A_sg_commutative_d S eq bop s); simpl.  
       + intros cmm A. unfold p2c_commutative_check. 
         rewrite A. rewrite <- correct_sg_certificates_classify_sg_C.
         unfold P2C_sg_C; simpl. reflexivity.
       + intros ncomm A. rewrite A; simpl. 
         unfold P2C_sg_NC; simpl. reflexivity. 
Qed.

Theorem correct_sg_proof_classify (A : sg_proofs_mcas S eq bop) :   
  sg_certificates_classify (P2C_proofs_mcas_sg S eq bop A)
  =
  P2C_proofs_mcas_sg S _ _ (sg_proof_classify S eq bop A).
Proof. unfold sg_certificates_classify, sg_proof_classify; destruct A; simpl.
       reflexivity.
       apply correct_sg_certificates_classify_sg.
       apply correct_sg_certificates_classify_sg_C.
       apply correct_sg_certificates_classify_sg_NC.
       apply correct_sg_certificates_classify_sg_CS.
       apply correct_sg_certificates_classify_sg_CI.
       apply correct_sg_certificates_classify_sg_CNI.
       apply correct_sg_certificates_classify_sg_CK.
Qed. 

(* ********************************************* *)                   
                  
End Proofs.

Section Combinators.   

  Variables (S : Type).

Lemma correct_sg_classify_sg_BNC (a : A_sg_BNC S) : 
  MCAS_sg_BNC (A2C_sg_BNC S a) = MCAS_sg_BNC (A2C_sg_BNC S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_CS (a : A_sg_CS S) : 
  MCAS_sg_CS (A2C_sg_CS S a) = MCAS_sg_CS (A2C_sg_CS S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_CS_with_id (a : A_sg_CS_with_id S) : 
  MCAS_sg_CS_with_id (A2C_sg_CS_with_id S a) =
  MCAS_sg_CS_with_id (A2C_sg_CS_with_id S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_CS_with_ann (a : A_sg_CS_with_ann S) : 
  MCAS_sg_CS_with_ann (A2C_sg_CS_with_ann S a) =
  MCAS_sg_CS_with_ann (A2C_sg_CS_with_ann S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_BCS (a : A_sg_BCS S) : 
  MCAS_sg_BCS (A2C_sg_BCS S a) = MCAS_sg_BCS (A2C_sg_BCS S a).
Proof. reflexivity. Qed.         

Lemma correct_sg_classify_sg_CI  (a : A_sg_CI S) : 
  MCAS_sg_CI (A2C_sg_CI S a) = MCAS_sg_CI (A2C_sg_CI S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_CI_with_id (a : A_sg_CI_with_id S) : 
  MCAS_sg_CI_with_id (A2C_sg_CI_with_id S a) =
  MCAS_sg_CI_with_id (A2C_sg_CI_with_id S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_CI_with_ann (a : A_sg_CI_with_ann S) : 
  MCAS_sg_CI_with_ann (A2C_sg_CI_with_ann S a) =
  MCAS_sg_CI_with_ann (A2C_sg_CI_with_ann S a).
Proof. reflexivity. Qed.   

Lemma correct_sg_classify_sg_BCI (a : A_sg_BCI S) : 
  MCAS_sg_BCI (A2C_sg_BCI S a) = MCAS_sg_BCI (A2C_sg_BCI S a).
Proof. reflexivity. Qed. 
                                             
Lemma correct_sg_classify_sg_CNI (a : A_sg_CNI S) : 
  sg_classify_sg_CNI (A2C_sg_CNI S a) =
  A2C_mcas_sg S (A_sg_classify_sg_CNI S a).
Proof. unfold sg_classify_sg_CNI, A_sg_classify_sg_CNI.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg_CNI.
       case(A_sg_proofs_classify_sg_CNI S (A_eqv_eq S A_sg_CNI_eqv0) A_sg_CNI_bop0 A_sg_CNI_proofs0); simpl.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + unfold A2C_sg_CNI; simpl. reflexivity. 
       + unfold A2C_sg_CK; simpl. reflexivity. 
Qed.          


         
Lemma correct_sg_classify_sg_CNI_with_id (a : A_sg_CNI_with_id S) : 
  sg_classify_sg_CNI_with_id (A2C_sg_CNI_with_id S a) =
  A2C_mcas_sg S (A_sg_classify_sg_CNI_with_id S a).
Proof. unfold sg_classify_sg_CNI_with_id, A_sg_classify_sg_CNI_with_id.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg_CNI.
       case(A_sg_proofs_classify_sg_CNI S (A_eqv_eq S A_sg_CNI_wi_eqv0) A_sg_CNI_wi_bop0 A_sg_CNI_wi_proofs0); simpl.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + reflexivity.
       + unfold A2C_sg_CNI_with_id; simpl. reflexivity. 
       + unfold A2C_sg_CK_with_id; simpl. reflexivity. 
Qed.   

Lemma correct_sg_classify_sg_CNI_with_ann (a : A_sg_CNI_with_ann S) : 
  MCAS_sg_CNI_with_ann (A2C_sg_CNI_with_ann S a) =
  MCAS_sg_CNI_with_ann (A2C_sg_CNI_with_ann S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_BCNI (a : A_sg_BCNI S) : 
  MCAS_sg_BCNI (A2C_sg_BCNI S a) = MCAS_sg_BCNI (A2C_sg_BCNI S a).
Proof. reflexivity. Qed.

Lemma correct_sg_classify_sg_CK (a : A_sg_CK S) : 
  MCAS_sg_CK (A2C_sg_CK S a) = MCAS_sg_CK (A2C_sg_CK S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_CK_with_id (a : A_sg_CK_with_id S) : 
  MCAS_sg_CK_with_id (A2C_sg_CK_with_id S a) =
  MCAS_sg_CK_with_id (A2C_sg_CK_with_id S a). 
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_NC_with_id (a : A_sg_NC_with_id S) : 
  MCAS_sg_NC_with_id (A2C_sg_NC_with_id S a) =
  MCAS_sg_NC_with_id (A2C_sg_NC_with_id S a).
Proof. reflexivity. Qed. 

Lemma correct_sg_classify_sg_NC_with_ann (a : A_sg_NC_with_ann S) : 
  MCAS_sg_NC_with_ann (A2C_sg_NC_with_ann S a) =
  MCAS_sg_NC_with_ann (A2C_sg_NC_with_ann S a).  
Proof. reflexivity. Qed. 



Lemma correct_sg_classify_sg_NC (a : A_sg_NC S) : 
  MCAS_sg_NC (A2C_sg_NC S a) = MCAS_sg_NC (A2C_sg_NC S a).
Proof. reflexivity. Qed. 


Lemma correct_sg_classify_sg_BC   (a : A_sg_BC S) : 
  sg_classify_sg_BC (A2C_sg_BC S a) = A2C_mcas_sg S (A_sg_classify_sg_BC S a).
Proof. unfold sg_classify_sg_BC, A_sg_classify_sg_BC.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg_C.
       case(A_sg_proofs_classify_sg_C S (A_eqv_eq S A_sg_BC_eqv0) A_sg_BC_bop0 A_sg_BC_proofs0); simpl.
       + reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_BC; simpl. reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_BCS; simpl. reflexivity. 
       + unfold A2C_sg_BCI; simpl. reflexivity.          
       + unfold A2C_sg_BCNI; simpl. reflexivity. 
       + reflexivity. 
Qed.          


Lemma correct_sg_classify_sg_C_with_ann (a : A_sg_C_with_ann S) : 
  sg_classify_sg_C_with_ann (A2C_sg_C_with_ann S a) =
  A2C_mcas_sg S (A_sg_classify_sg_C_with_ann S a).
Proof. unfold sg_classify_sg_C_with_ann, A_sg_classify_sg_C_with_ann.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg_C.
       case(A_sg_proofs_classify_sg_C S (A_eqv_eq S A_sg_C_wa_eqv0) A_sg_C_wa_bop0 A_sg_C_wa_proofs0); simpl.
       + reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_C_with_ann; simpl. reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_CS_with_ann; simpl. reflexivity. 
       + unfold A2C_sg_CI_with_ann; simpl. reflexivity.          
       + unfold A2C_sg_CNI_with_ann; simpl. reflexivity. 
       + reflexivity. 
Qed.          



Lemma correct_sg_classify_sg_C_with_id (a : A_sg_C_with_id S) : 
  sg_classify_sg_C_with_id (A2C_sg_C_with_id S a) =
  A2C_mcas_sg S (A_sg_classify_sg_C_with_id S a).
Proof. unfold sg_classify_sg_C_with_id, A_sg_classify_sg_C_with_id.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg_C.
       case(A_sg_proofs_classify_sg_C S (A_eqv_eq S A_sg_C_wi_eqv0) A_sg_C_wi_bop0 A_sg_C_wi_proofs0); simpl.
       + reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_C_with_id; simpl. reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_CS_with_id; simpl. reflexivity. 
       + unfold A2C_sg_CI_with_id; simpl. reflexivity.          
       + unfold A2C_sg_CNI_with_id; simpl. reflexivity. 
       + reflexivity. 
Qed.          



Lemma correct_sg_classify_sg_C (a : A_sg_C S) : 
  sg_classify_sg_C (A2C_sg_C S a) = A2C_mcas_sg S (A_sg_classify_sg_C S a).
Proof. unfold sg_classify_sg_C, A_sg_classify_sg_C.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg_C.
       case(A_sg_proofs_classify_sg_C S (A_eqv_eq S A_sg_C_eqv0) A_sg_C_bop0 A_sg_C_proofs0); simpl.
       + reflexivity. 
       + reflexivity. 
       + reflexivity. 
       + reflexivity. 
       + unfold A2C_sg_CS; simpl. reflexivity. 
       + unfold A2C_sg_CI; simpl. reflexivity.          
       + unfold A2C_sg_CNI; simpl. reflexivity. 
       + unfold A2C_sg_CK; simpl. reflexivity. 
Qed.          

Lemma correct_sg_classify_sg (a : A_sg S) : 
  sg_classify_sg (A2C_sg S a) = A2C_mcas_sg S (A_sg_classify_sg S a).
Proof. unfold sg_classify_sg, A_sg_classify_sg.
       destruct a; simpl. 
       rewrite correct_sg_certificates_classify_sg.
       case(A_sg_proofs_classify_sg S (A_eqv_eq S A_sg_eqv0) A_sg_bop0 A_sg_proofs0); simpl. 
       + intro l. reflexivity. 
       + reflexivity. 
       + destruct A_sg_exists_id_d0 as [[id A] | nid]; destruct A_sg_exists_ann_d0 as [[ann B] | nann]; simpl. 
         ++ unfold A2C_sg_BC; simpl. reflexivity. 
         ++ unfold A2C_sg_C; simpl. reflexivity. 
         ++ unfold A2C_sg_C_with_ann; simpl. reflexivity. 
         ++ unfold A2C_sg_C; simpl. reflexivity.
       + destruct A_sg_exists_id_d0 as [[id A] | nid]; destruct A_sg_exists_ann_d0 as [[ann B] | nann]; simpl. 
         ++ unfold A2C_sg_BNC; simpl. reflexivity. 
         ++ unfold A2C_sg_NC; simpl. reflexivity. 
         ++ unfold A2C_sg_NC_with_ann; simpl. reflexivity. 
         ++ unfold A2C_sg_NC; simpl. reflexivity.
       + destruct A_sg_exists_id_d0 as [[id A] | nid]; destruct A_sg_exists_ann_d0 as [[ann B] | nann]; simpl. 
         ++ unfold A2C_sg_BCS; simpl. reflexivity. 
         ++ unfold A2C_sg_CS; simpl. reflexivity. 
         ++ unfold A2C_sg_CS_with_ann; simpl. reflexivity. 
         ++ unfold A2C_sg_CS; simpl. reflexivity.
       + destruct A_sg_exists_id_d0 as [[id A] | nid]; destruct A_sg_exists_ann_d0 as [[ann B] | nann]; simpl. 
         ++ unfold A2C_sg_BCI; simpl. reflexivity. 
         ++ unfold A2C_sg_CI; simpl. reflexivity. 
         ++ unfold A2C_sg_CI_with_ann; simpl. reflexivity. 
         ++ unfold A2C_sg_CI; simpl. reflexivity.
       + destruct A_sg_exists_id_d0 as [[id A] | nid]; destruct A_sg_exists_ann_d0 as [[ann B] | nann]; simpl. 
         ++ unfold A2C_sg_BCNI; simpl. reflexivity. 
         ++ unfold A2C_sg_CNI; simpl. reflexivity. 
         ++ unfold A2C_sg_CNI_with_ann; simpl. reflexivity. 
         ++ unfold A2C_sg_CNI; simpl. reflexivity.
       + destruct A_sg_exists_id_d0 as [[id A] | nid]; destruct A_sg_exists_ann_d0 as [[ann B] | nann]; simpl. 
         ++ reflexivity. 
         ++ unfold A2C_sg_CK_with_id; simpl. reflexivity. 
         ++ reflexivity. 
         ++ unfold A2C_sg_CK; simpl. reflexivity.
Qed. 


Theorem correct_sg_classify (A : A_sg_mcas S) :   
  sg_classify S (A2C_mcas_sg S A)
  =
  A2C_mcas_sg S (A_sg_classify S A).
Proof. unfold sg_classify, A_sg_classify; destruct A; simpl.
       reflexivity. 
       apply correct_sg_classify_sg. 
       apply correct_sg_classify_sg_C.                
       apply correct_sg_classify_sg_C_with_id.
       apply correct_sg_classify_sg_C_with_ann.
       apply correct_sg_classify_sg_BC.                       
       apply correct_sg_classify_sg_NC.                
       apply correct_sg_classify_sg_NC_with_id.
       apply correct_sg_classify_sg_NC_with_ann.
       apply correct_sg_classify_sg_BNC.                       
       apply correct_sg_classify_sg_CS.                
       apply correct_sg_classify_sg_CS_with_id.
       apply correct_sg_classify_sg_CS_with_ann.
       apply correct_sg_classify_sg_BCS.                       
       apply correct_sg_classify_sg_CI.                
       apply correct_sg_classify_sg_CI_with_id.
       apply correct_sg_classify_sg_CI_with_ann.
       apply correct_sg_classify_sg_BCI.                       
       apply correct_sg_classify_sg_CNI.                
       apply correct_sg_classify_sg_CNI_with_id.
       apply correct_sg_classify_sg_CNI_with_ann.
       apply correct_sg_classify_sg_BCNI.                       
       apply correct_sg_classify_sg_CK.                
       apply correct_sg_classify_sg_CK_with_id.
Qed.

End Combinators. 

End Verify.   
