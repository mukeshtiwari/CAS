Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.proof_records.
Require Import CAS.coq.common.brel_properties.
Require Import CAS.coq.common.bop_properties.
Require Import CAS.coq.common.bs_properties.
Require Import CAS.coq.common.lt_properties. 

(* eqv *) 
Record A_eqv (S : Type) := {
  A_eqv_eq          : brel S
; A_eqv_proofs      : eqv_proofs S A_eqv_eq

(* put "cardinality" info in a separate record? *)                                  
; A_eqv_witness       : S         (* not empty *) 
; A_eqv_new           : S -> S
; A_eqv_not_trivial   : brel_not_trivial S A_eqv_eq A_eqv_new
; A_eqv_exactly_two_d : brel_exactly_two_decidable S A_eqv_eq 

(* another record for this stuff? *)                                                    
; A_eqv_data        : S -> data (* for printing in ocaml-land *) 
; A_eqv_rep         : S -> S    (* for reductions? need proved properties for this? *) 
; A_eqv_ast         : ast_eqv 
}.


(* orders *) 

(* quasi order *) 
Record A_qo (S : Type) := {
  A_qo_eqv        : A_eqv S 
; A_qo_brel       : brel S 
; A_qo_proofs     : qo_proofs S (A_eqv_eq S A_qo_eqv) A_qo_brel 
; A_qo_ast        : ast_qo
}.

(* partial order *) 
Record A_po (S : Type) := {
  A_po_eqv        : A_eqv S 
; A_po_brel       : brel S 
; A_po_proofs     : po_proofs S (A_eqv_eq S A_po_eqv) A_po_brel 
; A_po_ast        : ast_po
}.

(* total order *) 
Record A_to (S : Type) := {
  A_to_eqv        : A_eqv S 
; A_to_brel       : brel S 
; A_to_proofs     : to_proofs S (A_eqv_eq S A_to_eqv) A_to_brel 
; A_to_ast        : ast_to
}.




(* semigroups *) 
Record A_sg (S : Type) := {
  A_sg_eq         : A_eqv S 
; A_sg_bop        : binary_op S 
; A_sg_proofs     : sg_proofs S (A_eqv_eq S A_sg_eq) A_sg_bop 
; A_sg_bop_ast    : ast_bop                      
; A_sg_ast        : ast_sg
}.



(* sg_C = commutative semigroup *) 
Record A_sg_C (S : Type) := {
  A_sg_C_eqv         : A_eqv S 
; A_sg_C_bop         : binary_op S 
; A_sg_C_proofs      : sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_bop_ast     : ast_bop                      
; A_sg_C_ast         : ast_sg_C
}.


(* sg_CI = commutative idempotent semigroup *) 
Record A_sg_CI (S : Type) := {
  A_sg_CI_eqv          : A_eqv S
; A_sg_CI_bop          : binary_op S 
; A_sg_CI_proofs       : sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_bop_ast      : ast_bop                                                            
; A_sg_CI_ast          : ast_sg_CI
}.


(* sg_CS = commutative selective semigroup *) 
Record A_sg_CS (S : Type) := {
  A_sg_CS_eqv          : A_eqv S 
; A_sg_CS_bop          : binary_op S 
; A_sg_CS_proofs       : sg_CS_proofs S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_bop_ast      : ast_bop                                                            
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
; A_sg_CK_bop_ast     : ast_bop                                                           
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
; A_bs_plus_ast     : ast_bop
; A_bs_times_ast    : ast_bop                                                                            
; A_bs_ast          : ast_bs
}.


Record A_bs_CS (S : Type) := {
  A_bs_CS_eqv          : A_eqv S 
; A_bs_CS_plus         : binary_op S 
; A_bs_CS_times        : binary_op S 
; A_bs_CS_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus
; A_bs_CS_times_proofs : sg_proofs S    (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times 
; A_bs_CS_proofs       : bs_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_plus_ast     : ast_bop
; A_bs_CS_times_ast    : ast_bop                                                                            
; A_bs_CS_ast          : ast_bs_CS
}.

Record A_bs_CI (S : Type) := {
  A_bs_CI_eqv          : A_eqv S 
; A_bs_CI_plus         : binary_op S 
; A_bs_CI_times        : binary_op S 
; A_bs_CI_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus
; A_bs_CI_times_proofs : sg_proofs S    (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_times 
; A_bs_CI_proofs       : bs_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_plus_ast     : ast_bop
; A_bs_CI_times_ast    : ast_bop                                                                            
; A_bs_CI_ast          : ast_bs_CI
}.


Record A_bs_C (S : Type) := {
  A_bs_C_eqv          : A_eqv S 
; A_bs_C_plus         : binary_op S 
; A_bs_C_times        : binary_op S 
; A_bs_C_plus_proofs  : sg_C_proofs S (A_eqv_eq S A_bs_C_eqv) A_bs_C_plus
; A_bs_C_times_proofs : sg_proofs S   (A_eqv_eq S A_bs_C_eqv) A_bs_C_times 
; A_bs_C_proofs       : bs_proofs S (A_eqv_eq S A_bs_C_eqv) A_bs_C_plus A_bs_C_times
; A_bs_C_plus_ast     : ast_bop
; A_bs_C_times_ast    : ast_bop                                                                            
; A_bs_C_ast          : ast_bs_C
}.


Record A_semiring (S : Type) := {
  A_semiring_eqv          : A_eqv S 
; A_semiring_plus         : binary_op S 
; A_semiring_times        : binary_op S 
; A_semiring_plus_proofs  : sg_C_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus
; A_semiring_times_proofs : sg_proofs S   (A_eqv_eq S A_semiring_eqv) A_semiring_times 
; A_semiring_proofs       : semiring_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_plus_ast     : ast_bop
; A_semiring_times_ast    : ast_bop                                                                            
; A_semiring_ast          : ast_semiring
}.

Record A_dioid (S : Type) := {
  A_dioid_eqv          : A_eqv S 
; A_dioid_plus         : binary_op S 
; A_dioid_times        : binary_op S 
; A_dioid_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus
; A_dioid_times_proofs : sg_proofs S   (A_eqv_eq S A_dioid_eqv) A_dioid_times 
; A_dioid_proofs       : semiring_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_plus_ast     : ast_bop
; A_dioid_times_ast    : ast_bop                                                                            
; A_dioid_ast          : ast_dioid
}.

Record A_selective_dioid (S : Type) := {
  A_selective_dioid_eqv          : A_eqv S 
; A_selective_dioid_plus         : binary_op S 
; A_selective_dioid_times        : binary_op S 
; A_selective_dioid_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus
; A_selective_dioid_times_proofs : sg_proofs S   (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_times 
; A_selective_dioid_proofs       : semiring_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_plus_ast     : ast_bop
; A_selective_dioid_times_ast    : ast_bop                                                                            
; A_selective_dioid_ast          : ast_selective_dioid
}.


Record A_lattice (S : Type) := {
  A_lattice_eqv         : A_eqv S 
; A_lattice_join        : binary_op S 
; A_lattice_meet        : binary_op S 
; A_lattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join
; A_lattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_meet 
; A_lattice_proofs      : lattice_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet
; A_lattice_join_ast    : ast_bop
; A_lattice_meet_ast   : ast_bop                                                                            
; A_lattice_ast         : ast_lattice
}.

Record A_distributive_lattice (S : Type) := {
  A_distributive_lattice_eqv         : A_eqv S 
; A_distributive_lattice_join        : binary_op S 
; A_distributive_lattice_meet        : binary_op S 
; A_distributive_lattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_join
; A_distributive_lattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_meet 
; A_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet
; A_distributive_lattice_join_ast    : ast_bop
; A_distributive_lattice_meet_ast   : ast_bop                                                                            
; A_distributive_lattice_ast         : ast_distributive_lattice
}.



Record A_selective_distributive_lattice (S : Type) := {
  A_selective_distributive_lattice_eqv         : A_eqv S 
; A_selective_distributive_lattice_join        : binary_op S 
; A_selective_distributive_lattice_meet        : binary_op S 
; A_selective_distributive_lattice_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_join
; A_selective_distributive_lattice_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_meet 
; A_selective_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_lattice_eqv)
                                          A_selective_distributive_lattice_join
                                          A_selective_distributive_lattice_meet
; A_selective_distributive_lattice_join_ast    : ast_bop
; A_selective_distributive_lattice_meet_ast    : ast_bop                                                                            
; A_selective_distributive_lattice_ast         : ast_selective_distributive_lattice
}.

(* order-semigroups *) 

Record A_os (S : Type) := {
  A_os_eqv          : A_eqv S 
; A_os_lte          : brel S 
; A_os_times        : binary_op S 
; A_os_lte_proofs   : po_proofs S (A_eqv_eq S A_os_eqv) A_os_lte
; A_os_times_proofs : sg_proofs S (A_eqv_eq S A_os_eqv) A_os_times 
; A_os_proofs       : os_proofs S A_os_lte A_os_times 
; A_os_ast          : ast_os
}.

(*   
    Tranforms 
*)

Record ltr_proofs (S L : Type) (eqS : brel S) (eqL : brel L) (ltr : L -> (S -> S)) := 
{
  A_ltr_congruence          : lt_congruence L S eqL eqS ltr
; A_ltr_is_right_d          : lt_is_right_decidable L S eqS ltr
; A_ltr_exists_id_d         : lt_exists_id_decidable L S eqS ltr
; A_ltr_left_cancellative_d : lt_left_cancellative_decidable L S eqS ltr
}.

Record A_ltr (S L : Type) :=
{
  A_ltr_carrier : A_eqv S
; A_ltr_label   : A_eqv L                                                       
; A_ltr_trans   : left_transform L S (* T -> (S -> S) *) 
; A_ltr_proofs  : ltr_proofs S L (A_eqv_eq S A_ltr_carrier) (A_eqv_eq L A_ltr_label)  A_ltr_trans
; A_ltr_ast     : ast_ltr
}.


Definition sltr_distributive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition sltr_not_distributive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition sltr_distributive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_distributive S L r add ltr) + (sltr_not_distributive S L r add ltr). 
 
Definition sltr_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition sltr_not_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition sltr_absorptive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_absorptive S L r add ltr) + (sltr_not_absorptive S L r add ltr). 

Record sltr_proofs (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :=
{
  sltr_distributive_d : sltr_distributive_decidable S L r add ltr
; sltr_absorptive_d   : sltr_absorptive_decidable S L r add ltr                                  
}.

Record A_sltr (S L : Type) :=
{
  A_sltr_carrier      : A_eqv S
; A_sltr_label        : A_eqv L
; A_sltr_plus         : binary_op S                                               
; A_sltr_trans        : left_transform L S (* L -> (S -> S) *)
; A_sltr_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_sltr_carrier) A_sltr_plus                                 
; A_sltr_trans_proofs : ltr_proofs S L (A_eqv_eq S A_sltr_carrier) (A_eqv_eq L A_sltr_label)  A_sltr_trans
; A_sltr_proofs       : sltr_proofs S L (A_eqv_eq S A_sltr_carrier) A_sltr_plus A_sltr_trans                                  
; A_sltr_ast          : ast_sltr
}.



