Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.proof_records.
Require Import CAS.coq.common.brel_properties.
Require Import CAS.coq.common.bop_properties.

(* eqv : for "carrier types" *) 
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
; A_eqv_finite_d    : carrier_is_finite_decidable S A_eqv_eq                             
; A_eqv_ast         : cas_ast
}.


(* semigroups 

sg    = semigroup 
sg_C  = commutative semigroup 
sg_CS = commutative idempotent semigroup 
sg_CS = commutative selective semigroup 
sg_CK = commutative cancellative semigroup 

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

If cancellative, 

    LK: a * b = a * c -> b = c      

suppose c is any idempotent : c * c = c, then c = id 

    c * a = (c * c) * a = c * (c * a) 
    -LK-> a = c * a 

     LK -> idem(c) -> left_id(c), etc 

So any cancellative idempotent commutative semigroup will be trivial {id}. 

*) 

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

(* bi-semigroups *) 

Record A_bs (S : Type) := {
  A_bs_eqv          : A_eqv S 
; A_bs_plus         : binary_op S 
; A_bs_times        : binary_op S 
; A_bs_plus_proofs   : asg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus
; A_bs_times_proofs  : msg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_times
; A_bs_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times                                 
; A_bs_proofs        : bs_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times
; A_bs_ast           : cas_ast
}.


Record A_bs_CS (S : Type) := {
  A_bs_CS_eqv           : A_eqv S 
; A_bs_CS_plus          : binary_op S 
; A_bs_CS_times         : binary_op S 
; A_bs_CS_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus
; A_bs_CS_times_proofs  : msg_proofs S    (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times
; A_bs_CS_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_proofs        : bs_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_ast           : cas_ast
}.

Record A_bs_CI (S : Type) := {
  A_bs_CI_eqv           : A_eqv S 
; A_bs_CI_plus          : binary_op S 
; A_bs_CI_times         : binary_op S 
; A_bs_CI_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus
; A_bs_CI_times_proofs  : msg_proofs S    (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_times
; A_bs_CI_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_proofs        : bs_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_ast           : cas_ast
}.

Record A_presemiring (S : Type) := {
  A_presemiring_eqv           : A_eqv S 
; A_presemiring_plus          : binary_op S 
; A_presemiring_times         : binary_op S 
; A_presemiring_plus_proofs   : sg_C_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus
; A_presemiring_times_proofs  : msg_proofs S   (A_eqv_eq S A_presemiring_eqv) A_presemiring_times
; A_presemiring_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus A_presemiring_times
; A_presemiring_proofs        : semiring_proofs S (A_eqv_eq S A_presemiring_eqv) A_presemiring_plus A_presemiring_times
; A_presemiring_ast           : cas_ast
}.

Record A_selective_presemiring (S : Type) := {
  A_selective_presemiring_eqv           : A_eqv S 
; A_selective_presemiring_plus          : binary_op S 
; A_selective_presemiring_times         : binary_op S 
; A_selective_presemiring_plus_proofs   : sg_CS_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus
; A_selective_presemiring_times_proofs  : msg_proofs S   (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_times
; A_selective_presemiring_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus A_selective_presemiring_times
; A_selective_presemiring_proofs        : semiring_proofs S (A_eqv_eq S A_selective_presemiring_eqv) A_selective_presemiring_plus A_selective_presemiring_times
; A_selective_presemiring_ast           : cas_ast
}.


Record A_semiring (S : Type) := {
  A_semiring_eqv          : A_eqv S 
; A_semiring_plus         : binary_op S 
; A_semiring_times        : binary_op S 
; A_semiring_plus_proofs  : sg_C_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus
; A_semiring_times_proofs : msg_proofs S   (A_eqv_eq S A_semiring_eqv) A_semiring_times
; A_semiring_id_ann_proofs : zero_one_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_proofs       : semiring_proofs S (A_eqv_eq S A_semiring_eqv) A_semiring_plus A_semiring_times
; A_semiring_ast          : cas_ast
}.

Record A_selective_semiring (S : Type) := {
  A_selective_semiring_eqv          : A_eqv S 
; A_selective_semiring_plus         : binary_op S 
; A_selective_semiring_times        : binary_op S 
; A_selective_semiring_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus
; A_selective_semiring_times_proofs : msg_proofs S   (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_times
; A_selective_semiring_id_ann_proofs : zero_one_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_proofs       : semiring_proofs S (A_eqv_eq S A_selective_semiring_eqv) A_selective_semiring_plus A_selective_semiring_times
; A_selective_semiring_ast          : cas_ast
}.

Record A_dioid (S : Type) := {
  A_dioid_eqv           : A_eqv S 
; A_dioid_plus          : binary_op S 
; A_dioid_times         : binary_op S 
; A_dioid_plus_proofs   : sg_CI_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus
; A_dioid_times_proofs  : msg_proofs S   (A_eqv_eq S A_dioid_eqv) A_dioid_times
; A_dioid_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_proofs        : semiring_proofs S (A_eqv_eq S A_dioid_eqv) A_dioid_plus A_dioid_times
; A_dioid_ast           : cas_ast
}.

Record A_selective_dioid (S : Type) := {
  A_selective_dioid_eqv          : A_eqv S 
; A_selective_dioid_plus         : binary_op S 
; A_selective_dioid_times        : binary_op S 
; A_selective_dioid_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus
; A_selective_dioid_times_proofs : msg_proofs S   (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_times
; A_selective_dioid_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_proofs       : semiring_proofs S (A_eqv_eq S A_selective_dioid_eqv) A_selective_dioid_plus A_selective_dioid_times
; A_selective_dioid_ast          : cas_ast
}.



Record A_prelattice (S : Type) := {
  A_prelattice_eqv           : A_eqv S 
; A_prelattice_join          : binary_op S 
; A_prelattice_meet          : binary_op S 
; A_prelattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join
; A_prelattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_meet
; A_prelattice_id_ann_proofs : id_ann_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join A_prelattice_meet      
; A_prelattice_proofs        : lattice_proofs S (A_eqv_eq S A_prelattice_eqv) A_prelattice_join A_prelattice_meet
; A_prelattice_ast           : cas_ast
}.

Record A_distributive_prelattice (S : Type) := {
  A_distributive_prelattice_eqv         : A_eqv S 
; A_distributive_prelattice_join        : binary_op S 
; A_distributive_prelattice_meet        : binary_op S 
; A_distributive_prelattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_prelattice_eqv) A_distributive_prelattice_join
; A_distributive_prelattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_prelattice_eqv) A_distributive_prelattice_meet
; A_distributive_prelattice_id_ann_proofs : id_ann_proofs S
                                          (A_eqv_eq S A_distributive_prelattice_eqv)
                                          A_distributive_prelattice_join
                                          A_distributive_prelattice_meet                                                        
; A_distributive_prelattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_distributive_prelattice_eqv)
                                          A_distributive_prelattice_join
                                          A_distributive_prelattice_meet
; A_distributive_prelattice_ast         : cas_ast
}.

Record A_selective_distributive_prelattice (S : Type) := {
  A_selective_distributive_prelattice_eqv         : A_eqv S 
; A_selective_distributive_prelattice_join        : binary_op S 
; A_selective_distributive_prelattice_meet        : binary_op S 
; A_selective_distributive_prelattice_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_eqv) A_selective_distributive_prelattice_join
; A_selective_distributive_prelattice_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_prelattice_eqv) A_selective_distributive_prelattice_meet
; A_selective_distributive_prelattice_id_ann_proofs : id_ann_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_eqv)
                                          A_selective_distributive_prelattice_join
                                          A_selective_distributive_prelattice_meet                                                                  
; A_selective_distributive_prelattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_prelattice_eqv)
                                          A_selective_distributive_prelattice_join
                                          A_selective_distributive_prelattice_meet
; A_selective_distributive_prelattice_ast         : cas_ast
}.


Record A_lattice (S : Type) := {
  A_lattice_eqv           : A_eqv S 
; A_lattice_join          : binary_op S 
; A_lattice_meet          : binary_op S 
; A_lattice_join_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join
; A_lattice_meet_proofs   : sg_CI_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_meet
; A_lattice_id_ann_proofs : bounded_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet      
; A_lattice_proofs        : lattice_proofs S (A_eqv_eq S A_lattice_eqv) A_lattice_join A_lattice_meet
; A_lattice_ast           : cas_ast
}.

Record A_distributive_lattice (S : Type) := {
  A_distributive_lattice_eqv         : A_eqv S 
; A_distributive_lattice_join        : binary_op S 
; A_distributive_lattice_meet        : binary_op S 
; A_distributive_lattice_join_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_join
; A_distributive_lattice_meet_proofs : sg_CI_proofs S (A_eqv_eq S A_distributive_lattice_eqv) A_distributive_lattice_meet
; A_distributive_lattice_id_ann_proofs : bounded_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet                                                        
; A_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_distributive_lattice_eqv)
                                          A_distributive_lattice_join
                                          A_distributive_lattice_meet
; A_distributive_lattice_ast         : cas_ast
}.

Record A_selective_distributive_lattice (S : Type) := {
  A_selective_distributive_lattice_eqv         : A_eqv S 
; A_selective_distributive_lattice_join        : binary_op S 
; A_selective_distributive_lattice_meet        : binary_op S 
; A_selective_distributive_lattice_join_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_join
; A_selective_distributive_lattice_meet_proofs : sg_CS_proofs S (A_eqv_eq S A_selective_distributive_lattice_eqv) A_selective_distributive_lattice_meet
; A_selective_distributive_lattice_id_ann_proofs : bounded_proofs S
                                          (A_eqv_eq S A_selective_distributive_lattice_eqv)
                                          A_selective_distributive_lattice_join
                                          A_selective_distributive_lattice_meet                                                                  
; A_selective_distributive_lattice_proofs      : distributive_lattice_proofs S
                                          (A_eqv_eq S A_selective_distributive_lattice_eqv)
                                          A_selective_distributive_lattice_join
                                          A_selective_distributive_lattice_meet
; A_selective_distributive_lattice_ast         : cas_ast
}.



(* orders *) 

(* quasi order *) 
Record A_qo (S : Type) := {
  A_qo_eqv        : A_eqv S 
; A_qo_brel       : brel S 
; A_qo_proofs     : qo_proofs S (A_eqv_eq S A_qo_eqv) A_qo_brel 
; A_qo_ast        : cas_ast
}.

(* partial order *) 
Record A_po (S : Type) := {
  A_po_eqv             : A_eqv S 
; A_po_lte             : brel S
; A_po_exists_top_d    : brel_exists_top_decidable S A_po_lte           
; A_po_exists_bottom_d : brel_exists_bottom_decidable S A_po_lte
; A_po_proofs          : po_proofs S (A_eqv_eq S A_po_eqv) A_po_lte 
; A_po_ast             : cas_ast
}.


(* partial order with bottom *) 
Record A_po_with_bottom (S : Type) := {
  A_powb_eqv           : A_eqv S 
; A_powb_lte           : brel S
; A_powb_exists_top_d  : brel_exists_top_decidable S A_powb_lte           
; A_powb_exists_bottom : brel_exists_bottom S A_powb_lte
; A_powb_proofs        : po_proofs S (A_eqv_eq S A_powb_eqv) A_powb_lte 
; A_powb_ast           : cas_ast
}.



(* total order *) 
Record A_to (S : Type) := {
  A_to_eqv        : A_eqv S 
; A_to_brel       : brel S 
; A_to_proofs     : to_proofs S (A_eqv_eq S A_to_eqv) A_to_brel 
; A_to_ast        : cas_ast
}.



(* order-semigroups *) 

Record A_os (S : Type) := {
  A_os_eqv          : A_eqv S 
; A_os_lte          : brel S 
; A_os_times        : binary_op S 
; A_os_lte_proofs   : po_proofs S (A_eqv_eq S A_os_eqv) A_os_lte
; A_os_times_proofs : sg_proofs S (A_eqv_eq S A_os_eqv) A_os_times 
; A_os_proofs       : os_proofs S A_os_lte A_os_times 
; A_os_ast          : cas_ast
}.

(*   
    Tranforms 
*)


Record A_ltr (S L : Type) :=
{
  A_ltr_carrier : A_eqv S
; A_ltr_label   : A_eqv L                                                       
; A_ltr_trans   : left_transform L S (* T -> (S -> S) *) 
; A_ltr_proofs  : ltr_proofs S L (A_eqv_eq S A_ltr_carrier) (A_eqv_eq L A_ltr_label)  A_ltr_trans
; A_ltr_ast     : cas_ast
}.

Record A_sltr_CS (S L : Type) :=
{
  A_sltr_CS_carrier      : A_eqv S
; A_sltr_CS_label        : A_eqv L
; A_sltr_CS_plus         : binary_op S                                               
; A_sltr_CS_trans        : left_transform L S (* L -> (S -> S) *)
; A_sltr_CS_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_sltr_CS_carrier) A_sltr_CS_plus                                 
; A_sltr_CS_trans_proofs : ltr_proofs S L (A_eqv_eq S A_sltr_CS_carrier) (A_eqv_eq L A_sltr_CS_label)  A_sltr_CS_trans
; A_sltr_CS_proofs       : sltr_proofs S L (A_eqv_eq S A_sltr_CS_carrier) A_sltr_CS_plus A_sltr_CS_trans                                  
; A_sltr_CS_ast          : cas_ast
}.

Record A_sltr_CI (S L : Type) :=
{
  A_sltr_CI_carrier      : A_eqv S
; A_sltr_CI_label        : A_eqv L
; A_sltr_CI_plus         : binary_op S                                               
; A_sltr_CI_trans        : left_transform L S (* L -> (S -> S) *)
; A_sltr_CI_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_sltr_CI_carrier) A_sltr_CI_plus                                 
; A_sltr_CI_trans_proofs : ltr_proofs S L (A_eqv_eq S A_sltr_CI_carrier) (A_eqv_eq L A_sltr_CI_label)  A_sltr_CI_trans
; A_sltr_CI_proofs       : sltr_proofs S L (A_eqv_eq S A_sltr_CI_carrier) A_sltr_CI_plus A_sltr_CI_trans                                  
; A_sltr_CI_ast          : cas_ast 
}.



