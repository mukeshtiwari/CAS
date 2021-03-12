Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.new.ast. 

Record eqv {S : Type} := {
  eqv_eq    : brel S 
; eqv_witness : S         
; eqv_new     : S -> S
; eqv_data  : S -> data (* for printing in ocaml-land *) 
; eqv_rep   : S -> S    (* for reductions.  Should this be an option? *)
; eqv_ast   : ast_eqv
}.  

Record sg {S : Type} := {
  sg_eq  : @eqv S 
; sg_bop : binary_op S
; sg_id  : option S
; sg_ann : option S
; sg_ast : ast_sg
}.
