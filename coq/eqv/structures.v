Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties. 


Section ACAS.

Record eqv_proofs (S : Type) (eq : brel S) := 
{
(*
; A_eqv_rep_correct    : brel_rep_correct S eq rep
; A_eqv_rep_idempotent : brel_rep_idempotent S eq rep  
*) 
  A_eqv_congruence     : brel_congruence S eq eq  
; A_eqv_reflexive      : brel_reflexive S eq            
; A_eqv_transitive     : brel_transitive S eq           
; A_eqv_symmetric      : brel_symmetric S eq
}.

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

End ACAS.

Section CAS.

Record eqv_certificates {S : Type} := 
{
  eqv_congruence     : @assert_brel_congruence S 
; eqv_reflexive      : @assert_reflexive S 
; eqv_transitive     : @assert_transitive S 
; eqv_symmetric      : @assert_symmetric S
}.
  
  
(* eqv *) 
Record eqv {S : Type} := {
  eqv_eq            : brel S
; eqv_certs         : @eqv_certificates S                                                   
; eqv_witness       : S         
; eqv_new           : S -> S                                                                                                   
; eqv_exactly_two_d : @check_exactly_two S 
; eqv_data          : S -> data (* for printing in ocaml-land *) 
; eqv_rep           : S -> S    (* for reductions.  Should this be an option? *)
; eqv_finite_d      : @check_is_finite S 
; eqv_ast           : cas_ast
}.  

End CAS.

Section Translation.


  Definition A2C_eqv : ∀ (S : Type), A_eqv S -> @eqv S 
:= λ S E,
let eq := A_eqv_eq S E in   
{| 
  eqv_eq      := eq
; eqv_certs   :=
    {|
       eqv_congruence     := @Assert_Brel_Congruence S 
     ; eqv_reflexive      := @Assert_Reflexive S
     ; eqv_transitive     := @Assert_Transitive S
     ; eqv_symmetric      := @Assert_Symmetric S

    |}  
; eqv_witness := A_eqv_witness S E
; eqv_new     := A_eqv_new S E
; eqv_exactly_two_d := p2c_exactly_two_check S eq (A_eqv_exactly_two_d S E)                           
; eqv_data    := A_eqv_data S E
; eqv_rep     := A_eqv_rep S E
; eqv_finite_d := p2c_is_finite_check S eq (A_eqv_finite_d S E)
; eqv_ast     := A_eqv_ast S E
|}. 



End Translation.   