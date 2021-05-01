Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.

(* all order structures required to have a bottom. 


         or 
       /   \
      /     \ 
    po       to 
     \       /
      q0    /
        \  /
         wp

or = order (ref, trans) 
to = total order   (ref, trans, antisymm, total) 
po = partial order (ref, trans, antisymm, not total)   
qo = quasi order (ref, trans, not_antisymm, not total) 
wp = weak preference order (ref, trans, not_antisymm, total) 
*) 
Section ACAS.

Record or_proofs (S : Type) (eq lte : brel S) := {
  A_or_congruence      : brel_congruence S eq lte
; A_or_reflexive       : brel_reflexive S lte       
; A_or_transitive      : brel_transitive S lte
; A_or_antisymmetric_d : brel_antisymmetric_decidable S eq lte
; A_or_total_d         : brel_total_decidable S lte            
(*; A_or_bottoms_finite_d : bottoms_finite_decidable S eq lte*) 
                                                }.

Record A_or (S : Type) := {
  A_or_eqv             : A_eqv S 
; A_or_lte             : brel S
; A_or_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_or_eqv) A_or_lte           
; A_or_exists_bottom   : brel_exists_qo_bottom S (A_eqv_eq S A_or_eqv) A_or_lte
; A_or_proofs          : or_proofs S (A_eqv_eq S A_or_eqv) A_or_lte 
; A_or_ast             : cas_ast
}.


Record po_proofs (S : Type) (eq lte : brel S) := {
  A_po_congruence    : brel_congruence S eq lte 
; A_po_reflexive     : brel_reflexive S lte            
; A_po_transitive    : brel_transitive S lte           
; A_po_antisymmetric : brel_antisymmetric S eq lte
; A_po_not_total     : brel_not_total S lte           
(* po/from_sg_left 
   needs not_selective, so need a sg_structure with 
   this property.   sg_CI_not_selective ...  
; A_po_total_d         : brel_total_decidable S lte

; A_po_bottoms_finite_d : bottoms_finite_decidable S eq lte
*) 
}.


Record A_po (S : Type) := {
  A_po_eqv             : A_eqv S 
; A_po_lte             : brel S
; A_po_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_po_eqv) A_po_lte           
; A_po_exists_bottom   : brel_exists_qo_bottom S (A_eqv_eq S A_po_eqv) A_po_lte
; A_po_proofs          : po_proofs S (A_eqv_eq S A_po_eqv) A_po_lte 
; A_po_ast             : cas_ast
}.


Record to_proofs (S : Type) (eq lte : brel S) := {
  A_to_congruence    : brel_congruence S eq lte 
; A_to_reflexive     : brel_reflexive S lte            
; A_to_transitive    : brel_transitive S lte           
; A_to_antisymmetric : brel_antisymmetric S eq lte 
; A_to_total         : brel_total S lte           
}.

Record A_to (S : Type) := {
  A_to_eqv             : A_eqv S 
; A_to_lte             : brel S
; A_to_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_to_eqv) A_to_lte           
; A_to_exists_bottom   : brel_exists_qo_bottom S (A_eqv_eq S A_to_eqv) A_to_lte
; A_to_proofs          : to_proofs S (A_eqv_eq S A_to_eqv) A_to_lte 
; A_to_ast             : cas_ast
}.


Record qo_proofs (S : Type) (eq lte : brel S) := {
  A_qo_congruence      : brel_congruence S eq lte
; A_qo_reflexive       : brel_reflexive S lte            
; A_qo_transitive      : brel_transitive S lte           
; A_qo_not_antisymmetric : brel_not_antisymmetric S eq lte
; A_qo_not_total        : brel_not_total S lte           
}.


Record A_qo (S : Type) := {
  A_qo_eqv             : A_eqv S 
; A_qo_lte             : brel S
; A_qo_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_qo_eqv) A_qo_lte           
; A_qo_exists_bottom   : brel_exists_qo_bottom S (A_eqv_eq S A_qo_eqv) A_qo_lte
; A_qo_proofs          : qo_proofs S (A_eqv_eq S A_qo_eqv) A_qo_lte 
; A_qo_ast             : cas_ast
}.


Record wp_proofs (S : Type) (eq lte : brel S) := {
  A_wp_congruence      : brel_congruence S eq lte
; A_wp_reflexive       : brel_reflexive S lte            
; A_wp_transitive      : brel_transitive S lte           
; A_wp_not_antisymmetric : brel_not_antisymmetric S eq lte
; A_wp_total             : brel_total S lte           
}.

Record A_wp (S : Type) := {
  A_wp_eqv             : A_eqv S 
; A_wp_lte             : brel S
; A_wp_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_wp_eqv) A_wp_lte           
; A_wp_exists_bottom   : brel_exists_qo_bottom S (A_eqv_eq S A_wp_eqv) A_wp_lte
; A_wp_proofs          : wp_proofs S (A_eqv_eq S A_wp_eqv) A_wp_lte 
; A_wp_ast             : cas_ast
}.


End ACAS. 

Section CAS.

Record or_certificates {S : Type} := {
  or_congruence       : @assert_brel_congruence S 
; or_reflexive        : @assert_reflexive S 
; or_transitive       : @assert_transitive S
; or_antisymmetric_d  : @check_antisymmetric S 
; or_total_d          : @check_total S
(*; or_bottoms_finite_d : @check_bottoms_finite S *) 
                                    }.
Record or {S : Type} := {
  or_eqv             : @eqv S
; or_lte             : @brel S
; or_exists_top_d    : @check_exists_qo_top S 
; or_exists_bottom   : @assert_exists_qo_bottom S 
; or_certs           : @or_certificates S
; or_ast             : cas_ast
}.
  

Record po_certificates {S : Type} := {
  po_congruence       : @assert_brel_congruence S 
; po_reflexive        : @assert_reflexive S 
; po_transitive       : @assert_transitive S
; po_antisymmetric    : @assert_antisymmetric S
(*; po_total_d          : @check_total S  *)
; po_not_total        : @assert_not_total S
(*; po_bottoms_finite_d : @check_bottoms_finite S *) 
}.

Record po {S : Type} := {
  po_eqv             : @eqv S
; po_lte             : @brel S
; po_exists_top_d    : @check_exists_qo_top S 
; po_exists_bottom   : @assert_exists_qo_bottom S 
; po_certs           : @po_certificates S
; po_ast             : cas_ast
}.


Record to_certificates {S : Type} := {
  to_congruence    : @assert_brel_congruence S 
; to_reflexive     : @assert_reflexive S 
; to_transitive    : @assert_transitive S
; to_antisymmetric : @assert_antisymmetric S 
; to_total         : @assert_total S 
}.

Record to {S : Type} := {
  to_eqv             : @eqv S
; to_lte             : @brel S
; to_exists_top_d    : @check_exists_qo_top S 
; to_exists_bottom   : @assert_exists_qo_bottom S 
; to_certs           : @to_certificates S
; to_ast             : cas_ast
}.

Record qo_certificates {S : Type}  := {
  qo_congruence        : @assert_brel_congruence S 
; qo_reflexive         : @assert_reflexive S 
; qo_transitive        : @assert_transitive S
; qo_not_antisymmetric : @assert_not_antisymmetric S 
; qo_not_total         : @assert_not_total S 
}.
  
Record qo {S : Type} := {
  qo_eqv             : @eqv S 
; qo_lte             : @brel S
; qo_exists_top_d    : @check_exists_qo_top S 
; qo_exists_bottom   : @assert_exists_qo_bottom S                        
; qo_certs           : @qo_certificates S
; qo_ast             : cas_ast
}.
 

Record wp_certificates {S : Type}  := {
  wp_congruence        : @assert_brel_congruence S 
; wp_reflexive         : @assert_reflexive S 
; wp_transitive        : @assert_transitive S
; wp_not_antisymmetric : @assert_not_antisymmetric S 
; wp_total             : @assert_total S 
}.
  
Record wp {S : Type} := {
  wp_eqv             : @eqv S 
; wp_lte             : @brel S
; wp_exists_top_d    : @check_exists_qo_top S 
; wp_exists_bottom   : @assert_exists_qo_bottom S                        
; wp_certs           : @wp_certificates S
; wp_ast             : cas_ast
}.
 
End CAS.


Section Translation.


Definition P2C_or : ∀ (S : Type) (eq lte : brel S), or_proofs S eq lte -> @or_certificates S 
:= λ S eq lte P,
{|
  or_congruence       := @Assert_Brel_Congruence S 
; or_reflexive        := @Assert_Reflexive S 
; or_transitive       := @Assert_Transitive S
; or_antisymmetric_d  := p2c_antisymmetric_check S eq lte (A_or_antisymmetric_d S eq lte P)
; or_total_d          := p2c_total_check S lte (A_or_total_d S eq lte P)
(*; or_bottoms_finite_d := p2c_bottoms_finite_check S eq lte (A_or_bottoms_finite_d S eq lte P) *) 
|}. 


Definition A2C_or : ∀ (S : Type), A_or S -> @or S 
  := λ S R,
let eq  := A_eqv_eq S (A_or_eqv S R) in
let lte := A_or_lte S R in   
{| 
  or_eqv              := A2C_eqv S (A_or_eqv S R) 
; or_lte              := A_or_lte S R
; or_exists_top_d     := p2c_exists_qo_top_check S eq lte (A_or_exists_top_d S R)
; or_exists_bottom    := p2c_exists_qo_bottom_assert S eq lte (A_or_exists_bottom S R)                          
; or_certs            := P2C_or S eq lte (A_or_proofs S R)
; or_ast              := A_or_ast S R                       
|}. 

  

Definition P2C_po : ∀ (S : Type) (eq lte : brel S), po_proofs S eq lte -> @po_certificates S 
:= λ S eq lte P,
{|
  po_congruence       := @Assert_Brel_Congruence S 
; po_reflexive        := @Assert_Reflexive S 
; po_transitive       := @Assert_Transitive S
; po_antisymmetric    := @Assert_Antisymmetric S
(*; po_total_d          := p2c_total_check S lte (A_po_total_d S eq lte P) *)                                              
; po_not_total        := p2c_not_total_assert S lte (A_po_not_total S eq lte P) 
(*; po_bottoms_finite_d := p2c_bottoms_finite_check S eq lte (A_po_bottoms_finite_d S eq lte P) *) 
|}. 


Definition A2C_po : ∀ (S : Type), A_po S -> @po S 
:= λ S R,
let eq  := A_eqv_eq S (A_po_eqv S R) in 
let lte := A_po_lte S R in 
{| 
  po_eqv     := A2C_eqv S (A_po_eqv S R) 
; po_lte    := A_po_lte S R
; po_exists_top_d     := p2c_exists_qo_top_check S eq lte (A_po_exists_top_d S R)
; po_exists_bottom     := p2c_exists_qo_bottom_assert S eq lte  (A_po_exists_bottom S R)                          
; po_certs   := P2C_po S eq lte (A_po_proofs S R)
; po_ast   := A_po_ast S R                       
|}. 

Definition P2C_to : ∀ (S : Type) (eq lte : brel S), to_proofs S eq lte -> @to_certificates S 
:= λ S eq lte P,
{|
  to_congruence    := @Assert_Brel_Congruence S 
; to_reflexive     := @Assert_Reflexive S 
; to_transitive    := @Assert_Transitive S
; to_antisymmetric := @Assert_Antisymmetric S 
; to_total         := @Assert_Total S 
|}. 

Definition A2C_to : ∀ (S : Type), A_to S -> @to S 
:= λ S R,
let eq  := A_eqv_eq S (A_to_eqv S R) in 
let lte := A_to_lte S R in 
{| 
  to_eqv           := A2C_eqv S (A_to_eqv S R) 
; to_lte           := A_to_lte S R
; to_exists_top_d  := p2c_exists_qo_top_check S eq lte (A_to_exists_top_d S R)
; to_exists_bottom := p2c_exists_qo_bottom_assert S eq lte (A_to_exists_bottom S R)                          
; to_certs         := P2C_to S eq lte (A_to_proofs S R)  
; to_ast           := A_to_ast S R
|}. 




Definition P2C_qo : ∀ (S : Type) (eq lte : brel S), qo_proofs S eq lte -> @qo_certificates S 
:= λ S eq lte P,
{|
  qo_congruence       := @Assert_Brel_Congruence S 
; qo_reflexive        := @Assert_Reflexive S 
; qo_transitive       := @Assert_Transitive S
; qo_not_antisymmetric := p2c_not_antisymmetric_assert S eq lte (A_qo_not_antisymmetric S eq lte P)
; qo_not_total        := p2c_not_total_assert S lte (A_qo_not_total S eq lte P)
|}. 

Definition A2C_qo : ∀ (S : Type), A_qo S -> @qo S 
:= λ S R,
{| 
  qo_eqv              := A2C_eqv S (A_qo_eqv S R) 
; qo_lte              := A_qo_lte S R
; qo_exists_top_d     := p2c_exists_qo_top_check S (A_eqv_eq S (A_qo_eqv S R)) (A_qo_lte S R) (A_qo_exists_top_d S R)
; qo_exists_bottom    := p2c_exists_qo_bottom_assert S (A_eqv_eq S (A_qo_eqv S R)) (A_qo_lte S R) (A_qo_exists_bottom S R)                          
; qo_certs            := P2C_qo S (A_eqv_eq S (A_qo_eqv S R)) (A_qo_lte S R) (A_qo_proofs S R)
; qo_ast              := A_qo_ast S R                       
|}. 




Definition P2C_wp : ∀ (S : Type) (eq lte : brel S), wp_proofs S eq lte -> @wp_certificates S 
:= λ S eq lte P,
{|
  wp_congruence       := @Assert_Brel_Congruence S 
; wp_reflexive        := @Assert_Reflexive S 
; wp_transitive       := @Assert_Transitive S
; wp_not_antisymmetric := p2c_not_antisymmetric_assert S eq lte (A_wp_not_antisymmetric S eq lte P)
; wp_total             := p2c_total_assert S lte (A_wp_total S eq lte P)
|}. 

Definition A2C_wp : ∀ (S : Type), A_wp S -> @wp S 
:= λ S R,
{| 
  wp_eqv              := A2C_eqv S (A_wp_eqv S R) 
; wp_lte              := A_wp_lte S R
; wp_exists_top_d     := p2c_exists_qo_top_check S (A_eqv_eq S (A_wp_eqv S R)) (A_wp_lte S R) (A_wp_exists_top_d S R)
; wp_exists_bottom    := p2c_exists_qo_bottom_assert S (A_eqv_eq S (A_wp_eqv S R)) (A_wp_lte S R) (A_wp_exists_bottom S R)                          
; wp_certs            := P2C_wp S (A_eqv_eq S (A_wp_eqv S R)) (A_wp_lte S R) (A_wp_proofs S R)
; wp_ast              := A_wp_ast S R                       
|}. 





End Translation.  