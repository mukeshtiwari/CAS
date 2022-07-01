Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory. 

(* order structures 

                or
              /   \
             /     \
    antisymm/       \not antisymm
           /         \ 
          /           \
          |            \ 
          |             \ 
          |              \
    total/ \not    total / \not             
        |   |           |   | 
       to  po           wo  qo 


or = order (ref, trans) 
to = total order   (ref, trans, antisymm, total) 
po = partial order (ref, trans, antisymm, not total)   
qo = quasi order (ref, trans, not_antisymm, not total) 
wo = weak preference order (ref, trans, not_antisymm, total) 

*) 
Section ACAS.

Record or_proofs (S : Type) (eq lte : brel S) := {
  A_or_congruence      : brel_congruence S eq lte
; A_or_reflexive       : brel_reflexive S lte       
; A_or_transitive      : brel_transitive S lte
; A_or_antisymmetric_d : brel_antisymmetric_decidable S eq lte
; A_or_total_d         : brel_total_decidable S lte
; A_or_trivial_d       : order_trivial_decidable S lte                                                          
}.

Record po_proofs (S : Type) (eq lte : brel S) := {
  A_po_congruence    : brel_congruence S eq lte 
; A_po_reflexive     : brel_reflexive S lte            
; A_po_transitive    : brel_transitive S lte           
; A_po_antisymmetric : brel_antisymmetric S eq lte
; A_po_not_total     : brel_not_total S lte           
}.

Record to_proofs (S : Type) (eq lte : brel S) := {
  A_to_congruence    : brel_congruence S eq lte 
; A_to_reflexive     : brel_reflexive S lte            
; A_to_transitive    : brel_transitive S lte           
; A_to_antisymmetric : brel_antisymmetric S eq lte 
; A_to_total         : brel_total S lte           
}.

Record qo_proofs (S : Type) (eq lte : brel S) := {
  A_qo_congruence      : brel_congruence S eq lte
; A_qo_reflexive       : brel_reflexive S lte            
; A_qo_transitive      : brel_transitive S lte           
; A_qo_not_antisymmetric : brel_not_antisymmetric S eq lte
; A_qo_not_total        : brel_not_total S lte
}.

Record wo_proofs (S : Type) (eq lte : brel S) := {
  A_wo_congruence      : brel_congruence S eq lte
; A_wo_reflexive       : brel_reflexive S lte            
; A_wo_transitive      : brel_transitive S lte           
; A_wo_not_antisymmetric : brel_not_antisymmetric S eq lte
; A_wo_total             : brel_total S lte
; A_wo_trivial_d         : order_trivial_decidable S lte                                                                                                   
}.


Record A_or (S : Type) := {
  A_or_eqv             : A_eqv S 
; A_or_lte             : brel S
; A_or_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_or_eqv) A_or_lte           
; A_or_exists_bottom_d : brel_exists_qo_bottom_decidable S (A_eqv_eq S A_or_eqv) A_or_lte
; A_or_proofs          : or_proofs S (A_eqv_eq S A_or_eqv) A_or_lte 
; A_or_ast             : cas_or_ast
}.

Record A_po (S : Type) := {
  A_po_eqv               : A_eqv S 
; A_po_lte               : brel S
; A_po_not_exists_top    : brel_not_exists_top S A_po_lte           
; A_po_not_exists_bottom : brel_not_exists_bottom S A_po_lte
; A_po_proofs            : po_proofs S (A_eqv_eq S A_po_eqv) A_po_lte 
; A_po_ast               : cas_or_ast
}.

Record A_po_with_bottom (S : Type) := {
  A_po_wb_eqv             : A_eqv S 
; A_po_wb_lte             : brel S
; A_po_wb_not_exists_top  : brel_not_exists_top S A_po_wb_lte           
; A_po_wb_exists_bottom   : brel_exists_bottom S A_po_wb_lte
; A_po_wb_proofs          : po_proofs S (A_eqv_eq S A_po_wb_eqv) A_po_wb_lte 
; A_po_wb_ast             : cas_or_ast
}.

Record A_po_with_top (S : Type) := {
  A_po_wt_eqv               : A_eqv S 
; A_po_wt_lte               : brel S
; A_po_wt_exists_top        : brel_exists_top S A_po_wt_lte           
; A_po_wt_not_exists_bottom : brel_not_exists_bottom S A_po_wt_lte
; A_po_wt_proofs            : po_proofs S (A_eqv_eq S A_po_wt_eqv) A_po_wt_lte 
; A_po_wt_ast               : cas_or_ast
}.

Record A_po_bounded (S : Type) := {
  A_po_bd_eqv               : A_eqv S 
; A_po_bd_lte               : brel S
; A_po_bd_exists_top        : brel_exists_top S A_po_bd_lte           
; A_po_bd_exists_bottom     : brel_exists_bottom S A_po_bd_lte
; A_po_bd_proofs            : po_proofs S (A_eqv_eq S A_po_bd_eqv) A_po_bd_lte 
; A_po_bd_ast               : cas_or_ast
}.


Record A_to (S : Type) := {
  A_to_eqv               : A_eqv S 
; A_to_lte               : brel S
; A_to_not_exists_top    : brel_not_exists_top S A_to_lte           
; A_to_not_exists_bottom : brel_not_exists_bottom S A_to_lte
; A_to_proofs            : to_proofs S (A_eqv_eq S A_to_eqv) A_to_lte 
; A_to_ast               : cas_or_ast
}.


Record A_to_with_bottom (S : Type) := {
  A_to_wb_eqv               : A_eqv S 
; A_to_wb_lte               : brel S
; A_to_wb_not_exists_top    : brel_not_exists_top S A_to_wb_lte           
; A_to_wb_exists_bottom     : brel_exists_bottom S A_to_wb_lte
; A_to_wb_proofs            : to_proofs S (A_eqv_eq S A_to_wb_eqv) A_to_wb_lte 
; A_to_wb_ast               : cas_or_ast
}.

Record A_to_with_top (S : Type) := {
  A_to_wt_eqv               : A_eqv S 
; A_to_wt_lte               : brel S
; A_to_wt_exists_top        : brel_exists_top S A_to_wt_lte           
; A_to_wt_not_exists_bottom : brel_not_exists_bottom S A_to_wt_lte
; A_to_wt_proofs            : to_proofs S (A_eqv_eq S A_to_wt_eqv) A_to_wt_lte 
; A_to_wt_ast               : cas_or_ast
}.

Record A_to_bounded (S : Type) := {
  A_to_bd_eqv               : A_eqv S 
; A_to_bd_lte               : brel S
; A_to_bd_exists_top        : brel_exists_top S A_to_bd_lte           
; A_to_bd_exists_bottom     : brel_exists_bottom S A_to_bd_lte
; A_to_bd_proofs            : to_proofs S (A_eqv_eq S A_to_bd_eqv) A_to_bd_lte 
; A_to_bd_ast               : cas_or_ast
}.


Record A_qo (S : Type) := {
  A_qo_eqv               : A_eqv S 
; A_qo_lte               : brel S
; A_qo_not_exists_top    : brel_not_exists_qo_top S (A_eqv_eq S A_qo_eqv) A_qo_lte           
; A_qo_not_exists_bottom : brel_not_exists_qo_bottom S (A_eqv_eq S A_qo_eqv) A_qo_lte
; A_qo_proofs            : qo_proofs S (A_eqv_eq S A_qo_eqv) A_qo_lte 
; A_qo_ast               : cas_or_ast
}.

Record A_qo_with_bottom (S : Type) := {
  A_qo_wb_eqv               : A_eqv S 
; A_qo_wb_lte               : brel S
; A_qo_wb_not_exists_top    : brel_not_exists_qo_top S (A_eqv_eq S A_qo_wb_eqv) A_qo_wb_lte           
; A_qo_wb_exists_bottom     : brel_exists_qo_bottom S (A_eqv_eq S A_qo_wb_eqv) A_qo_wb_lte
; A_qo_wb_proofs            : qo_proofs S (A_eqv_eq S A_qo_wb_eqv) A_qo_wb_lte 
; A_qo_wb_ast               : cas_or_ast
}.


Record A_qo_with_top (S : Type) := {
  A_qo_wt_eqv               : A_eqv S 
; A_qo_wt_lte               : brel S
; A_qo_wt_exists_top        : brel_exists_qo_top S (A_eqv_eq S A_qo_wt_eqv) A_qo_wt_lte           
; A_qo_wt_not_exists_bottom : brel_not_exists_qo_bottom S (A_eqv_eq S A_qo_wt_eqv) A_qo_wt_lte
; A_qo_wt_proofs            : qo_proofs S (A_eqv_eq S A_qo_wt_eqv) A_qo_wt_lte 
; A_qo_wt_ast               : cas_or_ast
}.


Record A_qo_bounded (S : Type) := {
  A_qo_bd_eqv               : A_eqv S 
; A_qo_bd_lte               : brel S
; A_qo_bd_exists_top        : brel_exists_qo_top S (A_eqv_eq S A_qo_bd_eqv) A_qo_bd_lte           
; A_qo_bd_exists_bottom     : brel_exists_qo_bottom S (A_eqv_eq S A_qo_bd_eqv) A_qo_bd_lte
; A_qo_bd_proofs            : qo_proofs S (A_eqv_eq S A_qo_bd_eqv) A_qo_bd_lte 
; A_qo_bd_ast               : cas_or_ast
}.

Record A_wo (S : Type) := {
  A_wo_eqv               : A_eqv S 
; A_wo_lte               : brel S
; A_wo_not_exists_top    : brel_not_exists_qo_top S (A_eqv_eq S A_wo_eqv) A_wo_lte           
; A_wo_not_exists_bottom : brel_not_exists_qo_bottom S (A_eqv_eq S A_wo_eqv) A_wo_lte
; A_wo_proofs            : wo_proofs S (A_eqv_eq S A_wo_eqv) A_wo_lte 
; A_wo_ast               : cas_or_ast
}.

Record A_wo_with_bottom (S : Type) := {
  A_wo_wb_eqv               : A_eqv S 
; A_wo_wb_lte               : brel S
; A_wo_wb_not_exists_top    : brel_not_exists_qo_top S (A_eqv_eq S A_wo_wb_eqv) A_wo_wb_lte           
; A_wo_wb_exists_bottom     : brel_exists_qo_bottom S (A_eqv_eq S A_wo_wb_eqv) A_wo_wb_lte
; A_wo_wb_proofs            : wo_proofs S (A_eqv_eq S A_wo_wb_eqv) A_wo_wb_lte 
; A_wo_wb_ast               : cas_or_ast
}.


Record A_wo_with_top (S : Type) := {
  A_wo_wt_eqv               : A_eqv S 
; A_wo_wt_lte               : brel S
; A_wo_wt_exists_top        : brel_exists_qo_top S (A_eqv_eq S A_wo_wt_eqv) A_wo_wt_lte           
; A_wo_wt_not_exists_bottom : brel_not_exists_qo_bottom S (A_eqv_eq S A_wo_wt_eqv) A_wo_wt_lte
; A_wo_wt_proofs            : wo_proofs S (A_eqv_eq S A_wo_wt_eqv) A_wo_wt_lte 
; A_wo_wt_ast               : cas_or_ast
}.

Record A_wo_bounded (S : Type) := {
  A_wo_bd_eqv               : A_eqv S 
; A_wo_bd_lte               : brel S
; A_wo_bd_exists_top        : brel_exists_qo_top S (A_eqv_eq S A_wo_bd_eqv) A_wo_bd_lte           
; A_wo_bd_exists_bottom     : brel_exists_qo_bottom S (A_eqv_eq S A_wo_bd_eqv) A_wo_bd_lte
; A_wo_bd_proofs            : wo_proofs S (A_eqv_eq S A_wo_bd_eqv) A_wo_bd_lte 
; A_wo_bd_ast               : cas_or_ast
}.


Inductive A_or_mcas {S : Type} := 
| A_OR_Error          : list string        -> @A_or_mcas S
| A_OR_or             : A_or S             -> @A_or_mcas S
| A_OR_po             : A_po S             -> @A_or_mcas S
| A_OR_po_with_bottom : A_po_with_bottom S -> @A_or_mcas S
| A_OR_po_with_top    : A_po_with_top S    -> @A_or_mcas S
| A_OR_po_bounded     : A_po_bounded S     -> @A_or_mcas S
| A_OR_to             : A_to S             -> @A_or_mcas S                                                        
| A_OR_to_with_bottom : A_to_with_bottom S -> @A_or_mcas S
| A_OR_to_with_top    : A_to_with_top S    -> @A_or_mcas S
| A_OR_to_bounded     : A_to_bounded S     -> @A_or_mcas S
| A_OR_qo             : A_qo S             -> @A_or_mcas S                                                        
| A_OR_qo_with_bottom : A_qo_with_bottom S -> @A_or_mcas S
| A_OR_qo_with_top    : A_qo_with_top S    -> @A_or_mcas S
| A_OR_qo_bounded     : A_qo_bounded S     -> @A_or_mcas S
| A_OR_wo             : A_wo S             -> @A_or_mcas S                                                        
| A_OR_wo_with_bottom : A_wo_with_bottom S -> @A_or_mcas S
| A_OR_wo_with_top    : A_wo_with_top S    -> @A_or_mcas S
| A_OR_wo_bounded     : A_wo_bounded S     -> @A_or_mcas S                                                            
.

Definition A_or_classify_or {S : Type} (A : A_or S) : @A_or_mcas S :=
let P := A_or_proofs _ A in
match A_or_antisymmetric_d _ _ _ P, A_or_total_d _ _ _ P with
| inl anti, inl tot =>
  let to_P :=
      {|
          A_to_congruence     := A_or_congruence _ _ _ P
        ; A_to_reflexive      := A_or_reflexive _ _ _ P
        ; A_to_transitive     := A_or_transitive _ _ _ P
        ; A_to_antisymmetric  := anti 
        ; A_to_total          := tot 
      |} in 
  match A_or_exists_top_d _ A, A_or_exists_bottom_d _ A with
  | inl topP, inl botP =>
    A_OR_to_bounded
      {|
          A_to_bd_eqv               := A_or_eqv _ A 
        ; A_to_bd_lte               := A_or_lte _ A
        ; A_to_bd_exists_top        := brel_exists_top_from_brel_exists_qo_top _ _ _ topP 
        ; A_to_bd_exists_bottom     := brel_exists_bottom_from_brel_exists_qo_bottom _ _ _ botP 
        ; A_to_bd_proofs            := to_P
        ; A_to_bd_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inl botP =>
    A_OR_to_with_bottom
      {|
          A_to_wb_eqv               := A_or_eqv _ A 
        ; A_to_wb_lte               := A_or_lte _ A
        ; A_to_wb_not_exists_top    := brel_not_exists_top_from_brel_not_exists_qo_top _ _ _ anti ntopP 
        ; A_to_wb_exists_bottom     := brel_exists_bottom_from_brel_exists_qo_bottom _ _ _ botP 
        ; A_to_wb_proofs            := to_P 
        ; A_to_wb_ast               := A_or_ast _ A 
      |}
  | inl topP, inr nbotP =>
    A_OR_to_with_top
      {|
          A_to_wt_eqv               := A_or_eqv _ A 
        ; A_to_wt_lte               := A_or_lte _ A
        ; A_to_wt_exists_top        := brel_exists_top_from_brel_exists_qo_top _ _ _ topP 
        ; A_to_wt_not_exists_bottom := brel_not_exists_bottom_from_brel_not_exists_qo_bottom _ _ _ anti nbotP 
        ; A_to_wt_proofs            := to_P 
        ; A_to_wt_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inr nbotP =>
    A_OR_to
      {|
          A_to_eqv               := A_or_eqv _ A 
        ; A_to_lte               := A_or_lte _ A
        ; A_to_not_exists_top    := brel_not_exists_top_from_brel_not_exists_qo_top _ _ _ anti ntopP 
        ; A_to_not_exists_bottom := brel_not_exists_bottom_from_brel_not_exists_qo_bottom _ _ _ anti nbotP 
        ; A_to_proofs            := to_P 
        ; A_to_ast               := A_or_ast _ A 
      |}
  end
| inl anti, inr ntot =>
  let po_P :=
      {|
          A_po_congruence     := A_or_congruence _ _ _ P
        ; A_po_reflexive      := A_or_reflexive _ _ _ P
        ; A_po_transitive     := A_or_transitive _ _ _ P
        ; A_po_antisymmetric  := anti 
        ; A_po_not_total      := ntot 
      |} in 
  match A_or_exists_top_d _ A, A_or_exists_bottom_d _ A with
  | inl topP, inl botP =>
    A_OR_po_bounded
      {|
          A_po_bd_eqv               := A_or_eqv _ A 
        ; A_po_bd_lte               := A_or_lte _ A
        ; A_po_bd_exists_top        := brel_exists_top_from_brel_exists_qo_top _ _ _ topP 
        ; A_po_bd_exists_bottom     := brel_exists_bottom_from_brel_exists_qo_bottom _ _ _ botP 
        ; A_po_bd_proofs            := po_P
        ; A_po_bd_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inl botP =>
    A_OR_po_with_bottom
      {|
          A_po_wb_eqv               := A_or_eqv _ A 
        ; A_po_wb_lte               := A_or_lte _ A
        ; A_po_wb_not_exists_top    := brel_not_exists_top_from_brel_not_exists_qo_top _ _ _ anti ntopP 
        ; A_po_wb_exists_bottom     := brel_exists_bottom_from_brel_exists_qo_bottom _ _ _ botP 
        ; A_po_wb_proofs            := po_P 
        ; A_po_wb_ast               := A_or_ast _ A 
      |}
  | inl topP, inr nbotP =>
    A_OR_po_with_top
      {|
          A_po_wt_eqv               := A_or_eqv _ A 
        ; A_po_wt_lte               := A_or_lte _ A
        ; A_po_wt_exists_top        := brel_exists_top_from_brel_exists_qo_top _ _ _ topP 
        ; A_po_wt_not_exists_bottom := brel_not_exists_bottom_from_brel_not_exists_qo_bottom _ _ _ anti nbotP 
        ; A_po_wt_proofs            := po_P 
        ; A_po_wt_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inr nbotP =>
    A_OR_po
      {|
          A_po_eqv               := A_or_eqv _ A 
        ; A_po_lte               := A_or_lte _ A
        ; A_po_not_exists_top    := brel_not_exists_top_from_brel_not_exists_qo_top _ _ _ anti ntopP 
        ; A_po_not_exists_bottom := brel_not_exists_bottom_from_brel_not_exists_qo_bottom _ _ _ anti nbotP 
        ; A_po_proofs            := po_P 
        ; A_po_ast               := A_or_ast _ A 
      |}
  end 
| inr nanti, inl tot =>
  let wo_P :=
      {|
          A_wo_congruence     := A_or_congruence _ _ _ P
        ; A_wo_reflexive      := A_or_reflexive _ _ _ P
        ; A_wo_transitive     := A_or_transitive _ _ _ P
        ; A_wo_not_antisymmetric := nanti 
        ; A_wo_total          := tot
        ; A_wo_trivial_d      := A_or_trivial_d _ _ _ P                                    
      |} in 
  match A_or_exists_top_d _ A, A_or_exists_bottom_d _ A with
  | inl topP, inl botP =>
    A_OR_wo_bounded
      {|
          A_wo_bd_eqv               := A_or_eqv _ A 
        ; A_wo_bd_lte               := A_or_lte _ A
        ; A_wo_bd_exists_top        := topP 
        ; A_wo_bd_exists_bottom     := botP 
        ; A_wo_bd_proofs            := wo_P
        ; A_wo_bd_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inl botP =>
    A_OR_wo_with_bottom
      {|
          A_wo_wb_eqv               := A_or_eqv _ A 
        ; A_wo_wb_lte               := A_or_lte _ A
        ; A_wo_wb_not_exists_top    := ntopP 
        ; A_wo_wb_exists_bottom     := botP 
        ; A_wo_wb_proofs            := wo_P 
        ; A_wo_wb_ast               := A_or_ast _ A 
      |}
  | inl topP, inr nbotP =>
    A_OR_wo_with_top
      {|
          A_wo_wt_eqv               := A_or_eqv _ A 
        ; A_wo_wt_lte               := A_or_lte _ A
        ; A_wo_wt_exists_top        := topP 
        ; A_wo_wt_not_exists_bottom := nbotP 
        ; A_wo_wt_proofs            := wo_P 
        ; A_wo_wt_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inr nbotP =>
    A_OR_wo
      {|
          A_wo_eqv               := A_or_eqv _ A 
        ; A_wo_lte               := A_or_lte _ A
        ; A_wo_not_exists_top    := ntopP 
        ; A_wo_not_exists_bottom := nbotP 
        ; A_wo_proofs            := wo_P 
        ; A_wo_ast               := A_or_ast _ A 
      |}
  end
| inr nanti, inr ntot =>
  let qo_P :=
      {|
          A_qo_congruence     := A_or_congruence _ _ _ P
        ; A_qo_reflexive      := A_or_reflexive _ _ _ P
        ; A_qo_transitive     := A_or_transitive _ _ _ P
        ; A_qo_not_antisymmetric  := nanti 
        ; A_qo_not_total      := ntot 
      |} in 
  match A_or_exists_top_d _ A, A_or_exists_bottom_d _ A with
  | inl topP, inl botP =>
    A_OR_qo_bounded
      {|
          A_qo_bd_eqv               := A_or_eqv _ A 
        ; A_qo_bd_lte               := A_or_lte _ A
        ; A_qo_bd_exists_top        := topP 
        ; A_qo_bd_exists_bottom     := botP 
        ; A_qo_bd_proofs            := qo_P
        ; A_qo_bd_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inl botP =>
    A_OR_qo_with_bottom
      {|
          A_qo_wb_eqv               := A_or_eqv _ A 
        ; A_qo_wb_lte               := A_or_lte _ A
        ; A_qo_wb_not_exists_top    := ntopP 
        ; A_qo_wb_exists_bottom     := botP 
        ; A_qo_wb_proofs            := qo_P 
        ; A_qo_wb_ast               := A_or_ast _ A 
      |}
  | inl topP, inr nbotP =>
    A_OR_qo_with_top
      {|
          A_qo_wt_eqv               := A_or_eqv _ A 
        ; A_qo_wt_lte               := A_or_lte _ A
        ; A_qo_wt_exists_top        := topP 
        ; A_qo_wt_not_exists_bottom := nbotP 
        ; A_qo_wt_proofs            := qo_P 
        ; A_qo_wt_ast               := A_or_ast _ A 
      |}
  | inr ntopP, inr nbotP =>
    A_OR_qo
      {|
          A_qo_eqv               := A_or_eqv _ A 
        ; A_qo_lte               := A_or_lte _ A
        ; A_qo_not_exists_top    := ntopP 
        ; A_qo_not_exists_bottom := nbotP 
        ; A_qo_proofs            := qo_P 
        ; A_qo_ast               := A_or_ast _ A 
      |}
  end 
end.

Definition A_or_classify {S : Type} (A : @A_or_mcas S) : @A_or_mcas S :=
match A with
| A_OR_or B => A_or_classify_or B 
| _ => A                                                       
end.

End ACAS. 

Section CAS.

Record or_certificates {S : Type} := {
  or_congruence       : @assert_brel_congruence S 
; or_reflexive        : @assert_reflexive S 
; or_transitive       : @assert_transitive S
; or_antisymmetric_d  : @certify_antisymmetric S 
; or_total_d          : @certify_total S
; or_trivial_d        : @order_trivial_certifiable S                                       
}.

Record po_certificates {S : Type} := {
  po_congruence       : @assert_brel_congruence S 
; po_reflexive        : @assert_reflexive S 
; po_transitive       : @assert_transitive S
; po_antisymmetric    : @assert_antisymmetric S
; po_not_total        : @assert_not_total S
}.

Record to_certificates {S : Type} := {
  to_congruence    : @assert_brel_congruence S 
; to_reflexive     : @assert_reflexive S 
; to_transitive    : @assert_transitive S
; to_antisymmetric : @assert_antisymmetric S 
; to_total         : @assert_total S 
}.

Record qo_certificates {S : Type}  := {
  qo_congruence        : @assert_brel_congruence S 
; qo_reflexive         : @assert_reflexive S 
; qo_transitive        : @assert_transitive S
; qo_not_antisymmetric : @assert_not_antisymmetric S 
; qo_not_total         : @assert_not_total S 
}.

Record wo_certificates {S : Type}  := {
  wo_congruence        : @assert_brel_congruence S 
; wo_reflexive         : @assert_reflexive S 
; wo_transitive        : @assert_transitive S
; wo_not_antisymmetric : @assert_not_antisymmetric S 
; wo_total             : @assert_total S
; wo_trivial_d         : @order_trivial_certifiable S                                                                              
}.

Record or {S : Type} := {
  or_eqv             : @eqv S
; or_lte             : @brel S
; or_exists_top_d    : @certify_exists_qo_top S 
; or_exists_bottom_d : @certify_exists_qo_bottom S 
; or_certs           : @or_certificates S
; or_ast             : cas_or_ast
}.

Record po {S : Type} := {
  po_eqv                 : @eqv S
; po_lte                 : @brel S
; po_not_exists_top      : @assert_not_exists_top S 
; po_not_exists_bottom   : @assert_not_exists_bottom S 
; po_certs               : @po_certificates S
; po_ast                 : cas_or_ast
                       }.

Record po_with_bottom {S : Type} := {
  po_wb_eqv               : @eqv S
; po_wb_lte               : @brel S
; po_wb_not_exists_top    : @assert_not_exists_top S 
; po_wb_exists_bottom     : @assert_exists_bottom S 
; po_wb_certs             : @po_certificates S
; po_wb_ast               : cas_or_ast
}.

Record po_with_top {S : Type} := {
  po_wt_eqv               : @eqv S
; po_wt_lte               : @brel S
; po_wt_exists_top        : @assert_exists_top S 
; po_wt_not_exists_bottom : @assert_not_exists_bottom S 
; po_wt_certs             : @po_certificates S
; po_wt_ast               : cas_or_ast
}.

Record po_bounded {S : Type} := {
  po_bd_eqv               : @eqv S
; po_bd_lte               : @brel S
; po_bd_exists_top        : @assert_exists_top S 
; po_bd_exists_bottom     : @assert_exists_bottom S 
; po_bd_certs             : @po_certificates S
; po_bd_ast               : cas_or_ast
}.


Record to {S : Type} := {
  to_eqv               : @eqv S
; to_lte               : @brel S
; to_not_exists_top    : @assert_not_exists_top S 
; to_not_exists_bottom : @assert_not_exists_bottom S 
; to_certs             : @to_certificates S
; to_ast               : cas_or_ast
}.

Record to_with_bottom {S : Type} := {
  to_wb_eqv               : @eqv S
; to_wb_lte               : @brel S
; to_wb_not_exists_top    : @assert_not_exists_top S 
; to_wb_exists_bottom     : @assert_exists_bottom S 
; to_wb_certs             : @to_certificates S
; to_wb_ast               : cas_or_ast
}.

Record to_with_top {S : Type} := {
  to_wt_eqv               : @eqv S
; to_wt_lte               : @brel S
; to_wt_exists_top        : @assert_exists_top S 
; to_wt_not_exists_bottom : @assert_not_exists_bottom S 
; to_wt_certs             : @to_certificates S
; to_wt_ast               : cas_or_ast
}.

Record to_bounded {S : Type} := {
  to_bd_eqv               : @eqv S
; to_bd_lte               : @brel S
; to_bd_exists_top        : @assert_exists_top S 
; to_bd_exists_bottom     : @assert_exists_bottom S 
; to_bd_certs             : @to_certificates S
; to_bd_ast               : cas_or_ast
}.

  
Record qo {S : Type} := {
  qo_eqv               : @eqv S 
; qo_lte               : @brel S
; qo_not_exists_top    : @assert_not_exists_qo_top S 
; qo_not_exists_bottom : @assert_not_exists_qo_bottom S                        
; qo_certs             : @qo_certificates S
; qo_ast               : cas_or_ast
}.

Record qo_with_bottom {S : Type} := {
  qo_wb_eqv               : @eqv S 
; qo_wb_lte               : @brel S
; qo_wb_not_exists_top    : @assert_not_exists_qo_top S 
; qo_wb_exists_bottom     : @assert_exists_qo_bottom S                        
; qo_wb_certs             : @qo_certificates S
; qo_wb_ast               : cas_or_ast
}.

Record qo_with_top {S : Type} := {
  qo_wt_eqv               : @eqv S 
; qo_wt_lte               : @brel S
; qo_wt_exists_top        : @assert_exists_qo_top S 
; qo_wt_not_exists_bottom : @assert_not_exists_qo_bottom S                        
; qo_wt_certs             : @qo_certificates S
; qo_wt_ast               : cas_or_ast
}.

Record qo_bounded {S : Type} := {
  qo_bd_eqv               : @eqv S 
; qo_bd_lte               : @brel S
; qo_bd_exists_top        : @assert_exists_qo_top S 
; qo_bd_exists_bottom     : @assert_exists_qo_bottom S                        
; qo_bd_certs             : @qo_certificates S
; qo_bd_ast               : cas_or_ast
}.

Record wo {S : Type} := {
  wo_eqv               : @eqv S 
; wo_lte               : @brel S
; wo_not_exists_top    : @assert_not_exists_qo_top S 
; wo_not_exists_bottom : @assert_not_exists_qo_bottom S                        
; wo_certs             : @wo_certificates S
; wo_ast               : cas_or_ast
}.

Record wo_with_bottom {S : Type} := {
  wo_wb_eqv               : @eqv S 
; wo_wb_lte               : @brel S
; wo_wb_not_exists_top    : @assert_not_exists_qo_top S 
; wo_wb_exists_bottom     : @assert_exists_qo_bottom S                        
; wo_wb_certs             : @wo_certificates S
; wo_wb_ast               : cas_or_ast
}.

Record wo_with_top {S : Type} := {
  wo_wt_eqv               : @eqv S 
; wo_wt_lte               : @brel S
; wo_wt_exists_top        : @assert_exists_qo_top S 
; wo_wt_not_exists_bottom : @assert_not_exists_qo_bottom S                        
; wo_wt_certs             : @wo_certificates S
; wo_wt_ast               : cas_or_ast
}.

Record wo_bounded {S : Type} := {
  wo_bd_eqv               : @eqv S 
; wo_bd_lte               : @brel S
; wo_bd_exists_top        : @assert_exists_qo_top S 
; wo_bd_exists_bottom     : @assert_exists_qo_bottom S                        
; wo_bd_certs             : @wo_certificates S
; wo_bd_ast               : cas_or_ast
                               }.


Inductive or_mcas {S : Type} := 
| OR_Error          : list string        -> @or_mcas S
| OR_or             : @or S             -> @or_mcas S
| OR_po             : @po S             -> @or_mcas S
| OR_po_with_bottom : @po_with_bottom S -> @or_mcas S
| OR_po_with_top    : @po_with_top S    -> @or_mcas S
| OR_po_bounded     : @po_bounded S     -> @or_mcas S
| OR_to             : @to S             -> @or_mcas S                                                        
| OR_to_with_bottom : @to_with_bottom S -> @or_mcas S
| OR_to_with_top    : @to_with_top S    -> @or_mcas S
| OR_to_bounded     : @to_bounded S     -> @or_mcas S
| OR_qo             : @qo S             -> @or_mcas S                                                        
| OR_qo_with_bottom : @qo_with_bottom S -> @or_mcas S
| OR_qo_with_top    : @qo_with_top S    -> @or_mcas S
| OR_qo_bounded     : @qo_bounded S     -> @or_mcas S
| OR_wo             : @wo S             -> @or_mcas S                                                        
| OR_wo_with_bottom : @wo_with_bottom S -> @or_mcas S
| OR_wo_with_top    : @wo_with_top S    -> @or_mcas S
| OR_wo_bounded     : @wo_bounded S     -> @or_mcas S                                                            
.

Definition or_classify_or {S : Type} (A : @or S) : @or_mcas S :=
let P := or_certs A in
match or_antisymmetric_d  P, or_total_d  P with
| Certify_Antisymmetric, Certify_Total =>
  let to_P :=
      {|
          to_congruence     := or_congruence  P
        ; to_reflexive      := or_reflexive  P
        ; to_transitive     := or_transitive  P
        ; to_antisymmetric  := Assert_Antisymmetric 
        ; to_total          := Assert_Total 
      |} in 
  match or_exists_top_d A, or_exists_bottom_d A with
  | Certify_Exists_Qo_Top top, Certify_Exists_Qo_Bottom bot =>
    OR_to_bounded
      {|
          to_bd_eqv               := or_eqv A 
        ; to_bd_lte               := or_lte A
        ; to_bd_exists_top        := Assert_Exists_Top top
        ; to_bd_exists_bottom     := Assert_Exists_Bottom bot
        ; to_bd_certs            := to_P
        ; to_bd_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Exists_Qo_Bottom bot =>
    OR_to_with_bottom
      {|
          to_wb_eqv               := or_eqv A 
        ; to_wb_lte               := or_lte A
        ; to_wb_not_exists_top    := Assert_Not_Exists_Top
        ; to_wb_exists_bottom     := Assert_Exists_Bottom bot
        ; to_wb_certs            := to_P 
        ; to_wb_ast               := or_ast A 
      |}
  | Certify_Exists_Qo_Top top, Certify_Not_Exists_Qo_Bottom =>
    OR_to_with_top
      {|
          to_wt_eqv               := or_eqv A 
        ; to_wt_lte               := or_lte A
        ; to_wt_exists_top        := Assert_Exists_Top top
        ; to_wt_not_exists_bottom := Assert_Not_Exists_Bottom 
        ; to_wt_certs            := to_P 
        ; to_wt_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Not_Exists_Qo_Bottom =>
    OR_to
      {|
          to_eqv               := or_eqv A 
        ; to_lte               := or_lte A
        ; to_not_exists_top    := Assert_Not_Exists_Top
        ; to_not_exists_bottom := Assert_Not_Exists_Bottom 
        ; to_certs            := to_P 
        ; to_ast               := or_ast A 
      |}
  end
| Certify_Antisymmetric, Certify_Not_Total p2 =>
  let po_P :=
      {|
          po_congruence     := or_congruence  P
        ; po_reflexive      := or_reflexive  P
        ; po_transitive     := or_transitive  P
        ; po_antisymmetric  := Assert_Antisymmetric 
        ; po_not_total      := Assert_Not_Total p2 
      |} in 
  match or_exists_top_d A, or_exists_bottom_d A with
  | Certify_Exists_Qo_Top top, Certify_Exists_Qo_Bottom bot =>
    OR_po_bounded
      {|
          po_bd_eqv               := or_eqv A 
        ; po_bd_lte               := or_lte A
        ; po_bd_exists_top        := Assert_Exists_Top top
        ; po_bd_exists_bottom     := Assert_Exists_Bottom bot
        ; po_bd_certs            := po_P
        ; po_bd_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Exists_Qo_Bottom bot =>
    OR_po_with_bottom
      {|
          po_wb_eqv               := or_eqv A 
        ; po_wb_lte               := or_lte A
        ; po_wb_not_exists_top    := Assert_Not_Exists_Top
        ; po_wb_exists_bottom     := Assert_Exists_Bottom bot
        ; po_wb_certs            := po_P 
        ; po_wb_ast               := or_ast A 
      |}
  | Certify_Exists_Qo_Top top, Certify_Not_Exists_Qo_Bottom =>
    OR_po_with_top
      {|
          po_wt_eqv               := or_eqv A 
        ; po_wt_lte               := or_lte A
        ; po_wt_exists_top        := Assert_Exists_Top top
        ; po_wt_not_exists_bottom := Assert_Not_Exists_Bottom 
        ; po_wt_certs            := po_P 
        ; po_wt_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Not_Exists_Qo_Bottom =>
    OR_po
      {|
          po_eqv               := or_eqv A 
        ; po_lte               := or_lte A
        ; po_not_exists_top    := Assert_Not_Exists_Top
        ; po_not_exists_bottom := Assert_Not_Exists_Bottom
        ; po_certs            := po_P 
        ; po_ast               := or_ast A 
      |}
  end 
| Certify_Not_Antisymmetric p1, Certify_Total =>
  let wo_P :=
      {|
          wo_congruence     := or_congruence  P
        ; wo_reflexive      := or_reflexive  P
        ; wo_transitive     := or_transitive  P
        ; wo_not_antisymmetric := Assert_Not_Antisymmetric p1 
        ; wo_total          := Assert_Total
        ; wo_trivial_d      := or_trivial_d P
      |} in 
  match or_exists_top_d A, or_exists_bottom_d A with
  | Certify_Exists_Qo_Top top, Certify_Exists_Qo_Bottom bot =>
    OR_wo_bounded
      {|
          wo_bd_eqv               := or_eqv A 
        ; wo_bd_lte               := or_lte A
        ; wo_bd_exists_top        := Assert_Exists_Qo_Top top 
        ; wo_bd_exists_bottom     := Assert_Exists_Qo_Bottom bot
        ; wo_bd_certs            := wo_P
        ; wo_bd_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Exists_Qo_Bottom bot =>
    OR_wo_with_bottom
      {|
          wo_wb_eqv               := or_eqv A 
        ; wo_wb_lte               := or_lte A
        ; wo_wb_not_exists_top    := Assert_Not_Exists_Qo_Top
        ; wo_wb_exists_bottom     := Assert_Exists_Qo_Bottom bot
        ; wo_wb_certs            := wo_P 
        ; wo_wb_ast               := or_ast A 
      |}
  | Certify_Exists_Qo_Top top, Certify_Not_Exists_Qo_Bottom =>
    OR_wo_with_top
      {|
          wo_wt_eqv               := or_eqv A 
        ; wo_wt_lte               := or_lte A
        ; wo_wt_exists_top        := Assert_Exists_Qo_Top top 
        ; wo_wt_not_exists_bottom := Assert_Not_Exists_Qo_Bottom
        ; wo_wt_certs            := wo_P 
        ; wo_wt_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Not_Exists_Qo_Bottom =>
    OR_wo
      {|
          wo_eqv               := or_eqv A 
        ; wo_lte               := or_lte A
        ; wo_not_exists_top    := Assert_Not_Exists_Qo_Top
        ; wo_not_exists_bottom := Assert_Not_Exists_Qo_Bottom
        ; wo_certs            := wo_P 
        ; wo_ast               := or_ast A 
      |}
  end
| Certify_Not_Antisymmetric p1, Certify_Not_Total p2 =>
  let qo_P :=
      {|
          qo_congruence     := or_congruence  P
        ; qo_reflexive      := or_reflexive  P
        ; qo_transitive     := or_transitive P
        ; qo_not_antisymmetric  := Assert_Not_Antisymmetric p1 
        ; qo_not_total      := Assert_Not_Total p2
      |} in 
  match or_exists_top_d A, or_exists_bottom_d A with
  | Certify_Exists_Qo_Top top, Certify_Exists_Qo_Bottom bot =>
    OR_qo_bounded
      {|
          qo_bd_eqv               := or_eqv A 
        ; qo_bd_lte               := or_lte A
        ; qo_bd_exists_top        := Assert_Exists_Qo_Top top 
        ; qo_bd_exists_bottom     := Assert_Exists_Qo_Bottom bot
        ; qo_bd_certs            := qo_P
        ; qo_bd_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Exists_Qo_Bottom bot =>
    OR_qo_with_bottom
      {|
          qo_wb_eqv               := or_eqv A 
        ; qo_wb_lte               := or_lte A
        ; qo_wb_not_exists_top    := Assert_Not_Exists_Qo_Top
        ; qo_wb_exists_bottom     := Assert_Exists_Qo_Bottom bot
        ; qo_wb_certs            := qo_P 
        ; qo_wb_ast               := or_ast A 
      |}
  | Certify_Exists_Qo_Top top, Certify_Not_Exists_Qo_Bottom =>
    OR_qo_with_top
      {|
          qo_wt_eqv               := or_eqv A 
        ; qo_wt_lte               := or_lte A
        ; qo_wt_exists_top        := Assert_Exists_Qo_Top top 
        ; qo_wt_not_exists_bottom := Assert_Not_Exists_Qo_Bottom
        ; qo_wt_certs            := qo_P 
        ; qo_wt_ast               := or_ast A 
      |}
  | Certify_Not_Exists_Qo_Top, Certify_Not_Exists_Qo_Bottom =>
    OR_qo
      {|
          qo_eqv               := or_eqv A 
        ; qo_lte               := or_lte A
        ; qo_not_exists_top    := Assert_Not_Exists_Qo_Top
        ; qo_not_exists_bottom := Assert_Not_Exists_Qo_Bottom
        ; qo_certs            := qo_P 
        ; qo_ast               := or_ast A 
      |}
  end 
end.

Definition or_classify {S : Type} (A : @or_mcas S) : @or_mcas S :=
match A with
| OR_or B => or_classify_or B 
| _ => A                                                       
end.



End CAS.


Section Translation.

Definition P2C_or {S : Type} (eq lte : brel S) (P : or_proofs S eq lte) : @or_certificates S := 
{|
  or_congruence       := @Assert_Brel_Congruence S 
; or_reflexive        := @Assert_Reflexive S 
; or_transitive       := @Assert_Transitive S
; or_antisymmetric_d  := p2c_antisymmetric_check S eq lte (A_or_antisymmetric_d S eq lte P)
; or_total_d          := p2c_total_check S lte (A_or_total_d S eq lte P)
; or_trivial_d        := p2c_order_trivial_certificate S lte (A_or_trivial_d S eq lte P)                                         
|}. 

Definition P2C_po {S : Type} (eq lte : brel S) (P : po_proofs S eq lte) : @po_certificates S := 
{|
  po_congruence       := @Assert_Brel_Congruence S 
; po_reflexive        := @Assert_Reflexive S 
; po_transitive       := @Assert_Transitive S
; po_antisymmetric    := @Assert_Antisymmetric S
; po_not_total        := p2c_not_total_assert S lte (A_po_not_total S eq lte P) 
|}. 

Definition P2C_to {S : Type} (eq lte : brel S) (P : to_proofs S eq lte) : @to_certificates S := 
{|
  to_congruence    := @Assert_Brel_Congruence S 
; to_reflexive     := @Assert_Reflexive S 
; to_transitive    := @Assert_Transitive S
; to_antisymmetric := @Assert_Antisymmetric S 
; to_total         := @Assert_Total S 
|}. 

Definition P2C_qo {S : Type} (eq lte : brel S) (P : qo_proofs S eq lte) : @qo_certificates S := 
{|
  qo_congruence       := @Assert_Brel_Congruence S 
; qo_reflexive        := @Assert_Reflexive S 
; qo_transitive       := @Assert_Transitive S
; qo_not_antisymmetric := p2c_not_antisymmetric_assert S eq lte (A_qo_not_antisymmetric S eq lte P)
; qo_not_total        := p2c_not_total_assert S lte (A_qo_not_total S eq lte P)
|}. 

Definition P2C_wo {S : Type} (eq lte : brel S) (P : wo_proofs S eq lte) : @wo_certificates S := 
{|
  wo_congruence       := @Assert_Brel_Congruence S 
; wo_reflexive        := @Assert_Reflexive S 
; wo_transitive       := @Assert_Transitive S
; wo_not_antisymmetric := p2c_not_antisymmetric_assert S eq lte (A_wo_not_antisymmetric S eq lte P)
; wo_total             := p2c_total_assert S lte (A_wo_total S eq lte P)
; wo_trivial_d        := p2c_order_trivial_certificate S lte (A_wo_trivial_d S eq lte P)               
|}. 

Definition A2C_or {S : Type} (R : A_or S) : @or S := 
let eq  := A_eqv_eq S (A_or_eqv S R) in
let lte := A_or_lte S R in   
{| 
  or_eqv              := A2C_eqv S (A_or_eqv S R) 
; or_lte              := A_or_lte S R
; or_exists_top_d     := p2c_exists_qo_top_check S eq lte (A_or_exists_top_d S R)
; or_exists_bottom_d  := p2c_exists_qo_bottom_check S eq lte (A_or_exists_bottom_d S R)                          
; or_certs            := P2C_or eq lte (A_or_proofs S R)
; or_ast              := A_or_ast S R                       
|}. 



Definition A2C_po {S : Type} (R : A_po S) : @po S := 
let eq  := A_eqv_eq S (A_po_eqv S R) in 
let lte := A_po_lte S R in 
{| 
  po_eqv               := A2C_eqv S (A_po_eqv S R) 
; po_lte               := lte 
; po_not_exists_top    := p2c_not_exists_top_assert S lte (A_po_not_exists_top S R)
; po_not_exists_bottom := p2c_not_exists_bottom_assert S lte  (A_po_not_exists_bottom S R)                          
; po_certs             := P2C_po eq lte (A_po_proofs S R)
; po_ast               := A_po_ast S R                       
|}. 

Definition A2C_po_with_bottom {S : Type} (R : A_po_with_bottom S) : @po_with_bottom S := 
let eq  := A_eqv_eq S (A_po_wb_eqv S R) in 
let lte := A_po_wb_lte S R in 
{| 
  po_wb_eqv               := A2C_eqv S (A_po_wb_eqv S R) 
; po_wb_lte               := lte 
; po_wb_not_exists_top    := p2c_not_exists_top_assert S lte (A_po_wb_not_exists_top S R)
; po_wb_exists_bottom     := p2c_exists_bottom_assert S lte  (A_po_wb_exists_bottom S R)                          
; po_wb_certs             := P2C_po eq lte (A_po_wb_proofs S R)
; po_wb_ast               := A_po_wb_ast S R                       
|}. 

Definition A2C_po_with_top {S : Type} (R : A_po_with_top S) : @po_with_top S := 
let eq  := A_eqv_eq S (A_po_wt_eqv S R) in 
let lte := A_po_wt_lte S R in 
{| 
  po_wt_eqv               := A2C_eqv S (A_po_wt_eqv S R) 
; po_wt_lte               := lte 
; po_wt_exists_top        := p2c_exists_top_assert S lte (A_po_wt_exists_top S R)
; po_wt_not_exists_bottom := p2c_not_exists_bottom_assert S lte  (A_po_wt_not_exists_bottom S R)                          
; po_wt_certs             := P2C_po eq lte (A_po_wt_proofs S R)
; po_wt_ast               := A_po_wt_ast S R                       
|}. 


Definition A2C_po_bounded {S : Type} (R : A_po_bounded S) : @po_bounded S := 
let eq  := A_eqv_eq S (A_po_bd_eqv S R) in 
let lte := A_po_bd_lte S R in 
{| 
  po_bd_eqv               := A2C_eqv S (A_po_bd_eqv S R) 
; po_bd_lte               := lte 
; po_bd_exists_top        := p2c_exists_top_assert S lte (A_po_bd_exists_top S R)
; po_bd_exists_bottom     := p2c_exists_bottom_assert S lte  (A_po_bd_exists_bottom S R)                          
; po_bd_certs             := P2C_po eq lte (A_po_bd_proofs S R)
; po_bd_ast               := A_po_bd_ast S R                       
|}. 


Definition A2C_to {S : Type} (R : A_to S) : @to S := 
let eq  := A_eqv_eq S (A_to_eqv S R) in 
let lte := A_to_lte S R in 
{| 
  to_eqv               := A2C_eqv S (A_to_eqv S R) 
; to_lte               := A_to_lte S R
; to_not_exists_top    := p2c_not_exists_top_assert S lte (A_to_not_exists_top S R)
; to_not_exists_bottom := p2c_not_exists_bottom_assert S lte (A_to_not_exists_bottom S R)                          
; to_certs             := P2C_to eq lte (A_to_proofs S R)  
; to_ast               := A_to_ast S R
|}. 

Definition A2C_to_with_bottom {S : Type} (R : A_to_with_bottom S) : @to_with_bottom S := 
let eq  := A_eqv_eq S (A_to_wb_eqv S R) in 
let lte := A_to_wb_lte S R in 
{| 
  to_wb_eqv               := A2C_eqv S (A_to_wb_eqv S R) 
; to_wb_lte               := A_to_wb_lte S R
; to_wb_not_exists_top    := p2c_not_exists_top_assert S lte (A_to_wb_not_exists_top S R)
; to_wb_exists_bottom     := p2c_exists_bottom_assert S lte (A_to_wb_exists_bottom S R)                          
; to_wb_certs             := P2C_to eq lte (A_to_wb_proofs S R)  
; to_wb_ast               := A_to_wb_ast S R
|}. 

Definition A2C_to_with_top {S : Type} (R : A_to_with_top S) : @to_with_top S := 
let eq  := A_eqv_eq S (A_to_wt_eqv S R) in 
let lte := A_to_wt_lte S R in 
{| 
  to_wt_eqv               := A2C_eqv S (A_to_wt_eqv S R) 
; to_wt_lte               := A_to_wt_lte S R
; to_wt_exists_top        := p2c_exists_top_assert S lte (A_to_wt_exists_top S R)
; to_wt_not_exists_bottom := p2c_not_exists_bottom_assert S lte (A_to_wt_not_exists_bottom S R)                          
; to_wt_certs             := P2C_to eq lte (A_to_wt_proofs S R)  
; to_wt_ast               := A_to_wt_ast S R
|}. 

Definition A2C_to_bounded {S : Type} (R : A_to_bounded S) : @to_bounded S := 
let eq  := A_eqv_eq S (A_to_bd_eqv S R) in 
let lte := A_to_bd_lte S R in 
{| 
  to_bd_eqv               := A2C_eqv S (A_to_bd_eqv S R) 
; to_bd_lte               := A_to_bd_lte S R
; to_bd_exists_top        := p2c_exists_top_assert S lte (A_to_bd_exists_top S R)
; to_bd_exists_bottom     := p2c_exists_bottom_assert S lte (A_to_bd_exists_bottom S R)                          
; to_bd_certs             := P2C_to eq lte (A_to_bd_proofs S R)  
; to_bd_ast               := A_to_bd_ast S R
|}. 

Definition A2C_qo {S : Type} (R : A_qo S) : @qo S := 
{| 
  qo_eqv               := A2C_eqv S (A_qo_eqv S R) 
; qo_lte               := A_qo_lte S R
; qo_not_exists_top    := p2c_not_exists_qo_top_assert S (A_eqv_eq S (A_qo_eqv S R)) (A_qo_lte S R) (A_qo_not_exists_top S R)
; qo_not_exists_bottom := p2c_not_exists_qo_bottom_assert S (A_eqv_eq S (A_qo_eqv S R)) (A_qo_lte S R) (A_qo_not_exists_bottom S R)                          
; qo_certs             := P2C_qo (A_eqv_eq S (A_qo_eqv S R)) (A_qo_lte S R) (A_qo_proofs S R)
; qo_ast               := A_qo_ast S R                       
|}. 

Definition A2C_qo_with_bottom {S : Type} (R : A_qo_with_bottom S) : @qo_with_bottom S := 
{| 
  qo_wb_eqv               := A2C_eqv S (A_qo_wb_eqv S R) 
; qo_wb_lte               := A_qo_wb_lte S R
; qo_wb_not_exists_top    := p2c_not_exists_qo_top_assert S (A_eqv_eq S (A_qo_wb_eqv S R)) (A_qo_wb_lte S R) (A_qo_wb_not_exists_top S R)
; qo_wb_exists_bottom     := p2c_exists_qo_bottom_assert S (A_eqv_eq S (A_qo_wb_eqv S R)) (A_qo_wb_lte S R) (A_qo_wb_exists_bottom S R)
; qo_wb_certs             := P2C_qo (A_eqv_eq S (A_qo_wb_eqv S R)) (A_qo_wb_lte S R) (A_qo_wb_proofs S R)
; qo_wb_ast               := A_qo_wb_ast S R                       
|}. 

Definition A2C_qo_with_top {S : Type} (R : A_qo_with_top S) : @qo_with_top S := 
{| 
  qo_wt_eqv               := A2C_eqv S (A_qo_wt_eqv S R) 
; qo_wt_lte               := A_qo_wt_lte S R
; qo_wt_exists_top        := p2c_exists_qo_top_assert S (A_eqv_eq S (A_qo_wt_eqv S R)) (A_qo_wt_lte S R) (A_qo_wt_exists_top S R)
; qo_wt_not_exists_bottom := p2c_not_exists_qo_bottom_assert S (A_eqv_eq S (A_qo_wt_eqv S R)) (A_qo_wt_lte S R) (A_qo_wt_not_exists_bottom S R)
; qo_wt_certs             := P2C_qo (A_eqv_eq S (A_qo_wt_eqv S R)) (A_qo_wt_lte S R) (A_qo_wt_proofs S R)
; qo_wt_ast               := A_qo_wt_ast S R                       
|}. 

Definition A2C_qo_bounded {S : Type} (R : A_qo_bounded S) : @qo_bounded S := 
{| 
  qo_bd_eqv               := A2C_eqv S (A_qo_bd_eqv S R) 
; qo_bd_lte               := A_qo_bd_lte S R
; qo_bd_exists_top        := p2c_exists_qo_top_assert S (A_eqv_eq S (A_qo_bd_eqv S R)) (A_qo_bd_lte S R) (A_qo_bd_exists_top S R)
; qo_bd_exists_bottom     := p2c_exists_qo_bottom_assert S (A_eqv_eq S (A_qo_bd_eqv S R)) (A_qo_bd_lte S R) (A_qo_bd_exists_bottom S R)
; qo_bd_certs             := P2C_qo (A_eqv_eq S (A_qo_bd_eqv S R)) (A_qo_bd_lte S R) (A_qo_bd_proofs S R)
; qo_bd_ast               := A_qo_bd_ast S R                       
|}. 

Definition A2C_wo {S : Type} (R : A_wo S) : @wo S := 
{| 
  wo_eqv               := A2C_eqv S (A_wo_eqv S R) 
; wo_lte               := A_wo_lte S R
; wo_not_exists_top    := p2c_not_exists_qo_top_assert S (A_eqv_eq S (A_wo_eqv S R)) (A_wo_lte S R) (A_wo_not_exists_top S R)
; wo_not_exists_bottom := p2c_not_exists_qo_bottom_assert S (A_eqv_eq S (A_wo_eqv S R)) (A_wo_lte S R) (A_wo_not_exists_bottom S R)                          
; wo_certs             := P2C_wo (A_eqv_eq S (A_wo_eqv S R)) (A_wo_lte S R) (A_wo_proofs S R)
; wo_ast               := A_wo_ast S R                       
|}. 


Definition A2C_wo_with_bottom {S : Type} (R : A_wo_with_bottom S) : @wo_with_bottom S := 
{| 
  wo_wb_eqv               := A2C_eqv S (A_wo_wb_eqv S R) 
; wo_wb_lte               := A_wo_wb_lte S R
; wo_wb_not_exists_top    := p2c_not_exists_qo_top_assert S (A_eqv_eq S (A_wo_wb_eqv S R)) (A_wo_wb_lte S R) (A_wo_wb_not_exists_top S R)
; wo_wb_exists_bottom     := p2c_exists_qo_bottom_assert S (A_eqv_eq S (A_wo_wb_eqv S R)) (A_wo_wb_lte S R) (A_wo_wb_exists_bottom S R) 
; wo_wb_certs             := P2C_wo (A_eqv_eq S (A_wo_wb_eqv S R)) (A_wo_wb_lte S R) (A_wo_wb_proofs S R)
; wo_wb_ast               := A_wo_wb_ast S R                       
|}. 


Definition A2C_wo_with_top {S : Type} (R : A_wo_with_top S) : @wo_with_top S := 
{| 
  wo_wt_eqv               := A2C_eqv S (A_wo_wt_eqv S R) 
; wo_wt_lte               := A_wo_wt_lte S R
; wo_wt_exists_top        := p2c_exists_qo_top_assert S (A_eqv_eq S (A_wo_wt_eqv S R)) (A_wo_wt_lte S R) (A_wo_wt_exists_top S R)
; wo_wt_not_exists_bottom := p2c_not_exists_qo_bottom_assert S (A_eqv_eq S (A_wo_wt_eqv S R)) (A_wo_wt_lte S R) (A_wo_wt_not_exists_bottom S R) 
; wo_wt_certs             := P2C_wo (A_eqv_eq S (A_wo_wt_eqv S R)) (A_wo_wt_lte S R) (A_wo_wt_proofs S R)
; wo_wt_ast               := A_wo_wt_ast S R                       
|}. 


Definition A2C_wo_bounded {S : Type} (R : A_wo_bounded S) : @wo_bounded S := 
{| 
  wo_bd_eqv               := A2C_eqv S (A_wo_bd_eqv S R) 
; wo_bd_lte               := A_wo_bd_lte S R
; wo_bd_exists_top        := p2c_exists_qo_top_assert S (A_eqv_eq S (A_wo_bd_eqv S R)) (A_wo_bd_lte S R) (A_wo_bd_exists_top S R)
; wo_bd_exists_bottom     := p2c_exists_qo_bottom_assert S (A_eqv_eq S (A_wo_bd_eqv S R)) (A_wo_bd_lte S R) (A_wo_bd_exists_bottom S R) 
; wo_bd_certs             := P2C_wo (A_eqv_eq S (A_wo_bd_eqv S R)) (A_wo_bd_lte S R) (A_wo_bd_proofs S R)
; wo_bd_ast               := A_wo_bd_ast S R                       
|}. 

Definition A2C_mcas_or {S : Type} (R : @A_or_mcas S) : @or_mcas S :=
match R with
| A_OR_Error sl         => OR_Error sl
| A_OR_or A             => OR_or (A2C_or A)            
| A_OR_po A             => OR_po (A2C_po A)            
| A_OR_po_with_bottom A => OR_po_with_bottom (A2C_po_with_bottom A)            
| A_OR_po_with_top A    => OR_po_with_top (A2C_po_with_top A)            
| A_OR_po_bounded A     => OR_po_bounded (A2C_po_bounded A)            
| A_OR_to A             => OR_to (A2C_to A)            
| A_OR_to_with_bottom A => OR_to_with_bottom  (A2C_to_with_bottom  A)            
| A_OR_to_with_top A    => OR_to_with_top (A2C_to_with_top A)  
| A_OR_to_bounded A     => OR_to_bounded (A2C_to_bounded A)                  
| A_OR_qo A             => OR_qo (A2C_qo A)            
| A_OR_qo_with_bottom A => OR_qo_with_bottom (A2C_qo_with_bottom A)            
| A_OR_qo_with_top A    => OR_qo_with_top (A2C_qo_with_top A)            
| A_OR_qo_bounded A     => OR_qo_bounded (A2C_qo_bounded A)            
| A_OR_wo A             => OR_wo (A2C_wo A)            
| A_OR_wo_with_bottom A => OR_wo_with_bottom (A2C_wo_with_bottom A)            
| A_OR_wo_with_top A    => OR_wo_with_top (A2C_wo_with_top A)                               
| A_OR_wo_bounded A     => OR_wo_bounded (A2C_wo_bounded A)                  
end.


End Translation.

Section Verify.

Lemma correct_or_classify_or {S : Type} (a : A_or S) : 
  or_classify_or (A2C_or a)
  =
  A2C_mcas_or (A_or_classify_or a).
Proof. destruct a. destruct A_or_proofs0.
       destruct A_or_exists_top_d0 as [[top [A B]] | ntopP];
       destruct A_or_exists_bottom_d0 as [[bot [D E]] | nbotP];
       destruct A_or_antisymmetric_d0 as [antiP | [p1 nantiP]];
       destruct A_or_total_d0 as [totP | [p2 ntotP]];
       unfold or_classify_or, A_or_classify_or, A2C_or, A2C_mcas_or; simpl;
       try reflexivity. 
Qed.        


Theorem correct_or_classify {S : Type} (A : @A_or_mcas S) :   
  or_classify (A2C_mcas_or A)
  =
  A2C_mcas_or (A_or_classify A).
Proof. unfold or_classify, A_or_classify; destruct A; simpl; 
       try ((try reflexivity)
            ||
            (try (apply correct_or_classify_or))). 
Qed.
  

End Verify. 
