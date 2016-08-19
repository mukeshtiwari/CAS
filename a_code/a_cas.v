Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.data.


Require Import CAS.a_code.a_cast.

Require Import CAS.theory.bs.union_intersect. 
Require Import CAS.theory.bs.intersect_union. 


Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.construct_proofs. 


(* eqv *) 

Definition A_eqv_eq_bool : A_eqv bool 
:= {| 
      A_eqv_eq     := brel_eq_bool 
    ; A_eqv_proofs := eqv_proofs_eq_bool
    ; A_eqv_data     := λ b, DATA_bool b 
    ; A_eqv_rep      := λ b, b 
    ; A_eqv_ast    := Ast_eqv_bool 
   |}. 


Definition A_eqv_eq_nat : A_eqv nat
:= {| 
      A_eqv_eq     := brel_eq_nat 
    ; A_eqv_proofs := eqv_proofs_eq_nat
    ; A_eqv_data     := λ n, DATA_nat n 
    ; A_eqv_rep      := λ b, b 
    ; A_eqv_ast    := Ast_eqv_nat
   |}. 

Definition A_eqv_add_constant : ∀ (S : Type),  A_eqv S -> cas_constant -> A_eqv (with_constant S) 
:= λ S eqvS c, 
   {| 
      A_eqv_eq     := brel_add_constant S (A_eqv_eq S eqvS) c
    ; A_eqv_proofs := eqv_proofs_add_constant S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
    ; A_eqv_data   := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (A_eqv_data S eqvS a) end)
    ; A_eqv_rep    := λ d, (match d with inl s => inl _ s  | inr s => inr _ (A_eqv_rep S eqvS s) end )
    ; A_eqv_ast    := Ast_eqv_add_constant (c, A_eqv_ast S eqvS)
   |}. 

Definition A_eqv_list : ∀ (S : Type),  A_eqv S -> A_eqv (list S) 
:= λ S eqvS, 
   {| 
      A_eqv_eq     := brel_list S (A_eqv_eq S eqvS) 
    ; A_eqv_proofs := eqv_proofs_brel_list S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)
    ; A_eqv_data   := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)
    ; A_eqv_rep    := λ l, List.map (A_eqv_rep S eqvS) l
    ; A_eqv_ast    := Ast_eqv_list (A_eqv_ast S eqvS)
   |}. 


Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S) 
:= λ S eqvS, 
   {| 
      A_eqv_eq     := brel_set S (A_eqv_eq S eqvS) 
    ; A_eqv_proofs := eqv_proofs_brel_set S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)
    ; A_eqv_data   := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)   (* ??? *) 
    ; A_eqv_rep    := λ l, List.map (A_eqv_rep S eqvS) l                (* ??? *) 
      ; A_eqv_ast  := Ast_eqv_set (A_eqv_ast _ eqvS)
   |}. 


Definition A_eqv_product : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S * T) 
:= λ S T eqvS eqvT, 
   {| 
     A_eqv_eq     := brel_product S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
   ; A_eqv_proofs := eqv_proofs_product S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
    ; A_eqv_data  := λ p, DATA_pair (A_eqv_data S eqvS (fst p), A_eqv_data T eqvT (snd p))
    ; A_eqv_rep   := λ p, (A_eqv_rep S eqvS (fst p), A_eqv_rep T eqvT (snd p))
    ; A_eqv_ast   := Ast_eqv_product (A_eqv_ast _ eqvS, A_eqv_ast _ eqvT)
   |}. 

Definition A_eqv_sum : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S + T) 
:= λ S T eqvS eqvT, 
   {| 
     A_eqv_eq     := brel_sum S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
   ; A_eqv_proofs := eqv_proofs_sum S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
    ; A_eqv_data  := λ d, (match d with inl s => DATA_inl (A_eqv_data S eqvS s) | inr t => DATA_inr (A_eqv_data T eqvT t) end)
    ; A_eqv_rep   := λ d, (match d with inl s => inl _ (A_eqv_rep S eqvS s) | inr t => inr _ (A_eqv_rep T eqvT t) end)
    ; A_eqv_ast   := Ast_eqv_sum (A_eqv_ast S eqvS, A_eqv_ast T eqvT)
   |}. 


(* orders *) 

Definition A_po_dual : ∀ (S : Type), A_po S -> A_po S 
:= λ S poS, 
{|
  A_po_eqv        := A_po_eqv S poS 
; A_po_brel       := brel_dual S (A_po_brel S poS)
; A_po_proofs     := po_proofs_dual _ _ _ (A_po_proofs _ poS)
; A_po_ast        := Ast_po_dual (A_po_ast S poS)
|}.


Definition A_po_llte : ∀ (S : Type), A_sg_CI S -> A_po S 
:= λ S sgS, 
let eqv  := A_sg_CI_eqv S sgS                  in 
let eqvP := A_eqv_proofs S eqv                 in 
let r    := A_eqv_eq S eqv                     in 
let b    := brel_llte S r (A_sg_CI_bop S sgS)  in 
{|
  A_po_eqv        := eqv 
; A_po_brel       := b 
; A_po_proofs     := po_proofs_llte _ _ _ eqvP (A_sg_CI_proofs S sgS)
; A_po_ast        := Ast_po_llte (A_sg_CI_ast S sgS)
|}.


Definition A_po_rlte : ∀ (S : Type), A_sg_CI S -> A_po S 
:= λ S sgS, 
let eqv  := A_sg_CI_eqv S sgS                  in 
let eqvP := A_eqv_proofs S eqv                 in 
let r    := A_eqv_eq S eqv                     in 
let b    := brel_rlte S r (A_sg_CI_bop S sgS)  in 
{|
  A_po_eqv        := eqv 
; A_po_brel       := b 
; A_po_proofs     := po_proofs_rlte _ _ _ eqvP (A_sg_CI_proofs S sgS)
; A_po_ast        := Ast_po_rlte (A_sg_CI_ast S sgS)
|}.


Definition A_to_bool : A_to bool
:= {|
  A_to_eqv        := A_eqv_eq_bool
; A_to_brel       := brel_to_bool 
; A_to_proofs     := to_proofs_bool 
; A_to_ast        := Ast_to_bool
|}.


Definition A_to_nat : A_to nat 
:= {| 
  A_to_eqv        := A_eqv_eq_nat 
; A_to_brel       := brel_to_nat 
; A_to_proofs     := to_proofs_nat 
; A_to_ast        := Ast_to_nat
|}.

Definition A_to_dual : ∀ (S : Type), A_to S -> A_to S 
:= λ S toS, 
{|
  A_to_eqv        := A_to_eqv S toS 
; A_to_brel       := brel_dual S (A_to_brel S toS)
; A_to_proofs     := to_proofs_dual _ _ _ (A_to_proofs _ toS)
; A_to_ast        := Ast_to_dual (A_to_ast S toS)
|}.


Definition A_to_llte : ∀ (S : Type), A_sg_CS S -> A_to S 
:= λ S sgS, 
let eqv  := A_sg_CS_eqv S sgS                  in 
let eqvP := A_eqv_proofs S eqv                 in 
let r    := A_eqv_eq S eqv                     in 
let b    := brel_llte S r (A_sg_CS_bop S sgS)  in 
{|
  A_to_eqv        := eqv 
; A_to_brel       := b 
; A_to_proofs     := to_proofs_llte _ _ _ eqvP (A_sg_CS_proofs S sgS)
; A_to_ast        := Ast_to_llte (A_sg_CS_ast S sgS)
|}.


Definition A_to_rlte : ∀ (S : Type), A_sg_CS S -> A_to S 
:= λ S sgS, 
let eqv  := A_sg_CS_eqv S sgS                  in 
let eqvP := A_eqv_proofs S eqv                 in 
let r    := A_eqv_eq S eqv                     in 
let b    := brel_rlte S r (A_sg_CS_bop S sgS)  in 
{|
  A_to_eqv        := eqv 
; A_to_brel       := b 
; A_to_proofs     := to_proofs_rlte _ _ _ eqvP (A_sg_CS_proofs S sgS)
; A_to_ast        := Ast_to_rlte (A_sg_CS_ast S sgS)
|}.


(* semigroups *) 

(* basics *) 



Definition A_sg_and : A_sg bool
:= {| 
     A_sg_eq         := A_eqv_eq_bool
   ; A_sg_bop         := bop_and
   ; A_sg_proofs      := sg_proofs_and
   ; A_sg_ast         := Ast_sg_and 
   |}. 


Definition A_sg_or : A_sg bool
:= {| 
     A_sg_eq         := A_eqv_eq_bool
   ; A_sg_bop         := bop_or
   ; A_sg_proofs      := sg_proofs_or
   ; A_sg_ast         := Ast_sg_or 
   |}. 

Definition A_sg_min : A_sg nat 
:= {| 
     A_sg_eq         := A_eqv_eq_nat 
   ; A_sg_bop         := bop_min 
   ; A_sg_proofs      := sg_proofs_min 
   ; A_sg_ast         := Ast_sg_min 
   |}. 

Definition A_sg_max : A_sg nat 
:= {| 
     A_sg_eq         := A_eqv_eq_nat 
   ; A_sg_bop         := bop_max
   ; A_sg_proofs      := sg_proofs_max
   ; A_sg_ast         := Ast_sg_max
   |}. 



Definition A_sg_times : A_sg nat 
:= {| 
     A_sg_eq        := A_eqv_eq_nat 
   ; A_sg_bop        := bop_times
   ; A_sg_proofs     := sg_proofs_times
   ; A_sg_ast        := Ast_sg_times
   |}. 


Definition A_sg_plus : A_sg nat 
:= {| 
     A_sg_eq         := A_eqv_eq_nat 
   ; A_sg_bop         := bop_plus
   ; A_sg_proofs      := sg_proofs_plus
   ; A_sg_ast         := Ast_sg_plus 
   |}. 





Definition A_sg_CS_and : A_sg_CS bool
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_bool
   ; A_sg_CS_bop         := bop_and
   ; A_sg_CS_proofs      := sg_CS_proofs_and
   ; A_sg_CS_ast         := Ast_sg_CS_and 
   |}. 


Definition A_sg_CS_or : A_sg_CS bool
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_bool
   ; A_sg_CS_bop         := bop_or
   ; A_sg_CS_proofs      := sg_CS_proofs_or
   ; A_sg_CS_ast         := Ast_sg_CS_or 
   |}. 

Definition A_sg_CS_min : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_nat 
   ; A_sg_CS_bop         := bop_min 
   ; A_sg_CS_proofs      := sg_CS_proofs_min 
   ; A_sg_CS_ast         := Ast_sg_CS_min 
   |}. 

Definition A_sg_CS_max : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_nat 
   ; A_sg_CS_bop         := bop_max
   ; A_sg_CS_proofs      := sg_CS_proofs_max
   ; A_sg_CS_ast         := Ast_sg_CS_max
   |}. 



Definition A_sg_C_times : A_sg_C nat 
:= {| 
     A_sg_C_eqv        := A_eqv_eq_nat 
   ; A_sg_C_bop        := bop_times
   ; A_sg_C_proofs     := sg_C_proofs_times
   ; A_sg_C_ast        := Ast_sg_C_times
   |}. 


Definition A_sg_CK_plus : A_sg_CK nat 
:= {| 
     A_sg_CK_eqv         := A_eqv_eq_nat 
   ; A_sg_CK_bop         := bop_plus
   ; A_sg_CK_proofs      := sg_CK_proofs_plus
   ; A_sg_CK_ast         := Ast_sg_CK_plus 
   |}. 



Definition A_sg_concat : ∀ (S : Type),  A_eqv S -> A_sg (list S) 
:= λ S eqvS, 
   {| 
     A_sg_eq         := A_eqv_list S eqvS
   ; A_sg_bop        := bop_concat S 
   ; A_sg_proofs     := sg_proofs_concat S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_concat (A_eqv_ast S eqvS)
   |}. 

Definition A_sg_left: ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq        := eqvS
   ; A_sg_bop       := bop_left S 
   ; A_sg_proofs    := sg_proofs_left S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast       := Ast_sg_left (A_eqv_ast _ eqvS)
   |}. 


Definition A_sg_right : ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq         := eqvS
   ; A_sg_bop        := bop_right S 
   ; A_sg_proofs     := sg_proofs_right S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_right (A_eqv_ast _ eqvS)
   |}. 


(* semigroup add_id *) 



Definition A_sg_add_id : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_eq        := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop       := bop_add_id S (A_sg_bop S sgS) c 
   ; A_sg_proofs    := sg_proofs_add_id S (A_eqv_eq S (A_sg_eq S sgS)) c 
                                           (A_sg_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_eq S sgS))
                                           (A_sg_proofs S sgS) 
   ; A_sg_ast       := Ast_sg_add_id (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_id S (A_sg_C_bop S sgS) c 
   ; A_sg_C_proofs    := sg_C_proofs_add_id S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                           (A_sg_C_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                           (A_sg_C_proofs S sgS) 
   ; A_sg_C_ast       := Ast_sg_C_add_id (c, A_sg_C_ast S sgS)
   |}. 


Definition A_sg_CI_add_id : ∀ (S : Type) (c : cas_constant), A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_id S (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_id S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                           (A_sg_CI_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                           (A_sg_CI_proofs S sgS) 
   ; A_sg_CI_ast       := Ast_sg_CI_add_id (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_id S (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_id S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                           (A_sg_CS_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                           (A_sg_CS_proofs S sgS) 
   ; A_sg_CS_ast       := Ast_sg_CS_add_id (c, A_sg_CS_ast S sgS)
   |}. 


(* semigroup add_ann *) 

Definition A_sg_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_eq        := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop       := bop_add_ann S (A_sg_bop S sgS) c 
   ; A_sg_proofs    := sg_proofs_add_ann S (A_eqv_eq S (A_sg_eq S sgS)) c 
                                            (A_sg_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_eq S sgS))
                                            (A_sg_proofs S sgS) 
   ; A_sg_ast       := Ast_sg_add_ann (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_ann S (A_sg_C_bop S sgS) c 
   ; A_sg_C_proofs    := sg_C_proofs_add_ann S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                            (A_sg_C_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                            (A_sg_C_proofs S sgS) 
   ; A_sg_C_ast       := Ast_sg_C_add_ann (c, A_sg_C_ast S sgS)
   |}. 


Definition A_sg_CI_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_ann S (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_ann S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                            (A_sg_CI_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                            (A_sg_CI_proofs S sgS) 
   ; A_sg_CI_ast       := Ast_sg_CI_add_ann (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_ann S (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_ann S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                            (A_sg_CS_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                            (A_sg_CS_proofs S sgS) 
   ; A_sg_CS_ast       := Ast_sg_CS_add_ann (c, A_sg_CS_ast S sgS)
   |}. 


(* semigroup sums *) 

Definition A_sg_left_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_sum S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_left_sum S T 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs    := sg_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_left_sum (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 

Definition A_sg_right_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_sum S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_right_sum S T 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs := sg_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_right_sum (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 



Definition A_sg_C_left_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv       := A_eqv_sum S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_left_sum S T 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs    := sg_C_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_left_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 

Definition A_sg_C_right_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv       := A_eqv_sum S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_right_sum S T 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs := sg_C_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_right_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 


Definition A_sg_CI_left_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_left_sum S T 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs    := sg_CI_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_left_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 

Definition A_sg_CI_right_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_right_sum S T 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_right_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CS_left_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CS_eqv       := A_eqv_sum S T 
                           (A_sg_CS_eqv S sgS) 
                           (A_sg_CS_eqv T sgT) 
   ; A_sg_CS_bop       := bop_left_sum S T 
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
   ; A_sg_CS_proofs    := sg_CS_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CS_eqv T sgT))
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT) 
   ; A_sg_CS_ast       := Ast_sg_CS_left_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
   |}. 

Definition A_sg_CS_right_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CS_eqv       := A_eqv_sum S T 
                           (A_sg_CS_eqv S sgS) 
                           (A_sg_CS_eqv T sgT) 
   ; A_sg_CS_bop       := bop_right_sum S T 
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
   ; A_sg_CS_proofs := sg_CS_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CS_eqv T sgT))
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT) 
   ; A_sg_CS_ast       := Ast_sg_CS_right_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
   |}. 


(* semigroup products *) 

Definition A_sg_product : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_product S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_product S T 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_product (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 


Definition A_sg_C_product : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv    := A_eqv_product S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_product S T 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs := sg_C_proofs_product S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_product (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 


Definition A_sg_CI_product : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv    := A_eqv_product S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_product S T 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_product S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_product (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CK_product : ∀ (S T : Type),  A_sg_CK S -> A_sg_CK T -> A_sg_CK (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CK_eqv    := A_eqv_product S T 
                           (A_sg_CK_eqv S sgS) 
                           (A_sg_CK_eqv T sgT) 
   ; A_sg_CK_bop       := bop_product S T 
                           (A_sg_CK_bop S sgS) 
                           (A_sg_CK_bop T sgT) 
   ; A_sg_CK_proofs := sg_CK_proofs_product S T 
                           (A_eqv_eq S (A_sg_CK_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CK_eqv T sgT))
                           (A_sg_CK_bop S sgS) 
                           (A_sg_CK_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CK_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CK_eqv T sgT)) 
                           (A_sg_CK_proofs S sgS) 
                           (A_sg_CK_proofs T sgT) 
   ; A_sg_CK_ast       := Ast_sg_CK_product (A_sg_CK_ast S sgS, A_sg_CK_ast T sgT)
   |}. 



(* semigroup lexicographic *) 


Definition A_sg_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg T -> A_sg (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_eq     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_eq T sgT) 
      ; A_sg_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_bop T sgT) 
      ; A_sg_proofs := sg_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_eq T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_eq T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_proofs T sgT) 
      ; A_sg_ast    := Ast_sg_llex (A_sg_CS_ast S sgS, A_sg_ast T sgT)  
      |}. 





Definition A_sg_C_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_C T -> A_sg_C (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_C_eqv     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_C_eqv T sgT) 
      ; A_sg_C_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_C_bop T sgT) 
      ; A_sg_C_proofs := sg_C_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_C_eqv T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_C_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_C_eqv T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_C_proofs T sgT) 
      ; A_sg_C_ast    := Ast_sg_C_llex (A_sg_CS_ast S sgS, A_sg_C_ast T sgT)  
      |}. 



Definition A_sg_CI_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CI T -> A_sg_CI (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_CI_eqv     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_CI_eqv T sgT) 
      ; A_sg_CI_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CI_bop T sgT) 
      ; A_sg_CI_proofs := sg_CI_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_CI_eqv T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CI_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_CI_eqv T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_CI_proofs T sgT) 
      ; A_sg_CI_ast    := Ast_sg_CI_llex (A_sg_CS_ast S sgS, A_sg_CI_ast T sgT)  
      |}. 




Definition A_sg_CS_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_CS_eqv     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_CS_eqv T sgT) 
      ; A_sg_CS_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CS_bop T sgT) 
      ; A_sg_CS_proofs := sg_CS_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_CS_eqv T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CS_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_CS_eqv T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_CS_proofs T sgT) 
      ; A_sg_CS_ast    := Ast_sg_CS_llex (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)  
      |}. 


(* SETS *) 


Definition A_sg_union : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_sg (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_sg_eq    := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c  
   ; A_sg_bop    := bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c 
   ; A_sg_proofs := sg_proofs_union S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_sg_ast    := Ast_sg_union (c, A_eqv_ast S eqvS)
   |}. 

Definition A_sg_intersect : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_sg (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_sg_eq    := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c  
   ; A_sg_bop    := bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c 
   ; A_sg_proofs := sg_proofs_intersect S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_sg_ast    := Ast_sg_intersect (c, A_eqv_ast S eqvS)
   |}. 




Definition A_bs_and_or : A_bs bool := 
{|
  A_bs_eqv          := A_eqv_eq_bool
; A_bs_plus         := bop_and
; A_bs_times        := bop_or
; A_bs_plus_proofs  := sg_proofs_and
; A_bs_times_proofs := sg_proofs_or
; A_bs_proofs       := bs_proofs_and_or 
; A_bs_ast          := Ast_bs_and_or
|}.


Definition A_bs_or_and : A_bs bool := 
{|
  A_bs_eqv          := A_eqv_eq_bool
; A_bs_plus         := bop_or
; A_bs_times        := bop_and
; A_bs_plus_proofs  := sg_proofs_or
; A_bs_times_proofs := sg_proofs_and
; A_bs_proofs       := bs_proofs_or_and
; A_bs_ast          := Ast_bs_or_and 
|}.


Definition A_bs_min_max : A_bs nat := 
{|
  A_bs_eqv          := A_eqv_eq_nat 
; A_bs_plus         := bop_min
; A_bs_times        := bop_max
; A_bs_plus_proofs  := sg_proofs_min
; A_bs_times_proofs := sg_proofs_max
; A_bs_proofs       := bs_proofs_min_max
; A_bs_ast          := Ast_bs_min_max
|}.

Definition A_bs_max_min : A_bs nat := 
{|
  A_bs_eqv          := A_eqv_eq_nat 
; A_bs_plus         := bop_max
; A_bs_times        := bop_min
; A_bs_plus_proofs  := sg_proofs_max
; A_bs_times_proofs := sg_proofs_min
; A_bs_proofs       := bs_proofs_max_min
; A_bs_ast          := Ast_bs_max_min
|}.

Definition A_bs_min_plus : A_bs nat := 
{|
  A_bs_eqv          := A_eqv_eq_nat 
; A_bs_plus         := bop_min
; A_bs_times        := bop_plus
; A_bs_plus_proofs  := sg_proofs_min
; A_bs_times_proofs := sg_proofs_plus
; A_bs_proofs       := bs_proofs_min_plus
; A_bs_ast          := Ast_bs_min_plus
|}.


Definition A_bs_max_plus : A_bs nat := 
{|
  A_bs_eqv          := A_eqv_eq_nat 
; A_bs_plus         := bop_max
; A_bs_times        := bop_plus
; A_bs_plus_proofs  := sg_proofs_max
; A_bs_times_proofs := sg_proofs_plus
; A_bs_proofs       := bs_proofs_max_plus
; A_bs_ast          := Ast_bs_max_plus
|}.





(* bs *) 

Definition bs_proofs_union_intersect : ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S),  
              bs_proofs 
                (with_constant (finite_set S)) 
                (brel_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c)
                (bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c)
                (bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c)
:= λ S c eqvS, 
  let r := A_eqv_eq S eqvS in 
  let ref := A_eqv_reflexive _ r (A_eqv_proofs _ eqvS) in 
  let sym := A_eqv_symmetric _ r (A_eqv_proofs _ eqvS) in 
  let trn := A_eqv_transitive _ r (A_eqv_proofs _ eqvS) in  
  {| 
     A_bs_left_distributive_d      := inl _ (bops_union_intersect_left_distributive S r c ref sym trn) 
   ; A_bs_right_distributive_d     := inl _ (bops_union_intersect_right_distributive S r c ref sym trn)

   ; A_bs_plus_id_is_times_ann_d   := inl _ (bops_union_intersect_id_equals_ann S r c ref sym trn)
   ; A_bs_times_id_is_plus_ann_d   := inl _ (bops_union_intersect_ann_equals_id S r c ref sym trn) 

   ; A_bs_left_left_absorptive_d   := inl _ (bops_union_intersect_left_left_absorptive S r c ref sym trn) 
   ; A_bs_left_right_absorptive_d  := inl _ (bops_union_intersect_left_right_absorptive S r c ref sym trn) 
   ; A_bs_right_left_absorptive_d  := inl _ (bops_union_intersect_right_left_absorptive S r c ref sym trn) 
   ; A_bs_right_right_absorptive_d := inl _ (bops_union_intersect_right_right_absorptive S r c ref sym trn) 
  |}. 



Definition A_bs_union_intersect : ∀ (S : Type) (c : cas_constant),  
              A_eqv S -> A_bs (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_bs_eqv     := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c  
   ; A_bs_plus    := bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c 
   ; A_bs_times   := bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c 
   ; A_bs_plus_proofs  := sg_proofs_union S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_bs_times_proofs := sg_proofs_intersect S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_bs_proofs  := bs_proofs_union_intersect S c eqvS 
   ; A_bs_ast     := Ast_bs_union_intersect (c, A_eqv_ast S eqvS)
   |}. 



Definition bs_proofs_intersect_union : ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S),  
              bs_proofs 
                (with_constant (finite_set S)) 
                (brel_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c)
                (bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c)
                (bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c)
:= λ S c eqvS, 
  let r := A_eqv_eq S eqvS in 
  let ref := A_eqv_reflexive _ r (A_eqv_proofs _ eqvS) in 
  let sym := A_eqv_symmetric _ r (A_eqv_proofs _ eqvS) in 
  let trn := A_eqv_transitive _ r (A_eqv_proofs _ eqvS) in  
  {| 
     A_bs_left_distributive_d      := inl _ (bops_intersect_union_left_distributive S r c ref sym trn) 
   ; A_bs_right_distributive_d     := inl _ (bops_intersect_union_right_distributive S r c ref sym trn)

   ; A_bs_plus_id_is_times_ann_d   := inl _ (bops_intersect_union_id_equals_ann S r c ref sym trn)
   ; A_bs_times_id_is_plus_ann_d   := inl _ (bops_intersect_union_ann_equals_id S r c ref sym trn) 

   ; A_bs_left_left_absorptive_d   := inl _ (bops_intersect_union_left_left_absorptive S r c ref sym trn) 
   ; A_bs_left_right_absorptive_d  := inl _ (bops_intersect_union_left_right_absorptive S r c ref sym trn) 
   ; A_bs_right_left_absorptive_d  := inl _ (bops_intersect_union_right_left_absorptive S r c ref sym trn) 
   ; A_bs_right_right_absorptive_d := inl _ (bops_intersect_union_right_right_absorptive S r c ref sym trn) 
  |}. 



Definition A_bs_intersect_union : ∀ (S : Type) (c : cas_constant),  
              A_eqv S -> A_bs (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_bs_eqv     := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c  
   ; A_bs_plus    := bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c 
   ; A_bs_times   := bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c 
   ; A_bs_plus_proofs  := sg_proofs_intersect S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_bs_times_proofs := sg_proofs_union S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_bs_proofs  := bs_proofs_intersect_union S c eqvS 
   ; A_bs_ast     := Ast_bs_intersect_union (c, A_eqv_ast S eqvS)
   |}. 



Definition A_bs_product : ∀ (S T : Type),  A_bs S -> A_bs T -> A_bs (S * T) 
:= λ S T bsS bsT, 
{| 
     A_bs_eqv        := A_eqv_product S T 
                           (A_bs_eqv S bsS) 
                           (A_bs_eqv T bsT) 
   ; A_bs_plus       := bop_product S T 
                           (A_bs_plus S bsS) 
                           (A_bs_plus T bsT) 
   ; A_bs_times       := bop_product S T 
                           (A_bs_times S bsS) 
                           (A_bs_times T bsT) 
   ; A_bs_plus_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_bs_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_eqv T bsT))
                           (A_bs_plus S bsS) 
                           (A_bs_plus T bsT) 
                           (A_eqv_proofs S (A_bs_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_eqv T bsT)) 
                           (A_bs_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_bs_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_eqv T bsT))
                           (A_bs_times S bsS) 
                           (A_bs_times T bsT) 
                           (A_eqv_proofs S (A_bs_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_eqv T bsT)) 
                           (A_bs_times_proofs S bsS) 
                           (A_bs_times_proofs T bsT) 
   ; A_bs_proofs    := bs_proofs_product S T 
                           (A_eqv_eq S (A_bs_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_eqv T bsT))
                           (A_bs_plus S bsS) 
                           (A_bs_times S bsS) 
                           (A_bs_plus T bsT) 
                           (A_bs_times T bsT) 
                           (A_eqv_proofs S (A_bs_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_eqv T bsT)) 
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT) 
   ; A_bs_ast        := Ast_bs_product(A_bs_ast S bsS, A_bs_ast T bsT)
|}. 



Definition A_bs_add_zero : ∀ (S : Type),  A_bs S -> cas_constant -> A_bs (with_constant S) 
:= λ S bsS c, 
{| 
     A_bs_eqv          := A_eqv_add_constant S (A_bs_eqv S bsS) c 
   ; A_bs_plus         := bop_add_id S (A_bs_plus S bsS) c
   ; A_bs_times        := bop_add_ann S (A_bs_times S bsS) c
   ; A_bs_plus_proofs  := sg_proofs_add_id S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_plus S bsS) 
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_plus_proofs S bsS) 
   ; A_bs_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_times S bsS)  
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_times_proofs S bsS) 
   ; A_bs_proofs       := bs_proofs_add_zero S _ c 
                                (A_bs_plus S bsS) 
                                (A_bs_times S bsS)  
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_proofs S bsS)
   ; A_bs_ast          := Ast_bs_add_zero (c, A_bs_ast S bsS)
|}. 

Definition A_bs_add_one : ∀ (S : Type),  A_bs S -> cas_constant -> A_bs (with_constant S) 
:= λ S bsS c, 
{| 
     A_bs_eqv          := A_eqv_add_constant S (A_bs_eqv S bsS) c 
   ; A_bs_plus         := bop_add_ann S (A_bs_plus S bsS) c
   ; A_bs_times        := bop_add_id S (A_bs_times S bsS) c
   ; A_bs_plus_proofs  := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_plus S bsS) 
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_plus_proofs S bsS) 
   ; A_bs_times_proofs := sg_proofs_add_id S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_times S bsS)  
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_times_proofs S bsS) 
   ; A_bs_proofs       := bs_proofs_add_one S _ c 
                                (A_bs_plus S bsS) 
                                (A_bs_times S bsS)  
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_plus_proofs S bsS) 
                                (A_bs_proofs S bsS)
   ; A_bs_ast          := Ast_bs_add_one (c, A_bs_ast S bsS)
|}. 


(*
Definition A_sg_CS_sg_add_zero : ∀ (S : Type),  A_sg_CS_sg S -> cas_constant -> A_sg_CS_sg (with_constant S) 
:= λ S bsS c, 
{| 
     A_sg_CS_sg_eqv          := A_eqv_add_constant S (A_sg_CS_sg_eqv S bsS) c 
   ; A_sg_CS_sg_plus         := bop_add_id S (A_sg_CS_sg_plus S bsS) c
   ; A_sg_CS_sg_times        := bop_add_ann S (A_sg_CS_sg_times S bsS) c
   ; A_sg_CS_sg_plus_proofs  := sg_CS_proofs_add_id S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S bsS)) c 
                                (A_sg_CS_sg_plus S bsS) 
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S bsS)) 
                                (A_sg_CS_sg_plus_proofs S bsS) 
   ; A_sg_CS_sg_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S bsS)) c 
                                (A_sg_CS_sg_times S bsS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S bsS)) 
                                (A_sg_CS_sg_times_proofs S bsS) 
   ; A_sg_CS_sg_proofs       := bs_proofs_add_zero S _ c 
                                (A_sg_CS_sg_plus S bsS) 
                                (A_sg_CS_sg_times S bsS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S bsS)) 
                                (A_sg_CS_sg_proofs S bsS)
   ; A_sg_CS_sg_ast          := Ast_sg_CS_sg_add_zero (c, A_sg_CS_sg_ast S bsS)
|}. 



*) 

(*
Definition A_sg_C_sg_add_one : ∀ (S : Type),  A_sg_C_sg S -> cas_constant -> A_sg_C_sg (with_constant S) 
:= λ S bsS c, 
{| 
     A_sg_C_sg_eqv          := A_eqv_add_constant S (A_sg_C_sg_eqv S bsS) c 
   ; A_sg_C_sg_plus         := bop_add_ann S (A_sg_C_sg_plus S bsS) c
   ; A_sg_C_sg_times        := bop_add_id S (A_sg_C_sg_times S bsS) c
   ; A_sg_C_sg_plus_proofs  := sg_C_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_C_sg_eqv S bsS)) c 
                                (A_sg_C_sg_plus S bsS) 
                                (A_eqv_proofs S (A_sg_C_sg_eqv S bsS)) 
                                (A_sg_C_sg_plus_proofs S bsS) 
   ; A_sg_C_sg_times_proofs := sg_proofs_add_id S 
                                (A_eqv_eq S (A_sg_C_sg_eqv S bsS)) c 
                                (A_sg_C_sg_times S bsS)  
                                (A_eqv_proofs S (A_sg_C_sg_eqv S bsS)) 
                                (A_sg_C_sg_times_proofs S bsS) 
   ; A_sg_C_sg_proofs       := bs_proofs_add_one S _ c 
                                (A_sg_C_sg_plus S bsS) 
                                (A_sg_C_sg_times S bsS)  
                                (A_eqv_proofs S (A_sg_C_sg_eqv S bsS)) 
                                (A_sg_C_sg_plus_proofs S bsS) 
                                (A_sg_C_sg_proofs S bsS)
   ; A_sg_C_sg_ast          := Ast_sg_C_sg_add_one (c, A_sg_C_sg_ast S bsS)
|}. 

Definition A_sg_CS_sg_add_one : ∀ (S : Type),  A_sg_CS_sg S -> cas_constant -> A_sg_CS_sg (with_constant S) 
:= λ S bsS c, 
{| 
     A_sg_CS_sg_eqv          := A_eqv_add_constant S (A_sg_CS_sg_eqv S bsS) c 
   ; A_sg_CS_sg_plus         := bop_add_ann S (A_sg_CS_sg_plus S bsS) c
   ; A_sg_CS_sg_times        := bop_add_id S (A_sg_CS_sg_times S bsS) c
   ; A_sg_CS_sg_plus_proofs  := sg_CS_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S bsS)) c 
                                (A_sg_CS_sg_plus S bsS) 
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S bsS)) 
                                (A_sg_CS_sg_plus_proofs S bsS) 
   ; A_sg_CS_sg_times_proofs := sg_proofs_add_id S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S bsS)) c 
                                (A_sg_CS_sg_times S bsS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S bsS)) 
                                (A_sg_CS_sg_times_proofs S bsS) 
   ; A_sg_CS_sg_proofs       := sg_CS_sg_proofs_add_one S _ c 
                                (A_sg_CS_sg_plus S bsS) 
                                (A_sg_CS_sg_times S bsS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S bsS)) 
                                (A_sg_CS_sg_plus_proofs S bsS) 
                                (A_sg_CS_sg_proofs S bsS)
   ; A_sg_CS_sg_ast          := Ast_sg_CS_sg_add_one (c, A_sg_CS_sg_ast S bsS)
|}. 

*) 


Definition A_bs_C_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_C T -> A_bs_C (S * T) 
:= λ S T bsS bsT, 
{| 
     A_bs_C_eqv        := A_eqv_product S T 
                           (A_bs_CS_eqv S bsS) 
                           (A_bs_C_eqv T bsT) 
   ; A_bs_C_plus       := bop_llex S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_bs_CS_plus S bsS) 
                           (A_bs_C_plus T bsT) 
   ; A_bs_C_times       := bop_product S T 
                           (A_bs_CS_times S bsS) 
                           (A_bs_C_times T bsT) 
   ; A_bs_C_plus_proofs := sg_C_proofs_llex S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_C_eqv T bsT))
                           (A_bs_CS_plus S bsS) 
                           (A_bs_C_plus T bsT) 
                           (A_eqv_proofs S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_C_eqv T bsT)) 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_C_plus_proofs T bsT) 
   ; A_bs_C_times_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_C_eqv T bsT))
                           (A_bs_CS_times S bsS) 
                           (A_bs_C_times T bsT) 
                           (A_eqv_proofs S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_C_eqv T bsT)) 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_C_times_proofs T bsT)
   ; A_bs_C_proofs    := bs_proofs_llex S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_C_eqv T bsT))
                           (A_bs_CS_plus S bsS) 
                           (A_bs_CS_times S bsS) 
                           (A_bs_C_plus T bsT) 
                           (A_bs_C_times T bsT) 
                           (A_eqv_proofs S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_C_eqv T bsT)) 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_times_proofs S bsS) 
                           (A_bs_C_plus_proofs T bsT) 
                           (A_bs_C_times_proofs T bsT) 
                           (A_bs_CS_proofs S bsS) 
                           (A_bs_C_proofs T bsT) 
   ; A_bs_C_ast        := Ast_bs_C_llex (A_bs_CS_ast S bsS, A_bs_C_ast T bsT)
|}. 


Definition A_bs_CS_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_CS T -> A_bs_CS (S * T) 
:= λ S T bsS bsT, 
{| 
     A_bs_CS_eqv        := A_eqv_product S T 
                           (A_bs_CS_eqv S bsS) 
                           (A_bs_CS_eqv T bsT) 
   ; A_bs_CS_plus       := bop_llex S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_bs_CS_plus S bsS) 
                           (A_bs_CS_plus T bsT) 
   ; A_bs_CS_times       := bop_product S T 
                           (A_bs_CS_times S bsS) 
                           (A_bs_CS_times T bsT) 
   ; A_bs_CS_plus_proofs := sg_CS_proofs_llex S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_CS_eqv T bsT))
                           (A_bs_CS_plus S bsS) 
                           (A_bs_CS_plus T bsT) 
                           (A_eqv_proofs S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_CS_eqv T bsT)) 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_plus_proofs T bsT) 
   ; A_bs_CS_times_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_CS_eqv T bsT))
                           (A_bs_CS_times S bsS) 
                           (A_bs_CS_times T bsT) 
                           (A_eqv_proofs S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_CS_eqv T bsT)) 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_CS_times_proofs T bsT)
   ; A_bs_CS_proofs    := bs_proofs_llex S T 
                           (A_eqv_eq S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_eq T (A_bs_CS_eqv T bsT))
                           (A_bs_CS_plus S bsS) 
                           (A_bs_CS_times S bsS) 
                           (A_bs_CS_plus T bsT) 
                           (A_bs_CS_times T bsT) 
                           (A_eqv_proofs S (A_bs_CS_eqv S bsS)) 
                           (A_eqv_proofs T (A_bs_CS_eqv T bsT)) 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_times_proofs S bsS) 
                           (A_sg_C_proofs_from_sg_CI_proofs _ _ _ (A_eqv_proofs T (A_bs_CS_eqv T bsT))
                              (A_sg_CI_proofs_from_sg_CS_proofs _ _ _ (A_bs_CS_plus_proofs T bsT)))
                           (A_bs_CS_times_proofs T bsT) 
                           (A_bs_CS_proofs S bsS) 
                           (A_bs_CS_proofs T bsT) 
   ; A_bs_CS_ast        := Ast_bs_CS_llex (A_bs_CS_ast S bsS, A_bs_CS_ast T bsT)
|}. 
