Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.theory.facts. 

(* UPCASTS *) 


Definition A_sg_proofs_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_C_proofs S r b -> sg_proofs S r b 
:= λ S r b eqvS sgS, 
{|
  A_sg_associative      := A_sg_C_associative S r b sgS 
; A_sg_congruence       := A_sg_C_congruence S r b sgS 
; A_sg_commutative_d    := inl _ (A_sg_C_commutative S r b sgS) 
; A_sg_selective_d      := A_sg_C_selective_d S r b sgS    
; A_sg_is_left_d        := inr _ (bop_commutative_implies_not_is_left S r b 
                                     (A_eqv_nontrivial S r eqvS) 
                                     (A_eqv_symmetric S r eqvS) 
                                     (A_eqv_transitive S r eqvS) 
                                     (A_sg_C_commutative S r b sgS))
; A_sg_is_right_d       := inr _ (bop_commutative_implies_not_is_right S r b 
                                     (A_eqv_nontrivial S r eqvS) 
                                     (A_eqv_symmetric S r eqvS) 
                                     (A_eqv_transitive S r eqvS) 
                                     (A_sg_C_commutative S r b sgS))
; A_sg_idempotent_d     := A_sg_C_idempotent_d S r b sgS    
; A_sg_exists_id_d      := A_sg_C_exists_id_d S r b sgS    
; A_sg_exists_ann_d     := A_sg_C_exists_ann_d S r b sgS    
; A_sg_left_cancel_d    := A_sg_C_left_cancel_d S r b sgS    
; A_sg_right_cancel_d   := A_sg_C_right_cancel_d S r b sgS    
; A_sg_left_constant_d  := A_sg_C_left_constant_d S r b sgS
; A_sg_right_constant_d := A_sg_C_right_constant_d S r b sgS
; A_sg_anti_left_d      := A_sg_C_anti_left_d S r b sgS
; A_sg_anti_right_d     := A_sg_C_anti_right_d S r b sgS
|}. 

Definition A_sg_from_sg_C : ∀ (S : Type),  A_sg_C S -> A_sg S 
:= λ S sgS, 
   {| 
     A_sg_eq          := A_sg_C_eqv S sgS
   ; A_sg_bop         := A_sg_C_bop S sgS
   ; A_sg_proofs      := A_sg_proofs_from_sg_C_proofs S 
                            (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_bop S sgS) 
                            (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_proofs S sgS) 
   ; A_sg_ast        := Ast_sg_from_sg_C (A_sg_C_ast S sgS)
   |}. 

 

Definition A_sg_C_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CI_proofs S r b -> sg_C_proofs S r b 
:= λ S r b eqvS sgS, 
{|
  A_sg_C_associative      := A_sg_CI_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CI_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CI_commutative S r b sgS
; A_sg_C_selective_d      := A_sg_CI_selective_d S r b sgS    
; A_sg_C_idempotent_d     := inl _ (A_sg_CI_idempotent S r b sgS) 
; A_sg_C_exists_id_d      := A_sg_CI_exists_id_d S r b sgS    
; A_sg_C_exists_ann_d     := A_sg_CI_exists_ann_d S r b sgS    
; A_sg_C_left_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_associative S r b sgS)
                                       (A_sg_CI_congruence S r b sgS)
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                       (A_sg_CI_selective_d S r b sgS)
                                   )
; A_sg_C_right_cancel_d   := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative S r b 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_associative S r b sgS)
                                       (A_sg_CI_congruence S r b sgS)
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                       (A_sg_CI_selective_d S r b sgS)
                                   )
; A_sg_C_left_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                   ) 
; A_sg_C_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant S r b
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                   ) 
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b 
                                       (brel_nontrivial_witness S r (A_eqv_nontrivial S r eqvS)) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                   )
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b 
                                       (brel_nontrivial_witness S r (A_eqv_nontrivial S r eqvS)) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                   )
|}. 


Definition A_sg_C_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv         := A_sg_CI_eqv S sgS
   ; A_sg_C_bop         := A_sg_CI_bop S sgS
   ; A_sg_C_proofs      := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_bop S sgS) 
                            (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_proofs S sgS) 
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CI (A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CI_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CS_proofs S r b -> sg_CI_proofs S r b 
:= λ S r b sg_CSS, 
{|
  A_sg_CI_associative        := A_sg_CS_associative S r b sg_CSS 
; A_sg_CI_congruence         := A_sg_CS_congruence S r b sg_CSS 
; A_sg_CI_commutative        := A_sg_CS_commutative S r b sg_CSS
; A_sg_CI_idempotent         := bop_selective_implies_idempotent S r b (A_sg_CS_selective S r b sg_CSS)
; A_sg_CI_selective_d        := inl _ (A_sg_CS_selective S r b sg_CSS) 
; A_sg_CI_exists_id_d        := A_sg_CS_exists_id_d S r b sg_CSS    
; A_sg_CI_exists_ann_d       := A_sg_CS_exists_ann_d S r b sg_CSS    
|}. 


Definition A_sg_CI_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_CI S 
:= λ S sgS, 
   {| 
     A_sg_CI_eqv         := A_sg_CS_eqv S sgS
   ; A_sg_CI_bop         := A_sg_CS_bop S sgS
   ; A_sg_CI_proofs      := A_sg_CI_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_bop S sgS) 
                            (A_sg_CS_proofs S sgS) 
   ; A_sg_CI_ast        := Ast_sg_CI_from_sg_CS (A_sg_CS_ast S sgS)
   |}. 



Definition A_sg_C_proofs_from_sg_CK_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CK_proofs S r b -> sg_C_proofs S r b 
:= λ S r b eqvS sgS, 
let right_cancel := bop_commutative_and_left_cancellative_imply_right_cancellative S r b 
                      (A_eqv_transitive S r eqvS) 
                      (A_sg_CK_commutative S r b sgS)
                      (A_sg_CK_left_cancel S r b sgS)    
in 
let not_idem := bop_cancellative_implies_not_idempotent S r b 
                   (A_eqv_nontrivial S r eqvS)
                   (A_eqv_reflexive S r eqvS)  
                   (A_eqv_symmetric S r eqvS) 
                   (A_eqv_transitive S r eqvS) 
                   (A_sg_CK_associative S r b sgS)
                   (A_sg_CK_congruence S r b sgS)
                   (A_sg_CK_left_cancel S r b sgS)    
                   right_cancel 
                   (A_sg_CK_exists_id_d S r b sgS)
in 
{|
  A_sg_C_associative      := A_sg_CK_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CK_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CK_commutative S r b sgS
; A_sg_C_selective_d      := inr _ (bop_not_idempotent_implies_not_selective S r b not_idem)
; A_sg_C_idempotent_d     := inr _ not_idem 
; A_sg_C_exists_id_d      := A_sg_CK_exists_id_d S r b sgS    
; A_sg_C_exists_ann_d     := inr (bop_left_cancellative_implies_not_exists_ann S r b 
                                    (A_eqv_symmetric S r eqvS) 
                                    (A_eqv_transitive S r eqvS) 
                                    (A_eqv_nontrivial S r eqvS) 
                                    (A_sg_CK_left_cancel S r b sgS)    
                                 )
; A_sg_C_left_cancel_d    := inl _ (A_sg_CK_left_cancel S r b sgS)    
; A_sg_C_right_cancel_d   := inl _ right_cancel 
; A_sg_C_left_constant_d  := inr _ (bop_left_cancellative_implies_not_left_constant S r b 
                                       (A_eqv_nontrivial S r eqvS) 
                                       (A_sg_CK_left_cancel S r b sgS)    
                                   )
; A_sg_C_right_constant_d := inr _ (bop_right_cancellative_implies_not_right_constant S r b 
                                       (A_eqv_nontrivial S r eqvS) 
                                       right_cancel    
                                   )
; A_sg_C_anti_left_d      := A_sg_CK_anti_left_d S r b sgS 
; A_sg_C_anti_right_d     := A_sg_CK_anti_right_d S r b sgS
|}. 



Definition A_sg_C_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv         := A_sg_CK_eqv S sgS
   ; A_sg_C_bop         := A_sg_CK_bop S sgS
   ; A_sg_C_proofs      := A_sg_C_proofs_from_sg_CK_proofs S 
                            (A_eqv_eq S (A_sg_CK_eqv S sgS)) 
                            (A_sg_CK_bop S sgS)  
                            (A_eqv_proofs S (A_sg_CK_eqv S sgS)) 
                            (A_sg_CK_proofs S sgS) 
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CK (A_sg_CK_ast S sgS)
   |}. 




(* DERIVED UPCASTS *) 

Definition A_sg_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CI S sgS).  

Definition A_sg_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CK S sgS).  

Definition A_sg_C_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_C S 
:= λ S sgS, A_sg_C_from_sg_CI S (A_sg_CI_from_sg_CS S sgS ). 

Definition A_sg_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CS S sgS).  


(* finish someday .... 
Definition A_sg_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CI_proofs S r b -> sg_proofs S r b 
:= λ S r b sgS, A_sg_proofs_from_sg_C_proofs S r b (A_sg_C_proofs_from_sg_CI_proofs S r b sgS).  


Definition A_sg_proofs_from_csg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CK_proofs S r b -> sg_proofs S r b 
:= λ S r b sgS, A_sg_proofs_from_sg_C_proofs S r b (A_sg_C_proofs_from_sg_CK_proofs S r b sgS).  

Definition A_sg_C_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S),  sg_CS_proofs S r b -> sg_C_proofs S r b
:= λ S r b sg_CSS, A_sg_C_proofs_from_sg_CI_proofs S r b (A_sg_CI_proofs_from_sg_CS_proofs S r b sg_CSS ). 

Definition A_sg_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CS_proofs S r b -> sg_proofs S r b 
:= λ S r b sg_CSS, A_sg_proofs_from_sg_C_proofs S r b (A_sg_C_proofs_from_sg_CS_proofs S r b sg_CSS).

*) 


(* DOWNCASTS *) 

Definition A_sg_C_proofs_option_from_sg_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_proofs S r b -> option (sg_C_proofs S r b) 
:= λ S r b sgS, 
   match A_sg_commutative_d S r b sgS with 
   | inl comm  => Some
      {|
        A_sg_C_associative   := A_sg_associative S r b sgS    
      ; A_sg_C_congruence    := A_sg_congruence S r b sgS    
      ; A_sg_C_commutative   := comm 
      ; A_sg_C_selective_d   := A_sg_selective_d S r b sgS    
      ; A_sg_C_idempotent_d  := A_sg_idempotent_d S r b sgS    
      ; A_sg_C_exists_id_d   := A_sg_exists_id_d S r b sgS    
      ; A_sg_C_exists_ann_d  := A_sg_exists_ann_d S r b sgS    
      ; A_sg_C_left_cancel_d    := A_sg_left_cancel_d S r b sgS    
      ; A_sg_C_right_cancel_d   := A_sg_right_cancel_d S r b sgS    
      ; A_sg_C_left_constant_d  := A_sg_left_constant_d S r b sgS
      ; A_sg_C_right_constant_d := A_sg_right_constant_d S r b sgS
      ; A_sg_C_anti_left_d      := A_sg_anti_left_d  S r b sgS
      ; A_sg_C_anti_right_d     := A_sg_anti_right_d S r b sgS
     |}
   | _ => None
   end . 


Definition A_sg_C_option_from_sg: ∀ (S : Type),  A_sg S -> option (A_sg_C S) 
:= λ S sgS, 
   match A_sg_C_proofs_option_from_sg_proofs S _ _ (A_sg_proofs S sgS) with 
   | None => None
   | Some proofs => Some
      {| 
        A_sg_C_eqv         := A_sg_eq S sgS
      ; A_sg_C_bop         := A_sg_bop S sgS
      ; A_sg_C_proofs      := proofs 
      ; A_sg_C_ast         := Ast_sg_C_from_sg (A_sg_ast S sgS)
      |}
   end. 


Definition A_sg_CI_proofs_option_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_C_proofs S r b -> option (sg_CI_proofs S r b) 
:= λ S r b sgS, 
   match A_sg_C_idempotent_d S r b sgS with 
   | inl idem => Some
      {|
        A_sg_CI_associative        := A_sg_C_associative S r b sgS    
      ; A_sg_CI_congruence         := A_sg_C_congruence S r b sgS    
      ; A_sg_CI_commutative        := A_sg_C_commutative S r b sgS    
      ; A_sg_CI_idempotent         := idem 
      ; A_sg_CI_selective_d        := A_sg_C_selective_d S r b sgS    
      ; A_sg_CI_exists_id_d        := A_sg_C_exists_id_d S r b sgS    
      ; A_sg_CI_exists_ann_d       := A_sg_C_exists_ann_d S r b sgS    
     |}
   |  _ => None
   end . 


Definition A_sg_CI_option_from_sg_C: ∀ (S : Type),  A_sg_C S -> option (A_sg_CI S) 
:= λ S sgS, 
   match A_sg_CI_proofs_option_from_sg_C_proofs S _ _ (A_sg_C_proofs S sgS) with 
   | None => None
   | Some proofs => Some
      {| 
        A_sg_CI_eqv         := A_sg_C_eqv S sgS
      ; A_sg_CI_bop         := A_sg_C_bop S sgS
      ; A_sg_CI_proofs      := proofs 
      ; A_sg_CI_ast         := Ast_sg_CI_from_sg_C (A_sg_C_ast S sgS)
      |}
   end. 

Definition A_sg_CS_proofs_option_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CI_proofs S r b -> option (sg_CS_proofs S r b) 
:= λ S r b sgS, 
   match A_sg_CI_selective_d S r b sgS with 
   | inl sel => Some
      {|
        A_sg_CS_associative   := A_sg_CI_associative S r b sgS    
      ; A_sg_CS_congruence    := A_sg_CI_congruence S r b sgS    
      ; A_sg_CS_commutative   := A_sg_CI_commutative S r b sgS    
      ; A_sg_CS_selective     := sel 
      ; A_sg_CS_exists_id_d   := A_sg_CI_exists_id_d S r b sgS    
      ; A_sg_CS_exists_ann_d  := A_sg_CI_exists_ann_d S r b sgS    
     |}
   | _ => None
   end . 

Definition A_sg_CS_option_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> option (A_sg_CS S) 
:= λ S sgS, 
   match A_sg_CS_proofs_option_from_sg_CI_proofs S _ _ (A_sg_CI_proofs S sgS) with 
   | None => None
   | Some proofs => Some
      {| 
        A_sg_CS_eqv         := A_sg_CI_eqv S sgS
      ; A_sg_CS_bop         := A_sg_CI_bop S sgS
      ; A_sg_CS_proofs      := proofs 
      ; A_sg_CS_ast         := Ast_sg_CS_from_sg_CI (A_sg_CI_ast S sgS)
      |}
   end. 


Definition A_sg_CK_proofs_option_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_C_proofs S r b -> option (sg_CK_proofs S r b) 
:= λ S r b sgS, 
   match A_sg_C_left_cancel_d S r b sgS with 
   | inl lcS => Some
      {|
        A_sg_CK_associative        := A_sg_C_associative S r b sgS    
      ; A_sg_CK_congruence         := A_sg_C_congruence S r b sgS    
      ; A_sg_CK_commutative        := A_sg_C_commutative S r b sgS    
      ; A_sg_CK_left_cancel        := lcS 
      ; A_sg_CK_exists_id_d        := A_sg_C_exists_id_d S r b sgS    
      ; A_sg_CK_anti_left_d        := A_sg_C_anti_left_d S r b sgS   
      ; A_sg_CK_anti_right_d       := A_sg_C_anti_right_d S r b sgS   
     |}
   |  _ => None
   end . 


Definition A_sg_CK_option_from_sg_C: ∀ (S : Type),  A_sg_C S -> option (A_sg_CK S) 
:= λ S sgS, 
   match A_sg_CK_proofs_option_from_sg_C_proofs S _ _ (A_sg_C_proofs S sgS) with 
   | None => None
   | Some proofs => Some
      {| 
        A_sg_CK_eqv         := A_sg_C_eqv S sgS
      ; A_sg_CK_bop         := A_sg_C_bop S sgS
      ; A_sg_CK_proofs      := proofs 
      ; A_sg_CK_ast         := Ast_sg_CK_from_sg_C (A_sg_C_ast S sgS)
      |}
   end. 


(* DERIVED DOWNCASTS *) 

Definition A_sg_CI_option_from_sg: ∀ (S : Type),  A_sg S -> option (A_sg_CI S) 
:= λ S sgS, 
   match A_sg_C_option_from_sg S sgS with 
   | None => None
   | Some sgS => A_sg_CI_option_from_sg_C S sgS 
   end. 


Definition A_sg_CK_option_from_sg: ∀ (S : Type),  A_sg S -> option (A_sg_CK S) 
:= λ S sgS, 
   match A_sg_C_option_from_sg S sgS with 
   | None => None
   | Some sgS => A_sg_CK_option_from_sg_C S sgS 
   end. 


Definition A_sg_CS_option_from_sg_C : ∀ (S : Type),  A_sg_C S -> option (A_sg_CS S) 
:= λ S sgS, 
   match A_sg_CI_option_from_sg_C S sgS with 
   | None => None
   | Some sgS => A_sg_CS_option_from_sg_CI S sgS 
   end. 


Definition A_sg_CS_option_from_sg: ∀ (S : Type),  A_sg S -> option (A_sg_CS S) 
:= λ S sgS, 
   match A_sg_CI_option_from_sg S sgS with 
   | None => None
   | Some sgS => A_sg_CS_option_from_sg_CI S sgS 
   end. 


(* ******************************************************************

SG SG 

****************************************************************** *) 

(* UPCAST *) 

Definition A_sg_sg_from_sg_C_sg : ∀ (S : Type),  A_sg_C_sg S -> A_sg_sg S 
:= λ S s, 
{| 
  A_sg_sg_eqv          := A_sg_C_sg_eqv S s
; A_sg_sg_plus         := A_sg_C_sg_plus S s
; A_sg_sg_times        := A_sg_C_sg_times S s
; A_sg_sg_plus_proofs  := A_sg_proofs_from_sg_C_proofs S 
                            (A_eqv_eq S (A_sg_C_sg_eqv S s))
                            (A_sg_C_sg_plus S s)
                            (A_eqv_proofs S (A_sg_C_sg_eqv S s)) 
                            (A_sg_C_sg_plus_proofs S s)  
; A_sg_sg_times_proofs := A_sg_C_sg_times_proofs S s
; A_sg_sg_proofs       := A_sg_C_sg_proofs S s 
; A_sg_sg_ast          := Ast_sg_sg_from_sg_C_sg (A_sg_C_sg_ast S s)
|}. 




Definition A_sg_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CS_proofs S r b -> sg_proofs S r b 
:= λ S r b eqvS sgS,  
    A_sg_proofs_from_sg_C_proofs S r b eqvS
      (A_sg_C_proofs_from_sg_CI_proofs S r b eqvS 
         (A_sg_CI_proofs_from_sg_CS_proofs S r b sgS)).  


Definition A_sg_proofs_from_sg_CK_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CK_proofs S r b -> sg_proofs S r b 
:= λ S r b eqvS sgS,  
    A_sg_proofs_from_sg_C_proofs S r b eqvS
         (A_sg_C_proofs_from_sg_CK_proofs S r b eqvS sgS).  


Definition A_sg_C_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CS_proofs S r b -> sg_C_proofs S r b 
:= λ S r b eqvS sgS,  
      A_sg_C_proofs_from_sg_CI_proofs S r b eqvS 
         (A_sg_CI_proofs_from_sg_CS_proofs S r b sgS).  

Definition A_sg_C_sg_from_sg_CS_sg : ∀ (S : Type),  A_sg_CS_sg S -> A_sg_C_sg S 
:= λ S s, 
{| 
  A_sg_C_sg_eqv          := A_sg_CS_sg_eqv S s
; A_sg_C_sg_plus         := A_sg_CS_sg_plus S s
; A_sg_C_sg_times        := A_sg_CS_sg_times S s
; A_sg_C_sg_plus_proofs  := A_sg_C_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_sg_eqv S s))
                            (A_sg_CS_sg_plus S s)
                            (A_eqv_proofs S (A_sg_CS_sg_eqv S s)) 
                            (A_sg_CS_sg_plus_proofs S s)  
; A_sg_C_sg_times_proofs := A_sg_CS_sg_times_proofs S s
; A_sg_C_sg_proofs       := A_sg_CS_sg_proofs S s 
; A_sg_C_sg_ast          := Ast_sg_C_sg_from_sg_CS_sg (A_sg_CS_sg_ast S s)
|}. 


Definition A_sg_sg_from_sg_CS_sg : ∀ (S : Type),  A_sg_CS_sg S -> A_sg_sg S 
:= λ S s, A_sg_sg_from_sg_C_sg S (A_sg_C_sg_from_sg_CS_sg S s). 

Definition A_sg_sg_proofs_from_sg_sg_LD_proofs : 
   ∀ (S : Type) (eq : brel S) (plus : binary_op S) (times : binary_op S), 
        brel_transitive S eq -> 
        bop_congruence S eq plus -> 
        bop_commutative S eq plus -> 
        bop_commutative S eq times -> 
       sg_sg_LD_proofs S eq plus times -> sg_sg_proofs S eq plus times
:= λ S eq plus times transS congP commP commT s,  
{|
  A_sg_sg_left_distributive_d    := inl _ (A_sg_sg_LD_left_distributive S eq plus times s) 
; A_sg_sg_right_distributive_d   := inl _ (bop_left_distributive_implies_right S eq plus times
                                              transS congP commP commT
                                              (A_sg_sg_LD_left_distributive S eq plus times s))

; A_sg_sg_left_absorption_d      := A_sg_sg_LD_left_absorption_d S eq plus times s
; A_sg_sg_right_absorption_d     := A_sg_sg_LD_right_absorption_d S eq plus times s

; A_sg_sg_plus_id_is_times_ann_d := A_sg_sg_LD_plus_id_is_times_ann_d S eq plus times s
; A_sg_sg_times_id_is_plus_ann_d := A_sg_sg_LD_times_id_is_plus_ann_d S eq plus times s
|}. 


Definition A_sg_sg_proofs_from_sg_sg_LA_proofs : 
   ∀ (S : Type) (eq : brel S) (plus : binary_op S) (times : binary_op S), 
        brel_reflexive S eq -> 
        brel_transitive S eq -> 
        bop_congruence S eq plus -> 
        bop_commutative S eq times -> 
       sg_sg_LA_proofs S eq plus times -> sg_sg_proofs S eq plus times
:= λ S eq plus times refS transS congP commT s,  
{|
  A_sg_sg_left_distributive_d    := A_sg_sg_LA_left_distributive_d S eq plus times s 
; A_sg_sg_right_distributive_d   := A_sg_sg_LA_right_distributive_d S eq plus times s

; A_sg_sg_left_absorption_d      := inl _ (A_sg_sg_LA_left_absorption S eq plus times s)
; A_sg_sg_right_absorption_d     := inl _ (bops_left_absorption_and_times_commutative_imply_right_absorption S eq plus times
                                              refS transS congP commT
                                              (A_sg_sg_LA_left_absorption S eq plus times s))

; A_sg_sg_plus_id_is_times_ann_d := A_sg_sg_LA_plus_id_is_times_ann_d S eq plus times s
; A_sg_sg_times_id_is_plus_ann_d := A_sg_sg_LA_times_id_is_plus_ann_d S eq plus times s
|}. 


Definition A_sg_sg_proofs_from_sg_sg_LALD_proofs : 
   ∀ (S : Type) (eq : brel S) (plus : binary_op S) (times : binary_op S), 
        brel_reflexive S eq -> 
        brel_transitive S eq -> 
        bop_congruence S eq plus -> 
        bop_commutative S eq plus -> 
        bop_commutative S eq times -> 
       sg_sg_LALD_proofs S eq plus times -> sg_sg_proofs S eq plus times
:= λ S eq plus times refS transS congP commP commT s,  
{|
  A_sg_sg_left_distributive_d    := inl _ (A_sg_sg_LALD_left_distributive S eq plus times s) 
; A_sg_sg_right_distributive_d   := inl _ (bop_left_distributive_implies_right S eq plus times
                                              transS congP commP commT
                                              (A_sg_sg_LALD_left_distributive S eq plus times s))


; A_sg_sg_left_absorption_d      := inl _ (A_sg_sg_LALD_left_absorption S eq plus times s)
; A_sg_sg_right_absorption_d     := inl _ (bops_left_absorption_and_times_commutative_imply_right_absorption S eq plus times
                                              refS transS congP commT
                                              (A_sg_sg_LALD_left_absorption S eq plus times s))

; A_sg_sg_plus_id_is_times_ann_d := A_sg_sg_LALD_plus_id_is_times_ann_d S eq plus times s
; A_sg_sg_times_id_is_plus_ann_d := A_sg_sg_LALD_times_id_is_plus_ann_d S eq plus times s
|}. 





Definition A_sg_CS_sg_from_sg_CS_sg_CK_AD : ∀ (S : Type),  A_sg_CS_sg_CK_AD S -> A_sg_CS_sg S 
:= λ S s,  
{|
  A_sg_CS_sg_eqv          := A_sg_CS_sg_CK_AD_eqv S s 
; A_sg_CS_sg_plus         := A_sg_CS_sg_CK_AD_plus S s 
; A_sg_CS_sg_times        := A_sg_CS_sg_CK_AD_times S s 
; A_sg_CS_sg_plus_proofs  := A_sg_CS_sg_CK_AD_plus_proofs S s  
; A_sg_CS_sg_times_proofs := A_sg_proofs_from_sg_CK_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                (A_sg_CS_sg_CK_AD_times S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CK_AD_eqv S s))
                                (A_sg_CS_sg_CK_AD_times_proofs S s) 
; A_sg_CS_sg_proofs       := A_sg_sg_proofs_from_sg_sg_LALD_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                (A_sg_CS_sg_CK_AD_plus S s)
                                (A_sg_CS_sg_CK_AD_times S s)
                                (A_eqv_reflexive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CK_AD_eqv S s))) 
                                (A_eqv_transitive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CK_AD_eqv S s))) 
                                (A_sg_CS_congruence S _ _ (A_sg_CS_sg_CK_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CK_AD_plus_proofs S s)) 
                                (A_sg_CK_commutative S _ _ (A_sg_CS_sg_CK_AD_times_proofs S s))
                                (A_sg_CS_sg_CK_AD_proofs S s)  
; A_sg_CS_sg_ast          :=  Ast_sg_CS_sg_from_sg_CS_sg_CK_AD (A_sg_CS_sg_CK_AD_ast S s)  
|}.




Definition A_sg_C_sg_from_sg_CS_sg_CS_AD : ∀ (S : Type),  A_sg_CS_sg_CS_AD S -> A_sg_C_sg S 
:= λ S s,  
{|
  A_sg_C_sg_eqv          := A_sg_CS_sg_CS_AD_eqv S s 
; A_sg_C_sg_plus         := A_sg_CS_sg_CS_AD_plus S s 
; A_sg_C_sg_times        := A_sg_CS_sg_CS_AD_times S s 
; A_sg_C_sg_plus_proofs  := A_sg_C_proofs_from_sg_CS_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus_proofs S s)  
; A_sg_C_sg_times_proofs := A_sg_proofs_from_sg_CS_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_times S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_times_proofs S s) 
; A_sg_C_sg_proofs       := A_sg_sg_proofs_from_sg_sg_LALD_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus S s)
                                (A_sg_CS_sg_CS_AD_times S s)
                                (A_eqv_reflexive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s)))
                                (A_eqv_transitive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s)))
                                (A_sg_CS_congruence S _ _ (A_sg_CS_sg_CS_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CS_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CS_AD_times_proofs S s))
                                (A_sg_CS_sg_CS_AD_proofs S s)  
; A_sg_C_sg_ast          :=  Ast_sg_C_sg_from_sg_CS_sg_CS_AD (A_sg_CS_sg_CS_AD_ast S s)  
|}.


Definition A_sg_CS_sg_from_sg_CS_sg_CS_AD : ∀ (S : Type),  A_sg_CS_sg_CS_AD S -> A_sg_CS_sg S 
:= λ S s,  
{|
  A_sg_CS_sg_eqv          := A_sg_CS_sg_CS_AD_eqv S s 
; A_sg_CS_sg_plus         := A_sg_CS_sg_CS_AD_plus S s 
; A_sg_CS_sg_times        := A_sg_CS_sg_CS_AD_times S s 
; A_sg_CS_sg_plus_proofs  := A_sg_CS_sg_CS_AD_plus_proofs S s  
; A_sg_CS_sg_times_proofs := A_sg_proofs_from_sg_CS_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_times S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_times_proofs S s) 
; A_sg_CS_sg_proofs       := A_sg_sg_proofs_from_sg_sg_LALD_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus S s)
                                (A_sg_CS_sg_CS_AD_times S s)
                                (A_eqv_reflexive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))) 
                                (A_eqv_transitive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))) 
                                (A_sg_CS_congruence S _ _ (A_sg_CS_sg_CS_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CS_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CS_AD_times_proofs S s))
                                (A_sg_CS_sg_CS_AD_proofs S s)  
; A_sg_CS_sg_ast          :=  Ast_sg_CS_sg_from_sg_CS_sg_CS_AD (A_sg_CS_sg_CS_AD_ast S s)  
|}.


