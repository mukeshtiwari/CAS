Require Import CAS.code.basic_types. 
Require Import CAS.theory.properties.

(* eqv *) 
Record eqv_proofs (S : Type) (eq : brel S) := {
  A_eqv_nontrivial  : brel_nontrivial S eq          
; A_eqv_congruence  : brel_congruence S eq eq  
; A_eqv_reflexive   : brel_reflexive S eq            
; A_eqv_transitive  : brel_transitive S eq           
; A_eqv_symmetric   : brel_symmetric S eq            
}.

(* semigroups *) 

Record sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required *) 
  A_sg_associative      : bop_associative S eq bop 
; A_sg_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sg_commutative_d    : bop_commutative_decidable S eq bop  
; A_sg_selective_d      : bop_selective_decidable S eq bop  
; A_sg_idempotent_d     : bop_idempotent_decidable S eq bop  
; A_sg_exists_id_d      : bop_exists_id_decidable S eq bop 
; A_sg_exists_ann_d     : bop_exists_ann_decidable S eq bop 

(* needed to decide selectivity of product *) 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  

(* needed (directly or indirectly) to decide distributivity of lex *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop 
}. 


Definition bop_commutative_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * S) & 
          match p with 
            inl _      => bop_commutative S r b 
          | inr (s, t) => r (b s t) (b t s) = false
          end }.


Definition bop_selective_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * S) & 
          match p with 
            inl _      => bop_selective S r b 
          | inr (s, t) => (r (b s t) s = false)  * (r (b s t) t = false)
          end }.


Definition bop_idempotent_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + S & 
          match p with 
            inl _ => bop_idempotent S r b 
          | inr s => r (b s s) s = false
          end }.


Definition bop_exists_id_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : S + unit & 
          match p with 
            inl s => bop_is_id S r b s 
          | inr _ => bop_not_exists_id S r b 
          end }.



Definition bop_exists_ann_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : S + unit & 
          match p with 
            inl s => bop_is_ann S r b s 
          | inr _ => bop_not_exists_ann S r b 
          end }.


Definition bop_is_left_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * S) & 
          match p with 
            inl _      => bop_is_left S r b 
          | inr (s, t) => r (b s t) s = false
          end }.


Definition bop_is_right_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * S) & 
          match p with 
            inl _      => bop_is_right S r b 
          | inr (s, t) => r (b s t) t = false
          end }.


Definition bop_left_cancellative_decidable_new (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * (S * S)) & 
          match p with 
            inl _           => bop_left_cancellative S r b 
          | inr (s, (t, u)) => (r (b s t) (b s u) = true) * (r t u = false)
          end }.


Definition bop_right_cancellative_decidable_new (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * (S * S)) & 
          match p with 
            inl _           => bop_right_cancellative S r b 
          | inr (s, (t, u)) => (r (b t s) (b u s) = true) * (r t u = false)
          end }.


Definition bop_left_constant_decidable_new (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * (S * S)) & 
          match p with 
            inl _           => bop_left_constant S r b 
          | inr (s, (t, u)) =>  r (b s t) (b s u) = false 
          end }.

Definition bop_right_constant_decidable_new (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * (S * S)) & 
          match p with 
            inl _           => bop_right_constant S r b 
          | inr (s, (t, u)) =>  r (b t s) (b u s) = false
          end }.


Definition bop_anti_left_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * S) & 
          match p with 
            inl _      => bop_anti_left S r b 
          | inr (s, t) => r s (b s t) = true
          end }.


Definition bop_anti_right_decidable_new  (S : Type) (r : brel S) (b : binary_op S) := 
    { p : unit + (S * S) & 
          match p with 
            inl _      => bop_anti_right S r b 
          | inr (s, t) => r s (b t s) = true 
          end }.

Record sg_proofs_new (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required *) 
  A_sgn_associative      : bop_associative S eq bop 
; A_sgn_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sgn_commutative_d    : bop_commutative_decidable_new S eq bop  
; A_sgn_selective_d      : bop_selective_decidable_new S eq bop  
; A_sgn_idempotent_d     : bop_idempotent_decidable_new S eq bop  
; A_sgn_exists_id_d      : bop_exists_id_decidable_new S eq bop 
; A_sgn_exists_ann_d     : bop_exists_ann_decidable_new S eq bop 

(* needed to decide selectivity of product *) 
; A_sgn_is_left_d        : bop_is_left_decidable_new S eq bop  
; A_sgn_is_right_d       : bop_is_right_decidable_new S eq bop  

(* needed (directly or indirectly) to decide distributivity of lex *) 
; A_sgn_left_cancel_d    : bop_left_cancellative_decidable_new S eq bop 
; A_sgn_right_cancel_d   : bop_right_cancellative_decidable_new S eq bop 

; A_sgn_left_constant_d  : bop_left_constant_decidable_new S eq bop 
; A_sgn_right_constant_d : bop_right_constant_decidable_new S eq bop 

; A_sgn_anti_left_d      : bop_anti_left_decidable_new S eq bop 
; A_sgn_anti_right_d     : bop_anti_right_decidable_new S eq bop 
}. 





Record sg_C_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_C_associative      : bop_associative S eq bop 
; A_sg_C_congruence       : bop_congruence S eq bop   
; A_sg_C_commutative      : bop_commutative S eq bop  
; A_sg_C_selective_d      : bop_selective_decidable S eq bop  
; A_sg_C_idempotent_d     : bop_idempotent_decidable S eq bop  
; A_sg_C_exists_id_d      : bop_exists_id_decidable S eq bop 
; A_sg_C_exists_ann_d     : bop_exists_ann_decidable S eq bop 
; A_sg_C_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_C_right_cancel_d   : bop_right_cancellative_decidable S eq bop 
; A_sg_C_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_C_right_constant_d : bop_right_constant_decidable S eq bop 
; A_sg_C_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_C_anti_right_d     : bop_anti_right_decidable S eq bop 
}. 


Record sg_CS_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CS_associative        : bop_associative S eq bop 
; A_sg_CS_congruence         : bop_congruence S eq bop   
; A_sg_CS_commutative        : bop_commutative S eq bop  
; A_sg_CS_selective          : bop_selective S eq bop  
; A_sg_CS_exists_id_d        : bop_exists_id_decidable S eq bop 
; A_sg_CS_exists_ann_d       : bop_exists_ann_decidable S eq bop 
}. 

Record sg_CI_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CI_associative        : bop_associative S eq bop 
; A_sg_CI_congruence         : bop_congruence S eq bop   
; A_sg_CI_commutative        : bop_commutative S eq bop  
; A_sg_CI_idempotent         : bop_idempotent S eq bop  
; A_sg_CI_selective_d        : bop_selective_decidable S eq bop  
; A_sg_CI_exists_id_d        : bop_exists_id_decidable S eq bop 
; A_sg_CI_exists_ann_d       : bop_exists_ann_decidable S eq bop 
}. 

Record sg_CK_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CK_associative        : bop_associative S eq bop 
; A_sg_CK_congruence         : bop_congruence S eq bop   
; A_sg_CK_commutative        : bop_commutative S eq bop  
; A_sg_CK_left_cancel        : bop_left_cancellative S eq bop  
; A_sg_CK_exists_id_d        : bop_exists_id_decidable S eq bop 
; A_sg_CK_anti_left_d        : bop_anti_left_decidable S eq bop 
; A_sg_CK_anti_right_d       : bop_anti_right_decidable S eq bop 
}. 

(* sg_sg = bi-semigroup 
*) 

(* 
Record sg_sg_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_left_distributive_plus_times_d  : bop_left_distributive_decidable S eq plus times 
; A_sg_sg_right_distributive_plus_times_d : bop_right_distributive_decidable S eq plus times 
; A_sg_sg_left_distributive_times_plus_d  : bop_left_distributive_decidable S eq times plus 
; A_sg_sg_right_distributive_times_plus_d : bop_right_distributive_decidable S eq times plus 

; A_sg_sg_left_absorption_plus_times_d   : bops_left_absorption_decidable S eq plus times 
; A_sg_sg_right_absorption_plus_times_d  : bops_right_absorption_decidable S eq plus times 
; A_sg_sg_left_absorption_times_plus_d   : bops_left_absorption_decidable S eq times plus 
; A_sg_sg_right_absorption_times_plus_d  : bops_right_absorption_decidable S eq times plus 

; A_sg_sg_id_is_ann_plus_times_d         : bops_id_equals_ann_decidable S eq plus times 
; A_sg_sg_id_is_ann_times_plus_d         : bops_id_equals_ann_decidable S eq times plus 
; A_sg_sg_id_is_id_plus_times_d          : bops_id_equals_id_decidable S eq plus times 
; A_sg_sg_ann_is_ann_plus_times_d        : bops_ann_equals_ann_decidable S eq plus times 
}. 
*) 




Record sg_sg_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_left_distributive_d    : bop_left_distributive_decidable S eq plus times 
; A_sg_sg_right_distributive_d   : bop_right_distributive_decidable S eq plus times 

; A_sg_sg_left_absorption_d      : bops_left_absorption_decidable S eq plus times 
; A_sg_sg_right_absorption_d     : bops_right_absorption_decidable S eq plus times 

; A_sg_sg_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_sg_sg_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus 
}. 


Record sg_sg_LD_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_LD_left_distributive      : bop_left_distributive S eq plus times 
; A_sg_sg_LD_left_absorption_d      : bops_left_absorption_decidable S eq plus times 
; A_sg_sg_LD_right_absorption_d     : bops_right_absorption_decidable S eq plus times 
; A_sg_sg_LD_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_sg_sg_LD_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus
}. 

Record sg_sg_LA_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_LA_left_distributive_d    : bop_left_distributive_decidable S eq plus times 
; A_sg_sg_LA_right_distributive_d   : bop_right_distributive_decidable S eq plus times 
; A_sg_sg_LA_left_absorption        : bops_left_absorption S eq plus times 
; A_sg_sg_LA_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_sg_sg_LA_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus
}. 

Record sg_sg_LALD_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_LALD_left_distributive      : bop_left_distributive S eq plus times 
; A_sg_sg_LALD_left_absorption        : bops_left_absorption S eq plus times 
; A_sg_sg_LALD_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_sg_sg_LALD_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus
}. 

(*
Record sg_sg_D_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_D_left_distributive      : bop_left_distributive S eq plus times 
; A_sg_sg_D_right_distributive     : bop_right_distributive S eq plus times 
; A_sg_sg_D_plus_id_is_times_ann_d : bops_id_equals_ann_decidable S eq plus times 
; A_sg_sg_D_times_id_is_plus_ann_d : bops_id_equals_ann_decidable S eq times plus
}. 


(* B = Bounded  *) 
Record sg_sg_BD_proofs (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_sg_sg_BD_left_distributive    : bop_left_distributive S eq plus times 
; A_sg_sg_BD_right_distributive   : bop_right_distributive S eq plus times 
; A_sg_sg_BD_plus_id_is_times_ann : bops_id_equals_ann S eq plus times 
; A_sg_sg_BD_times_id_is_plus_ann : bops_id_equals_ann S eq times plus
}. 


(* orders *) 
Record po_proofs (S: Type) (eq : brel S) (r : brel S) := {
(*   A_po_not_trivial   : brel_not_trivial S r *) 
  A_po_congruence    : brel_congruence S eq r  
; A_po_reflexive     : brel_reflexive S r
; A_po_transitive    : brel_transitive S r
; A_po_antisymmetric : brel_antisymmetric S eq r 
; A_po_total_d       : brel_total_decidable S r 
}. 

Record to_proofs (S: Type) (eq : brel S) (r : brel S) := {
(*   A_to_not_trivial   : brel_not_trivial S *) 
  A_to_congruence    : brel_congruence S eq r  
; A_to_reflexive     : brel_reflexive S r
; A_to_transitive    : brel_transitive S r
; A_to_antisymmetric : brel_antisymmetric S eq r 
; A_to_total         : brel_total S r 
}. 


(*

*) 


*) 