Require Import CAS.code.basic_types. 


(* 
Inductive certify_not_true {S : Type} := 
| Certify_Not_True : S → S → certify_not_true S. 

Inductive certify_not_false {S : Type} := 
| Certify_Not_False : S → S → certify_not_false S. 

Record assert_not_trivial {S : Type} := {
  certify_not_trivial_not_true  : certify_not_true S
; certify_not_trivial_not_false : certify_not_false S 
}. 
*)  
(*
Inductive certify_witness {S : Type} := 
| Certify_Witness : S → certify_witness (S := S). 

Inductive certify_negate {S : Type} := 
| Certify_Negate : (S → S) → certify_negate (S := S).  

Record assert_nontrivial {S : Type} := {
  certify_nontrivial_witness : certify_witness (S := S) 
; certify_nontrivial_negate  : certify_negate (S := S) 
}. 
 *)

Inductive assert_brel_congruence {S : Type} := 
| Assert_Brel_Congruence : assert_brel_congruence (S := S). 

Inductive assert_reflexive {S : Type} := 
| Assert_Reflexive : assert_reflexive (S := S). 

Inductive check_reflexive {S : Type} := 
| Certify_Reflexive : check_reflexive (S := S)
| Certify_Not_Reflexive : S → check_reflexive (S := S). 

Inductive assert_irreflexive {S : Type} := 
| Assert_Irreflexive : assert_irreflexive (S := S). 

Inductive check_irreflexive {S : Type} := 
| Certify_Irreflexive : check_irreflexive (S := S)
| Certify_Not_Irreflexive : S → check_irreflexive (S := S).  

Inductive assert_transitive {S : Type} := 
| Assert_Transitive : assert_transitive (S := S). 

Inductive check_transitive {S : Type} := 
| Certify_Transitive : check_transitive (S := S)
| Certify_Not_Transitive : (S * (S * S)) → check_transitive (S := S). 

Inductive assert_symmetric {S : Type} := 
| Assert_Symmetric : assert_symmetric (S := S). 

Inductive check_symmetric {S : Type} := 
| Certify_Symmetric : check_symmetric (S := S)
| Certify_Not_Symmetric : (S * S) → check_symmetric (S := S). 

Inductive assert_antisymmetric {S : Type} := 
| Assert_Antisymmetric : assert_antisymmetric (S := S). 

Inductive check_antisymmetric {S : Type} := 
| Certify_Antisymmetric : check_antisymmetric (S := S)
| Certify_Not_Antisymmetric : (S * S) → check_antisymmetric (S := S). 

Inductive assert_asymmetric {S : Type} := 
| Assert_Asymmetric : assert_asymmetric (S := S). 

Inductive check_asymmetric {S : Type} := 
| Certify_Asymmetric : check_asymmetric (S := S)
| Certify_Not_Asymmetric : (S * S) → check_asymmetric (S := S). 

Inductive assert_total {S : Type} := 
| Assert_Total : assert_total (S := S). 

Inductive check_total {S : Type} := 
| Certify_Total : check_total (S := S)
| Certify_Not_Total : (S * S) → check_total (S := S). 

(* some useful functions 

Definition get_witness :  ∀ {S : Type},  certify_witness (S := S) -> S 
:= λ {S} cwS, 
   match cwS with  
   | Certify_Witness s => s 
   end. 

Definition get_negate :  ∀ {S : Type},  certify_negate (S := S) -> (S -> S)
:= λ {S} cnS, 
   match cnS with  
   | Certify_Negate f => f 
   end. 

Definition nontrivial_witness :  ∀ {S : Type},  assert_nontrivial (S := S) -> S 
:= λ {S} ntS, get_witness (certify_nontrivial_witness ntS). 

Definition nontrivial_negate :  ∀ {S : Type},  assert_nontrivial (S := S) -> (S -> S) 
:= λ {S} ntS, get_negate (certify_nontrivial_negate ntS). 

Definition nontrivial_pair :  ∀ {S : Type},  assert_nontrivial (S := S) -> (S * S) 
:= λ {S} ntS, 
   let w := nontrivial_witness ntS in 
   let f := nontrivial_negate ntS in 
   (w, f w). 

*) 







