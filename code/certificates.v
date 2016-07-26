Require Import CAS.code.basic_types. 


(* 
Inductive certify_not_true (S : Type) := 
| Certify_Not_True : S → S → certify_not_true S. 

Inductive certify_not_false (S : Type) := 
| Certify_Not_False : S → S → certify_not_false S. 

Record assert_not_trivial (S : Type) := {
  certify_not_trivial_not_true  : certify_not_true S
; certify_not_trivial_not_false : certify_not_false S 
}. 
*)  

Inductive certify_witness (S : Type) := 
| Certify_Witness : S → certify_witness S. 

Inductive certify_negate (S : Type) := 
| Certify_Negate : (S → S) → certify_negate S. 

Record assert_nontrivial (S : Type) := {
  certify_nontrivial_witness : certify_witness S
; certify_nontrivial_negate  : certify_negate S 
}. 

Inductive assert_brel_congruence (S : Type) := 
| Assert_Brel_Congruence : assert_brel_congruence S. 

Inductive assert_reflexive (S : Type) := 
| Assert_Reflexive : assert_reflexive S. 

Inductive check_reflexive (S : Type) := 
| Certify_Reflexive : check_reflexive S
| Certify_Not_Reflexive : S → check_reflexive S. 

Inductive assert_irreflexive (S : Type) := 
| Assert_Irreflexive : assert_irreflexive S. 

Inductive check_irreflexive (S : Type) := 
| Certify_Irreflexive : check_irreflexive S
| Certify_Not_Irreflexive : S → check_irreflexive S. 

Inductive assert_transitive (S : Type) := 
| Assert_Transitive : assert_transitive S. 

Inductive check_transitive (S : Type) := 
| Certify_Transitive : check_transitive S
| Certify_Not_Transitive : (S * (S * S)) → check_transitive S. 

Inductive assert_symmetric (S : Type) := 
| Assert_Symmetric : assert_symmetric S. 

Inductive check_symmetric (S : Type) := 
| Certify_Symmetric : check_symmetric S
| Certify_Not_Symmetric : (S * S) → check_symmetric S. 

Inductive assert_antisymmetric (S : Type) := 
| Assert_Antisymmetric : assert_antisymmetric S. 

Inductive check_antisymmetric (S : Type) := 
| Certify_Antisymmetric : check_antisymmetric S
| Certify_Not_Antisymmetric : (S * S) → check_antisymmetric S. 

Inductive assert_asymmetric (S : Type) := 
| Assert_Asymmetric : assert_asymmetric S. 

Inductive check_asymmetric (S : Type) := 
| Certify_Asymmetric : check_asymmetric S
| Certify_Not_Asymmetric : (S * S) → check_asymmetric S. 

Inductive assert_bop_congruence (S : Type) := 
| Assert_Bop_Congruence : assert_bop_congruence S. 

Inductive assert_associative (S : Type) := 
| Assert_Associative : assert_associative S. 

Inductive assert_exists_id (S : Type) := 
| Assert_Exists_Id : S -> assert_exists_id S .

Inductive check_exists_id (S : Type) := 
| Certify_Exists_Id : S -> check_exists_id S 
| Certify_Not_Exists_Id : check_exists_id S.  

Inductive assert_exists_ann (S : Type) := 
| Assert_Exists_Ann : S -> assert_exists_ann S.

Inductive check_exists_ann (S : Type) := 
| Certify_Exists_Ann : S -> check_exists_ann S 
| Certify_Not_Exists_Ann : check_exists_ann S.  


Inductive assert_commutative (S : Type) := 
| Assert_Commutative : assert_commutative S. 

Inductive check_commutative (S : Type) := 
| Certify_Commutative : check_commutative S 
| Certify_Not_Commutative : (S * S) → check_commutative S. 

Inductive assert_idempotent (S : Type) := 
| Assert_Idempotent : assert_idempotent S. 

Inductive assert_not_idempotent (S : Type) := 
| Assert_Not_Idempotent : S → assert_not_idempotent S. 

Inductive check_idempotent (S : Type) := 
| Certify_Idempotent : check_idempotent S
| Certify_Not_Idempotent : S → check_idempotent S. 

Inductive assert_selective (S : Type) := 
| Assert_Selective : assert_selective S .

Inductive check_selective (S : Type) := 
| Certify_Selective : check_selective S 
| Certify_Not_Selective : (S * S) → check_selective S.  

Inductive assert_left_cancellative (S : Type) := 
| Assert_Left_Cancellative : assert_left_cancellative S. 

Inductive assert_not_left_cancellative (S : Type) := 
| Assert_Not_Left_Cancellative : (S * (S * S)) → assert_not_left_cancellative S. 

Inductive check_left_cancellative (S : Type) := 
| Certify_Left_Cancellative : check_left_cancellative S 
| Certify_Not_Left_Cancellative : (S * (S * S)) → check_left_cancellative S. 


Inductive assert_right_cancellative (S : Type) := 
| Assert_Right_Cancellative : assert_right_cancellative S. 

Inductive assert_not_right_cancellative (S : Type) := 
| Assert_Not_Right_Cancellative : (S * (S * S)) → assert_not_right_cancellative S. 

Inductive check_right_cancellative (S : Type) := 
| Certify_Right_Cancellative : check_right_cancellative S 
| Certify_Not_Right_Cancellative : (S * (S * S)) → check_right_cancellative S. 

Inductive assert_left_constant (S : Type) := 
| Assert_Left_Constant : assert_left_constant S. 

Inductive assert_not_left_constant (S : Type) := 
| Assert_Not_Left_Constant : (S * (S * S)) → assert_not_left_constant S. 

Inductive check_left_constant (S : Type) := 
| Certify_Left_Constant : check_left_constant S 
| Certify_Not_Left_Constant : (S * (S * S)) → check_left_constant S. 

Inductive assert_right_constant (S : Type) := 
| Assert_Right_Constant : assert_right_constant S. 

Inductive assert_not_right_constant (S : Type) := 
| Assert_Not_Right_Constant : (S * (S * S)) → assert_not_right_constant S. 

Inductive check_right_constant (S : Type) := 
| Certify_Right_Constant : check_right_constant S 
| Certify_Not_Right_Constant : (S * (S * S)) → check_right_constant S. 

Inductive assert_anti_left (S : Type) := 
| Assert_Anti_Left : assert_anti_left S. 

Inductive assert_not_anti_left (S : Type) := 
| Assert_Not_Anti_Left : (S * S) → assert_not_anti_left S. 

Inductive check_anti_left (S : Type) := 
| Certify_Anti_Left : check_anti_left S 
| Certify_Not_Anti_Left : (S * S) → check_anti_left S. 

Inductive assert_anti_right (S : Type) := 
| Assert_Anti_Right : assert_anti_right S. 

Inductive assert_not_anti_right (S : Type) := 
| Assert_Not_Anti_Right : (S * S) → assert_not_anti_right S. 

Inductive check_anti_right (S : Type) := 
| Certify_Anti_Right : check_anti_right S 
| Certify_Not_Anti_Right : (S * S) → check_anti_right S. 

Inductive assert_total (S : Type) := 
| Assert_Total : assert_total S. 

Inductive check_total (S : Type) := 
| Certify_Total : check_total S
| Certify_Not_Total : (S * S) → check_total S. 

Inductive check_has_2_chain (S : Type) := 
| Certify_Has_2_Chain : (S * S) → S → check_has_2_chain S
| Certify_Not_Has_2_Chain : check_has_2_chain S. 

Inductive assert_not_is_left (S : Type) := 
| Assert_Not_Is_Left : (S * S) → assert_not_is_left S. 

Inductive check_is_left (S : Type) := 
| Certify_Is_Left : check_is_left S
| Certify_Not_Is_Left : (S * S) → check_is_left S. 

Inductive assert_not_is_right (S : Type) := 
| Assert_Not_Is_Right : (S * S) → assert_not_is_right S. 

Inductive check_is_right (S : Type) := 
| Certify_Is_Right : check_is_right S
| Certify_Not_Is_Right : (S * S) → check_is_right S. 

(* *) 

Inductive assert_left_distributive (S : Type) := 
| Assert_Left_Distributive : assert_left_distributive S. 

Inductive check_left_distributive (S : Type) := 
| Certify_Left_Distributive : check_left_distributive S
| Certify_Not_Left_Distributive : (S * (S * S)) → check_left_distributive S.

Inductive assert_right_distributive (S : Type) := 
| Assert_Right_Distributive : assert_right_distributive S. 

Inductive check_right_distributive (S : Type) := 
| Certify_Right_Distributive : check_right_distributive S
| Certify_Not_Right_Distributive : (S * (S * S)) → check_right_distributive S.

Inductive assert_plus_id_equals_times_ann (S : Type) := 
| Assert_Plus_Id_Equals_Times_Ann : assert_plus_id_equals_times_ann S. 

Inductive check_plus_id_equals_times_ann (S : Type) := 
| Certify_Plus_Id_Equals_Times_Ann : check_plus_id_equals_times_ann S
| Certify_Not_Plus_Id_Equals_Times_Ann : check_plus_id_equals_times_ann S.

Inductive assert_times_id_equals_plus_ann (S : Type) := 
| Assert_Times_Id_Equals_Plus_Ann : assert_times_id_equals_plus_ann S. 

Inductive check_times_id_equals_plus_ann (S : Type) := 
| Certify_Times_Id_Equals_Plus_Ann : check_times_id_equals_plus_ann S
| Certify_Not_Times_Id_Equals_Plus_Ann : check_times_id_equals_plus_ann S.


Inductive assert_left_left_absorptive (S : Type) := 
| Assert_Left_Left_Absorptive : assert_left_left_absorptive S. 

Inductive check_left_left_absorptive (S : Type) := 
| Certify_Left_Left_Absorptive : check_left_left_absorptive S
| Certify_Not_Left_Left_Absorptive : (S * S) → check_left_left_absorptive S.




Inductive assert_left_right_absorptive (S : Type) := 
| Assert_Left_Right_Absorptive : assert_left_right_absorptive S. 

Inductive check_left_right_absorptive (S : Type) := 
| Certify_Left_Right_Absorptive : check_left_right_absorptive S
| Certify_Not_Left_Right_Absorptive : (S * S) → check_left_right_absorptive S.


Inductive assert_right_left_absorptive (S : Type) := 
| Assert_Right_Left_Absorptive : assert_right_left_absorptive S. 

Inductive check_right_left_absorptive (S : Type) := 
| Certify_Right_Left_Absorptive : check_right_left_absorptive S
| Certify_Not_Right_Left_Absorptive : (S * S) → check_right_left_absorptive S.


Inductive assert_right_right_absorptive (S : Type) := 
| Assert_Right_Right_Absorptive : assert_right_right_absorptive S. 

Inductive check_right_right_absorptive (S : Type) := 
| Certify_Right_Right_Absorptive : check_right_right_absorptive S
| Certify_Not_Right_Right_Absorptive : (S * S) → check_right_right_absorptive S.







(* some useful functions *) 

Definition get_witness :  ∀ (S : Type),  certify_witness S -> S 
:= λ S cwS, 
   match cwS with  
   | Certify_Witness s => s 
   end. 

Definition get_negate :  ∀ (S : Type),  certify_negate S -> (S -> S)
:= λ S cnS, 
   match cnS with  
   | Certify_Negate f => f 
   end. 

Definition nontrivial_witness :  ∀ (S : Type),  assert_nontrivial S -> S 
:= λ S ntS, get_witness S (certify_nontrivial_witness S ntS). 

Definition nontrivial_negate :  ∀ (S : Type),  assert_nontrivial S -> (S -> S) 
:= λ S ntS, get_negate S (certify_nontrivial_negate S ntS). 

Definition nontrivial_pair :  ∀ (S : Type),  assert_nontrivial S -> (S * S) 
:= λ S ntS, 
   let w := nontrivial_witness S ntS in 
   let f := nontrivial_negate S ntS in 
   (w, f w). 









