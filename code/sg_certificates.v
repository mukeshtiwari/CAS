Require Import CAS.code.basic_types. 

Inductive assert_bop_congruence {S : Type} := 
| Assert_Bop_Congruence : @assert_bop_congruence S. 

Inductive assert_associative {S : Type} := 
| Assert_Associative : assert_associative (S := S). 

Inductive assert_exists_id {S : Type} := 
| Assert_Exists_Id : S -> assert_exists_id (S := S). 

Inductive check_exists_id {S : Type} := 
| Certify_Exists_Id : S -> check_exists_id (S := S)
| Certify_Not_Exists_Id : check_exists_id (S := S). 

Inductive assert_exists_ann {S : Type} := 
| Assert_Exists_Ann : S -> assert_exists_ann (S := S). 

Inductive check_exists_ann {S : Type} := 
| Certify_Exists_Ann : S -> check_exists_ann (S := S)
| Certify_Not_Exists_Ann : check_exists_ann (S := S). 


Inductive assert_commutative {S : Type} := 
| Assert_Commutative : assert_commutative (S := S). 

Inductive check_commutative {S : Type} := 
| Certify_Commutative : check_commutative (S := S)
| Certify_Not_Commutative : (S * S) → check_commutative (S := S). 

Inductive assert_idempotent {S : Type} := 
| Assert_Idempotent : assert_idempotent (S := S). 

Inductive assert_not_idempotent {S : Type} := 
| Assert_Not_Idempotent : S → assert_not_idempotent (S := S). 

Inductive check_idempotent {S : Type} := 
| Certify_Idempotent : check_idempotent (S := S)
| Certify_Not_Idempotent : S → check_idempotent (S := S). 

Inductive assert_selective {S : Type} := 
| Assert_Selective : assert_selective (S := S). 

Inductive check_selective {S : Type} := 
| Certify_Selective : check_selective (S := S)
| Certify_Not_Selective : (S * S) → check_selective (S := S). 

Inductive assert_left_cancellative {S : Type} := 
| Assert_Left_Cancellative : assert_left_cancellative (S := S). 

Inductive assert_not_left_cancellative {S : Type} := 
| Assert_Not_Left_Cancellative : (S * (S * S)) → assert_not_left_cancellative (S := S). 

Inductive check_left_cancellative {S : Type} := 
| Certify_Left_Cancellative : check_left_cancellative (S := S)
| Certify_Not_Left_Cancellative : (S * (S * S)) → check_left_cancellative (S := S). 


Inductive assert_right_cancellative {S : Type} := 
| Assert_Right_Cancellative : assert_right_cancellative (S := S). 

Inductive assert_not_right_cancellative {S : Type} := 
| Assert_Not_Right_Cancellative : (S * (S * S)) → assert_not_right_cancellative (S := S). 

Inductive check_right_cancellative {S : Type} := 
| Certify_Right_Cancellative : check_right_cancellative (S := S)
| Certify_Not_Right_Cancellative : (S * (S * S)) → check_right_cancellative (S := S). 

Inductive assert_left_constant {S : Type} := 
| Assert_Left_Constant : assert_left_constant (S := S). 

Inductive assert_not_left_constant {S : Type} := 
| Assert_Not_Left_Constant : (S * (S * S)) → assert_not_left_constant (S := S). 

Inductive check_left_constant {S : Type} := 
| Certify_Left_Constant : check_left_constant (S := S)
| Certify_Not_Left_Constant : (S * (S * S)) → check_left_constant (S := S). 

Inductive assert_right_constant {S : Type} := 
| Assert_Right_Constant : assert_right_constant (S := S). 

Inductive assert_not_right_constant {S : Type} := 
| Assert_Not_Right_Constant : (S * (S * S)) → assert_not_right_constant (S := S). 

Inductive check_right_constant {S : Type} := 
| Certify_Right_Constant : check_right_constant (S := S)
| Certify_Not_Right_Constant : (S * (S * S)) → check_right_constant (S := S). 

Inductive assert_anti_left {S : Type} := 
| Assert_Anti_Left : assert_anti_left (S := S). 

Inductive assert_not_anti_left {S : Type} := 
| Assert_Not_Anti_Left : (S * S) → assert_not_anti_left (S := S). 

Inductive check_anti_left {S : Type} := 
| Certify_Anti_Left : check_anti_left (S := S)
| Certify_Not_Anti_Left : (S * S) → check_anti_left (S := S). 

Inductive assert_anti_right {S : Type} := 
| Assert_Anti_Right : assert_anti_right (S := S). 

Inductive assert_not_anti_right {S : Type} := 
| Assert_Not_Anti_Right : (S * S) → assert_not_anti_right (S := S). 

Inductive check_anti_right {S : Type} := 
| Certify_Anti_Right : check_anti_right (S := S)
| Certify_Not_Anti_Right : (S * S) → check_anti_right (S := S). 

Inductive check_has_2_chain {S : Type} := 
| Certify_Has_2_Chain : (S * S) → S → check_has_2_chain (S := S)
| Certify_Not_Has_2_Chain : check_has_2_chain (S := S). 

Inductive assert_not_is_left {S : Type} := 
| Assert_Not_Is_Left : (S * S) → assert_not_is_left (S := S). 

Inductive check_is_left {S : Type} := 
| Certify_Is_Left : check_is_left (S := S)
| Certify_Not_Is_Left : (S * S) → check_is_left (S := S). 

Inductive assert_not_is_right {S : Type} := 
| Assert_Not_Is_Right : (S * S) → assert_not_is_right (S := S). 

Inductive check_is_right {S : Type} := 
| Certify_Is_Right : check_is_right (S := S)
| Certify_Not_Is_Right : (S * S) → check_is_right (S := S). 

