Require Import CAS.code.basic_types. 


Inductive assert_left_distributive {S : Type} := 
| Assert_Left_Distributive : assert_left_distributive (S := S). 

Inductive check_left_distributive {S : Type} := 
| Certify_Left_Distributive : check_left_distributive (S := S)
| Certify_Not_Left_Distributive : (S * (S * S)) → check_left_distributive (S := S).

Inductive check_left_distributive_dual {S : Type} := 
| Certify_Left_Distributive_Dual : @check_left_distributive_dual S
| Certify_Not_Left_Distributive_Dual : (S * (S * S)) → @check_left_distributive_dual S. 

Inductive assert_right_distributive {S : Type} := 
| Assert_Right_Distributive : assert_right_distributive (S := S). 

Inductive check_right_distributive {S : Type} := 
| Certify_Right_Distributive : check_right_distributive (S := S)
| Certify_Not_Right_Distributive : (S * (S * S)) → check_right_distributive (S := S).

Inductive assert_plus_id_equals_times_ann {S : Type} := 
| Assert_Plus_Id_Equals_Times_Ann : assert_plus_id_equals_times_ann (S := S). 

Inductive check_plus_id_equals_times_ann {S : Type} := 
| Certify_Plus_Id_Equals_Times_Ann : check_plus_id_equals_times_ann (S := S)
| Certify_Not_Plus_Id_Equals_Times_Ann : check_plus_id_equals_times_ann (S := S).

Inductive assert_times_id_equals_plus_ann {S : Type} := 
| Assert_Times_Id_Equals_Plus_Ann : assert_times_id_equals_plus_ann (S := S). 

Inductive check_times_id_equals_plus_ann {S : Type} := 
| Certify_Times_Id_Equals_Plus_Ann : check_times_id_equals_plus_ann (S := S)
| Certify_Not_Times_Id_Equals_Plus_Ann : check_times_id_equals_plus_ann (S := S).


Inductive assert_left_left_absorptive {S : Type} := 
| Assert_Left_Left_Absorptive : assert_left_left_absorptive (S := S).

Inductive assert_left_left_absorptive_dual {S : Type} := 
| Assert_Left_Left_Absorptive_Dual : @assert_left_left_absorptive_dual S. 


Inductive check_left_left_absorptive {S : Type} := 
| Certify_Left_Left_Absorptive : check_left_left_absorptive (S := S)
| Certify_Not_Left_Left_Absorptive : (S * S) → check_left_left_absorptive (S := S).


Inductive assert_left_right_absorptive {S : Type} := 
| Assert_Left_Right_Absorptive : assert_left_right_absorptive (S := S). 

Inductive check_left_right_absorptive {S : Type} := 
| Certify_Left_Right_Absorptive : check_left_right_absorptive (S := S)
| Certify_Not_Left_Right_Absorptive : (S * S) → check_left_right_absorptive (S := S).


Inductive assert_right_left_absorptive {S : Type} := 
| Assert_Right_Left_Absorptive : assert_right_left_absorptive (S := S). 

Inductive check_right_left_absorptive {S : Type} := 
| Certify_Right_Left_Absorptive : check_right_left_absorptive (S := S)
| Certify_Not_Right_Left_Absorptive : (S * S) → check_right_left_absorptive (S := S).


Inductive assert_right_right_absorptive {S : Type} := 
| Assert_Right_Right_Absorptive : assert_right_right_absorptive (S := S). 

Inductive check_right_right_absorptive {S : Type} := 
| Certify_Right_Right_Absorptive : check_right_right_absorptive (S := S)
| Certify_Not_Right_Right_Absorptive : (S * S) → check_right_right_absorptive (S := S).

