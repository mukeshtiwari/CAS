open Data 
open Certificates
open Cert_records
open Cas_records
open Cast
open Cas

let rec string_of_list = function 
  | [] -> "" 
  | [a] -> a 
  | a::rest -> a ^ ", " ^(string_of_list rest) 

let rec string_of_data = function 
| DATA_nat n -> string_of_int n 
| DATA_bool b -> string_of_bool b 
| DATA_string l -> String.concat "" (List.map (String.make 1) l) 
| DATA_pair (d1, d2) -> "(" ^ (string_of_data d1) ^  ", " ^ (string_of_data d2) ^ ")" 
| DATA_inl d -> "inl(" ^ (string_of_data d) ^ ")" 
| DATA_inr d -> "inr(" ^ (string_of_data d) ^ ")" 
| DATA_list l -> "[" ^ (string_of_list (List.map string_of_data l)) ^ "]" 

let string_of_check_exists_id data = function 
    | Certify_Not_Exists_Id -> 
	"No Identity" 
    | Certify_Exists_Id a -> 
	"Identity  "
          ^ (string_of_data (data a))


let string_of_check_exists_ann data = function 
    | Certify_Not_Exists_Ann -> 
	"No Annihilator" 
    | Certify_Exists_Ann a -> 
	"Annihilator  "
          ^ (string_of_data (data a))

let string_of_check_commutative data = function 
    | Certify_Commutative -> 
	"Commutative" 
    | Certify_Not_Commutative (a, b) -> 
	"Not Commutative "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))

let string_of_check_idempotent data = function 
    | Certify_Idempotent -> 
	"Idempotent" 
    | Certify_Not_Idempotent a -> 
	"Not Idempotent "
          ^ (string_of_data (data a))

let string_of_check_selective data = function 
    | Certify_Selective -> 
	"Selective" 
    | Certify_Not_Selective (a, b) -> 
	"Not Selective "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))

let string_of_check_left_cancellative data = function 
    | Certify_Left_Cancellative -> 
	"Left Cancellative" 
    | Certify_Not_Left_Cancellative (a, (b, c)) -> 
	"Not Left Cancellative "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
	  ^  ", " 
	  ^ (string_of_data (data c))

let string_of_check_right_cancellative data = function 
    | Certify_Right_Cancellative -> 
	"Right Cancellative" 
    | Certify_Not_Right_Cancellative (a, (b, c)) -> 
	"Not Right Cancellative "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
	  ^  ", " 
	  ^ (string_of_data (data c))

let string_of_check_left_constant data = function 
    | Certify_Left_Constant -> 
	"Left Constant" 
    | Certify_Not_Left_Constant (a, (b, c)) -> 
	"Not Left Constant "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
	  ^  ", " 
	  ^ (string_of_data (data c))

let string_of_check_right_constant data = function 
    | Certify_Right_Constant -> 
	"Right Constant" 
    | Certify_Not_Right_Constant (a, (b, c)) -> 
	"Not Right Constant "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
	  ^  ", " 
	  ^ (string_of_data (data c))

let string_of_check_anti_left data = function 
    | Certify_Anti_Left -> 
	"Anti Left" 
    | Certify_Not_Anti_Left (a, b) -> 
	"Not Anti Left "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))


let string_of_check_anti_right data = function 
    | Certify_Anti_Right -> 
	"Anti Right" 
    | Certify_Not_Anti_Right (a, b) -> 
	"Not Anti Right "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))


let string_of_check_is_left data = function 
    | Certify_Is_Left -> 
	"Is Left" 
    | Certify_Not_Is_Left (a, b) -> 
	"Not Is Left "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))

let string_of_check_is_right data = function 
    | Certify_Is_Right -> 
	"Is Right" 
    | Certify_Not_Is_Right (a, b) -> 
	"Not Is Right "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))


let string_of_check_left_distributive data = function 
    | Certify_Left_Distributive -> 
	"Left Distributive" 
    | Certify_Not_Left_Distributive (a, (b, c)) -> 
	"Not Left Distributive "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
	  ^  ", " 
	  ^ (string_of_data (data c))

let string_of_check_right_distributive data = function 
    | Certify_Right_Distributive -> 
	"Right Distributive" 
    | Certify_Not_Right_Distributive (a, (b, c)) -> 
	"Not Right Distributive "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
	  ^  ", " 
	  ^ (string_of_data (data c))


let string_of_check_left_absorptive data = function 
    | Certify_Left_Absorptive -> 
	"Left Absorptive" 
    | Certify_Not_Left_Absorptive (a, b) -> 
	"Not Left Absorptive "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))

let string_of_check_right_absorptive data = function 
    | Certify_Right_Absorptive -> 
	"Right Absorptive" 
    | Certify_Not_Right_Absorptive (a, b) -> 
	"Not Right Absorptive "
          ^ (string_of_data (data a))
	  ^  ", " 
	  ^ (string_of_data (data b))
       
let string_of_check_plus_id_is_times_ann = function 
    | Certify_Plus_Id_Equals_Times_Ann -> "id(+) == ann(*)"
    | Certify_Not_Plus_Id_Equals_Times_Ann -> "id(+) != ann(*)"

let string_of_check_times_id_is_plus_ann = function 
    | Certify_Times_Id_Equals_Plus_Ann -> "id(*) == ann(+)"
    | Certify_Not_Times_Id_Equals_Plus_Ann -> "id(*) != ann(+)"

let sg_certs_describe data certs = 
      [
       string_of_check_exists_id data (sg_exists_id_d certs) ; 
       string_of_check_exists_ann data (sg_exists_ann_d certs) ; 
       string_of_check_idempotent data (sg_idempotent_d certs) ; 
       string_of_check_commutative data (sg_commutative_d certs) ; 
       string_of_check_selective data (sg_selective_d certs) ; 
       string_of_check_left_cancellative data (sg_left_cancel_d certs) ; 
       string_of_check_right_cancellative data (sg_right_cancel_d certs) ; 
       string_of_check_left_constant data (sg_left_constant_d certs) ; 
       string_of_check_right_constant data (sg_right_constant_d certs) ; 
       string_of_check_anti_left data (sg_anti_left_d certs) ; 
       string_of_check_anti_right data (sg_anti_right_d certs) ; 
       string_of_check_is_left data (sg_is_left_d certs) ;  
       string_of_check_is_right data (sg_is_right_d certs)
     ] 



let sg_describe sg = sg_certs_describe (eqv_data (sg_eq sg)) (sg_certs sg)
let sg_C_describe sg  = sg_describe (sg_from_sg_C sg)
let sg_CS_describe sg = sg_describe (sg_from_sg_CS sg)
let sg_CI_describe sg = sg_describe (sg_from_sg_CI sg)
let sg_CK_describe sg = sg_describe (sg_from_sg_CK sg)


let sg_sg_certs_describe data certs = 
      [
       string_of_check_left_distributive data (sg_sg_left_distributive_d certs) ; 
       string_of_check_right_distributive data (sg_sg_right_distributive_d certs) ; 
       string_of_check_left_absorptive data (sg_sg_left_absorptive_d certs) ; 
       string_of_check_right_absorptive data (sg_sg_right_absorptive_d certs) ; 
       string_of_check_plus_id_is_times_ann (sg_sg_plus_id_is_times_ann_d certs) ; 
       string_of_check_times_id_is_plus_ann (sg_sg_times_id_is_plus_ann_d certs) 
     ] 

let sg_sg_describe bs = 
    let data        = eqv_data (sg_sg_eqv bs) in 
    let plus_certs  = sg_sg_plus_certs bs     in 
    let times_certs = sg_sg_times_certs bs    in 
    let certs       = sg_sg_certs bs          in 
      (
       sg_certs_describe data plus_certs, 
       sg_certs_describe data times_certs, 
       sg_sg_certs_describe data certs
      )
 

