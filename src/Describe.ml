
open Data 
open Certificates
open Cert_records
open Cas_records
open Cas

let rec string_of_data = function 
| DATA_nat n -> string_of_int n 
| DATA_bool b -> string_of_bool b 
| DATA_string l -> "NOT YET" 
| DATA_pair (d1, d2) -> "(" ^ (string_of_data d1) ^  ", " ^ (string_of_data d2) ^ ")" 
| DATA_inl d -> "inl(" ^ (string_of_data d) ^ ")" 
| DATA_inr d -> "inr(" ^ (string_of_data d) ^ ")" 
| DATA_list l -> "NOT YET"

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


let sg_describe sg = 
    let eqv = sg_eq sg in 
    let data = eqv_data eqv in 
    let certs = sg_certs sg in 
      [
       string_of_check_exists_id data (sg_exists_id_d certs) ; 
       string_of_check_exists_ann data (sg_exists_ann_d certs) ; 
       string_of_check_idempotent data (sg_idempotent_d certs) ; 
       string_of_check_commutative data (sg_commutative_d certs) 
     ] 
        


