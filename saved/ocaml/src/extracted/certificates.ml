type 's certify_witness =
| Certify_Witness of 's

type 's certify_negate =
| Certify_Negate of ('s -> 's)

type 's assert_nontrivial = { certify_nontrivial_witness : 's certify_witness;
                              certify_nontrivial_negate : 's certify_negate }

(** val certify_nontrivial_witness :
    'a1 assert_nontrivial -> 'a1 certify_witness **)

let certify_nontrivial_witness x = x.certify_nontrivial_witness

(** val certify_nontrivial_negate :
    'a1 assert_nontrivial -> 'a1 certify_negate **)

let certify_nontrivial_negate x = x.certify_nontrivial_negate

type 's check_exists_id =
| Certify_Exists_Id of 's
| Certify_Not_Exists_Id

type 's check_exists_ann =
| Certify_Exists_Ann of 's
| Certify_Not_Exists_Ann

type 's check_commutative =
| Certify_Commutative
| Certify_Not_Commutative of ('s*'s)

type 's check_idempotent =
| Certify_Idempotent
| Certify_Not_Idempotent of 's

type 's check_selective =
| Certify_Selective
| Certify_Not_Selective of ('s*'s)

type 's check_left_cancellative =
| Certify_Left_Cancellative
| Certify_Not_Left_Cancellative of ('s*('s*'s))

type 's check_right_cancellative =
| Certify_Right_Cancellative
| Certify_Not_Right_Cancellative of ('s*('s*'s))

type 's check_left_constant =
| Certify_Left_Constant
| Certify_Not_Left_Constant of ('s*('s*'s))

type 's check_right_constant =
| Certify_Right_Constant
| Certify_Not_Right_Constant of ('s*('s*'s))

type 's check_anti_left =
| Certify_Anti_Left
| Certify_Not_Anti_Left of ('s*'s)

type 's check_anti_right =
| Certify_Anti_Right
| Certify_Not_Anti_Right of ('s*'s)

type 's check_is_left =
| Certify_Is_Left
| Certify_Not_Is_Left of ('s*'s)

type 's check_is_right =
| Certify_Is_Right
| Certify_Not_Is_Right of ('s*'s)

type 's check_left_distributive =
| Certify_Left_Distributive
| Certify_Not_Left_Distributive of ('s*('s*'s))

type 's check_right_distributive =
| Certify_Right_Distributive
| Certify_Not_Right_Distributive of ('s*('s*'s))

type 's check_plus_id_equals_times_ann =
| Certify_Plus_Id_Equals_Times_Ann
| Certify_Not_Plus_Id_Equals_Times_Ann

type 's check_times_id_equals_plus_ann =
| Certify_Times_Id_Equals_Plus_Ann
| Certify_Not_Times_Id_Equals_Plus_Ann

type 's check_left_absorptive =
| Certify_Left_Absorptive
| Certify_Not_Left_Absorptive of ('s*'s)

type 's check_right_absorptive =
| Certify_Right_Absorptive
| Certify_Not_Right_Absorptive of ('s*'s)

(** val get_witness : 'a1 certify_witness -> 'a1 **)

let get_witness = function
| Certify_Witness s -> s

(** val get_negate : 'a1 certify_negate -> 'a1 -> 'a1 **)

let get_negate = function
| Certify_Negate f -> f

(** val nontrivial_witness : 'a1 assert_nontrivial -> 'a1 **)

let nontrivial_witness ntS =
  get_witness ntS.certify_nontrivial_witness

(** val nontrivial_negate : 'a1 assert_nontrivial -> 'a1 -> 'a1 **)

let nontrivial_negate ntS =
  get_negate ntS.certify_nontrivial_negate

(** val nontrivial_pair : 'a1 assert_nontrivial -> 'a1*'a1 **)

let nontrivial_pair ntS =
  let w = nontrivial_witness ntS in let f = nontrivial_negate ntS in w,(f w)

