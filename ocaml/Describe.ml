open Cas

exception Error of string list 

let error s = raise (Error [s])
let errors sl = raise (Error sl) 		    
       
let nl s = s ^ "\n"       

let char_list_to_string cl = String.concat "" (List.map (String.make 1) cl)

let rec from_to start finish =
  if start > finish
  then []
  else start :: (from_to (start + 1) finish);;

let string_to_char_list s = List.map (String.get s) (from_to 0 ((String.length s) - 1));;

let make_constant' s1 s2 = make_constant (string_to_char_list s1) (string_to_char_list s2);;

let infinity = make_constant' "INF"  "\\infty";;
let self = make_constant' "SELF"  "\\bot";;


(* expand these ... *)
let get_plus bs =
  match bs with
  | BS_dioid d -> d.dioid_plus
  | _ -> error "get_plus: nope!" ;; 

let get_times bs =
  match bs with
  | BS_dioid d -> d.dioid_times
  | _ -> error "get_times: nope!" ;;

let get_eq bs =
  match bs with
  | BS_dioid d -> d.dioid_eqv.eqv_eq
  | _ -> error "get_eq : nope!" ;; 
  
let get_data bs =
  match bs with
  | BS_dioid d -> d.dioid_eqv.eqv_data
  | _ -> error "get_data : nope!" ;; 
  

type string_type = Ascii | Latex


let rec data_to_string st = function 
| DATA_nat n         -> string_of_int n 
| DATA_bool b        -> string_of_bool b 
| DATA_string l      -> String.concat "" (List.map (String.make 1) l)
| DATA_constant c    -> String.concat "" (List.map (String.make 1) (c.Cas.constant_ascii))
| DATA_pair (d1, d2) -> (match st with
              		| Ascii -> "(" ^ (data_to_string st d1) ^  ", " ^ (data_to_string st d2) ^ ")"
			| Latex -> "(" ^ (data_to_string st d1) ^  ", " ^ (data_to_string st d2) ^ ")" )
| DATA_inl d         -> (match st with
			 | Ascii -> "inl(" ^ (data_to_string st d) ^ ")"
			 | Latex -> "\\inl{" ^ (data_to_string st d) ^ "}")
| DATA_inr d         -> (match st with
			 | Ascii -> "inr(" ^ (data_to_string st d) ^ ")"
			 | Latex -> "\\inr{" ^ (data_to_string st d) ^ "}" )
| DATA_list l        -> (match st with
			 | Ascii -> "[" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "]"
			 | Latex -> "[" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "]")
| DATA_set l         -> (match st with
			 | Ascii -> "{" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "}"	 
                         | Latex -> "\\{" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "\\}")
| DATA_ascii c       -> "DATA_ascii : Not Yet Implemented"
(*| DATA_square_matrix _ -> "DATA_square_matrix : Not Yet Implemented"*) 
			     
let rec data_to_ascii = data_to_string Ascii
let rec data_to_latex = data_to_string Latex 
			     


let rec unfold_eqv_ast = function 
| Ast_eqv_ascii  -> "ascii" 
| Ast_eqv_bool   -> "bool" 
| Ast_eqv_nat    -> "nat" 
| Ast_eqv_matrix -> "matrix?" 
| Ast_eqv_list eqv -> "(" ^ (unfold_eqv_ast eqv) ^ ") list"
| Ast_eqv_set eqv -> "(" ^ (unfold_eqv_ast eqv) ^ ") set"
| Ast_eqv_product (eqv1, eqv2) -> "(" ^ (unfold_eqv_ast eqv1) ^ ") * (" ^ (unfold_eqv_ast eqv2) ^ ")" 
| Ast_eqv_sum (eqv1, eqv2) -> "(" ^ (unfold_eqv_ast eqv1) ^ ") + (" ^ (unfold_eqv_ast eqv2) ^ ")" 
| Ast_eqv_add_constant (c, eqv) -> "{" ^ (char_list_to_string c.constant_ascii) ^ "} + (" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_eqv_nat_ceiling n -> "[" ^ (string_of_int n) ^ "]"
| Ast_eqv_minset orsg -> "(" ^ (unfold_or_ast orsg) ^ ") minimal_set"
| Ast_eqv_of_or ord -> "Ast_eqv_of_or ord : Fix me" 
| Ast_eqv_of_sg sg -> "Ast_eqv_of_sg : Fix me"
| Ast_eqv_of_bs gs -> "Ast_eqv_of_bs : Fix me"
| Ast_eqv_of_os os -> "Ast_eqv_of_or : Fix me"
and unfold_or_ast = function 
| Ast_or_nat -> "(nat, <=)"
| Ast_or_bool -> "or_bool : NEEDED?"
| Ast_or_add_bottom (c, ord) -> "add_bottom(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (unfold_or_ast ord) ^ ")" 
| Ast_or_add_top (c, ord) -> "add_top(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (unfold_or_ast ord) ^ ")" 
| Ast_or_dual ord -> "dual(" ^ (unfold_or_ast ord) ^ ")" 
| Ast_or_llte sg -> "left_lte_from_sg(" ^ (unfold_sg_ast sg) ^ ")" 
| Ast_or_rlte sg -> "right_lte_from_sg(" ^ (unfold_sg_ast sg) ^ ")" 
| Ast_or_length eqv -> "list_length(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_or_llex (ord1, ord2) -> "order_llex_product(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_product (ord1, ord2) -> "order_product(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_subset eqv -> "or_subset : NEEDED?"
| Ast_or_set eqv -> "or_set : NEEDED?"
| Ast_or_left_sum (ord1, ord2) -> "left_sum(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_right_sum (ord1, ord2) -> "right_sum(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_trivial eqv -> "trivial_order(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_or_of_os os -> "Ast_or_of_os : fix me"
and unfold_sg_ast = function 
| Ast_sg_times -> "(nat, *" ^ ")"
| Ast_sg_plus -> "(nat, +)"
| Ast_sg_or -> "(bool, or)"
| Ast_sg_and -> "(bool, and)"
| Ast_sg_min -> "(nat, min)"
| Ast_sg_max -> "(nat, max)"
| Ast_sg_add_id (c, sg) -> "add_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_sg_ast sg) ^ ")"
| Ast_sg_add_ann (c, sg) -> "add_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_sg_ast sg) ^ ")"
| Ast_sg_concat eqv -> "sg_concat(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_union eqv -> "sg_union(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_intersect eqv -> "sg_intersect(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_left eqv -> "sg_left(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_right eqv -> "sg_right(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_left_sum (sg1, sg2) -> "sg_left_sum(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_right_sum (sg1, sg2) -> "sg_right_sum(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_lift sg -> "lift(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_sg_llex (sg1, sg2) -> "sg_llex(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_product (sg1, sg2) -> "sg_product(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_minset_lift os -> "sg_minset_lift(" ^ (unfold_os_ast os) ^ ")"
| Ast_sg_minset_union ord -> "sg_minset_union(" ^ (unfold_or_ast ord) ^ ")"
| Ast_sg_plus_of_bs bs -> "Ast_sg_plus_of_bs : fix me" 
| Ast_sg_times_of_bs bs -> "Ast_sg_times_of_bs : fix me" 
| Ast_sg_times_of_os os -> "Ast_sg_times_of_os : fix me" 
and unfold_bs_ast = function 
| Ast_min_plus -> "(nat, min, +)" 
| Ast_max_plus -> "(nat, max, +)" 
| Ast_and_or -> "(bool, and, or)" 
| Ast_or_and -> "(bool, or, and)" 
| Ast_max_min -> "(nat, max, min)" 
| Ast_min_max -> "(nat, min, max)" 
| Ast_bs_add_zero (c, bs) -> "add_zero(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_bs_ast bs) ^ ")"
| Ast_bs_add_one (c, bs) -> "add_one(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_bs_ast bs) ^ ")"
| Ast_bs_product (bs1, bs2) -> "product(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_llex_product (bs1, bs2) -> "llex_product(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_union_lift sg -> "union_lift(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_bs_left_sum_right_sum (bs1, bs2) -> "left_sum_right_sum(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_right_sum_left_sum (bs1, bs2) -> "right_sum_left_sum(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_left sg  -> "bs_left(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_bs_right sg -> "bs_right(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_union_intersect eqv  -> "union_intersect(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_intersect_union eqv  -> "intersect_union(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_bs_dual bs           -> "dual(" ^ (unfold_bs_ast bs) ^ ")" 
| Ast_minset_lift_union os -> "minset_lift_union(" ^ (unfold_os_ast os) ^ ")"
| Ast_minset_union_lift os -> "minset_union_lift(" ^ (unfold_os_ast os) ^ ")"
| Ast_lift_union sg        -> "lift_union(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_union_lift sg        -> "union_lift(" ^ (unfold_sg_ast sg) ^ ")"
and unfold_os_ast = function 
| Ast_os_from_bs_left bs  -> "os_from_bs_left(" ^ (unfold_bs_ast bs) ^ ")" 
| Ast_os_from_bs_right bs  -> "os_from_bs_right(" ^ (unfold_bs_ast bs) ^ ")" 
| Ast_os_llex_product (os1, os2) -> "os_llex_product(" ^ (unfold_os_ast os1) ^ ", " ^ (unfold_os_ast os2) ^ ")" 
| Ast_os_product (os1, os2) -> "os_product(" ^ (unfold_os_ast os1) ^ ", " ^ (unfold_os_ast os2) ^ ")" 
| Ast_os_add_bottom_id (c, os) -> "os_add_bottom_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_os_ast os) ^ ")"
| Ast_os_add_top_ann (c, os) -> "os_add_top_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_os_ast os) ^ ")"
and unfold_ltr_ast = function 
| Ast_ltr_cons eqv  -> "ltr_cons(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_ltr_product (ltr1, ltr2) -> "ltr_product(" ^ (unfold_ltr_ast ltr1) ^ ", " ^ (unfold_ltr_ast ltr2) ^ ")" 
| Ast_ltr_left_sum (ltr1, ltr2) -> "ltr_left_sum(" ^ (unfold_ltr_ast ltr1) ^ ", " ^ (unfold_ltr_ast ltr2) ^ ")" 
| Ast_ltr_right_sum (ltr1, ltr2) -> "ltr_right_sum(" ^ (unfold_ltr_ast ltr1) ^ ", " ^ (unfold_ltr_ast ltr2) ^ ")" 
| Ast_ltr_lift ltr -> "ltr_lift(" ^ (unfold_ltr_ast ltr) ^ ")"
| Ast_ltr_from_sg ltr -> "ltr_from_sg : constructor has wrong type"
| Ast_ltr_with_policy ltr -> "ltr_from_policy : Not Yet Implemented"
and destribe_lstr_ast = function 
| Ast_lstr_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
| Ast_lstr_llex_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
and unfold_lotr_ast = function 
| Ast_lotr_length_cons eqv  -> "length_cons(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_lotr_product (lotr1, lotr2) -> "lotr_product(" ^ (unfold_lotr_ast lotr1) ^ ", " ^ (unfold_lotr_ast lotr2) ^ ")" 
| Ast_lotr_llex_product (lotr1, lotr2) -> "lotr_llex_product(" ^ (unfold_lotr_ast lotr1) ^ ", " ^ (unfold_lotr_ast lotr2) ^ ")" 



				       

let rec describe_eqv_ast = function 
| Ast_eqv_ascii  -> "ascii" 
| Ast_eqv_bool   -> "bool" 
| Ast_eqv_nat    -> "nat" 
| Ast_eqv_matrix -> "matrix?" 
| Ast_eqv_list eqv -> "(" ^ (describe_eqv_ast eqv) ^ ") list"
| Ast_eqv_set eqv -> "(" ^ (describe_eqv_ast eqv) ^ ") set"
| Ast_eqv_product (eqv1, eqv2) -> "(" ^ (describe_eqv_ast eqv1) ^ ") * (" ^ (describe_eqv_ast eqv2) ^ ")" 
| Ast_eqv_sum (eqv1, eqv2) -> "(" ^ (describe_eqv_ast eqv1) ^ ") + (" ^ (describe_eqv_ast eqv2) ^ ")" 
| Ast_eqv_add_constant (c, eqv) -> "{" ^ (char_list_to_string c.constant_ascii) ^ "} + (" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_eqv_nat_ceiling n -> "[" ^ (string_of_int n) ^ "]"
| Ast_eqv_minset orsg -> "(" ^ (describe_or_ast orsg) ^ ") minimal_set"
| Ast_eqv_of_or ord -> "Ast_eqv_of_or ord : Fix me" 
| Ast_eqv_of_sg sg -> "Ast_eqv_of_sg : Fix me"
| Ast_eqv_of_bs gs -> "Ast_eqv_of_bs : Fix me"
| Ast_eqv_of_os os -> "Ast_eqv_of_or : Fix me"
and describe_or_ast = function 
| Ast_or_nat -> "(nat, <=)"
| Ast_or_bool -> "or_bool : NEEDED?"
| Ast_or_add_bottom (c, ord) -> "add_bottom(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (describe_or_ast ord) ^ ")" 
| Ast_or_add_top (c, ord) -> "add_top(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (describe_or_ast ord) ^ ")" 
| Ast_or_dual ord -> "dual(" ^ (describe_or_ast ord) ^ ")" 
| Ast_or_llte sg -> "left_lte_from_sg(" ^ (describe_sg_ast sg) ^ ")" 
| Ast_or_rlte sg -> "right_lte_from_sg(" ^ (describe_sg_ast sg) ^ ")" 
| Ast_or_length eqv -> "list_length(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_or_llex (ord1, ord2) -> "order_llex_product(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_product (ord1, ord2) -> "order_product(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_subset eqv -> "or_subset : NEEDED?"
| Ast_or_set eqv -> "or_set : NEEDED?"
| Ast_or_left_sum (ord1, ord2) -> "left_sum(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_right_sum (ord1, ord2) -> "right_sum(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_trivial eqv -> "trivial_order(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_or_of_os os -> "Ast_or_of_os : fix me"
and describe_sg_ast = function 
| Ast_sg_times -> "(nat, *" ^ ")"
| Ast_sg_plus -> "(nat, +)"
| Ast_sg_or -> "(bool, or)"
| Ast_sg_and -> "(bool, and)"
| Ast_sg_min -> "(nat, min)"
| Ast_sg_max -> "(nat, max)"
| Ast_sg_add_id (c, sg) -> "add_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_sg_ast sg) ^ ")"
| Ast_sg_add_ann (c, sg) -> "add_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_sg_ast sg) ^ ")"
| Ast_sg_concat eqv -> "sg_concat(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_union eqv -> "sg_union(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_intersect eqv -> "sg_intersect(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_left eqv -> "sg_left(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_right eqv -> "sg_right(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_left_sum (sg1, sg2) -> "sg_left_sum(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_right_sum (sg1, sg2) -> "sg_right_sum(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_lift sg -> "lift(" ^ (describe_sg_ast sg) ^ ")"
| Ast_sg_llex (sg1, sg2) -> "sg_llex(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_product (sg1, sg2) -> "sg_product(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_minset_lift os -> "sg_minset_lift(" ^ (describe_os_ast os) ^ ")"
| Ast_sg_minset_union ord -> "sg_minset_union(" ^ (describe_or_ast ord) ^ ")"
| Ast_sg_plus_of_bs bs -> "Ast_sg_plus_of_bs : fix me" 
| Ast_sg_times_of_bs bs -> "Ast_sg_times_of_bs : fix me" 
| Ast_sg_times_of_os os -> "Ast_sg_times_of_os : fix me" 
and describe_bs_ast = function 
| Ast_min_plus -> "(nat, min, +)" 
| Ast_max_plus -> "(nat, max, +)" 
| Ast_and_or -> "(bool, and, or)" 
| Ast_or_and -> "(bool, or, and)" 
| Ast_max_min -> "(nat, max, min)" 
| Ast_min_max -> "(nat, min, max)" 
| Ast_bs_add_zero (c, bs) -> "add_zero(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_bs_ast bs) ^ ")"
| Ast_bs_add_one (c, bs) -> "add_one(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_bs_ast bs) ^ ")"
| Ast_bs_product (bs1, bs2) -> "product(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_llex_product (bs1, bs2) -> "llex_product(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_union_lift sg -> "union_lift(" ^ (describe_sg_ast sg) ^ ")"
| Ast_bs_left_sum_right_sum (bs1, bs2) -> "left_sum_right_sum(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_right_sum_left_sum (bs1, bs2) -> "right_sum_left_sum(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_left sg  -> "bs_left(" ^ (describe_sg_ast sg) ^ ")"
| Ast_bs_right sg -> "bs_right(" ^ (describe_sg_ast sg) ^ ")"
| Ast_union_intersect eqv  -> "union_intersect(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_intersect_union eqv  -> "intersect_union(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_bs_dual bs           -> "dual(" ^ (describe_bs_ast bs) ^ ")" 
| Ast_minset_lift_union os -> "minset_lift_union(" ^ (describe_os_ast os) ^ ")"
| Ast_minset_union_lift os -> "minset_union_lift(" ^ (describe_os_ast os) ^ ")"
| Ast_lift_union sg        -> "lift_union(" ^ (describe_sg_ast sg) ^ ")"
| Ast_union_lift sg        -> "union_lift(" ^ (describe_sg_ast sg) ^ ")"
and describe_os_ast = function 
| Ast_os_from_bs_left bs  -> "os_from_bs_left(" ^ (describe_bs_ast bs) ^ ")" 
| Ast_os_from_bs_right bs  -> "os_from_bs_right(" ^ (describe_bs_ast bs) ^ ")" 
| Ast_os_llex_product (os1, os2) -> "os_llex_product(" ^ (describe_os_ast os1) ^ ", " ^ (describe_os_ast os2) ^ ")" 
| Ast_os_product (os1, os2) -> "os_product(" ^ (describe_os_ast os1) ^ ", " ^ (describe_os_ast os2) ^ ")" 
| Ast_os_add_bottom_id (c, os) -> "os_add_bottom_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_os_ast os) ^ ")"
| Ast_os_add_top_ann (c, os) -> "os_add_top_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_os_ast os) ^ ")"
and describe_ltr_ast = function 
| Ast_ltr_cons eqv  -> "ltr_cons(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_ltr_product (ltr1, ltr2) -> "ltr_product(" ^ (describe_ltr_ast ltr1) ^ ", " ^ (describe_ltr_ast ltr2) ^ ")" 
| Ast_ltr_left_sum (ltr1, ltr2) -> "ltr_left_sum(" ^ (describe_ltr_ast ltr1) ^ ", " ^ (describe_ltr_ast ltr2) ^ ")" 
| Ast_ltr_right_sum (ltr1, ltr2) -> "ltr_right_sum(" ^ (describe_ltr_ast ltr1) ^ ", " ^ (describe_ltr_ast ltr2) ^ ")" 
| Ast_ltr_lift ltr -> "ltr_lift(" ^ (describe_ltr_ast ltr) ^ ")"
| Ast_ltr_from_sg ltr -> "ltr_from_sg : constructor has wrong type"
| Ast_ltr_with_policy ltr -> "ltr_from_policy : Not Yet Implemented"
and destribe_lstr_ast = function 
| Ast_lstr_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
| Ast_lstr_llex_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
and describe_lotr_ast = function 
| Ast_lotr_length_cons eqv  -> "length_cons(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_lotr_product (lotr1, lotr2) -> "lotr_product(" ^ (describe_lotr_ast lotr1) ^ ", " ^ (describe_lotr_ast lotr2) ^ ")" 
| Ast_lotr_llex_product (lotr1, lotr2) -> "lotr_llex_product(" ^ (describe_lotr_ast lotr1) ^ ", " ^ (describe_lotr_ast lotr2) ^ ")" 
 

			     


(*
let rec ast_type_to_string st = function 
| Ast_type_bool             -> (match st with
			       | Ascii -> "bool"
                               | Latex -> "bool")		    
| Ast_type_nat              -> (match st with
			       | Ascii -> "int"
                               | Latex -> "int")		    
| Ast_type_list t           -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t) ^ ") list"
                               | Latex -> "(" ^ (ast_type_to_string st t) ^ ") list")		    
| Ast_type_set t            -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t) ^ ") set"
                               | Latex -> "(" ^ (ast_type_to_string st t) ^ ") set")		    
| Ast_type_product (t1, t2) -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t1) ^ " * " ^ (ast_type_to_string st t2) ^ ")"
                               | Latex -> "(" ^ (ast_type_to_string st t1) ^ " * " ^ (ast_type_to_string st t2) ^ ")")		    
| Ast_type_sum (t1, t2)     -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t1) ^ " + " ^ (ast_type_to_string st t2) ^ ")"
                               | Latex -> "(" ^ (ast_type_to_string st t1) ^ " + " ^ (ast_type_to_string st t2) ^ ")")		    
| Ast_type_add_constant (c,t) -> (match st with
			       | Ascii ->  "(" ^ "cas_constant" ^ " + " ^ (ast_type_to_string st t) ^ ")"
                               | Latex -> "(" ^ "cas_constant" ^ " + " ^ (ast_type_to_string st t) ^ ")"
				 )		    

let rec ast_type_to_string st = function
  | Ast_eqv_bool -> "bool"
  | _ -> "NADA"

let rec ast_type_to_ascii = ast_type_to_string Ascii
let rec ast_type_to_latex = ast_type_to_string Latex

					       
let rec ast_to_string st = function
| Ast_eqv_bool                  -> "bool"
| Ast_eqv_nat                   -> "int"
| Ast_eqv_list eqv              -> "(" ^ (ast_to_string st eqv) ^ ") list"
| Ast_eqv_set eqv               -> "(" ^ (ast_to_string st eqv) ^ ") set"
| Ast_eqv_product (eqv1, eqv2)  -> "(" ^ (ast_to_string st eqv1) ^ " * " ^ (ast_to_string st eqv2) ^ ")"
| Ast_eqv_sum (eqv1, eqv2)      -> "(" ^ (ast_to_string st eqv1) ^ " + " ^ (ast_to_string st eqv2) ^ ")"
| Ast_eqv_add_constant (c, eqv) -> "({" ^ (char_list_to_string c.constant_ascii)      ^ "} + " ^ (ast_to_string st eqv) ^ ")"
| Ast_eqv_nat_ceiling  n        -> "[" ^ (string_of_int (n +1)) ^ "]"
| Ast_eqv_minset po             -> "minset ..." 
| _ -> "NADA"

let ast_to_ascii = ast_to_string Ascii
let ast_to_latex = ast_to_string Latex 									     

 *)
							     
let string_of_check_exists_id data = function 
    | Certify_Not_Exists_Id -> "No Identity\n" 
    | Certify_Exists_Id a -> "Identity " ^ (data_to_ascii (data a)) ^ "\n"

let string_of_check_exists_ann data = function 
    | Certify_Not_Exists_Ann -> "No Annihilator\n" 
    | Certify_Exists_Ann a -> "Annihilator " ^ (data_to_ascii (data a)) ^ "\n"
          
let string_of_check_commutative eq bop data = function 
    | Certify_Commutative -> "Commutative\n" 
    | Certify_Not_Commutative (a, b) ->
       let lhs = bop a b in
       let rhs = bop b a in
       if eq lhs rhs
       then "INTERNAL ERROR : Not Commutative\n"
       else "Not Commutative: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data lhs)) ^ "\n" ^
	      "   " ^ (data_to_ascii (data b)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data rhs)) ^ "\n"

let string_of_check_idempotent eq bop data = function 
    | Certify_Idempotent -> "Idempotent\n" 
    | Certify_Not_Idempotent a ->
       let result = bop a a in
       if eq a result
       then "INTERNAL ERROR : Not Idempotent\n"
       else "Not Idempotent: \n" ^
	    "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n" 

let string_of_check_selective eq bop data = function 
    | Certify_Selective -> "Selective \n" 
    | Certify_Not_Selective (a, b) ->
       let result = bop a b in
       if (eq a result) || (eq b result)
       then "INTERNAL ERROR : Not Selective\n"
       else "Not Selective: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"

let string_of_check_anti_left eq bop data = function 
    | Certify_Anti_Left -> "Anti Left\n" 
    | Certify_Not_Anti_Left (a, b) ->
       let result = bop a b in
       if eq a result 
       then "Not Anti Left: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
       else "INTERNAL ERROR : Not Anti Left\n"

let string_of_check_anti_right eq bop data = function 
    | Certify_Anti_Right -> "Anti Right\n" 
    | Certify_Not_Anti_Right (s, t) -> 
       let result = bop t s in
       if eq s result 
       then "Not Anti Right: \n" ^
	      "   " ^ (data_to_ascii (data t)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
       else "INTERNAL ERROR : Not Anti Right\n"


let string_of_check_is_left eq bop data = function 
    | Certify_Is_Left -> "Is Left\n" 
    | Certify_Not_Is_Left (a, b) ->
       let result = bop a b in
       if eq a result 
       then "INTERNAL ERROR : Not Is Left\n"
       else "Not Is Left: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"

let string_of_check_is_right eq bop data = function 
    | Certify_Is_Right -> "Is Right\n" 
    | Certify_Not_Is_Right (a, b) -> 
       let result = bop a b in
       if eq b result 
       then "INTERNAL ERROR : Not Is Right\n"
       else "Not Is Right: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
															   

let string_of_check_left_cancellative eq bop data = function 
    | Certify_Left_Cancellative -> "Left Cancellative\n" 
    | Certify_Not_Left_Cancellative (a, (b, c)) ->
       (* ab = ac and b <> c *)
       let ab = bop a b in
       let ac = bop a c in       
       if eq b c 
       then "INTERNAL ERROR : Not Left Cancellative\n"
       else if eq ab ac
            then "Not Left Cancellative: \n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data ab)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data c)) ^ " = " ^ (data_to_ascii (data ac)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data b)) ^ " <> " ^ (data_to_ascii (data c)) ^ "\n" 	       
            else  "INTERNAL ERROR\n"	      

let string_of_check_right_cancellative eq bop data = function 
    | Certify_Right_Cancellative ->  "Right Cancellative\n" 
    | Certify_Not_Right_Cancellative (a, (b, c)) ->
       (* ba = ca and b <> c *)
       let ba = bop b a in
       let ca = bop c a in       
       if eq b c 
       then "INTERNAL ERROR : Not Right Cancellative\n"
       else if eq ba ca
            then "Not Right Cancellative: \n" ^
		   "   " ^ (data_to_ascii (data b)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data ba)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data c)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data ca)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data b)) ^ " <> " ^ (data_to_ascii (data c)) ^ "\n" 	       
            else  "INTERNAL ERROR\n"	      

let string_of_check_left_constant eq bop data = function 
    | Certify_Left_Constant -> "Left Constant\n" 
    | Certify_Not_Left_Constant (a, (b, c)) ->
       (* ab <> ac *) 
       let ab = bop a b in
       let ac = bop a c in       
       if eq ab ac 
       then "INTERNAL ERROR Not Left Constant\n"
       else "Not Left Constant: \n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data ab)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data c)) ^ " = " ^ (data_to_ascii (data ac)) ^ "\n"


let string_of_check_right_constant eq bop data = function 
    | Certify_Right_Constant -> "Right Constant\n" 
    | Certify_Not_Right_Constant (s, (t, u)) -> 
       (* ts <> us *) 
       let ts = bop t s in
       let us = bop u s in       
       if eq ts us 
       then "INTERNAL ERROR : Not Right Constant???: \n" 
       else "Not Right Constant: \n" ^
		   "   " ^ (data_to_ascii (data t)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data ts)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data u)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data us)) ^ "\n"


let string_of_check_left_distributive eq plus times data = function 
    | Certify_Left_Distributive ->  "Left Distributive\n" 
    | Certify_Not_Left_Distributive (a, (b, c)) ->
       (* lhs = a*(b + c) <> a*b + a*c = rhs *)
       let plus_b_c = plus b c    in
       let lhs = times a plus_b_c in
       let times_a_b = times a b in
       let times_a_c = times a c in
       let rhs = plus  times_a_b  times_a_c in
       if eq lhs rhs
       then "INTERNAL ERROR : Not Left Distributive\n"
       else "Not Left Distributive:\n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   c = " ^ (data_to_ascii (data c)) ^ "\n" ^				  
	      "   lhs = a*(b + c) <> a*b + a*c = rhs: \n" ^
	      "   b + c = " ^ (data_to_ascii (data plus_b_c)) ^ "\n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   a*c = " ^ (data_to_ascii (data times_a_c)) ^ "\n" ^
	      "   lhs = " ^ (data_to_ascii (data lhs)) ^ "\n" ^				 
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 
		  
let string_of_check_right_distributive eq plus times data = function 
    | Certify_Right_Distributive -> "Right Distributive \n" 
    | Certify_Not_Right_Distributive (a, (b, c)) -> 
       (* lhs = (b + c)*a <> b*a + c*a = rhs *)
       let plus_b_c = plus b c    in
       let lhs = times plus_b_c a in
       let times_b_a = times b a in
       let times_c_a = times c a in
       let rhs = plus  times_b_a  times_c_a in
       if eq lhs rhs
       then "INTERNAL ERROR : Not Right Distributive\n"
       else "Not Right Distributive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   c = " ^ (data_to_ascii (data c)) ^ "\n" ^				  
	      "   lhs = (b + c)*a <> b*a + c*a = rhs: \n" ^
	      "   b + c = " ^ (data_to_ascii (data plus_b_c)) ^ "\n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   c*a = " ^ (data_to_ascii (data times_c_a)) ^ "\n" ^
	      "   lhs = " ^ (data_to_ascii (data lhs)) ^ "\n" ^				 
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 

							   
let string_of_check_left_left_absorptive eq plus times data = function 
    | Certify_Left_Left_Absorptive -> "Left Left Absorptive\n" 
    | Certify_Not_Left_Left_Absorptive (a, b) -> 
       (* a <> a + (a * b) *)
       let times_a_b = times a b in
       let rhs = plus a times_a_b in
       if eq a rhs
       then "INTERNAL ERROR : Not Left left Absorptive\n"
       else "Not Left left Absorptive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a + a*b = rhs: \n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 

let string_of_check_left_right_absorptive eq plus times data = function 
    | Certify_Left_Right_Absorptive -> "Left_Right Absorptive \n" 
    | Certify_Not_Left_Right_Absorptive (a, b) -> 
       (* a <> a + (b * a) *)
       let times_b_a = times b a in
       let rhs = plus a times_b_a in
       if eq a rhs
       then "INTERNAL ERROR : Not Left Right Absorptive\n"
       else "Not Left Right Absorptive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a + b*a = rhs: \n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 


let string_of_check_right_left_absorptive eq plus times data = function 
    | Certify_Right_Left_Absorptive -> "Right_Left Absorptive\n" 
    | Certify_Not_Right_Left_Absorptive (a, b) ->
       (* a <> (a * b) + a *)
       let times_a_b = times a b in
       let rhs = plus times_a_b a in
       if eq a rhs
       then "INTERNAL ERROR : Not Right left Absorptive\n"
       else "Not Right left Absorptive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a*b + a = rhs: \n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 
       

let string_of_check_right_right_absorptive eq plus times data = function 
    | Certify_Right_Right_Absorptive -> "Right_Right Absorptive \n" 
    | Certify_Not_Right_Right_Absorptive (a, b) -> 
       (* a <> (b * a) + a *)
       let times_b_a = times b a in
       let rhs = plus times_b_a a in
       if eq a rhs
       then "INTERNAL ERROR : Not Right left Absorptive\n"
       else "Not Right left Absorptive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> b*a + a = rhs: \n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 
(*       
let string_of_check_plus_id_is_times_ann = function 
    | Certify_Plus_Id_Equals_Times_Ann _ -> "plus id = times annihilator\n"
    | Certify_Not_Plus_Id_Equals_Times_Ann -> "plus id <> times annihilator\n"

let string_of_check_times_id_is_plus_ann = function 
    | Certify_Times_Id_Equals_Plus_Ann _ -> "times id = plus annihilator\n"
    | Certify_Not_Times_Id_Equals_Plus_Ann -> "times id <> plus annihilator\n"
 *) 


(*******************************************************)

(*			 
let bop_describe bop = (print_string "Binary operation ->\n";  print_string (nl (ast_to_ascii bop)))			 			 
let plus_describe bop = (print_string "\nAdditive operation ->\n";
			 print_string   "--------------------\n";
			 print_string (nl (ast_to_ascii bop)))			 
let times_describe bop = (print_string "\nMultiplicative operation ->\n";
			  print_string   "--------------------------\n";
			  print_string (nl (ast_to_ascii bop)))


let eqv_describe (eqv : 'a Cas.eqv) = print_string "eqv_describe"

  (
     print_string "Carrier type: ";  print_string (nl (ast_type_to_ascii (eqv_type_ast (eqv_certs eqv))));
     print_string "Equality: ";      print_string (nl (ast_to_ascii (eqv_brel_ast (eqv_certs eqv))));     
  )
 *)
						
let sg_certs_describe eq b data certs =
  (
       (* bop_describe (sg_bop_ast certs); 			    *) 
       print_string (string_of_check_idempotent eq b data (certs.sg_idempotent_d)) ; 
       print_string (string_of_check_commutative eq b data (certs.sg_commutative_d)) ; 
       print_string (string_of_check_selective eq b data (certs.sg_selective_d)) 
      )
			   
let sg_describe sg =
 ( print_string (string_of_check_exists_id sg.sg_eqv.eqv_data (sg.sg_exists_id_d)) ; 
   print_string (string_of_check_exists_ann sg.sg_eqv.eqv_data (sg.sg_exists_ann_d)) ; 
   sg_certs_describe sg.sg_eqv.eqv_eq sg.sg_bop sg.sg_eqv.eqv_data sg.sg_certs) 



let sg_certs_describe_fully eq b data certs =
  (
       print_string (string_of_check_idempotent eq b data (certs.sg_idempotent_d)) ; 
       print_string (string_of_check_commutative eq b data (certs.sg_commutative_d)) ; 
       print_string (string_of_check_selective eq b data (certs.sg_selective_d)) ;
       print_string (string_of_check_left_cancellative eq b data (certs.sg_left_cancel_d)) ; 
       print_string (string_of_check_right_cancellative eq b data (certs.sg_right_cancel_d)) ; 
       print_string (string_of_check_left_constant eq b data (certs.sg_left_constant_d)) ; 
       print_string (string_of_check_right_constant eq b data (certs.sg_right_constant_d)) ; 
       print_string (string_of_check_anti_left eq b data (certs.sg_anti_left_d)) ; 
       print_string (string_of_check_anti_right eq b data (certs.sg_anti_right_d)) ; 
       print_string (string_of_check_is_left eq b data (certs.sg_is_left_d)) ;  
       print_string (string_of_check_is_right eq b data (certs.sg_is_right_d))
      )

let sg_describe_fully sg =
  (print_string (string_of_check_exists_id sg.sg_eqv.eqv_data (sg.sg_exists_id_d)) ; 
   print_string (string_of_check_exists_ann sg.sg_eqv.eqv_data (sg.sg_exists_ann_d)) ; 
   sg_certs_describe_fully sg.sg_eqv.eqv_eq sg.sg_bop sg.sg_eqv.eqv_data sg.sg_certs)

let bs_certs_describe eq plus times data certs = 
  (print_string "Interaction of Additive and Multiplicative operations: \n";
   print_string   "-------------------------------------------------------\n"; 
   print_string (string_of_check_left_distributive eq plus times data (certs.bs_left_distributive_d) ); 
   print_string (string_of_check_right_distributive eq plus times data (certs.bs_right_distributive_d) );
(*   
   print_string (string_of_check_plus_id_is_times_ann (bs_plus_id_is_times_ann_d) ); 
   print_string (string_of_check_times_id_is_plus_ann (bs_times_id_is_plus_ann_d)) ; 
 *)
  )

let bs_certs_describe_fully eq plus times data certs = 
     (print_string "Interaction of Additive and Multiplicative operations\n";
      print_string   "-------------------------------------------------------\n";    
       print_string (string_of_check_left_distributive eq plus times data (certs.bs_left_distributive_d) ); 
       print_string (string_of_check_right_distributive eq plus times data (certs.bs_right_distributive_d) );
       print_string (string_of_check_left_left_absorptive eq plus times data (certs.bs_left_left_absorptive_d) ); 
       print_string (string_of_check_left_right_absorptive eq plus times data (certs.bs_left_right_absorptive_d) ); 
       print_string (string_of_check_right_left_absorptive eq plus times data (certs.bs_right_left_absorptive_d) ); 
       print_string (string_of_check_right_right_absorptive eq plus times data (certs.bs_right_right_absorptive_d) )
      )

let eqv_describe_fully eqv =
  print_string ((describe_eqv_ast eqv.eqv_ast) ^ "\n");;

let describe_id data = function 
| Id_Ann_Cert_None                -> print_string "No identity\n"
| Id_Ann_Cert_Id_None id          -> print_string ("Identity = " ^ (data_to_ascii (data id)) ^ "\n")
| Id_Ann_Cert_None_Ann _          -> print_string "No identity\n"
| Id_Ann_Cert_Equal id_ann        -> print_string ("Identity = " ^ (data_to_ascii (data id_ann)) ^ "\n")
| Id_Ann_Cert_Not_Equal (id, _)   -> print_string ("Identity = " ^ (data_to_ascii (data id)) ^ "\n");; 

let describe_ann data = function 
| Id_Ann_Cert_None                -> print_string "No annihilator\n"
| Id_Ann_Cert_Id_None _           -> print_string "No annihilator\n"
| Id_Ann_Cert_None_Ann ann        -> print_string ("Annihilator = " ^ (data_to_ascii (data ann)) ^ "\n")
| Id_Ann_Cert_Equal id_ann        -> print_string ("Annihilator = " ^ (data_to_ascii (data id_ann)) ^ "\n")
| Id_Ann_Cert_Not_Equal (_, ann)  -> print_string ("Annihilator = " ^ (data_to_ascii (data ann)) ^ "\n");; 
						  
  
let id_ann_certs_describe_plus data id_ann_certs =
  (describe_id data id_ann_certs.id_ann_plus_times_d;
   describe_ann data id_ann_certs.id_ann_times_plus_d);; 

let id_ann_certs_describe_times data id_ann_certs =
  (describe_id data id_ann_certs.id_ann_times_plus_d;
   describe_ann data id_ann_certs.id_ann_plus_times_d);; 
                                                      

let bs_describe bs =
    let eqv         = bs.bs_eqv          in        
    let eq          = bs.bs_eqv.eqv_eq   in   
    let data        = bs.bs_eqv.eqv_data in 
    let plus_certs  = bs.bs_plus_certs   in 
    let times_certs = bs.bs_times_certs  in
    let id_ann_certs = bs.bs_id_ann_certs  in     
    let certs       = bs.bs_certs        in
    let plus        = bs.bs_plus         in
    let times       = bs.bs_times        in
    let ast         = bs.bs_ast          in             
    (print_string "Carrier set:\n";
     eqv_describe_fully eqv;
     print_string "Additive properties:\n";
     print_string "--------------------\n";         
     sg_certs_describe eq plus data plus_certs;
     id_ann_certs_describe_plus data id_ann_certs;
     print_string "Multiplicative properties:\n";
     print_string "-------------------------\n";              
     sg_certs_describe eq times data times_certs;
     id_ann_certs_describe_times data id_ann_certs;
     bs_certs_describe eq plus times data certs
      )

let bs_describe_fully bs =
    let eqv         = bs.bs_eqv          in      
    let eq          = eqv.eqv_eq         in   
    let data        = bs.bs_eqv.eqv_data in 
    let plus_certs  = bs.bs_plus_certs   in 
    let times_certs = bs.bs_times_certs  in
    let id_ann_certs = bs.bs_id_ann_certs  in         
    let certs       = bs.bs_certs        in
    let plus        = bs.bs_plus         in
    let times       = bs.bs_times        in
    let ast         = bs.bs_ast          in             
    (print_string "Carrier set:\n";
     eqv_describe_fully eqv; 
     print_string "Additive properties:\n";
     print_string "--------------------\n";    
     sg_certs_describe_fully eq plus data plus_certs;
     id_ann_certs_describe_plus data id_ann_certs;
     print_string "Multiplicative properties:\n";
     print_string "-------------------------\n";         
     sg_certs_describe_fully eq times data times_certs;
     id_ann_certs_describe_times data id_ann_certs;
     bs_certs_describe_fully eq plus times data certs
    )


let string_of_bs_mcas_class mbs = 
match mbs with 
| BS_Error cll -> errors (List.map char_list_to_string cll)
| BS_bs _ -> "Bi-semigroup"
| BS_bs_CI _ -> "Commuative and Idempotent Bi-semigroup" 
| BS_bs_CS _ -> "Commuative and Selective Bi-semigroup" 
| BS_presemiring _ -> "Pre-Semiring"
| BS_semiring  _ -> "Semiring"
| BS_pre_dioid  _ -> "Pre-Dioid"
| BS_pre_dioid_with_one  _ -> "Pre-Dioid with One"
| BS_pre_dioid_with_zero _ -> "Pre-Dioid with Zero"
| BS_dioid _ -> "Dioid"
| BS_prelattice _ -> "Pre-Lattice"
| BS_distributive_prelattice _ -> "Distributive Pre-Lattice"
| BS_lattice _ -> "Lattice"
| BS_distributive_lattice _ -> "Distributive Lattice"
| BS_selective_presemiring _ -> "Selective Pre-Semiring"
| BS_selective_semiring _ -> "Selective Semiring"
| BS_selective_pre_dioid _ -> "Selective Pre-Dioid"
| BS_selective_pre_dioid_with_zero _ -> "Selective Pre-Dioid with Zero"
| BS_selective_pre_dioid_with_one _ -> "Selective Pre-Dioid with One"
| BS_selective_dioid _ -> "Selective Dioid"
| BS_selective_cancellative_pre_dioid _ -> "Selective Cancellative Pre-Dioid"
| BS_selective_cancellative_pre_dioid_with_zero _ -> "Selective Cancellative Pre-Dioid with Zero"
| BS_selective_cancellative_pre_dioid_with_one  _ -> "Selective Cancellative Pre-Dioid with One"
| BS_selective_cancellative_dioid _ -> "Selective Cancellative Dioid"
| BS_selective_distributive_prelattice _ -> "Selective Distributive Pre-Lattice"
| BS_selective_distributive_prelattice_with_zero _ -> "Selective Distributive Pre-Lattice with Zero"
| BS_selective_distributive_prelattice_with_one _ -> "Selective Distributive Pre-Lattice with One"
| BS_selective_distributive_lattice _ -> "Selective Distributive Lattice"


let mcas_bs_describe mbs =
  (print_string ("Class : " ^ (string_of_bs_mcas_class mbs) ^ "\n"); 
  match bs_mcas_cast_up mbs with
  | BS_bs bs -> bs_describe bs
  | _        -> error "internal error: mcas_bs_describe")
      
let mcas_bs_describe_fully mbs =
  (print_string ("Class : " ^ (string_of_bs_mcas_class mbs) ^ "\n");   
  match bs_mcas_cast_up mbs with
  | BS_bs bs -> bs_describe_fully bs
  | _        -> error "internal error: mcas_bs_describe_fully" )


(* **** *)

let get_plus = function 
| BS_Error cll -> errors (List.map char_list_to_string cll)
| BS_bs bs -> bs.bs_plus 
| BS_bs_CI bs -> bs.bs_CI_plus 
| BS_bs_CS bs -> bs.bs_CS_plus  
| BS_presemiring bs -> bs.presemiring_plus  
| BS_semiring  bs ->  bs.semiring_plus  
| BS_pre_dioid  bs ->  bs.pre_dioid_plus  
| BS_pre_dioid_with_one bs ->  bs.pre_dioid_with_one_plus  
| BS_pre_dioid_with_zero bs ->  bs.pre_dioid_with_zero_plus  
| BS_dioid bs ->  bs.dioid_plus  
| BS_prelattice bs ->  bs.prelattice_join
| BS_distributive_prelattice bs ->  bs.distributive_prelattice_join   
| BS_lattice bs ->  bs.lattice_join   
| BS_distributive_lattice bs ->  bs.distributive_lattice_join   
| BS_selective_presemiring bs ->  bs.selective_presemiring_plus  
| BS_selective_semiring bs ->  bs.selective_semiring_plus  
| BS_selective_pre_dioid bs ->  bs.selective_pre_dioid_plus  
| BS_selective_pre_dioid_with_zero bs -> bs.selective_pre_dioid_with_zero_plus  
| BS_selective_pre_dioid_with_one bs ->  bs.selective_pre_dioid_with_one_plus  
| BS_selective_dioid bs ->  bs.selective_dioid_plus  
| BS_selective_cancellative_pre_dioid bs -> bs.selective_cancellative_pre_dioid_plus   
| BS_selective_cancellative_pre_dioid_with_zero bs -> bs.selective_cancellative_pre_dioid_with_zero_plus    
| BS_selective_cancellative_pre_dioid_with_one  bs ->  bs.selective_cancellative_pre_dioid_with_one_plus    
| BS_selective_cancellative_dioid bs ->  bs.selective_cancellative_dioid_plus    
| BS_selective_distributive_prelattice bs ->  bs.selective_distributive_prelattice_join
| BS_selective_distributive_prelattice_with_zero bs -> bs.selective_distributive_prelattice_with_zero_join
| BS_selective_distributive_prelattice_with_one bs -> bs.selective_distributive_prelattice_with_one_join
| BS_selective_distributive_lattice bs -> bs.selective_distributive_lattice_join

let get_times = function 
| BS_Error cll -> errors (List.map char_list_to_string cll)
| BS_bs bs -> bs.bs_times 
| BS_bs_CI bs -> bs.bs_CI_times 
| BS_bs_CS bs -> bs.bs_CS_times  
| BS_presemiring bs -> bs.presemiring_times  
| BS_semiring  bs ->  bs.semiring_times  
| BS_pre_dioid  bs ->  bs.pre_dioid_times  
| BS_pre_dioid_with_one bs ->  bs.pre_dioid_with_one_times  
| BS_pre_dioid_with_zero bs ->  bs.pre_dioid_with_zero_times  
| BS_dioid bs ->  bs.dioid_times  
| BS_prelattice bs ->  bs.prelattice_meet
| BS_distributive_prelattice bs ->  bs.distributive_prelattice_meet   
| BS_lattice bs ->  bs.lattice_meet   
| BS_distributive_lattice bs ->  bs.distributive_lattice_meet   
| BS_selective_presemiring bs ->  bs.selective_presemiring_times  
| BS_selective_semiring bs ->  bs.selective_semiring_times  
| BS_selective_pre_dioid bs ->  bs.selective_pre_dioid_times  
| BS_selective_pre_dioid_with_zero bs -> bs.selective_pre_dioid_with_zero_times  
| BS_selective_pre_dioid_with_one bs ->  bs.selective_pre_dioid_with_one_times  
| BS_selective_dioid bs ->  bs.selective_dioid_times  
| BS_selective_cancellative_pre_dioid bs -> bs.selective_cancellative_pre_dioid_times   
| BS_selective_cancellative_pre_dioid_with_zero bs -> bs.selective_cancellative_pre_dioid_with_zero_times    
| BS_selective_cancellative_pre_dioid_with_one  bs ->  bs.selective_cancellative_pre_dioid_with_one_times    
| BS_selective_cancellative_dioid bs ->  bs.selective_cancellative_dioid_times    
| BS_selective_distributive_prelattice bs ->  bs.selective_distributive_prelattice_meet
| BS_selective_distributive_prelattice_with_zero bs -> bs.selective_distributive_prelattice_with_zero_meet
| BS_selective_distributive_prelattice_with_one bs -> bs.selective_distributive_prelattice_with_one_meet
| BS_selective_distributive_lattice bs -> bs.selective_distributive_lattice_meet


let get_eq = function 
| BS_Error cll -> errors (List.map char_list_to_string cll)
| BS_bs bs -> bs.bs_eqv.eqv_eq
| BS_bs_CI bs -> bs.bs_CI_times 
| BS_bs_CS bs -> bs.bs_CS_times  
| BS_presemiring bs -> bs.presemiring_times  
| BS_semiring  bs ->  bs.semiring_times  
| BS_pre_dioid  bs ->  bs.pre_dioid_times  
| BS_pre_dioid_with_one bs ->  bs.pre_dioid_with_one_times  
| BS_pre_dioid_with_zero bs ->  bs.pre_dioid_with_zero_times  
| BS_dioid bs ->  bs.dioid_times  
| BS_prelattice bs ->  bs.prelattice_meet
| BS_distributive_prelattice bs ->  bs.distributive_prelattice_meet   
| BS_lattice bs ->  bs.lattice_meet   
| BS_distributive_lattice bs ->  bs.distributive_lattice_meet   
| BS_selective_presemiring bs ->  bs.selective_presemiring_times  
| BS_selective_semiring bs ->  bs.selective_semiring_times  
| BS_selective_pre_dioid bs ->  bs.selective_pre_dioid_times  
| BS_selective_pre_dioid_with_zero bs -> bs.selective_pre_dioid_with_zero_times  
| BS_selective_pre_dioid_with_one bs ->  bs.selective_pre_dioid_with_one_times  
| BS_selective_dioid bs ->  bs.selective_dioid_times  
| BS_selective_cancellative_pre_dioid bs -> bs.selective_cancellative_pre_dioid_times   
| BS_selective_cancellative_pre_dioid_with_zero bs -> bs.selective_cancellative_pre_dioid_with_zero_times    
| BS_selective_cancellative_pre_dioid_with_one  bs ->  bs.selective_cancellative_pre_dioid_with_one_times    
| BS_selective_cancellative_dioid bs ->  bs.selective_cancellative_dioid_times    
| BS_selective_distributive_prelattice bs ->  bs.selective_distributive_prelattice_meet
| BS_selective_distributive_prelattice_with_zero bs -> bs.selective_distributive_prelattice_with_zero_meet
| BS_selective_distributive_prelattice_with_one bs -> bs.selective_distributive_prelattice_with_one_meet
| BS_selective_distributive_lattice bs -> bs.selective_distributive_lattice_meet
					    
    
