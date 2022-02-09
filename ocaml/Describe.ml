open Cas

let nl s = s ^ "\n"       

let char_list_to_string cl = String.concat "" (List.map (String.make 1) cl)

let rec from_to start finish =
  if start > finish
  then []
  else start :: (from_to (start + 1) finish);;

let string_to_char_list s = List.map (String.get s) (from_to 0 ((String.length s) - 1));;

let make_constant' s1 s2 = make_constant (string_to_char_list s1) (string_to_char_list s2);;

let infinity = make_constant' "INF"  "\\infty";;

type string_type = Ascii | Latex


(* 
type cas_eqv_ast =
| Ast_eqv_bool
| Ast_eqv_nat
| Ast_eqv_list of cas_eqv_ast
| Ast_eqv_set of cas_eqv_ast
| Ast_eqv_product of (cas_eqv_ast*cas_eqv_ast)
| Ast_eqv_sum of (cas_eqv_ast*cas_eqv_ast)
| Ast_eqv_add_constant of (cas_constant*cas_eqv_ast)
| Ast_eqv_nat_ceiling of int
| Ast_eqv_minset of cas_or_ast
| Ast_eqv_of_or of cas_or_ast
| Ast_eqv_of_sg of cas_sg_ast
| Ast_eqv_of_bs of cas_bs_ast
| Ast_eqv_of_os of cas_os_ast
and cas_or_ast =
| Ast_or_nat
| Ast_or_bool
| Ast_or_add_bottom of (cas_constant*cas_or_ast)
| Ast_or_add_top of (cas_constant*cas_or_ast)
| Ast_or_dual of cas_or_ast
| Ast_or_llte of cas_sg_ast
| Ast_or_rlte of cas_sg_ast
| Ast_or_length of cas_eqv_ast
| Ast_or_llex of (cas_or_ast*cas_or_ast)
| Ast_or_product of (cas_or_ast*cas_or_ast)
| Ast_or_subset of cas_eqv_ast
| Ast_or_set of cas_eqv_ast
| Ast_or_left_sum of (cas_or_ast*cas_or_ast)
| Ast_or_right_sum of (cas_or_ast*cas_or_ast)
| Ast_or_trivial of cas_eqv_ast
| Ast_or_of_os of cas_os_ast
and cas_sg_ast =
| Ast_sg_times
| Ast_sg_plus
| Ast_sg_or
| Ast_sg_and
| Ast_sg_min
| Ast_sg_max
| Ast_sg_add_id of (cas_constant*cas_sg_ast)
| Ast_sg_add_ann of (cas_constant*cas_sg_ast)
| Ast_sg_concat of cas_eqv_ast
| Ast_sg_union of (cas_constant*cas_eqv_ast)
| Ast_sg_intersect of (cas_constant*cas_eqv_ast)
| Ast_sg_left of cas_eqv_ast
| Ast_sg_right of cas_eqv_ast
| Ast_sg_left_sum of (cas_sg_ast*cas_sg_ast)
| Ast_sg_right_sum of (cas_sg_ast*cas_sg_ast)
| Ast_sg_lift of cas_sg_ast
| Ast_sg_llex of (cas_sg_ast*cas_sg_ast)
| Ast_sg_product of (cas_sg_ast*cas_sg_ast)
| Ast_sg_minset_lift of cas_os_ast
| Ast_sg_minset_union of cas_or_ast
| Ast_sg_plus_of_bs of cas_bs_ast
| Ast_sg_times_of_bs of cas_bs_ast
| Ast_sg_times_of_os of cas_os_ast
and cas_bs_ast =
| Ast_min_plus
| Ast_max_plus
| Ast_and_or
| Ast_or_and
| Ast_max_min
| Ast_min_max
| Ast_bs_add_zero of (cas_constant*cas_bs_ast)
| Ast_bs_add_one of (cas_constant*cas_bs_ast)
| Ast_bs_product of (cas_bs_ast*cas_bs_ast)
| Ast_bs_llex_product of (cas_bs_ast*cas_bs_ast)
| Ast_bs_union_lift of cas_sg_ast
| Ast_bs_left_sum_right_sum of (cas_bs_ast*cas_bs_ast)
| Ast_bs_right_sum_left_sum of (cas_bs_ast*cas_bs_ast)
| Ast_bs_left of cas_sg_ast
| Ast_bs_right of cas_sg_ast
| Ast_union_intersect of (cas_constant*cas_eqv_ast)
| Ast_intersect_union of (cas_constant*cas_eqv_ast)
| Ast_bs_dual of cas_bs_ast
| Ast_minset_lift_union of cas_os_ast
| Ast_minset_union_lift of cas_os_ast
| Ast_lift_union of cas_sg_ast
| Ast_union_lift of cas_sg_ast
and cas_os_ast =
| Ast_os_from_bs_left of cas_bs_ast
| Ast_os_from_bs_right of cas_bs_ast
| Ast_os_llex_product of (cas_os_ast*cas_os_ast)
| Ast_os_product of (cas_os_ast*cas_os_ast)
| Ast_os_add_bottom_id of (cas_constant*cas_os_ast)
| Ast_os_add_top_ann of (cas_constant*cas_os_ast)
and cas_ltr_ast =
| Ast_ltr_cons of cas_eqv_ast
| Ast_ltr_product of (cas_ltr_ast*cas_ltr_ast)
| Ast_ltr_left_sum of (cas_ltr_ast*cas_ltr_ast)
| Ast_ltr_right_sum of (cas_ltr_ast*cas_ltr_ast)
| Ast_ltr_lift of cas_ltr_ast
| Ast_ltr_from_sg of cas_ltr_ast
| Ast_ltr_with_policy of cas_ltr_ast
and cas_lstr_ast =
| Ast_lstr_product of (cas_lstr_ast*cas_lstr_ast)
| Ast_lstr_llex_product of (cas_lstr_ast*cas_lstr_ast)
and cas_lotr_ast =
| Ast_lotr_length_cons of cas_eqv_ast
| Ast_lotr_product of (cas_lotr_ast*cas_lotr_ast)
| Ast_lotr_llex_product of (cas_lotr_ast*cas_lotr_ast)

 *) 

			     

(*			     
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
			     
let rec data_to_ascii = data_to_string Ascii
let rec data_to_latex = data_to_string Latex 

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



 *)
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
       then "INTERNAL ERROR\n"
       else "Not Commutative -> \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data lhs)) ^ "\n" ^
	      "   " ^ (data_to_ascii (data b)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data rhs)) ^ "\n"

let string_of_check_idempotent eq bop data = function 
    | Certify_Idempotent -> "Idempotent\n" 
    | Certify_Not_Idempotent a ->
       let result = bop a a in
       if eq a result
       then "INTERNAL ERROR\n"
       else "Not Idempotent -> \n" ^
	    "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n" 

let string_of_check_selective eq bop data = function 
    | Certify_Selective -> "Selective \n" 
    | Certify_Not_Selective (a, b) ->
       let result = bop a b in
       if (eq a result) || (eq b result)
       then "INTERNAL ERROR\n"
       else "Not Selective -> \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"

let string_of_check_anti_left eq bop data = function 
    | Certify_Anti_Left -> "Anti Left\n" 
    | Certify_Not_Anti_Left (a, b) ->
       let result = bop a b in
       if eq a result 
       then "Not Anti Left -> \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
       else "INTERNAL ERROR\n"

let string_of_check_anti_right eq bop data = function 
    | Certify_Anti_Right -> "Anti Right\n" 
    | Certify_Not_Anti_Right (s, t) -> 
       let result = bop t s in
       if eq s result 
       then "Not Anti Right -> \n" ^
	      "   " ^ (data_to_ascii (data t)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
       else "INTERNAL ERROR\n"


let string_of_check_is_left eq bop data = function 
    | Certify_Is_Left -> "Is Left\n" 
    | Certify_Not_Is_Left (a, b) ->
       let result = bop a b in
       if eq a result 
       then "INTERNAL ERROR\n"
       else "Not Is Left -> \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"

let string_of_check_is_right eq bop data = function 
    | Certify_Is_Right -> "Is Right\n" 
    | Certify_Not_Is_Right (a, b) -> 
       let result = bop a b in
       if eq b result 
       then "INTERNAL ERROR\n"
       else "Not Is Right -> \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
															   

let string_of_check_left_cancellative eq bop data = function 
    | Certify_Left_Cancellative -> "Left Cancellative\n" 
    | Certify_Not_Left_Cancellative (a, (b, c)) ->
       (* ab = ac and b <> c *)
       let ab = bop a b in
       let ac = bop a c in       
       if eq b c 
       then "INTERNAL ERROR\n"
       else if eq ab ac
            then "Not Left Cancellative -> \n" ^
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
       then "INTERNAL ERROR\n"
       else if eq ba ca
            then "Not Right Cancellative -> \n" ^
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
       then "INTERNAL ERROR\n"
       else "Not Left Constant -> \n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data ab)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data c)) ^ " = " ^ (data_to_ascii (data ac)) ^ "\n"


let string_of_check_right_constant eq bop data = function 
    | Certify_Right_Constant -> "Right Constant\n" 
    | Certify_Not_Right_Constant (a, (b, c)) -> 
       (* ba <> ca *) 
       let ba = bop b a in
       let ca = bop c a in       
       if eq ba ca 
       then "INTERNAL ERROR\n"
       else "Not Right Constant -> \n" ^
		   "   " ^ (data_to_ascii (data b)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data ba)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data c)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data ca)) ^ "\n"


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
       then "INTERNAL ERROR\n"
       else "Not Left Distributive -> \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   c = " ^ (data_to_ascii (data c)) ^ "\n" ^				  
	      "   lhs = a*(b + c) <> a*b + a*c = rhs -> \n" ^
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
       then "INTERNAL ERROR\n"
       else "Not Right Distributive -> \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   c = " ^ (data_to_ascii (data c)) ^ "\n" ^				  
	      "   lhs = (b + c)*a <> b*a + c*a = rhs -> \n" ^
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
       then "INTERNAL ERROR\n"
       else "Not Left left Absorptive -> \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a + a*b = rhs -> \n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 

let string_of_check_left_right_absorptive eq plus times data = function 
    | Certify_Left_Right_Absorptive -> "Left_Right Absorptive \n" 
    | Certify_Not_Left_Right_Absorptive (a, b) -> 
       (* a <> a + (b * a) *)
       let times_b_a = times b a in
       let rhs = plus a times_b_a in
       if eq a rhs
       then "INTERNAL ERROR\n"
       else "Not Left Right Absorptive -> \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a + b*a = rhs -> \n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 


let string_of_check_right_left_absorptive eq plus times data = function 
    | Certify_Right_Left_Absorptive -> "Right_Left Absorptive\n" 
    | Certify_Not_Right_Left_Absorptive (a, b) ->
       (* a <> (a * b) + a *)
       let times_a_b = times a b in
       let rhs = plus times_a_b a in
       if eq a rhs
       then "INTERNAL ERROR\n"
       else "Not Right left Absorptive -> \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a*b + a = rhs -> \n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 
       

let string_of_check_right_right_absorptive eq plus times data = function 
    | Certify_Right_Right_Absorptive -> "Right_Right Absorptive \n" 
    | Certify_Not_Right_Right_Absorptive (a, b) -> 
       (* a <> (b * a) + a *)
       let times_b_a = times b a in
       let rhs = plus times_b_a a in
       if eq a rhs
       then "INTERNAL ERROR\n"
       else "Not Right left Absorptive -> \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> b*a + a = rhs -> \n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 
       
let string_of_check_plus_id_is_times_ann = function 
    | Certify_Plus_Id_Equals_Times_Ann _ -> "plus id = times annihilator\n"
    | Certify_Not_Plus_Id_Equals_Times_Ann -> "plus id <> times annihilator\n"

let string_of_check_times_id_is_plus_ann = function 
    | Certify_Times_Id_Equals_Plus_Ann _ -> "times id = plus annihilator\n"
    | Certify_Not_Times_Id_Equals_Plus_Ann -> "times id <> plus annihilator\n"



(*******************************************************)


let bop_describe bop = (print_string "Binary operation ->\n";  print_string (nl (ast_to_ascii bop)))			 			 
let plus_describe bop = (print_string "\nAdditive operation ->\n";
			 print_string   "--------------------\n";
			 print_string (nl (ast_to_ascii bop)))			 
let times_describe bop = (print_string "\nMultiplicative operation ->\n";
			  print_string   "--------------------------\n";
			  print_string (nl (ast_to_ascii bop)))


let eqv_describe (eqv : 'a Cas.eqv) = print_string "eqv_describe"
(*			 
  (
     print_string "Carrier type: ";  print_string (nl (ast_type_to_ascii (eqv_type_ast (eqv_certs eqv))));
     print_string "Equality: ";      print_string (nl (ast_to_ascii (eqv_brel_ast (eqv_certs eqv))));     
  )
 *) 			   
let sg_certs_describe eq b data sg =
  let certs = sg_certs sg in 
  (
       (* bop_describe (sg_bop_ast certs); 			    *) 
       print_string (string_of_check_idempotent eq b data (sg_idempotent_d certs)) ; 
       print_string (string_of_check_commutative eq b data (sg_commutative_d certs)) ; 
       print_string (string_of_check_selective eq b data (sg_selective_d certs)) ;
       print_string (string_of_check_exists_id data (sg_exists_id_d sg)) ; 
       print_string (string_of_check_exists_ann data (sg_exists_ann_d sg)) ; 
      )
			   

let asg_certs_describe eq b data sg certs =
     (
       print_string "Commutative\n" ; 
       print_string (string_of_check_idempotent eq b data (asg_idempotent_d certs)) ;
       print_string (string_of_check_selective eq b data (asg_selective_d certs)) ;       
(*       
       print_string (string_of_check_exists_ann data (asg_exists_ann_d sg)) ; 
       print_string (string_of_check_exists_id data (asg_exists_id_d sg)) ; 
 *) 

      )
			   

let msg_certs_describe eq b data certs = () 	
(*
let msg_certs_describe eq b data certs = 
      (
       print_string (string_of_check_commutative eq b data (msg_commutative_d certs)) ; 
       print_string (string_of_check_exists_id data (msg_exists_id_d certs)) ; 
       print_string (string_of_check_exists_ann data (msg_exists_ann_d certs)) ; 
      )
 *)	
	

let sg_describe sg =
  ((eqv_describe (sg_eq sg)); 
   sg_certs_describe (eqv_eq (sg_eq sg)) (sg_bop sg) (eqv_data (sg_eq sg)) sg)


let asg_certs_describe_fully = asg_certs_describe   

let msg_certs_describe_fully eq b data certs =  ()
(*						  
      (
       print_string (string_of_check_commutative eq b data (msg_commutative_d certs)) ; 
       print_string (string_of_check_exists_id data (msg_exists_id_d certs)) ; 
       print_string (string_of_check_exists_ann data (msg_exists_ann_d certs)) ; 
       print_string (string_of_check_left_cancellative eq b data (msg_left_cancel_d certs)) ; 
       print_string (string_of_check_right_cancellative eq b data (msg_right_cancel_d certs)) ; 
       print_string (string_of_check_left_constant eq b data (msg_left_constant_d certs)) ; 
       print_string (string_of_check_right_constant eq b data (msg_right_constant_d certs)) ; 
       print_string (string_of_check_anti_left eq b data (msg_anti_left_d certs)) ; 
       print_string (string_of_check_anti_right eq b data (msg_anti_right_d certs)) ; 
       print_string (string_of_check_is_left eq b data (msg_is_left_d certs)) ;  
       print_string (string_of_check_is_right eq b data (msg_is_right_d certs))
      )
 *)    
			   
let sg_certs_describe_fully eq b data sg =
  let certs = sg_certs sg in   
  (
    (* bop_describe (sg_bop_ast certs); 			        *)
       print_string (string_of_check_idempotent eq b data (sg_idempotent_d certs)) ; 
       print_string (string_of_check_commutative eq b data (sg_commutative_d certs)) ; 
       print_string (string_of_check_selective eq b data (sg_selective_d certs)) ;
       print_string (string_of_check_exists_id data (sg_exists_id_d sg)) ; 
       print_string (string_of_check_exists_ann data (sg_exists_ann_d sg)) ; 
       print_string (string_of_check_left_cancellative eq b data (sg_left_cancel_d certs)) ; 
       print_string (string_of_check_right_cancellative eq b data (sg_right_cancel_d certs)) ; 
       print_string (string_of_check_left_constant eq b data (sg_left_constant_d certs)) ; 
       print_string (string_of_check_right_constant eq b data (sg_right_constant_d certs)) ; 
       print_string (string_of_check_anti_left eq b data (sg_anti_left_d certs)) ; 
       print_string (string_of_check_anti_right eq b data (sg_anti_right_d certs)) ; 
       print_string (string_of_check_is_left eq b data (sg_is_left_d certs)) ;  
       print_string (string_of_check_is_right eq b data (sg_is_right_d certs))
      )

let sg_describe_fully sg =
  ((eqv_describe (sg_eq sg)); 
   sg_certs_describe_fully (eqv_eq (sg_eq sg)) (sg_bop sg) (eqv_data (sg_eq sg)) sg)

(*    
let sg_C_describe sg  = sg_describe (sg_from_sg_C sg)
let sg_CS_describe sg = sg_describe (sg_from_sg_CS sg)
let sg_CI_describe sg = sg_describe (sg_from_sg_CI sg)
let sg_CK_describe sg = sg_describe (sg_from_sg_CK sg)
 *)


let bs_certs_describe eq plus times data certs = 
  (print_string "\nInteraction of Additive and Multiplicative operations-> \n";
   print_string   "-------------------------------------------------------\n"; 
   print_string (string_of_check_left_distributive eq plus times data (bs_left_distributive_d certs) ); 
   print_string (string_of_check_right_distributive eq plus times data (bs_right_distributive_d certs) );
(*   
   print_string (string_of_check_plus_id_is_times_ann (bs_plus_id_is_times_ann_d certs) ); 
   print_string (string_of_check_times_id_is_plus_ann (bs_times_id_is_plus_ann_d certs)) ; 
 *)
  )

let bs_describe bs =
    let eq          = eqv_eq (bs_eqv bs)   in   
    let data        = eqv_data (bs_eqv bs) in 
    let plus_certs  = bs_plus_certs bs     in 
    let times_certs = bs_times_certs bs    in 
    let certs       = bs_certs bs          in
    let plus        = bs_plus bs           in
    let times       = bs_times bs          in
    let ast         = bs_ast bs            in             
    (

      eqv_describe (bs_eqv bs);
(*            
       plus_describe (bs_plus_ast bs); 
 *) 
      asg_certs_describe eq plus data plus_certs;
(*      
       times_describe (bs_times_ast bs);        
*)
       msg_certs_describe eq times data times_certs; 
       bs_certs_describe eq plus times data certs
      )
    

let bs_certs_describe_fully eq plus times data certs = 
     (print_string "\nInteraction of Additive and Multiplicative operations-> \n";
      print_string   "-------------------------------------------------------\n";    
       print_string (string_of_check_left_distributive eq plus times data (bs_left_distributive_d certs) ); 
       print_string (string_of_check_right_distributive eq plus times data (bs_right_distributive_d certs) );
       print_string (string_of_check_left_left_absorptive eq plus times data (bs_left_left_absorptive_d certs) ); 
       print_string (string_of_check_left_right_absorptive eq plus times data (bs_left_right_absorptive_d certs) ); 
       print_string (string_of_check_right_left_absorptive eq plus times data (bs_right_left_absorptive_d certs) ); 
       print_string (string_of_check_right_right_absorptive eq plus times data (bs_right_right_absorptive_d certs) )
      )


let id_ann_certs_describe_fully data certs = 
     (print_string "\nIdentiy and Annhilator-> \n";
      print_string   "------------------------\n";
       print_string (string_of_check_exists_id data (id_ann_exists_plus_id_d certs)) ; 
       print_string (string_of_check_exists_ann data (id_ann_exists_plus_ann_d certs)) ; 
       print_string (string_of_check_exists_id data (id_ann_exists_times_id_d certs)) ; 
       print_string (string_of_check_exists_ann data (id_ann_exists_times_ann_d certs)) ;       
       print_string (string_of_check_plus_id_is_times_ann (id_ann_plus_id_is_times_ann_d certs) ); 
       print_string (string_of_check_times_id_is_plus_ann (id_ann_times_id_is_plus_ann_d certs)) ; 
      )


       
let bs_describe_fully bs =
    let eq          = eqv_eq (bs_eqv bs)   in   
    let data        = eqv_data (bs_eqv bs) in 
    let plus_certs  = bs_plus_certs bs     in 
    let times_certs = bs_times_certs bs    in
    let id_ann_certs = bs_id_ann_certs bs    in     
    let certs       = bs_certs bs          in
    let plus        = bs_plus bs           in
    let times       = bs_times bs          in
    let ast         = bs_ast bs            in             
    (
      eqv_describe (bs_eqv bs);
      (*      plus_describe (asg_bop_ast plus_certs); *)
      asg_certs_describe_fully eq plus data plus_certs ;
      (*      times_describe (msg_bop_ast times_certs); *) 
      msg_certs_describe_fully eq times data times_certs;
      id_ann_certs_describe_fully data ;
      bs_certs_describe_fully eq plus times data certs
      )

					     

 *)
