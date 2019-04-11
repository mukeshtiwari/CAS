
let upto k = let rec aux m = if k <= m then [] else m :: (aux (m +1)) in aux 0        
let explode s = List.map (fun i -> String.get s i) (upto (String.length s)) 

(* mbind : 'a option -> ('a -> 'b option) -> 'b option  *) 
let mbind m f = match m with Some a -> f a | None -> None

(* mreturn : 'a -> 'a option = <fun> *) 
let mreturn a = Some a

(* ommap : ('a -> 'b) -> 'a option -> 'b option *) 
let mmap f m = mbind m (fun a -> mreturn (f a)) 

(* liftM : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option *) 
let liftM f m n = 
    mbind m (fun a -> 
    mbind n (fun b -> mreturn (f a b)))

(* liftN : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option *) 
let liftN f m n = 
    mbind m (fun a -> 
    mbind n (fun b -> f a b))

let make_constant s1 s2 = Cas.make_constant (explode s1) (explode s2)
let infinity      = make_constant "INFINITY" "\\infty" 
let self          = make_constant "SELF" "\\self" 
let bottom        = make_constant "BOTTOM"  "\\bottom" 
let top           = make_constant "TOP" "\\top" 
				      

let eq_nat           = Cas.eqv_eq_nat
let eqv_bool         = Cas.eqv_bool
let eqv_product      = Cas.eqv_product
let eqv_sum          = Cas.eqv_sum 
let eqv_add_constant c eqv = Cas.eqv_add_constant eqv c
let eqv_list         = Cas.eqv_list
let eqv_set          = Cas.eqv_set
let eqv_nat_ceiling  = Cas.eqv_nat_ceiling
			 
let sg_and   = Some (Cas.sg_from_sg_CS Cas.sg_CS_and)   (* : bool sg option *) 
let sg_or    = Some (Cas.sg_from_sg_CS Cas.sg_CS_or)    (* : bool sg option *) 

let sg_min   = Some (Cas.sg_from_sg_CS Cas.sg_CS_min)   (* : int sg option *) 
let sg_max   = Some (Cas.sg_from_sg_CS Cas.sg_CS_max)   (* : int sg option *) 
let sg_times = Some (Cas.sg_from_sg_C Cas.sg_C_times)   (* : int sg option *) 
let sg_plus  = Some (Cas.sg_from_sg_CK Cas.sg_CK_plus)  (* : int sg option *) 

let sg_left eqv       = Some(Cas.sg_left eqv)
let sg_right eqv      = Some(Cas.sg_right eqv)
let sg_concat eqv     = Some(Cas.sg_concat eqv)


let sg_add_id c sg      = mmap (Cas.sg_add_id c) sg
let sg_add_ann c sg    = mmap (Cas.sg_add_ann c) sg

let sg_product m n  = liftM Cas.sg_product m n   

let sg_left_sum m n = liftM Cas.sg_left_sum m n 
let sg_right_sum m n = liftM Cas.sg_right_sum m n


let sg_llex m n = 
    let sg_llex_aux sg1 sg2 = 
        match (Cas.sg_CS_option_from_sg sg1) with 
       | None -> None 
       | Some sg1'-> Some(Cas.sg_llex sg1' sg2)
    in liftN sg_llex_aux m n  

let sg_union eqv     = Some (Cas.sg_from_sg_CI (Cas.sg_CI_union eqv)) 
let sg_intersect eqv = Some (Cas.sg_from_sg_CI (Cas.sg_CI_intersect eqv)) 
let sg_lift sg       = mmap Cas.sg_lift sg

(* bi-semigroup *) 

let bs_and_or   = Some (Cas.bs_from_selective_distributive_lattice Cas.selective_distributive_lattice_and_or) 
let bs_or_and   = Some (Cas.bs_from_selective_distributive_lattice Cas.selective_distributive_lattice_or_and)  


let bs_min_max  = Some (Cas.bs_from_selective_distributive_lattice Cas.selective_distributive_lattice_min_max) 
let bs_max_min  = Some (Cas.bs_from_selective_distributive_lattice Cas.selective_distributive_lattice_max_min) 
let bs_min_plus = Some (Cas.bs_from_selective_dioid Cas.selective_dioid_min_plus) 
let bs_max_plus = Some (Cas.bs_from_selective_dioid Cas.selective_dioid_max_plus) 

let bs_sg_left = function
  | None -> None 
  | Some sg ->
     (match (Cas.sg_CS_option_from_sg sg) with 
       | None -> (match (Cas.sg_CI_option_from_sg sg) with 
                  | None -> None 
		  | Some sg'-> Some(Cas.bs_from_dioid (Cas.dioid_sg_left sg')))
       | Some sg'-> Some(Cas.bs_from_selective_dioid (Cas.selective_dioid_sg_left sg')))

let bs_sg_right = function
  | None -> None 
  | Some sg ->
     (match (Cas.sg_CS_option_from_sg sg) with 
       | None -> (match (Cas.sg_CI_option_from_sg sg) with 
                  | None -> None 
		  | Some sg'-> Some(Cas.bs_from_dioid (Cas.dioid_sg_right sg')))
       | Some sg'-> Some(Cas.bs_from_selective_dioid (Cas.selective_dioid_sg_right sg')))
       
       
let bs_union_lift sg = Some (Cas.bs_from_bs_C (Cas.bs_C_from_bs_CI (Cas.bs_CI_union_lift sg)))
let bs_union_intersect eqv = Some (Cas.bs_from_distributive_lattice (Cas.distributive_lattice_union_intersect eqv))
let bs_intersect_union eqv = Some (Cas.bs_from_distributive_lattice (Cas.distributive_lattice_intersect_union eqv))

let bs_add_zero bs c   = mmap (fun b -> Cas.bs_add_zero b c) bs 
let bs_add_one bs c    = mmap (fun b -> Cas.bs_add_one b c) bs

let bs_product m n  = liftM Cas.bs_product m n
let bs_left_sum m n  = liftM Cas.bs_left_sum m n
(*			     
let bs_right_sum m n  = liftM Cas.bs_right_sum m n   			    			     
*) 

let bs_llex_product m n = 
    let bs_llex_aux bs1 bs2 = 
        match Cas.bs_CS_option_from_bs bs1 with 
        | None -> None 
        | Some bs1'-> 
           (match Cas.bs_C_option_from_bs bs2 with 
            | None -> None 
	    | Some bs2'-> Some(Cas.bs_from_bs_C(Cas.bs_C_llex_product bs1' bs2'))
           )
    in liftN bs_llex_aux m n 

let bs_union_lift sg =
  match sg with
  | None -> None
  | Some sg -> Some(Cas.bs_from_bs_C (Cas.bs_C_from_bs_CI (Cas.bs_CI_union_lift sg)))

let bs_describe = function
  | None    -> print_string "bi-semigroup is not defined\n"
  | Some bs -> Describe.bs_describe bs     

let sg_describe = function
  | None    -> print_string "semigroup is not defined\n"
  | Some sg -> Describe.sg_describe sg

let bs_describe_fully = function
  | None    -> print_string "bi-semigroup is not defined\n"
  | Some bs -> Describe.bs_describe_fully bs     

let sg_describe_fully = function
  | None    -> print_string "semigroup is not defined\n"
  | Some sg -> Describe.sg_describe_fully sg
				    
(* Note: ocaml infix symbols must be made of 

    ! $ % & * + - . / : < = > ? @ ^ | ~

introduce an infix operators, 
  op : 'a sg option -> 'b sg option -> ('a * 'b) sg option
*)

let (<*>)  m n = sg_product m n  
let (<!*>) m n = sg_llex m n 
let (<!+>) m n = sg_left_sum m n
let (<+!>) m n = sg_right_sum m n			     

let (<**>) m n = bs_product m n  
let (<!**>) m n = bs_llex_product m n      
let (<!++>) m n = bs_left_sum m n      
