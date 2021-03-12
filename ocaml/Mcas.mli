

val mbind : 'a option -> ('a -> 'b option) -> 'b option  

val mreturn : 'a -> 'a option

val mmap : ('a -> 'b) -> 'a option -> 'b option 

val liftM : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option 

val liftN : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option 

(* combinators *)

val make_constant : string -> string -> Cas.cas_constant
val infinity      : Cas.cas_constant
val self          : Cas.cas_constant
val bottom        : Cas.cas_constant
val top           : Cas.cas_constant					  		 		      			

val eqv_nat          : int Cas.eqv
val eqv_bool         : bool Cas.eqv
val eqv_product      : 'a Cas.eqv -> 'b Cas.eqv -> ('a * 'b) Cas.eqv
val eqv_sum          : 'a Cas.eqv -> 'b Cas.eqv -> (('a , 'b) Cas.sum) Cas.eqv
val eqv_list         : 'a Cas.eqv -> ('a list) Cas.eqv
val eqv_set          : 'a Cas.eqv -> ('a Cas.finite_set) Cas.eqv
val eqv_add_constant : Cas.cas_constant -> 'a Cas.eqv -> ('a Cas.with_constant) Cas.eqv
val eqv_nat_ceiling  : int -> int Cas.eqv
val eqv_minset       : 'a Cas.po -> ('a Cas.finite_set) Cas.eqv										  

val sg_and   : (bool Cas.sg) option 
val sg_or    : (bool Cas.sg) option

val sg_min   : (int Cas.sg) option 
val sg_max   : (int Cas.sg) option 
val sg_times : (int Cas.sg) option 
val sg_plus  : (int Cas.sg) option 

val sg_product   : ('a Cas.sg) option -> ('b Cas.sg) option -> (('a * 'b) Cas.sg) option
val sg_llex      : ('a Cas.sg) option -> ('b Cas.sg) option -> (('a * 'b) Cas.sg) option

val sg_left   : 'a Cas.eqv -> ('a Cas.sg) option 
val sg_right  : 'a Cas.eqv -> ('a Cas.sg) option 
val sg_concat : 'a Cas.eqv -> ('a list Cas.sg) option 

val sg_add_id  :  Cas.cas_constant -> ('a Cas.sg) option -> ('a Cas.with_constant Cas.sg) option 
val sg_add_ann :  Cas.cas_constant -> ('a Cas.sg) option -> ('a Cas.with_constant Cas.sg) option 

val sg_left_sum  : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  
val sg_right_sum : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  

val sg_union     : 'a Cas.eqv -> (('a Cas.finite_set) Cas.sg) option 
val sg_intersect : 'a Cas.eqv -> (('a Cas.finite_set) Cas.sg) option
val sg_lift      : ('a Cas.sg) option -> (('a Cas.finite_set) Cas.sg) option   


(* bi-semigroup *) 

val bs_and_or   : (bool Cas.bs) option
val bs_or_and   : (bool Cas.bs) option

val bs_min_max  : (int Cas.bs) option
val bs_max_min  : (int Cas.bs) option
val bs_min_plus : (int Cas.bs) option
val bs_max_plus : (int Cas.bs) option

val bs_sg_left  : ('a Cas.sg) option -> ('a Cas.bs) option
val bs_sg_right : ('a Cas.sg) option -> ('a Cas.bs) option						   

val bs_union_intersect : 'a Cas.eqv -> (('a Cas.finite_set) Cas.bs) option 
val bs_intersect_union : 'a Cas.eqv -> (('a Cas.finite_set) Cas.bs) option 

val bs_left_sum : ('a Cas.bs) option -> ('b Cas.bs) option -> ((('a , 'b) Cas.sum) Cas.bs) option
(*  
val bs_right_sum : ('a Cas.bs) option -> ('b Cas.bs) option -> ((('a , 'b) Cas.sum) Cas.bs) option
*)


val bs_add_zero : ('a Cas.bs) option -> Cas.cas_constant -> (('a Cas.with_constant) Cas.bs) option 
val bs_add_one  : ('a Cas.bs) option -> Cas.cas_constant -> (('a Cas.with_constant) Cas.bs) option 

val bs_product      : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option 
val bs_llex_product : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option

val bs_union_lift : ('a Cas.sg) option -> (('a Cas.finite_set) Cas.bs) option 					      
val eqv_describe : 'a Cas.eqv -> unit
					
val sg_describe : 'a Cas.sg option -> unit
val bs_describe : 'a Cas.bs option -> unit

val sg_describe_fully : 'a Cas.sg option -> unit
val bs_describe_fully : 'a Cas.bs option -> unit
					
val (<*>)    : ('a Cas.sg) option -> ('b Cas.sg) option -> (('a * 'b) Cas.sg) option
val (<!*>)   : ('a Cas.sg) option -> ('b Cas.sg) option -> (('a * 'b) Cas.sg) option
val (<!+>)   : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  
val (<+!>)   : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option

val (<!**>)  : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option
val (<**>)   : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option
val (<!++>)  : ('a Cas.bs) option -> ('b Cas.bs) option -> ((('a , 'b) Cas.sum) Cas.bs) option

