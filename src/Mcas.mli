

val mbind : 'a option -> ('a -> 'b option) -> 'b option  

val mreturn : 'a -> 'a option

val mmap : ('a -> 'b) -> 'a option -> 'b option 

val liftM : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option 

val liftN : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option 

(* eqv constructions? *)

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

val sg_add_id  :  string -> ('a Cas.sg) option -> ('a Cas.with_constant Cas.sg) option 
val sg_add_ann :  string -> ('a Cas.sg) option -> ('a Cas.with_constant Cas.sg) option 

val sg_left_sum  : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  
val sg_right_sum : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  


val sg_union 
val sg_intersect 


(* bi-semigroup *) 
(*
val bs_and_or   : (bool Cas.bs) option
val bs_or_and   : (bool Cas.bs) option
*) 
(*
val bs_min_max  : (int Cas.bs) option
val bs_max_min  : (int Cas.bs) option
val bs_min_plus : (int Cas.bs) option
val bs_max_plus : (int Cas.bs) option
*) 

(*  
val bs_union_intersect : 
val bs_intersect_union : 
 *)


val bs_add_zero : ('a Cas.bs) option -> string -> (('a Cas.with_constant) Cas.bs) option 
val bs_add_one  : ('a Cas.bs) option -> string -> (('a Cas.with_constant) Cas.bs) option 

val bs_product      : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option 
(*
val bs_llex_product : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option 
*)

val sg_describe : 'a Cas.sg option -> (string list) option
val bs_describe : 'a Cas.bs option -> (string list * string list * string list) option

val (<*>)    : ('a Cas.sg) option -> ('b Cas.sg) option -> (('a * 'b) Cas.sg) option
val (<!*>)   : ('a Cas.sg) option -> ('b Cas.sg) option -> (('a * 'b) Cas.sg) option
val (<**>)   : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option 
(*
val (<!+>)   : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  
val (<+!>)   : ('a Cas.sg) option -> ('b Cas.sg) option -> ((('a , 'b) Cas.sum) Cas.sg) option  


val (<!**>)  : ('a Cas.bs) option -> ('b Cas.bs) option -> (('a * 'b) Cas.bs) option 
*) 
