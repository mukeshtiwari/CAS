
(*

From directory ../

./casml 

then 

#use "tests/demo.ml"; 

*) 

open Cas;;
open Describe;;
open Cast;;

let sg1 = sg_llex sg_CS_max (sg_from_sg_CK sg_CK_plus);;

let sg1_props = sg_describe sg1;; 


(* 
    A problem with the "low level" CAS combinators: 
    there are too many types! 
    For example :

     sg_C_times : int sg_C
     sg_CK_plus : int sg_CK
     sg_CS_and  : bool sg_CS
     sg_CS_or   : bool sg_CS
     sg_CS_min  : int sg_CS
     sg_CS_max  : int sg_CS
     ... 
     sg_product    : 'a sg    -> 'b sg    -> ('a * 'b) sg
     sg_C_product  : 'a sg_C  -> 'b sg_C  -> ('a *'b) sg_C
     sg_CI_product : 'a sg_CI -> 'b sg_CI -> ('a *'b) sg_CI
     ... 
     sg_C_from_sg_CK : 'a sg_CK -> 'a sg_C
     sg_from_sg_CI   : 'a sg_CI -> 'a sg
     sg_from_sg_CK   : 'a sg_CK -> 'a sg
     sg_C_from_sg_CS : 'a sg_CS -> 'a sg_C
     sg_from_sg_CS   : 'a sg_CS -> 'a sg
     ... 
     sg_CI_option_from_sg   : 'a sg   -> 'a sg_CI option
     sg_CK_option_from_sg   : 'a sg   -> 'a sg_CK option
     sg_CS_option_from_sg   : 'a sg   -> 'a sg_CS option
     sg_CK_option_from_sg_C : 'a sg_C -> 'a sg_CK option
     sg_CS_option_from_sg_C : 'a sg_C -> 'a sg_CS option

   This may cause many users to have fits. 
   Let's try to build a "higher level" CAS by 
   taking a monadic approach.  We'll use 
   the "option monad" (Also called the Maybe Monad). 
*) 

(* mbind : 'a option -> ('a -> 'b option) -> 'b option  *) 
let mbind m f = match m with Some a -> f a | None -> None;;

(* mreturn : 'a -> 'a option = <fun> *) 
let mreturn a = Some a;;

(* ommap : ('a -> 'b) -> 'a option -> 'b option *) 
let mmap f m = mbind m (fun a -> mreturn (f a));; 

(* liftM2 : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option *) 
let liftM2 f m n = 
    mbind m (fun a -> 
    mbind n (fun b -> mreturn (f a b)));;

(* liftN2 : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option *) 
let liftN2 f m n = 
    mbind m (fun a -> 
    mbind n (fun b -> f a b));;


(* Now, all of our basic semigroups and operators will be
   over the "sg option" type. 
*) 

let sg_and   = Some (sg_from_sg_CS sg_CS_and);;   (* : bool sg option *) 
let sg_or    = Some (sg_from_sg_CS sg_CS_or);;    (* : bool sg option *) 
let sg_min   = Some (sg_from_sg_CS sg_CS_min);;   (* : int sg option *) 
let sg_max   = Some (sg_from_sg_CS sg_CS_max);;   (* : int sg option *) 
let sg_times = Some (sg_from_sg_C sg_C_times);;   (* : int sg option *) 
let sg_plus  = Some (sg_from_sg_CK sg_CK_plus);;  (* : int sg option *) 


(* introduce an infix operator for direct product
  ( <*> ) : 'a sg option -> 'b sg option -> ('a * 'b) sg option
*) 
let (<*>) m n = liftM2 sg_product m n ;; 

let sg2 = sg_and <*> sg_or <*> sg_min <*> sg_max <*> sg_times <*> sg_plus;; 

let sg2_props = mmap sg_describe sg2;; 

(* Lex product requires an sg_CS as a first arg (for associativity). 

   sg_mllex_aux : a Cas_records.sg -> 'b Cas_records.sg -> ('a * 'b) Cas_records.sg option 
*) 
let sg_llex_aux sg1 sg2 = 
   match (sg_CS_option_from_sg sg1) with 
   | None -> None 
   | Some sg1'-> Some(sg_llex sg1' sg2);; 

(* infix for lexical product 
  ( <!*> ) : 'a sg option -> 'b sg option -> ('a * 'b) sg option
*) 
let (<!*>) m n = liftN2 sg_llex_aux m n ;; 

let sg3 = sg_and <!*> sg_or <!*> sg_min <!*> sg_max <!*> sg_times <*> sg_plus;; 

let sg3_props = mmap sg_describe sg3;; 
