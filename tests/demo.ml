
(*

From directory ../

_build/extraction/casml -I _build/extraction/ -I _build/src/


then 

#use "tests/demo.ml";; 

*) 

open Cas;;
open Describe;;
open Cast;;

let upto k = let rec aux m = if k <= m then [] else m :: (aux (m +1)) in aux 0;; 
let explode s = List.map (fun i -> String.get s i) (upto (String.length s));; 


let sg1 = sg_llex sg_CS_max (sg_from_sg_CK sg_CK_plus);;
let sg1_props = sg_describe sg1;; 


(* 
    A problem with the "low level" CAS combinators: 
    there are too many types! 
    For example :

     eqv_eq_bool      : bool eqv
     eqv_eq_nat       : int eqv
     eqv_add_constant : 'a eqv -> cas_constant -> 'a with_constant eqv
     eqv_list         : 'a eqv -> 'a list eqv
     eqv_set          : 'a eqv -> 'a finite_set eqv
     eqv_product      : 'a eqv -> 'b eqv -> ('a * 'b) eqv
     eqv_sum          : 'a eqv -> 'b eqv -> ('a, 'b) sum eqv

     sg_C_times : int sg_C
     sg_CK_plus : int sg_CK
     sg_CS_and  : bool sg_CS
     sg_CS_or   : bool sg_CS
     sg_CS_min  : int sg_CS
     sg_CS_max  : int sg_CS

     sg_CS_min_with_infinity : (int with_constant) sg_CS
     sg_CS_max_with_infinity : (int with_constant) sg_CS

     sg_concat     : 'a eqv -> 'a list sg
     sg_left       : 'a eqv -> 'a sg
     sg_right      : 'a eqv -> 'a sg

     sg_add_id     : cas_constant -> 'a sg    -> 'a with_constant sg
     sg_C_add_id   : cas_constant -> 'a sg_C  -> 'a with_constant sg_C
     sg_CI_add_id  : cas_constant -> 'a sg_CI -> 'a with_constant sg_CI
     sg_CS_add_id  : cas_constant -> 'a sg_CS -> 'a with_constant sg_CS

     sg_add_ann    : cas_constant -> 'a sg    -> 'a with_constant sg
     sg_C_add_ann  : cas_constant -> 'a sg_C  -> 'a with_constant sg_C
     sg_CI_add_ann : cas_constant -> 'a sg_CI -> 'a with_constant sg_CI
     sg_CS_add_ann : cas_constant -> 'a sg_CS -> 'a with_constant sg_CS

     sg_product    : 'a sg    -> 'b sg    -> ('a * 'b) sg
     sg_C_product  : 'a sg_C  -> 'b sg_C  -> ('a *'b) sg_C
     sg_CI_product : 'a sg_CI -> 'b sg_CI -> ('a *'b) sg_CI

     sg_left_sum     : 'a sg    -> 'b sg    -> ('a, 'b) sum sg
     sg_right_sum    : 'a sg    -> 'b sg    -> ('a, 'b) sum sg
     sg_C_left_sum   : 'a sg_C  -> 'b sg_C  -> ('a, 'b) sum sg_C
     sg_C_right_sum  : 'a sg_C  -> 'b sg_C  -> ('a, 'b) sum sg_C
     sg_CI_left_sum  : 'a sg_CI -> 'b sg_CI -> ('a, 'b) sum sg_CI
     sg_CI_right_sum : 'a sg_CI -> 'b sg_CI -> ('a, 'b) sum sg_CI
     sg_CS_left_sum  : 'a sg_CS -> 'b sg_CS -> ('a, 'b) sum sg_CS
     sg_CS_right_sum : 'a sg_CS -> 'b sg_CS -> ('a, 'b) sum sg_CS

     sg_llex    : 'a sg_CS -> 'b sg    -> ('a * 'b) sg
     sg_C_llex  : 'a sg_CS -> 'b sg_C  -> ('a * 'b) sg_C
     sg_CI_llex : 'a sg_CS -> 'b sg_CI -> ('a * 'b) sg_CI
     sg_CS_llex : 'a sg_CS -> 'b sg_CS -> ('a * 'b) sg_CS
     
     sg_CI_union_with_ann    : cas_constant -> 'a eqv -> ('a finite_set with_constant) sg_CI
     sg_CI_intersect_with_id : cas_constant -> 'a eqv -> ('a finite_set with_constant) sg_CI

     sg_from_sg_C     : 'a sg_C  -> 'a sg
     sg_from_sg_CI    : 'a sg_CI -> 'a sg
     sg_from_sg_CK    : 'a sg_CK -> 'a sg
     sg_from_sg_CS    : 'a sg_CS -> 'a sg
     sg_C_from_sg_CK  : 'a sg_CK -> 'a sg_C
     sg_C_from_sg_CS  : 'a sg_CS -> 'a sg_C
     sg_C_from_sg_CI  : 'a sg_CI -> 'a sg_C
     sg_CI_from_sg_CS : 'a sg_CS -> 'a sg_CI

     sg_C_option_from_sg     : 'a sg    -> 'a sg_C option
     sg_CI_option_from_sg    : 'a sg    -> 'a sg_CI option
     sg_CI_option_from_sg_C  : 'a sg_C  -> 'a sg_CI option
     sg_CS_option_from_sg_C  : 'a sg_C  -> 'a sg_CS option
     sg_CS_option_from_sg    : 'a sg    -> 'a sg_CS option
     sg_CS_option_from_sg_CI : 'a sg_CI -> 'a sg_CS option
     sg_CK_option_from_sg_C  : 'a sg_C  -> 'a sg_CK option
     sg_CK_option_from_sg    : 'a sg    -> 'a sg_CK option

     sg_sg_add_zero  : 'a sg_sg    -> cas_constant -> 'a with_constant sg_sg
     sg_C_sg_add_one : 'a sg_C_sg  -> cas_constant -> 'a with_constant sg_C_sg

     sg_sg_product   : 'a sg_sg    -> 'b sg_sg    -> ('a * 'b) sg_sg
     sg_C_sg_llex    : 'a sg_CS_sg -> 'b sg_C_sg  -> ('a * 'b) sg_C_sg
     sg_CS_sg_llex   : 'a sg_CS_sg -> 'b sg_CS_sg -> ('a * 'b) sg_CS_sg
     sg_CI_sg_llex   : 'a sg_CS_sg -> 'b sg_CI_sg -> ('a * 'b) sg_CI_sg

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

(* redefine *) 
let sg_concat eqv     = Some(sg_concat eqv);;
let sg_left eqv       = Some(sg_left eqv);;
let sg_right eqv      = Some(sg_right eqv);;

let sg_add_id id sg      = mmap (sg_add_id (explode id)) sg;;
let sg_add_ann ann sg    = mmap (sg_add_ann (explode ann)) sg;;

let sg_union c eqv     = Some (sg_union c eqv) 
let sg_intersect c eqv = Some (sg_intersect c eqv)

let sg_describe sg = mmap sg_describe sg;;     


(* Note: ocaml infix symbols must be made of 

    ! $ % & * + - . / : < = > ? @ ^ | ~

*) 

(* introduce an infix operators, 
  op : 'a sg option -> 'b sg option -> ('a * 'b) sg option
*) 
let (<*>) m n  = liftM2 sg_product m n  ;; 
let (<!+>) m n = liftM2 sg_left_sum m n ;;
let (<+!>) m n = liftM2 sg_right_sum m n;;
(* Lex product requires an sg_CS as a first arg (for associativity). 
   sg_mllex_aux : a sg -> 'b sg -> ('a * 'b) sg option 
  ( <!*> ) : 'a sg option -> 'b sg option -> ('a * 'b) sg option
*) 
let (<!*>) m n = 
    let sg_llex_aux sg1 sg2 = 
        match (sg_CS_option_from_sg sg1) with 
       | None -> None 
       | Some sg1'-> Some(sg_llex sg1' sg2)
    in liftN2 sg_llex_aux m n ;; 

let sg2 = sg_and <*> sg_or <*> sg_min <*> sg_max <*> sg_times <*> sg_plus;; 

let sg2_props = sg_describe sg2;; 

let sg3 = sg_and <!*> sg_or <!*> sg_min <!*> sg_max <!*> sg_times <*> sg_plus;; 

let sg3_props = sg_describe sg3;; 


let sg4 = sg_and <!*> sg_max <!+> sg_min <+!> sg_max <*> sg_or;;

let sg4_props = sg_describe sg4;;

(* However, note that this approach might not always be the best. 
   Suppose one wants to write parameterised "templates" --- 
   we then know at compile time that we will always produce a
   well-formed structure of a given kind. 
   Here are some examples. 
*) 

(* sg_CS_llex3 : 'a sg_CS * b' sg_CS * 'c sg_CS -> ('a * ('b * 'c)) sg_CS *) 
let sg_CS_llex3 (a, b, c) = sg_CS_llex a (sg_CS_llex b c) ;;

(* foo : 'a sg_CI -> (int * (int * 'a)) sg_CI *) 
let foo sg = sg_CI_llex sg_CS_min (sg_CI_llex sg_CS_max sg) ;;

(* bi-semigroup tests *) 

(* redefine *) 

let bs_and_or   = Some bs_and_or;; 
let bs_or_and   = Some bs_or_and ;; 
let bs_min_max  = Some bs_min_max ;; 
let bs_max_min  = Some bs_max_min;; 
let bs_min_plus = Some bs_min_plus;; 
let bs_max_plus = Some bs_max_plus;; 

let bs_union_intersect c eqv = Some (bs_union_intersect (explode c) eqv);;
let bs_intersect_union c eqv = Some (bs_intersect_union (explode c) eqv);;

let sg_add_id id sg      = mmap (sg_add_id id) sg;;
let sg_add_ann ann sg    = mmap (sg_add_ann ann) sg;;

let bs_add_zero bs c   = mmap (fun b -> bs_add_zero b (explode c)) bs;; 
let bs_add_one bs c    = mmap (fun b -> bs_add_one b (explode c)) bs;;

let bs_describe bs = mmap bs_describe bs;;     

(* direct product *) 
let (<**>) m n  = liftM2 bs_product m n  ;; 

(* (left) lex-product *) 
let (<!**>) m n = 
    let bs_llex_aux bs1 bs2 = 
        match bs_CS_option_from_bs bs1 with 
        | None -> None 
        | Some bs1'-> 
           (match bs_CS_option_from_bs bs2 with 
	   | None -> (match bs_C_option_from_bs bs2 with 
                     | None -> None 
		     | Some bs2'-> Some(bs_from_bs_C(bs_C_llex_product bs1' bs2'))
                     )
	   | Some bs2'-> Some(bs_from_bs_CS(bs_CS_llex_product bs1' bs2'))
           )
        in liftN2 bs_llex_aux m n ;; 

let bs1 = bs_min_plus <!**> bs_max_min;;
let bs2 = bs_add_zero bs1 "INFINITY";;
let bs3 = bs_add_one bs2 "ZERO";;

let bs4 = bs_min_plus <!**> (bs_add_one bs_max_min "ZERO");;
let bs5 = bs_add_zero bs4 "INFINITY";;   (* iso with bs3 ? *)

let bs6 = bs_max_min <!**> bs_min_plus;;

let bs7 = bs_min_plus <!**> bs_min_plus;;
