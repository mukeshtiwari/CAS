
(*
From main directory 

./casml 

then 

#use "tests/mcas_test.ml";; 

*)

open Mcas;;

  

let e0 = eqv_nat;;
eqv_describe  e0;;   
let e1 = eqv_bool;;
eqv_describe  e1;; 
let e2 = eqv_product e0 e1;;
eqv_describe  e2;;
let e3 = eqv_sum e0 e2;;
eqv_describe  e3;;
let e4 = eqv_list e3;;
eqv_describe  e4;;
let e5 = eqv_set e4;;
eqv_describe  e5;;
(* should have a guard for n < 0 *)     
let e6 = eqv_nat_ceiling 7;;     
eqv_describe  e6;;
List.map (Cas.eqv_new e6) [0;1;2;3;4;5;6;7;8;9];;
let e7 = eqv_add_constant infinity e5;;  
eqv_describe  e7;;   
(* eqv_minset po ? *) 

exception ErrString of string;;
let sg_bop = function Some sg -> Cas.sg_bop sg | _ -> raise (ErrString "Only found None");;
  
let s1 =   sg_max;;
sg_describe_fully s1;;
let s2 =   sg_min;;    
sg_describe_fully s2;;
let s3 =   sg_and;;        
sg_describe_fully s3;;
let s4 =   sg_or;;        
sg_describe_fully s4;;
let s5 =   sg_plus;;        
sg_describe_fully s5;;
let s6 =   sg_times;;        
sg_describe_fully s6;;
let s7 =   sg_product s5 s6;;        
sg_describe_fully s7;;
let s9 =   sg_left e1;;        
sg_describe_fully s9;;                    
let s10 =   sg_right e1;;        
sg_describe_fully s10;;
let s11 =   sg_concat e1;;        
sg_describe_fully s11;;
let s12 =   sg_left_sum s7 s9;;        
sg_describe_fully s12;;    
let s13 = sg_add_id infinity sg_min;;
sg_describe_fully s13;;
let s14 = sg_add_ann infinity sg_plus;;
sg_describe_fully s14;;
let s15= sg_llex sg_max sg_min ;;
sg_describe_fully s15;;
let r1 = sg_bop s15 (10, 8) (9, 10);;
let r2 = sg_bop s15 (7, 8) (9, 10);;
let s16 = sg_llex (sg_left_sum sg_max sg_min) s15;; 
sg_describe_fully s16;;
let r3 = sg_bop s16 (Cas.Inl 19, (7,8)) (Cas.Inr 19, (9, 10));;    

    
    
    
