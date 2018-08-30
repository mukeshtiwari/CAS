
(*
From main directory 

./casml 

then 

#use "tests/mcas_demo.ml";; 

Or use Tuareg ... 

 *)

open Mcas;;

sg_describe sg_max;;
sg_describe_fully sg_max;;    
sg_describe sg_min;;   

let sg_max_llex_min = sg_llex sg_max sg_min ;;
sg_describe_fully sg_max_llex_min;; 

let sg_min_llex_max = sg_llex sg_min sg_max ;;
sg_describe sg_min_llex_max;; 
  
let sg1 = sg_and <*> sg_or <*> sg_min <*> sg_max <*> sg_times <*> sg_plus;; 
sg_describe_fully sg1;; 

let sg2 = sg_and <*> sg_or <*> sg_min <*> sg_max;; 
sg_describe sg2;;

bs_describe bs_min_plus;; (* no zero, 1 = 0 *)
bs_describe bs_max_min;;  (* zero = 1, no 1 *)       
  
let bs_min_plus_llex_max_min = bs_min_plus <!**> bs_max_min;;
bs_describe bs_min_plus_llex_max_min;;  (* no zero, no one *) 

let bs_min_plus_infinity  = bs_add_zero bs_min_plus infinity ;; 
bs_describe  bs_min_plus_infinity;; 

let bs_max_min_self  = bs_add_one bs_max_min self ;; 
bs_describe  bs_max_min_self;; 

let bs_min_plus_llex_max_min_v2 = bs_min_plus_infinity <!**>  bs_max_min_self;;
bs_describe bs_min_plus_llex_max_min_v2;;  (* not distributive *) 

let bs_min_plus_llex_max_min_v3 = bs_min_plus <!**>  bs_max_min_self;;
bs_describe bs_min_plus_llex_max_min_v3;;  (* distributive, no zero *) 
  
let bs_min_plus_llex_max_min_v4 = bs_add_zero bs_min_plus_llex_max_min_v3 infinity ;;
bs_describe bs_min_plus_llex_max_min_v4;;  (* *) 

let bs_max_min_llex_min_plus = bs_max_min <!**> bs_min_plus;;
bs_describe bs_max_min_llex_min_plus;;  (* not distributive, no 0, no 1 *) 

bs_describe (bs_max_min <!++> bs_min_plus);; 


  
