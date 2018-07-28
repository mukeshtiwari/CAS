
(*
From main directory 

casml -I _build/extraction/ -I _build/src/

then 

#use "tests/demo.ml";; 

 *)

open Mcas

let sg1 = Cas.sg_llex Cas.sg_CS_max (Cas.sg_from_sg_CK Cas.sg_CK_plus);;
let sg1_props = Describe.sg_describe sg1;;

let sg2 = sg_llex sg_max sg_plus;;
let sg2_props = sg_describe sg2;;


(* The Mcas approach might not always be the best. 
   Suppose one wants to write parameterised "templates" --- 
   we then know at compile time that we will always produce a
   well-formed structure of a given kind. 
   Here are some examples. 
*) 

(* sg_CS_llex3 : 'a Cas.sg_CS * b' Cas.sg_CS * 'c Cas.sg_CS -> ('a * ('b * 'c)) Cas.sg_CS *) 
let sg_CS_llex3 (a, b, c) = Cas.sg_CS_llex a (Cas.sg_CS_llex b c) ;;

(* foo : 'a Cas.sg_CI -> (int * (int * 'a)) Cas.sg_CI *) 
let foo sg = Cas.sg_CI_llex Cas.sg_CS_min (Cas.sg_CI_llex Cas.sg_CS_max sg) ;;


  
let sg3 = sg_and <*> sg_or <*> sg_min <*> sg_max <*> sg_times <*> sg_plus;; 
let sg3_props = sg_describe sg3;; 


let sg4 = sg_and <!*> sg_or <!*> sg_min <!*> sg_max <!*> sg_times <*> sg_plus;; 
let sg4_props = sg_describe sg4;; 

let sg5 = sg_and <!*> sg_max <!+> sg_min <+!> sg_max <*> sg_or;;
let sg5_props = sg_describe sg5;;

let bs1 = bs_min_plus <!**> bs_max_min;;
let bs2 = bs_add_zero bs1 "INFINITY";;
let bs3 = bs_add_one bs2 "ZERO";;

let bs4 = bs_min_plus <!**> (bs_add_one bs_max_min "ZERO");;
let bs5 = bs_add_zero bs4 "INFINITY";;   (* iso with bs3 ? *)

let bs6 = bs_max_min <!**> bs_min_plus;;

let bs7 = bs_min_plus <!**> bs_min_plus;;

