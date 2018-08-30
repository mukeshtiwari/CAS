
(*
From main directory 

./casml 

then 

#use "tests/cas_demo.ml";; 

Or use Tuareg ... 

 *)

open Cas;;
       

(* The Mcas approach might not always be the best. 
   Suppose one wants to write parameterised "templates" --- 
   we then know at compile time that we will always produce a
   well-formed structure of a given kind. 
   Here are some examples. 
*) 

(* sg_CS_llex3 : 'a Cas.sg_CS * b' Cas.sg_CS * 'c Cas.sg_CS -> ('a * ('b * 'c)) Cas.sg_CS *) 
let sg_CS_llex3 (a, b, c) = Cas.sg_CS_llex a (Cas.sg_CS_llex b c) ;;

(* sg_CI_llex3 : 'a Cas.sg_CS * b' Cas.sg_CS * 'c Cas.sg_IS -> ('a * ('b * 'c)) Cas.sg_CI *) 
let sg_CI_llex3 (a, b, c) = Cas.sg_CI_llex a (Cas.sg_CI_llex b c) ;;

  
