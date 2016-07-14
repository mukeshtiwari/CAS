
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
