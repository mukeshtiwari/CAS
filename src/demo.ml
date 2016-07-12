
(* Hard coded! *) 
#load "/Users/timothygriffin/working/mre/cas-1.0/_build/extraction/cas.cma";;

open EqNat;; 
open Datatypes;;
open Peano;;
open Basic_types;;
open Brel;;
open Uop;;
open Bop;; 
open Ast;; 
open Cef;;
open Certificates;; 
open Check;; 
open Cert_records;; 
open Construct_certs;; 
open Cas_records;;
open Cas;;


let s1 = sg_CS_and;;
let c1 = sg_CS_certs s1;;

let sg_describe sg = 
    let eqv = sg_eq sg in 
    let data = eqv_data eqv in 
    let certs = sg_certs sg in 
    match sg_commutative_d certs with 
    | Certify_Commutative -> Certify_Commutative 
    | Certify_Not_Commutative (a, b) -> Certify_Not_Commutative (data a, data b) 
;; 

let sg_CS_describe sg = 
    let eqv = sg_CS_eqv sg in 
    let data = eqv_data eqv in 
    let certs = sg_CS_certs sg in 
    match sg_CS_exists_id_d certs with 
    | Certify_Not_Exists_Id -> Certify_Not_Exists_Id
    | Certify_Exists_Id i ->  Certify_Exists_Id (data i) 
;; 
