Require Import Coq.Bool.Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.     
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 

Inductive data : Type :=
   | DATA_ascii : ascii -> data 
   | DATA_nat : nat -> data 
   | DATA_bool : bool -> data 
   | DATA_string : string -> data
   | DATA_constant : cas_constant -> data                                
   | DATA_pair : data * data -> data 
   | DATA_inl : data -> data 
   | DATA_inr : data -> data 
   | DATA_list : list data -> data
   | DATA_set : list data -> data                                 
   . 
