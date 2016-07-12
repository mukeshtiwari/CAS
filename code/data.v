Require Import Coq.Bool.Bool. 
Require Import Coq.Arith.Arith.     
Require Import Coq.Strings.String. 

Inductive data : Type := 
   | DATA_nat : nat -> data 
   | DATA_bool : bool -> data 
   | DATA_string : string -> data 
   | DATA_pair : data * data -> data 
   | DATA_inl : data -> data 
   | DATA_inr : data -> data 
   | DATA_list : list data -> data 
   . 
