Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_nat.
Require Import CAS.theory.bop.plus. 
Require Import CAS.theory.bop.min. 

(* may need this someday if implement swap operation on bi-semigroups *) 


(*
      a min (b + c) <> (a + b) min (a + c)
 1 =  1 min (1 + 1) <> (1 + 1) min (1 + 1) = 2 
*) 
Lemma bop_plus_min_not_left_distributive : 
        bop_not_left_distributive nat brel_eq_nat bop_plus bop_min.
Proof. exists (1, (1, 1)); compute. reflexivity. Defined. 

Lemma bop_plus_min_not_right_distributive : 
        bop_not_right_distributive nat brel_eq_nat bop_plus bop_min.
Proof. exists (1, (1, 1)); compute. reflexivity. Defined. 



(*
  s <> s + (s min t) 
  1 <> 1 + (1 min 1) = 2
*) 
Lemma bops_plus_min_not_left_absorption : 
        bops_not_left_absorption nat brel_eq_nat bop_plus bop_min. 
Proof. exists (1, 1); compute. reflexivity. Defined. 

Lemma bops_plus_min_not_right_absorption : 
        bops_not_right_absorption nat brel_eq_nat bop_plus bop_min. 
Proof. exists (1, 1); compute. reflexivity. Defined. 


(* special elements 

 id(plus) = 0 
ann(plus) = NONE 

 id(min) = None 
ann(min) = 0 

*) 

Lemma bop_plus_min_id_equals_ann : 
        bops_id_equals_ann nat brel_eq_nat bop_plus bop_min. 
Proof. unfold bops_id_equals_ann. exists bop_plus_exists_id. exists bop_min_exists_ann. 
       compute. reflexivity. 
Defined. 


