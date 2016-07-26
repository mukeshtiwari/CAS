Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.construct_certs. 
Require Import CAS.code.cef. 
Require Import CAS.code.cas_records.
Require Import CAS.code.cast.
Require Import CAS.code.data.

(*CC*) (* proved correct in verify/cas_correct.v *) 
(*!!*) (* NOT proved correct in verify/cas_correct.v *) 

(* eqv *) 

(*CC*) 
Definition eqv_eq_bool : eqv bool 
:= {| 
      eqv_eq    := brel_eq_bool 
    ; eqv_certs := eqv_certs_eq_bool
    ; eqv_data  := λ b, DATA_bool b 
    ; eqv_rep  := λ b, b 
    ; eqv_ast   := Ast_eqv_bool 
   |}. 

(*CC*) 
Definition eqv_eq_nat : eqv nat
:= {| 
      eqv_eq    := brel_eq_nat 
    ; eqv_certs := eqv_certs_eq_nat
    ; eqv_data  := λ n, DATA_nat n 
    ; eqv_rep   := λ b, b 
    ; eqv_ast   := Ast_eqv_nat
   |}. 

(*CC*) 
Definition eqv_add_constant : ∀ (S : Type),  eqv S -> cas_constant -> eqv (with_constant S) 
:= λ S eqvS c, 
   {| 
      eqv_eq    := brel_add_constant S (eqv_eq S eqvS) c
    ; eqv_certs := eqv_certs_add_constant S c (eqv_certs S eqvS)
    ; eqv_data  := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (eqv_data S eqvS a) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ s  | inr s => inr _ (eqv_rep S eqvS s) end )
    ; eqv_ast   := Ast_eqv_add_constant (c, eqv_ast S eqvS)
   |}. 

(*CC*) 
Definition eqv_list : ∀ (S : Type),  eqv S -> eqv (list S) 
:= λ S eqvS, 
   {| 
      eqv_eq    := brel_list S (eqv_eq S eqvS) 
    ; eqv_certs := eqv_certs_brel_list S (eqv_certs S eqvS)
    ; eqv_data  := λ l, DATA_list (List.map (eqv_data S eqvS) l)
    ; eqv_rep   := λ l, List.map (eqv_rep S eqvS) l
    ; eqv_ast   := Ast_eqv_list (eqv_ast S eqvS)
   |}. 

(*CC*) 
Definition eqv_set : ∀ (S : Type),  eqv S -> eqv (finite_set S) 
:= λ S eqvS, 
   {| 
      eqv_eq    := brel_set S (eqv_eq S eqvS) 
    ; eqv_certs := eqv_certs_brel_set S (eqv_eq S eqvS) (eqv_certs S eqvS)
    ; eqv_data  := λ l, DATA_list (List.map (eqv_data S eqvS) l)   (* ??? *) 
    ; eqv_rep   := λ l, List.map (eqv_rep S eqvS) l                (* ??? *) 
    ; eqv_ast   := Ast_eqv_set (eqv_ast S eqvS)
   |}. 


(*CC*) 
Definition eqv_product : ∀ (S T : Type),  eqv S -> eqv T -> eqv (S * T) 
:= λ S T eqvS eqvT, 
   {| 
     eqv_eq    := brel_product S T 
                           (eqv_eq S eqvS) 
                           (eqv_eq T eqvT) 
   ; eqv_certs := eqv_certs_product S T 
                           (eqv_certs S eqvS) 
                           (eqv_certs T eqvT) 
    ; eqv_data  := λ p, DATA_pair (eqv_data S eqvS (fst p), eqv_data T eqvT (snd p))
    ; eqv_rep   := λ p, (eqv_rep S eqvS (fst p), eqv_rep T eqvT (snd p))
    ; eqv_ast  := Ast_eqv_product (eqv_ast S eqvS, eqv_ast T eqvT)
   |}. 

(*CC*) 
Definition eqv_sum : ∀ (S T : Type),  eqv S -> eqv T -> eqv (S + T) 
:= λ S T eqvS eqvT, 
   {| 
     eqv_eq    := brel_sum S T 
                           (eqv_eq S eqvS) 
                           (eqv_eq T eqvT) 
   ; eqv_certs := eqv_certs_sum S T 
                           (eqv_certs S eqvS) 
                           (eqv_certs T eqvT) 
    ; eqv_data  := λ d, (match d with inl s => DATA_inl (eqv_data S eqvS s) | inr t => DATA_inr (eqv_data T eqvT t) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ (eqv_rep S eqvS s) | inr t => inr _ (eqv_rep T eqvT t) end)
    ; eqv_ast   := Ast_eqv_sum (eqv_ast S eqvS, eqv_ast T eqvT)
   |}. 

(* semigroups *) 

(* basics *) 

(*CC*) 
Definition sg_C_times : sg_C nat 
:= {| 
     sg_C_eqv   := eqv_eq_nat 
   ; sg_C_bop   := bop_times
   ; sg_C_certs := sg_C_certs_times
   ; sg_C_ast   := Ast_sg_C_times
   |}. 

(*CC*) 
Definition sg_CK_plus : sg_CK nat 
:= {| 
     sg_CK_eqv   := eqv_eq_nat 
   ; sg_CK_bop   := bop_plus
   ; sg_CK_certs := sg_CK_certs_plus
   ; sg_CK_ast   := Ast_sg_CK_plus 
   |}. 

(*CC*) 
Definition sg_CS_and : sg_CS bool
:= {| 
     sg_CS_eqv   := eqv_eq_bool
   ; sg_CS_bop   := bop_and
   ; sg_CS_certs := sg_CS_certs_and
   ; sg_CS_ast   := Ast_sg_CS_and 
   |}. 

(*CC*) 
Definition sg_CS_or : sg_CS bool
:= {| 
     sg_CS_eqv   := eqv_eq_bool
   ; sg_CS_bop   := bop_or
   ; sg_CS_certs := sg_CS_certs_or
   ; sg_CS_ast   := Ast_sg_CS_or 
   |}. 

(*CC*) 
Definition sg_CS_min : sg_CS nat 
:= {| 
     sg_CS_eqv   := eqv_eq_nat 
   ; sg_CS_bop   := bop_min 
   ; sg_CS_certs := sg_CS_certs_min 
   ; sg_CS_ast   := Ast_sg_CS_min 
   |}. 

(*CC*) 
Definition sg_CS_max : sg_CS nat 
:= {| 
     sg_CS_eqv   := eqv_eq_nat 
   ; sg_CS_bop   := bop_max
   ; sg_CS_certs := sg_CS_certs_max
   ; sg_CS_ast   := Ast_sg_CS_max
   |}. 

(*CC*) 
Definition sg_concat: ∀ (S : Type),  eqv S -> sg (list S) 
:= λ S eqvS, 
   {| 
     sg_eq     := eqv_list S eqvS 
   ; sg_bop    := bop_concat S 
   ; sg_certs  := sg_certs_concat S (eqv_certs S eqvS) 
   ; sg_ast    := Ast_sg_concat (eqv_ast S eqvS)
   |}. 

(*CC*) 
Definition sg_left: ∀ (S : Type),  eqv S -> sg S 
:= λ S eqvS, 
   {| 
     sg_eq      := eqvS
   ; sg_bop     := bop_left S 
   ; sg_certs   := sg_certs_left S (eqv_certs S eqvS) 
   ; sg_ast     := Ast_sg_left (eqv_ast S eqvS)
   |}. 

(*CC*) 
Definition sg_right : ∀ (S : Type),  eqv S -> sg S 
:= λ S eqvS, 
   {| 
     sg_eq     := eqvS
   ; sg_bop    := bop_right S 
   ; sg_certs  := sg_certs_right S (eqv_certs S eqvS) 
   ; sg_ast    := Ast_sg_right (eqv_ast S eqvS)
   |}. 


(* semigroup add_id *) 

(*CC*) 
Definition sg_add_id: ∀ (S : Type),  cas_constant -> sg S -> sg (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_eq     := eqv_add_constant S (sg_eq S sgS) c 
   ; sg_bop    := bop_add_id S (sg_bop S sgS) c
   ; sg_certs  := sg_certs_add_id S c (eqv_certs S (sg_eq S sgS)) (sg_certs S sgS) 
   ; sg_ast    := Ast_sg_add_id (c, sg_ast S sgS)
   |}. 

(*CC*) 
Definition sg_C_add_id : ∀ (S : Type) (c : cas_constant),  sg_C S -> sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_C_eqv       := eqv_add_constant S (sg_C_eqv S sgS) c  
   ; sg_C_bop       := bop_add_id S (sg_C_bop S sgS) c 
   ; sg_C_certs     := sg_C_certs_add_id S c (eqv_certs S (sg_C_eqv S sgS)) (sg_C_certs S sgS) 
   ; sg_C_ast       := Ast_sg_C_add_id (c, sg_C_ast S sgS)
   |}. 

(*CC*) 
Definition sg_CI_add_id : ∀ (S : Type) (c : cas_constant), sg_CI S -> sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_CI_eqv       := eqv_add_constant S (sg_CI_eqv S sgS) c  
   ; sg_CI_bop       := bop_add_id S (sg_CI_bop S sgS) c 
   ; sg_CI_certs    := sg_CI_certs_add_id S c (eqv_certs S (sg_CI_eqv S sgS)) (sg_CI_certs S sgS) 
   ; sg_CI_ast       := Ast_sg_CI_add_id (c, sg_CI_ast S sgS)
   |}. 


(*CC*) 
Definition sg_CS_add_id : ∀ (S : Type) (c : cas_constant),  sg_CS S -> sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_CS_eqv       := eqv_add_constant S (sg_CS_eqv S sgS) c  
   ; sg_CS_bop       := bop_add_id S (sg_CS_bop S sgS) c 
   ; sg_CS_certs    := sg_CS_certs_add_id S c (eqv_certs S (sg_CS_eqv S sgS)) (sg_CS_certs S sgS) 
   ; sg_CS_ast       := Ast_sg_CS_add_id (c, sg_CS_ast S sgS)
   |}. 


(* semigroup add_ann *) 

(*CC*) 
Definition sg_add_ann:  ∀ (S : Type),  cas_constant -> sg S -> sg (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_eq     := eqv_add_constant S (sg_eq S sgS) c 
   ; sg_bop    := bop_add_ann S (sg_bop S sgS) c
   ; sg_certs  := sg_certs_add_ann S c (eqv_certs S (sg_eq S sgS)) (sg_certs S sgS) 
   ; sg_ast    := Ast_sg_add_ann (c, sg_ast S sgS)
   |}. 

(*CC*) 
Definition sg_C_add_ann : ∀ (S : Type) (c : cas_constant),  sg_C S -> sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_C_eqv       := eqv_add_constant S (sg_C_eqv S sgS) c  
   ; sg_C_bop       := bop_add_ann S (sg_C_bop S sgS) c 
   ; sg_C_certs     := sg_C_certs_add_ann S c (eqv_certs S (sg_C_eqv S sgS)) (sg_C_certs S sgS) 
   ; sg_C_ast       := Ast_sg_C_add_ann (c, sg_C_ast S sgS)
   |}. 

(*CC*) 
Definition sg_CI_add_ann : ∀ (S : Type) (c : cas_constant),  sg_CI S -> sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_CI_eqv       := eqv_add_constant S (sg_CI_eqv S sgS) c  
   ; sg_CI_bop       := bop_add_ann S (sg_CI_bop S sgS) c 
   ; sg_CI_certs    := sg_CI_certs_add_ann S c (eqv_certs S (sg_CI_eqv S sgS)) (sg_CI_certs S sgS) 
   ; sg_CI_ast       := Ast_sg_CI_add_ann (c, sg_CI_ast S sgS)
   |}. 

(*CC*) 
Definition sg_CS_add_ann : ∀ (S : Type) (c : cas_constant),  sg_CS S -> sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     sg_CS_eqv       := eqv_add_constant S (sg_CS_eqv S sgS) c  
   ; sg_CS_bop       := bop_add_ann S (sg_CS_bop S sgS) c 
   ; sg_CS_certs    := sg_CS_certs_add_ann S c (eqv_certs S (sg_CS_eqv S sgS)) (sg_CS_certs S sgS) 
   ; sg_CS_ast       := Ast_sg_CS_add_ann (c, sg_CS_ast S sgS)
   |}. 


(* semigroup products *) 

(*CC*) 
Definition sg_product : ∀ (S T : Type),  sg S -> sg T -> sg (S * T) 
:= λ S T sgS sgT, 
   {| 
     sg_eq     := eqv_product S T (sg_eq S sgS) (sg_eq T sgT) 
   ; sg_bop    := bop_product S T (sg_bop S sgS) (sg_bop T sgT) 
   ; sg_certs := sg_certs_product S T 
                    (eqv_certs S (sg_eq S sgS))
                    (eqv_certs T (sg_eq T sgT))
                    (sg_certs S sgS) 
                    (sg_certs T sgT) 
   ; sg_ast    := Ast_sg_product (sg_ast S sgS, sg_ast T sgT)
   |}. 



(*CC*) 
Definition sg_CK_product : ∀ (S T : Type),  sg_CK S -> sg_CK T -> sg_CK (S * T) 
:= λ S T sgS sgT, 
   {| 
     sg_CK_eqv    := eqv_product S T 
                           (sg_CK_eqv S sgS) 
                           (sg_CK_eqv T sgT) 
   ; sg_CK_bop       := bop_product S T 
                           (sg_CK_bop S sgS) 
                           (sg_CK_bop T sgT) 
   ; sg_CK_certs := sg_CK_certs_product S T 
                           (eqv_certs S (sg_CK_eqv S sgS)) 
                           (eqv_certs T (sg_CK_eqv T sgT)) 
                           (sg_CK_certs S sgS) 
                           (sg_CK_certs T sgT) 
   ; sg_CK_ast       := Ast_sg_CK_product (sg_CK_ast S sgS, sg_CK_ast T sgT)
   |}. 

(*!!*) 
Definition sg_C_product : ∀ (S T : Type),  sg_C S -> sg_C T -> sg_C (S * T) 
:= λ S T sgS sgT, 
   {| 
     sg_C_eqv    := eqv_product S T 
                           (sg_C_eqv S sgS) 
                           (sg_C_eqv T sgT) 
   ; sg_C_bop       := bop_product S T 
                           (sg_C_bop S sgS) 
                           (sg_C_bop T sgT) 
   ; sg_C_certs := sg_C_certs_product S T 
                           (eqv_eq S (sg_C_eqv S sgS)) 
                           (eqv_eq T (sg_C_eqv T sgT))
                           (sg_C_bop S sgS) 
                           (sg_C_bop T sgT) 
                           (eqv_certs S (sg_C_eqv S sgS)) 
                           (eqv_certs T (sg_C_eqv T sgT)) 
                           (sg_C_certs S sgS) 
                           (sg_C_certs T sgT) 
   ; sg_C_ast       := Ast_sg_C_product (sg_C_ast S sgS, sg_C_ast T sgT)
   |}. 

(*!!*) 
Definition sg_CI_product : ∀ (S T : Type),  sg_CI S -> sg_CI T -> sg_CI (S * T) 
:= λ S T sgS sgT, 
   {| 
     sg_CI_eqv    := eqv_product S T 
                           (sg_CI_eqv S sgS) 
                           (sg_CI_eqv T sgT) 
   ; sg_CI_bop       := bop_product S T 
                           (sg_CI_bop S sgS) 
                           (sg_CI_bop T sgT) 
   ; sg_CI_certs := sg_CI_certs_product S T 
                           (eqv_eq S (sg_CI_eqv S sgS)) 
                           (eqv_eq T (sg_CI_eqv T sgT))
                           (sg_CI_bop S sgS) 
                           (sg_CI_bop T sgT) 
                           (eqv_certs S (sg_CI_eqv S sgS)) 
                           (eqv_certs T (sg_CI_eqv T sgT)) 
                           (sg_CI_certs S sgS) 
                           (sg_CI_certs T sgT) 
   ; sg_CI_ast       := Ast_sg_CI_product (sg_CI_ast S sgS, sg_CI_ast T sgT)
   |}. 

(* semigroup sums *) 

(*CC*) 
Definition sg_left_sum : ∀ (S T : Type),  sg S -> sg T -> sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_eq     := eqv_sum S T (sg_eq S sgS) (sg_eq T sgT) 
   ; sg_bop    := bop_left_sum S T (sg_bop S sgS) (sg_bop T sgT) 
   ; sg_certs := sg_certs_left_sum S T 
                    (eqv_certs S (sg_eq S sgS))
                    (eqv_certs T (sg_eq T sgT)) 
                    (sg_certs S sgS) 
                    (sg_certs T sgT) 
   ; sg_ast    := Ast_sg_left_sum (sg_ast S sgS, sg_ast T sgT)
   |}. 

(*CC*) 
Definition sg_right_sum : ∀ (S T : Type),  sg S -> sg T -> sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_eq     := eqv_sum S T (sg_eq S sgS) (sg_eq T sgT) 
   ; sg_bop    := bop_right_sum S T (sg_bop S sgS) (sg_bop T sgT) 
   ; sg_certs  := sg_certs_right_sum S T 
                    (eqv_certs S (sg_eq S sgS))
                    (eqv_certs T (sg_eq T sgT)) 
                    (sg_certs S sgS) 
                    (sg_certs T sgT) 
   ; sg_ast    := Ast_sg_right_sum (sg_ast S sgS, sg_ast T sgT)
   |}. 

(*CC*) 
Definition sg_C_left_sum : ∀ (S T : Type),  sg_C S -> sg_C T -> sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_C_eqv       := eqv_sum S T 
                           (sg_C_eqv S sgS) 
                           (sg_C_eqv T sgT) 
   ; sg_C_bop       := bop_left_sum S T 
                           (sg_C_bop S sgS) 
                           (sg_C_bop T sgT) 
   ; sg_C_certs    := sg_C_certs_left_sum S T 
                           (eqv_certs S (sg_C_eqv S sgS)) 
                           (eqv_certs T (sg_C_eqv T sgT)) 
                           (sg_C_certs S sgS) 
                           (sg_C_certs T sgT) 
   ; sg_C_ast       := Ast_sg_C_left_sum (sg_C_ast S sgS, sg_C_ast T sgT)
   |}. 

(*CC*) 
Definition sg_C_right_sum : ∀ (S T : Type),  sg_C S -> sg_C T -> sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_C_eqv       := eqv_sum S T 
                           (sg_C_eqv S sgS) 
                           (sg_C_eqv T sgT) 
   ; sg_C_bop       := bop_right_sum S T 
                           (sg_C_bop S sgS) 
                           (sg_C_bop T sgT) 
   ; sg_C_certs := sg_C_certs_right_sum S T 
                           (eqv_certs S (sg_C_eqv S sgS)) 
                           (eqv_certs T (sg_C_eqv T sgT)) 
                           (sg_C_certs S sgS) 
                           (sg_C_certs T sgT) 
   ; sg_C_ast       := Ast_sg_C_right_sum (sg_C_ast S sgS, sg_C_ast T sgT)
   |}. 


(*CC*) 
Definition sg_CI_left_sum : ∀ (S T : Type),  sg_CI S -> sg_CI T -> sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_CI_eqv       := eqv_sum S T 
                           (sg_CI_eqv S sgS) 
                           (sg_CI_eqv T sgT) 
   ; sg_CI_bop       := bop_left_sum S T 
                           (sg_CI_bop S sgS) 
                           (sg_CI_bop T sgT) 
   ; sg_CI_certs    := sg_CI_certs_left_sum S T 
                           (eqv_certs S (sg_CI_eqv S sgS)) 
                           (eqv_certs T (sg_CI_eqv T sgT)) 
                           (sg_CI_certs S sgS) 
                           (sg_CI_certs T sgT) 
   ; sg_CI_ast       := Ast_sg_CI_left_sum (sg_CI_ast S sgS, sg_CI_ast T sgT)
   |}. 

(*CC*) 
Definition sg_CI_right_sum : ∀ (S T : Type),  sg_CI S -> sg_CI T -> sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_CI_eqv       := eqv_sum S T 
                           (sg_CI_eqv S sgS) 
                           (sg_CI_eqv T sgT) 
   ; sg_CI_bop       := bop_right_sum S T 
                           (sg_CI_bop S sgS) 
                           (sg_CI_bop T sgT) 
   ; sg_CI_certs := sg_CI_certs_right_sum S T 
                           (eqv_certs S (sg_CI_eqv S sgS)) 
                           (eqv_certs T (sg_CI_eqv T sgT)) 
                           (sg_CI_certs S sgS) 
                           (sg_CI_certs T sgT) 
   ; sg_CI_ast       := Ast_sg_CI_right_sum (sg_CI_ast S sgS, sg_CI_ast T sgT)
   |}. 

(*CC*) 
Definition sg_CS_left_sum : ∀ (S T : Type),  sg_CS S -> sg_CS T -> sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_CS_eqv       := eqv_sum S T 
                           (sg_CS_eqv S sgS) 
                           (sg_CS_eqv T sgT) 
   ; sg_CS_bop       := bop_left_sum S T 
                           (sg_CS_bop S sgS) 
                           (sg_CS_bop T sgT) 
   ; sg_CS_certs    := sg_CS_certs_left_sum S T 
                           (eqv_certs S (sg_CS_eqv S sgS)) 
                           (eqv_certs T (sg_CS_eqv T sgT)) 
                           (sg_CS_certs S sgS) 
                           (sg_CS_certs T sgT) 
   ; sg_CS_ast       := Ast_sg_CS_left_sum (sg_CS_ast S sgS, sg_CS_ast T sgT)
   |}. 

(*CC*) 
Definition sg_CS_right_sum : ∀ (S T : Type),  sg_CS S -> sg_CS T -> sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     sg_CS_eqv       := eqv_sum S T 
                           (sg_CS_eqv S sgS) 
                           (sg_CS_eqv T sgT) 
   ; sg_CS_bop       := bop_right_sum S T 
                           (sg_CS_bop S sgS) 
                           (sg_CS_bop T sgT) 
   ; sg_CS_certs := sg_CS_certs_right_sum S T 
                           (eqv_certs S (sg_CS_eqv S sgS)) 
                           (eqv_certs T (sg_CS_eqv T sgT)) 
                           (sg_CS_certs S sgS) 
                           (sg_CS_certs T sgT) 
   ; sg_CS_ast       := Ast_sg_CS_right_sum (sg_CS_ast S sgS, sg_CS_ast T sgT)
   |}. 


(* semigroup lexicographic *) 

(*CC*) 
Definition sg_llex : ∀ (S T : Type),  sg_CS S -> sg T -> sg (S * T)
:= λ S T sgS sgT, 
   {| 
     sg_eq    := eqv_product S T (sg_CS_eqv S sgS) (sg_eq T sgT) 
   ; sg_bop   := bop_llex S T (eqv_eq S (sg_CS_eqv S sgS)) (sg_CS_bop S sgS) (sg_bop T sgT) 
   ; sg_certs := sg_certs_llex S T 
                   (eqv_eq S (sg_CS_eqv S sgS)) 
                   (sg_CS_bop S sgS) 
                   (eqv_certs S (sg_CS_eqv S sgS)) 
                   (eqv_certs T (sg_eq T sgT)) 
                   (sg_CS_certs S sgS) 
                   (sg_certs T sgT) 
   ; sg_ast   := Ast_sg_llex (sg_CS_ast S sgS, sg_ast T sgT)
   |}. 


(*CC*) 
Definition sg_C_llex : ∀ (S T : Type),  sg_CS S -> sg_C T -> sg_C (S * T)
:= λ S T sgS sgT, 
      {| 
        sg_C_eqv     := eqv_product S T (sg_CS_eqv S sgS) (sg_C_eqv T sgT) 
      ; sg_C_bop    := bop_llex S T 
                          (eqv_eq S (sg_CS_eqv S sgS)) 
                          (sg_CS_bop S sgS) 
                          (sg_C_bop T sgT) 
      ; sg_C_certs := sg_C_certs_llex S T 
                          (eqv_eq S (sg_CS_eqv S sgS))
                          (sg_CS_bop S sgS) 
                          (eqv_certs S (sg_CS_eqv S sgS)) 
                          (eqv_certs T (sg_C_eqv T sgT))
                          (sg_CS_certs S sgS) 
                          (sg_C_certs T sgT) 
      ; sg_C_ast    := Ast_sg_C_llex (sg_CS_ast S sgS, sg_C_ast T sgT)  
      |}. 


(*CC*) 
Definition sg_CI_llex : ∀ (S T : Type),  sg_CS S -> sg_CI T -> sg_CI (S * T)
:= λ S T sgS sgT, 
      {| 
        sg_CI_eqv     := eqv_product S T (sg_CS_eqv S sgS) (sg_CI_eqv T sgT) 
      ; sg_CI_bop    := bop_llex S T 
                          (eqv_eq S (sg_CS_eqv S sgS)) 
                          (sg_CS_bop S sgS) 
                          (sg_CI_bop T sgT) 
      ; sg_CI_certs := sg_CI_certs_llex S T 
                          (eqv_eq S (sg_CS_eqv S sgS))
                          (sg_CS_bop S sgS) 
                          (eqv_certs S (sg_CS_eqv S sgS)) 
                          (eqv_certs T (sg_CI_eqv T sgT))
                          (sg_CS_certs S sgS) 
                          (sg_CI_certs T sgT) 
      ; sg_CI_ast    := Ast_sg_CI_llex (sg_CS_ast S sgS, sg_CI_ast T sgT)  
      |}. 


(*CC*) 
Definition sg_CS_llex : ∀ (S T : Type),  sg_CS S -> sg_CS T -> sg_CS (S * T)
:= λ S T sgS sgT, 
      {| 
        sg_CS_eqv    := eqv_product S T (sg_CS_eqv S sgS) (sg_CS_eqv T sgT) 
      ; sg_CS_bop    := bop_llex S T 
                          (eqv_eq S (sg_CS_eqv S sgS)) 
                          (sg_CS_bop S sgS) 
                          (sg_CS_bop T sgT) 
      ; sg_CS_certs := sg_CS_certs_llex S T 
                          (eqv_eq S (sg_CS_eqv S sgS))
                          (sg_CS_bop S sgS) 
                          (eqv_certs S (sg_CS_eqv S sgS)) 
                          (eqv_certs T (sg_CS_eqv T sgT))
                          (sg_CS_certs S sgS) 
                          (sg_CS_certs T sgT) 
      ; sg_CS_ast    := Ast_sg_CS_llex (sg_CS_ast S sgS, sg_CS_ast T sgT)  
      |}. 


(* SETS *) 





(* This is here because we have already constructed a new eqv structure. HACK. *) 
Definition sg_certs_union : 
   ∀ (S : Type), S ->             (* HACK *) 
                 (S -> S) ->      (* HACK *) 
                 cas_constant -> 
                 eqv (with_constant (finite_set S)) ->   (* HACK *) 
                 binary_op (with_constant (finite_set S)) -> 
                 sg_certificates (with_constant (finite_set S))
:= λ S x g c eqv_union b, 
let r := eqv_eq _ eqv_union in 
match certify_nontrivial_witness _ (eqv_nontrivial _ (eqv_certs _ eqv_union)), 
      certify_nontrivial_negate _ (eqv_nontrivial _ (eqv_certs _ eqv_union)) 
with 
| Certify_Witness s, Certify_Negate f =>  
let id := inr _ nil in 
let ann := inl _ c in 
{|
  sg_associative    := Assert_Associative _ 
; sg_congruence     := Assert_Bop_Congruence _  
; sg_commutative_d  := Certify_Commutative _ 
; sg_idempotent_d   := Certify_Idempotent _ 
(*
     NOTE  (x :: nil, (g x) :: nil)
     comes from a proof of bop_union_not_selective_raw, 
     before the ann is added. 
     Then (inr (x :: nil), inr (g x :: nil)) after add ann. 
     THIS IS A HACK.  Some abstraction is broken. FIX THIS. 
*) 
; sg_selective_d    := Certify_Not_Selective _ (inr _ (x :: nil), inr _ ((g x) :: nil))
; sg_exists_id_d    := Certify_Exists_Id _ id 
; sg_exists_ann_d   := Certify_Exists_Ann _ ann 
; sg_is_left_d      := Certify_Not_Is_Left _ (cef_commutative_implies_not_is_left _ r b s f)
; sg_is_right_d     := Certify_Not_Is_Right _ (cef_commutative_implies_not_is_right _ r b s f)

; sg_left_cancel_d  := Certify_Not_Left_Cancellative _ (ann, (s, f s))
; sg_right_cancel_d := Certify_Not_Right_Cancellative _ (ann, (s, f s))
; sg_left_constant_d  := Certify_Not_Left_Constant _ (id, (s, f s))
; sg_right_constant_d := Certify_Not_Right_Constant _ (id, (s, f s))
; sg_anti_left_d      := Certify_Not_Anti_Left _ (s, id)
; sg_anti_right_d     := Certify_Not_Anti_Right _ (s, id)
|}
end. 


Definition sg_union : ∀ (S : Type) (c : cas_constant),  eqv S -> sg (with_constant (finite_set S)) 
:= λ S c eqvS, 
match certify_nontrivial_witness _ (eqv_nontrivial _ (eqv_certs _ eqvS )), 
      certify_nontrivial_negate _ (eqv_nontrivial _ (eqv_certs _ eqvS)) 
with 
| Certify_Witness x, Certify_Negate g =>  
let eqv_union := eqv_add_constant (finite_set S) (eqv_set S eqvS) c in 
let b := bop_add_ann (finite_set S) (bop_union S (eqv_eq S eqvS)) c in 
   {| 
     sg_eq    := eqv_union 
   ; sg_bop   := b 
   ; sg_certs := sg_certs_union S x g c eqv_union b 
   ; sg_ast   := Ast_sg_union (c, eqv_ast S eqvS)
   |}
end. 



(* This is here because we have already constructed a new eqv structure. HACK. *) 
Definition sg_certs_intersect : 
   ∀ (S : Type), S ->             (* HACK *) 
                 (S -> S) ->      (* HACK *) 
                 cas_constant -> 
                 eqv (with_constant (finite_set S)) ->   (* HACK *) 
                 binary_op (with_constant (finite_set S)) -> 
                 sg_certificates (with_constant (finite_set S))
:= λ S x g c eqv_intersect b, 
let r := eqv_eq _ eqv_intersect in 
match certify_nontrivial_witness _ (eqv_nontrivial _ (eqv_certs _ eqv_intersect)), 
      certify_nontrivial_negate _ (eqv_nontrivial _ (eqv_certs _ eqv_intersect)) 
with 
| Certify_Witness s, Certify_Negate f =>  
let id := inl _ c in 
let ann := inr _ nil in 
{|
  sg_associative    := Assert_Associative _ 
; sg_congruence     := Assert_Bop_Congruence _  
; sg_commutative_d  := Certify_Commutative _ 
; sg_idempotent_d   := Certify_Idempotent _ 
(*
     NOTE  (x :: nil, (g x) :: nil)
     comes from a proof of bop_intersect_not_selective_raw, 
     before the ann is added. 
     Then (inr (x :: nil), inr (g x :: nil)) after add ann. 
     THIS IS A HACK.  Some abstraction is broken. FIX THIS. 
*) 
; sg_selective_d    := Certify_Not_Selective _ (inr _ (x :: nil), inr _ ((g x) :: nil))
; sg_exists_id_d    := Certify_Exists_Id _ id 
; sg_exists_ann_d   := Certify_Exists_Ann _ ann 
; sg_is_left_d      := Certify_Not_Is_Left _ (cef_commutative_implies_not_is_left _ r b s f)
; sg_is_right_d     := Certify_Not_Is_Right _ (cef_commutative_implies_not_is_right _ r b s f)

; sg_left_cancel_d  := Certify_Not_Left_Cancellative _ (ann, (s, f s))
; sg_right_cancel_d := Certify_Not_Right_Cancellative _ (ann, (s, f s))
; sg_left_constant_d  := Certify_Not_Left_Constant _ (id, (s, f s))
; sg_right_constant_d := Certify_Not_Right_Constant _ (id, (s, f s))
; sg_anti_left_d      := Certify_Not_Anti_Left _ (s, id)
; sg_anti_right_d     := Certify_Not_Anti_Right _ (s, id)
|}
end. 


Definition sg_intersect : ∀ (S : Type) (c : cas_constant),  eqv S -> sg (with_constant (finite_set S)) 
:= λ S c eqvS, 
match certify_nontrivial_witness _ (eqv_nontrivial _ (eqv_certs _ eqvS )), 
      certify_nontrivial_negate _ (eqv_nontrivial _ (eqv_certs _ eqvS)) 
with 
| Certify_Witness x, Certify_Negate g =>  
let eqv_intersect := eqv_add_constant (finite_set S) (eqv_set S eqvS) c in 
let b := bop_add_id (finite_set S) (bop_intersect S (eqv_eq S eqvS)) c in 
   {| 
     sg_eq    := eqv_intersect 
   ; sg_bop   := b 
   ; sg_certs := sg_certs_intersect S x g c eqv_intersect b 
   ; sg_ast   := Ast_sg_intersect (c, eqv_ast S eqvS)
   |}
end. 


(*

(*CC*) 
Definition sg_CI_union_with_ann : ∀ (S : Type) (c : cas_constant),  eqv S -> sg_CI (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     sg_CI_eqv   := eqv_add_constant (finite_set S) (eqv_set S eqvS) c
   ; sg_CI_bop   := bop_add_ann (finite_set S) (bop_union S (eqv_eq S eqvS)) c
   ; sg_CI_certs := sg_CI_certs_union_with_ann S c (eqv_certs S eqvS)
   ; sg_CI_ast   := Ast_sg_CI_union_with_ann (c, eqv_ast S eqvS)
   |}. 

Definition sg_CI_intersect_with_id : ∀ (S : Type) (c : cas_constant),  eqv S -> sg_CI (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     sg_CI_eqv   := eqv_add_constant (finite_set S) (eqv_set S eqvS) c
   ; sg_CI_bop   := bop_add_id (finite_set S) (bop_intersect S (eqv_eq S eqvS)) c
   ; sg_CI_certs := sg_CI_certs_intersect_with_id S c (eqv_certs S eqvS)
   ; sg_CI_ast   := Ast_sg_CI_intersect_with_id (c, eqv_ast S eqvS)
   |}. 
*) 

(*CC*) 
(* Need module for derived structures ... *) 
Definition sg_CS_min_with_infinity : sg_CS (with_constant nat) := 
           sg_CS_add_id nat cas_infinity sg_CS_min. 

Definition sg_CS_max_with_infinity : sg_CS (with_constant nat) := 
           sg_CS_add_ann nat cas_infinity sg_CS_max. 



(* Min PLUS 

Definition bsg_min_plus : bsg nat := 
   {| 
     bsg_eq          := brel_eq_nat 
   ; bsg_plus        := bop_min 
   ; bsg_times       := bop_plus 
   ; bsg_eqv_certs   := eqv_certs_eq_nat 
   ; bsg_plus_certs  := sg_certs_from_sg_CS_certs _ sg_CS_certs_min
   ; bsg_times_certs := sg_certs_from_csg_certs _ csg_certs_plus   
   ; bsg_bsg_certs   := bsg_certs_min_plus
   ; bsg_ast         := BSG_min_plus
   |}. 

*) 

(* MAX PLUS *) 

(* MAX MIN *) 

(* MIN MAX *) 

(*CC*) 
Definition bs_add_one : ∀ (S : Type), bs S -> cas_constant -> bs (with_constant S) 
:= λ S bsS c, 
{| 
     bs_eqv         := eqv_add_constant S (bs_eqv S bsS) c 
   ; bs_plus        := bop_add_ann S (bs_plus S bsS) c
   ; bs_times       := bop_add_id S (bs_times S bsS) c
   ; bs_plus_certs  := sg_certs_add_ann S c
                                (eqv_certs S (bs_eqv S bsS)) 
                                (bs_plus_certs S bsS) 
   ; bs_times_certs := sg_certs_add_id S c
                                (eqv_certs S (bs_eqv S bsS)) 
                                (bs_times_certs S bsS) 
   ; bs_certs       := bs_certs_add_one S c
                                (eqv_certs S (bs_eqv S bsS)) 
                                (bs_plus_certs S bsS) 
                                (bs_certs S bsS)
   ; bs_ast         := Ast_bs_add_one (c, bs_ast S bsS)
|}. 


(*CC*) 
Definition bs_add_zero : ∀ (S : Type),  bs S -> cas_constant -> bs (with_constant S) 
:= λ S bsS c, 
{| 
     bs_eqv          := eqv_add_constant S (bs_eqv S bsS) c 
   ; bs_plus         := bop_add_id S (bs_plus S bsS) c
   ; bs_times        := bop_add_ann S (bs_times S bsS) c
   ; bs_plus_certs  := sg_certs_add_id S c 
                                (eqv_certs S (bs_eqv S bsS)) 
                                (bs_plus_certs S bsS) 
   ; bs_times_certs := sg_certs_add_ann S c 
                                (eqv_certs S (bs_eqv S bsS)) 
                                (bs_times_certs S bsS) 
   ; bs_certs       := bs_certs_add_zero S 
                                (eqv_certs S (bs_eqv S bsS))  
                                (bs_certs S bsS)
   ; bs_ast          := Ast_bs_add_zero (c, bs_ast S bsS)
|}. 

(*CC*) 
Definition bs_product : ∀ (S T : Type),  bs S -> bs T -> bs (S * T) 
:= λ S T bsS bsT, 
   {| 
     bs_eqv         := eqv_product S T (bs_eqv S bsS) (bs_eqv T bsT) 
   ; bs_plus        := bop_product S T (bs_plus S bsS) (bs_plus T bsT) 
   ; bs_times       := bop_product S T (bs_times S bsS) (bs_times T bsT) 
   ; bs_plus_certs  := sg_certs_product S T 
                           (eqv_certs S (bs_eqv S bsS))
                           (eqv_certs T (bs_eqv T bsT)) 
                           (bs_plus_certs S bsS) 
                           (bs_plus_certs T bsT) 
   ; bs_times_certs := sg_certs_product S T 
                           (eqv_certs S (bs_eqv S bsS))
                           (eqv_certs T (bs_eqv T bsT)) 
                           (bs_times_certs S bsS) 
                           (bs_times_certs T bsT) 
   ; bs_certs       := bs_certs_product S T 
                           (eqv_certs S (bs_eqv S bsS))
                           (eqv_certs T (bs_eqv T bsT)) 
                           (bs_certs S bsS) 
                           (bs_certs T bsT) 
   ; bs_ast         := Ast_bs_product(bs_ast S bsS, bs_ast T bsT)
   |}. 


(****************


(*!!*) 
Definition sg_C_sg_product : ∀ (S T : Type),  sg_C_sg S -> sg_C_sg T -> sg_C_sg (S * T) 
:= λ S T bsS bsT, 
   {| 
     sg_C_sg_eqv         := eqv_product S T (sg_C_sg_eqv S bsS) (sg_C_sg_eqv T bsT) 
   ; sg_C_sg_plus        := bop_product S T (sg_C_sg_plus S bsS) (sg_C_sg_plus T bsT) 
   ; sg_C_sg_times       := bop_product S T (sg_C_sg_times S bsS) (sg_C_sg_times T bsT) 
   ; sg_C_sg_plus_certs  := sg_C_certs_product S T 
                             (eqv_eq S (sg_C_sg_eqv S bsS))
                             (eqv_eq T (sg_C_sg_eqv T bsT)) 
                             (sg_C_sg_plus S bsS) 
                             (sg_C_sg_plus T bsT) 
                             (eqv_certs S (sg_C_sg_eqv S bsS))
                             (eqv_certs T (sg_C_sg_eqv T bsT)) 
                             (sg_C_sg_plus_certs S bsS) 
                             (sg_C_sg_plus_certs T bsT) 
   ; sg_C_sg_times_certs := sg_certs_product S T 
                             (eqv_certs S (sg_C_sg_eqv S bsS))
                             (eqv_certs T (sg_C_sg_eqv T bsT)) 
                             (sg_C_sg_times_certs S bsS) 
                             (sg_C_sg_times_certs T bsT) 
   ; sg_C_sg_certs       := bs_certs_product S T 
                             (eqv_certs S (sg_C_sg_eqv S bsS))
                             (eqv_certs T (sg_C_sg_eqv T bsT)) 
                             (sg_C_sg_certs S bsS) 
                             (sg_C_sg_certs T bsT) 
   ; sg_C_sg_ast         := Ast_sg_C_sg_product(sg_C_sg_ast S bsS, sg_C_sg_ast T bsT)
   |}. 


(*!!*) 
Definition sg_CI_sg_product : ∀ (S T : Type),  sg_CI_sg S -> sg_CI_sg T -> sg_CI_sg (S * T) 
:= λ S T bsS bsT, 
   {| 
     sg_CI_sg_eqv         := eqv_product S T (sg_CI_sg_eqv S bsS) (sg_CI_sg_eqv T bsT) 
   ; sg_CI_sg_plus        := bop_product S T (sg_CI_sg_plus S bsS) (sg_CI_sg_plus T bsT) 
   ; sg_CI_sg_times       := bop_product S T (sg_CI_sg_times S bsS) (sg_CI_sg_times T bsT) 
   ; sg_CI_sg_plus_certs  := sg_CI_certs_product S T 
                             (eqv_eq S (sg_CI_sg_eqv S bsS))
                             (eqv_eq T (sg_CI_sg_eqv T bsT)) 
                             (sg_CI_sg_plus S bsS) 
                             (sg_CI_sg_plus T bsT) 
                             (eqv_certs S (sg_CI_sg_eqv S bsS))
                             (eqv_certs T (sg_CI_sg_eqv T bsT)) 
                             (sg_CI_sg_plus_certs S bsS) 
                             (sg_CI_sg_plus_certs T bsT) 
   ; sg_CI_sg_times_certs := sg_certs_product S T 
                             (eqv_certs S (sg_CI_sg_eqv S bsS))
                             (eqv_certs T (sg_CI_sg_eqv T bsT)) 
                             (sg_CI_sg_times_certs S bsS) 
                             (sg_CI_sg_times_certs T bsT) 
   ; sg_CI_sg_certs       := bs_certs_product S T 
                             (eqv_certs S (sg_CI_sg_eqv S bsS))
                             (eqv_certs T (sg_CI_sg_eqv T bsT)) 
                             (sg_CI_sg_certs S bsS) 
                             (sg_CI_sg_certs T bsT) 
   ; sg_CI_sg_ast         := Ast_sg_CI_sg_product(sg_CI_sg_ast S bsS, sg_CI_sg_ast T bsT)
   |}. 




(*CC*) 
Definition sg_C_sg_llex : ∀ (S T : Type),  sg_CS_sg S -> sg_C_sg T -> sg_C_sg (S * T) 
:= λ S T bsS bsT, 
{| 
     sg_C_sg_eqv        := eqv_product S T 
                           (sg_CS_sg_eqv S bsS) 
                           (sg_C_sg_eqv T bsT) 
   ; sg_C_sg_plus       := bop_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (sg_CS_sg_plus S bsS) 
                           (sg_C_sg_plus T bsT) 
   ; sg_C_sg_times       := bop_product S T 
                           (sg_CS_sg_times S bsS) 
                           (sg_C_sg_times T bsT) 
   ; sg_C_sg_plus_certs := sg_C_certs_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (sg_CS_sg_plus S bsS) 
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_C_sg_eqv T bsT)) 
                           (sg_CS_sg_plus_certs S bsS) 
                           (sg_C_sg_plus_certs T bsT) 
   ; sg_C_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_C_sg_eqv T bsT)) 
                           (sg_CS_sg_times_certs S bsS)
                           (sg_C_sg_times_certs T bsT)
   ; sg_C_sg_certs    := bs_certs_llex_product S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (eqv_eq T (sg_C_sg_eqv T bsT)) 
                           (sg_CS_sg_plus S bsS)
                           (sg_C_sg_plus T bsT) 
                           (sg_C_sg_times T bsT)  
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_C_sg_eqv T bsT)) 
                           (sg_CS_sg_times_certs S bsS) 
                           (sg_C_sg_times_certs T bsT) 
                           (sg_CS_sg_certs S bsS) 
                           (sg_C_sg_certs T bsT) 
   ; sg_C_sg_ast        := Ast_sg_C_sg_llex (sg_CS_sg_ast S bsS, sg_C_sg_ast T bsT)
|}. 

(*!!*) 
Definition sg_CS_sg_llex : ∀ (S T : Type),  sg_CS_sg S -> sg_CS_sg T -> sg_CS_sg (S * T) 
:= λ S T bsS bsT, 
{| 
     sg_CS_sg_eqv        := eqv_product S T 
                           (sg_CS_sg_eqv S bsS) 
                           (sg_CS_sg_eqv T bsT) 
   ; sg_CS_sg_plus       := bop_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (sg_CS_sg_plus S bsS) 
                           (sg_CS_sg_plus T bsT) 
   ; sg_CS_sg_times       := bop_product S T 
                           (sg_CS_sg_times S bsS) 
                           (sg_CS_sg_times T bsT) 
   ; sg_CS_sg_plus_certs := sg_CS_certs_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (sg_CS_sg_plus S bsS) 
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_CS_sg_eqv T bsT)) 
                           (sg_CS_sg_plus_certs S bsS) 
                           (sg_CS_sg_plus_certs T bsT) 
   ; sg_CS_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_CS_sg_eqv T bsT)) 
                           (sg_CS_sg_times_certs S bsS)
                           (sg_CS_sg_times_certs T bsT)
   ; sg_CS_sg_certs    := bs_certs_llex_product S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (eqv_eq T (sg_CS_sg_eqv T bsT)) 
                           (sg_CS_sg_plus S bsS)
                           (sg_CS_sg_plus T bsT) 
                           (sg_CS_sg_times T bsT)  
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_CS_sg_eqv T bsT)) 
                           (sg_CS_sg_times_certs S bsS) 
                           (sg_CS_sg_times_certs T bsT) 
                           (sg_CS_sg_certs S bsS) 
                           (sg_CS_sg_certs T bsT) 
   ; sg_CS_sg_ast        := Ast_sg_CS_sg_llex (sg_CS_sg_ast S bsS, sg_CS_sg_ast T bsT)
|}. 



(*!!*) 
Definition sg_CI_sg_llex : ∀ (S T : Type),  sg_CS_sg S -> sg_CI_sg T -> sg_CI_sg (S * T) 
:= λ S T bsS bsT, 
{| 
     sg_CI_sg_eqv        := eqv_product S T 
                           (sg_CS_sg_eqv S bsS) 
                           (sg_CI_sg_eqv T bsT) 
   ; sg_CI_sg_plus       := bop_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (sg_CS_sg_plus S bsS) 
                           (sg_CI_sg_plus T bsT) 
   ; sg_CI_sg_times       := bop_product S T 
                           (sg_CS_sg_times S bsS) 
                           (sg_CI_sg_times T bsT) 
   ; sg_CI_sg_plus_certs := sg_CI_certs_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (sg_CS_sg_plus S bsS) 
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_CI_sg_eqv T bsT)) 
                           (sg_CS_sg_plus_certs S bsS) 
                           (sg_CI_sg_plus_certs T bsT) 
   ; sg_CI_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_CI_sg_eqv T bsT)) 
                           (sg_CS_sg_times_certs S bsS)
                           (sg_CI_sg_times_certs T bsT)
   ; sg_CI_sg_certs    := bs_certs_llex_product S T 
                           (eqv_eq S (sg_CS_sg_eqv S bsS)) 
                           (eqv_eq T (sg_CI_sg_eqv T bsT)) 
                           (sg_CS_sg_plus S bsS)
                           (sg_CI_sg_plus T bsT) 
                           (sg_CI_sg_times T bsT)  
                           (eqv_certs S (sg_CS_sg_eqv S bsS)) 
                           (eqv_certs T (sg_CI_sg_eqv T bsT)) 
                           (sg_CS_sg_times_certs S bsS) 
                           (sg_CI_sg_times_certs T bsT) 
                           (sg_CS_sg_certs S bsS) 
                           (sg_CI_sg_certs T bsT) 
   ; sg_CI_sg_ast := Ast_sg_CI_sg_llex (sg_CS_sg_ast S bsS, sg_CI_sg_ast T bsT)
|}. 

******************) 

(*

Definition bs_and_or : bs bool := 
{|
  bs_eqv          := eqv_eq_bool
; bs_plus         := bop_and
; bs_times        := bop_or
; bs_plus_certs  := sg_certs_and
; bs_times_certs := sg_certs_or
; bs_certs       := bs_certs_and_or 
; bs_ast          := Ast_bs_and_or
|}.


Definition bs_or_and : bs bool := 
{|
  bs_eqv          := eqv_eq_bool
; bs_plus         := bop_or
; bs_times        := bop_and
; bs_plus_certs  := sg_certs_or
; bs_times_certs := sg_certs_and
; bs_certs       := bs_certs_or_and
; bs_ast          := Ast_bs_or_and 
|}.


Definition bs_min_max : bs nat := 
{|
  bs_eqv          := eqv_eq_nat 
; bs_plus         := bop_min
; bs_times        := bop_max
; bs_plus_certs  := sg_certs_min
; bs_times_certs := sg_certs_max
; bs_certs       := bs_certs_min_max
; bs_ast          := Ast_bs_min_max
|}.

Definition bs_max_min : bs nat := 
{|
  bs_eqv          := eqv_eq_nat 
; bs_plus         := bop_max
; bs_times        := bop_min
; bs_plus_certs  := sg_certs_max
; bs_times_certs := sg_certs_min
; bs_certs       := bs_certs_max_min
; bs_ast          := Ast_bs_max_min
|}.

Definition bs_min_plus : bs nat := 
{|
  bs_eqv          := eqv_eq_nat 
; bs_plus         := bop_min
; bs_times        := bop_plus
; bs_plus_certs  := sg_certs_min
; bs_times_certs := sg_certs_plus
; bs_certs       := bs_certs_min_plus
; bs_ast          := Ast_bs_min_plus
|}.
*) 

