Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.construct_certs. 
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
Definition sg_product_new : ∀ (S T : Type),  sg_new S -> sg_new T -> sg_new (S * T) 
:= λ S T sgS sgT, 
   {| 
     sgn_eq     := eqv_product S T (sgn_eq S sgS) (sgn_eq T sgT) 
   ; sgn_bop    := bop_product S T (sgn_bop S sgS) (sgn_bop T sgT) 
   ; sgn_certs := sg_certs_product_new S T 
                    (eqv_certs S (sgn_eq S sgS))
                    (eqv_certs T (sgn_eq T sgT))
                    (sgn_certs S sgS) 
                    (sgn_certs T sgT) 
   ; sgn_ast    := Ast_sg_product (sgn_ast S sgS, sgn_ast T sgT)
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


(*CC*) 

(* Need module for derived structures ... *) 
Definition sg_CS_min_with_infinity : sg_CS (with_constant nat) := 
           sg_CS_add_id nat cas_infinity sg_CS_min. 

Definition sg_CS_max_with_infinity : sg_CS (with_constant nat) := 
           sg_CS_add_ann nat cas_infinity sg_CS_max. 


(* SG SG *) 

(* MIN PLUS 

sg_CS_min

sg_CK_plus

LD RD 

LABS
RABS 




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
Definition sg_sg_add_zero : ∀ (S : Type),  sg_sg S -> cas_constant -> sg_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     sg_sg_eqv          := eqv_add_constant S (sg_sg_eqv S sg_sgS) c 
   ; sg_sg_plus         := bop_add_id S (sg_sg_plus S sg_sgS) c
   ; sg_sg_times        := bop_add_ann S (sg_sg_times S sg_sgS) c
   ; sg_sg_plus_certs  := sg_certs_add_id S c 
                                (eqv_certs S (sg_sg_eqv S sg_sgS)) 
                                (sg_sg_plus_certs S sg_sgS) 
   ; sg_sg_times_certs := sg_certs_add_ann S c 
                                (eqv_certs S (sg_sg_eqv S sg_sgS)) 
                                (sg_sg_times_certs S sg_sgS) 
   ; sg_sg_certs       := sg_sg_certs_add_zero S 
                                (eqv_certs S (sg_sg_eqv S sg_sgS))  
                                (sg_sg_certs S sg_sgS)
   ; sg_sg_ast          := Ast_sg_sg_add_zero (c, sg_sg_ast S sg_sgS)
|}. 


(*CC*) 
Definition sg_C_sg_add_one : ∀ (S : Type), sg_C_sg S -> cas_constant -> sg_C_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     sg_C_sg_eqv          := eqv_add_constant S (sg_C_sg_eqv S sg_sgS) c 
   ; sg_C_sg_plus         := bop_add_ann S (sg_C_sg_plus S sg_sgS) c
   ; sg_C_sg_times        := bop_add_id S (sg_C_sg_times S sg_sgS) c
   ; sg_C_sg_plus_certs  := sg_C_certs_add_ann S c
                                (eqv_certs S (sg_C_sg_eqv S sg_sgS)) 
                                (sg_C_sg_plus_certs S sg_sgS) 
   ; sg_C_sg_times_certs := sg_certs_add_id S c
                                (eqv_certs S (sg_C_sg_eqv S sg_sgS)) 
                                (sg_C_sg_times_certs S sg_sgS) 
   ; sg_C_sg_certs       := sg_sg_certs_add_one S c
                                (eqv_certs S (sg_C_sg_eqv S sg_sgS)) 
                                (sg_C_sg_plus_certs S sg_sgS) 
                                (sg_C_sg_certs S sg_sgS)
   ; sg_C_sg_ast          := Ast_sg_C_sg_add_one (c, sg_C_sg_ast S sg_sgS)
|}. 

(*CC*) 
Definition sg_sg_product : ∀ (S T : Type),  sg_sg S -> sg_sg T -> sg_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
   {| 
     sg_sg_eqv         := eqv_product S T (sg_sg_eqv S sg_sgS) (sg_sg_eqv T sg_sgT) 
   ; sg_sg_plus        := bop_product S T (sg_sg_plus S sg_sgS) (sg_sg_plus T sg_sgT) 
   ; sg_sg_times       := bop_product S T (sg_sg_times S sg_sgS) (sg_sg_times T sg_sgT) 
   ; sg_sg_plus_certs  := sg_certs_product S T 
                           (eqv_certs S (sg_sg_eqv S sg_sgS))
                           (eqv_certs T (sg_sg_eqv T sg_sgT)) 
                           (sg_sg_plus_certs S sg_sgS) 
                           (sg_sg_plus_certs T sg_sgT) 
   ; sg_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_sg_eqv S sg_sgS))
                           (eqv_certs T (sg_sg_eqv T sg_sgT)) 
                           (sg_sg_times_certs S sg_sgS) 
                           (sg_sg_times_certs T sg_sgT) 
   ; sg_sg_certs       := sg_sg_certs_product S T 
                           (eqv_certs S (sg_sg_eqv S sg_sgS))
                           (eqv_certs T (sg_sg_eqv T sg_sgT)) 
                           (sg_sg_certs S sg_sgS) 
                           (sg_sg_certs T sg_sgT) 
   ; sg_sg_ast         := Ast_sg_sg_product(sg_sg_ast S sg_sgS, sg_sg_ast T sg_sgT)
   |}. 



(*!!*) 
Definition sg_C_sg_product : ∀ (S T : Type),  sg_C_sg S -> sg_C_sg T -> sg_C_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
   {| 
     sg_C_sg_eqv         := eqv_product S T (sg_C_sg_eqv S sg_sgS) (sg_C_sg_eqv T sg_sgT) 
   ; sg_C_sg_plus        := bop_product S T (sg_C_sg_plus S sg_sgS) (sg_C_sg_plus T sg_sgT) 
   ; sg_C_sg_times       := bop_product S T (sg_C_sg_times S sg_sgS) (sg_C_sg_times T sg_sgT) 
   ; sg_C_sg_plus_certs  := sg_C_certs_product S T 
                             (eqv_eq S (sg_C_sg_eqv S sg_sgS))
                             (eqv_eq T (sg_C_sg_eqv T sg_sgT)) 
                             (sg_C_sg_plus S sg_sgS) 
                             (sg_C_sg_plus T sg_sgT) 
                             (eqv_certs S (sg_C_sg_eqv S sg_sgS))
                             (eqv_certs T (sg_C_sg_eqv T sg_sgT)) 
                             (sg_C_sg_plus_certs S sg_sgS) 
                             (sg_C_sg_plus_certs T sg_sgT) 
   ; sg_C_sg_times_certs := sg_certs_product S T 
                             (eqv_certs S (sg_C_sg_eqv S sg_sgS))
                             (eqv_certs T (sg_C_sg_eqv T sg_sgT)) 
                             (sg_C_sg_times_certs S sg_sgS) 
                             (sg_C_sg_times_certs T sg_sgT) 
   ; sg_C_sg_certs       := sg_sg_certs_product S T 
                             (eqv_certs S (sg_C_sg_eqv S sg_sgS))
                             (eqv_certs T (sg_C_sg_eqv T sg_sgT)) 
                             (sg_C_sg_certs S sg_sgS) 
                             (sg_C_sg_certs T sg_sgT) 
   ; sg_C_sg_ast         := Ast_sg_C_sg_product(sg_C_sg_ast S sg_sgS, sg_C_sg_ast T sg_sgT)
   |}. 


(*!!*) 
Definition sg_CI_sg_product : ∀ (S T : Type),  sg_CI_sg S -> sg_CI_sg T -> sg_CI_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
   {| 
     sg_CI_sg_eqv         := eqv_product S T (sg_CI_sg_eqv S sg_sgS) (sg_CI_sg_eqv T sg_sgT) 
   ; sg_CI_sg_plus        := bop_product S T (sg_CI_sg_plus S sg_sgS) (sg_CI_sg_plus T sg_sgT) 
   ; sg_CI_sg_times       := bop_product S T (sg_CI_sg_times S sg_sgS) (sg_CI_sg_times T sg_sgT) 
   ; sg_CI_sg_plus_certs  := sg_CI_certs_product S T 
                             (eqv_eq S (sg_CI_sg_eqv S sg_sgS))
                             (eqv_eq T (sg_CI_sg_eqv T sg_sgT)) 
                             (sg_CI_sg_plus S sg_sgS) 
                             (sg_CI_sg_plus T sg_sgT) 
                             (eqv_certs S (sg_CI_sg_eqv S sg_sgS))
                             (eqv_certs T (sg_CI_sg_eqv T sg_sgT)) 
                             (sg_CI_sg_plus_certs S sg_sgS) 
                             (sg_CI_sg_plus_certs T sg_sgT) 
   ; sg_CI_sg_times_certs := sg_certs_product S T 
                             (eqv_certs S (sg_CI_sg_eqv S sg_sgS))
                             (eqv_certs T (sg_CI_sg_eqv T sg_sgT)) 
                             (sg_CI_sg_times_certs S sg_sgS) 
                             (sg_CI_sg_times_certs T sg_sgT) 
   ; sg_CI_sg_certs       := sg_sg_certs_product S T 
                             (eqv_certs S (sg_CI_sg_eqv S sg_sgS))
                             (eqv_certs T (sg_CI_sg_eqv T sg_sgT)) 
                             (sg_CI_sg_certs S sg_sgS) 
                             (sg_CI_sg_certs T sg_sgT) 
   ; sg_CI_sg_ast         := Ast_sg_CI_sg_product(sg_CI_sg_ast S sg_sgS, sg_CI_sg_ast T sg_sgT)
   |}. 




(*CC*) 
Definition sg_C_sg_llex : ∀ (S T : Type),  sg_CS_sg S -> sg_C_sg T -> sg_C_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
{| 
     sg_C_sg_eqv        := eqv_product S T 
                           (sg_CS_sg_eqv S sg_sgS) 
                           (sg_C_sg_eqv T sg_sgT) 
   ; sg_C_sg_plus       := bop_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (sg_CS_sg_plus S sg_sgS) 
                           (sg_C_sg_plus T sg_sgT) 
   ; sg_C_sg_times       := bop_product S T 
                           (sg_CS_sg_times S sg_sgS) 
                           (sg_C_sg_times T sg_sgT) 
   ; sg_C_sg_plus_certs := sg_C_certs_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (sg_CS_sg_plus S sg_sgS) 
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_C_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_plus_certs S sg_sgS) 
                           (sg_C_sg_plus_certs T sg_sgT) 
   ; sg_C_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_C_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_times_certs S sg_sgS)
                           (sg_C_sg_times_certs T sg_sgT)
   ; sg_C_sg_certs    := sg_sg_certs_llex_product S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_eq T (sg_C_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_plus S sg_sgS)
                           (sg_C_sg_plus T sg_sgT) 
                           (sg_C_sg_times T sg_sgT)  
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_C_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_times_certs S sg_sgS) 
                           (sg_C_sg_times_certs T sg_sgT) 
                           (sg_CS_sg_certs S sg_sgS) 
                           (sg_C_sg_certs T sg_sgT) 
   ; sg_C_sg_ast        := Ast_sg_C_sg_llex (sg_CS_sg_ast S sg_sgS, sg_C_sg_ast T sg_sgT)
|}. 

(*!!*) 
Definition sg_CS_sg_llex : ∀ (S T : Type),  sg_CS_sg S -> sg_CS_sg T -> sg_CS_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
{| 
     sg_CS_sg_eqv        := eqv_product S T 
                           (sg_CS_sg_eqv S sg_sgS) 
                           (sg_CS_sg_eqv T sg_sgT) 
   ; sg_CS_sg_plus       := bop_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (sg_CS_sg_plus S sg_sgS) 
                           (sg_CS_sg_plus T sg_sgT) 
   ; sg_CS_sg_times       := bop_product S T 
                           (sg_CS_sg_times S sg_sgS) 
                           (sg_CS_sg_times T sg_sgT) 
   ; sg_CS_sg_plus_certs := sg_CS_certs_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (sg_CS_sg_plus S sg_sgS) 
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_CS_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_plus_certs S sg_sgS) 
                           (sg_CS_sg_plus_certs T sg_sgT) 
   ; sg_CS_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_CS_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_times_certs S sg_sgS)
                           (sg_CS_sg_times_certs T sg_sgT)
   ; sg_CS_sg_certs    := sg_sg_certs_llex_product S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_eq T (sg_CS_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_plus S sg_sgS)
                           (sg_CS_sg_plus T sg_sgT) 
                           (sg_CS_sg_times T sg_sgT)  
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_CS_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_times_certs S sg_sgS) 
                           (sg_CS_sg_times_certs T sg_sgT) 
                           (sg_CS_sg_certs S sg_sgS) 
                           (sg_CS_sg_certs T sg_sgT) 
   ; sg_CS_sg_ast        := Ast_sg_CS_sg_llex (sg_CS_sg_ast S sg_sgS, sg_CS_sg_ast T sg_sgT)
|}. 



(*!!*) 
Definition sg_CI_sg_llex : ∀ (S T : Type),  sg_CS_sg S -> sg_CI_sg T -> sg_CI_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
{| 
     sg_CI_sg_eqv        := eqv_product S T 
                           (sg_CS_sg_eqv S sg_sgS) 
                           (sg_CI_sg_eqv T sg_sgT) 
   ; sg_CI_sg_plus       := bop_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (sg_CS_sg_plus S sg_sgS) 
                           (sg_CI_sg_plus T sg_sgT) 
   ; sg_CI_sg_times       := bop_product S T 
                           (sg_CS_sg_times S sg_sgS) 
                           (sg_CI_sg_times T sg_sgT) 
   ; sg_CI_sg_plus_certs := sg_CI_certs_llex S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (sg_CS_sg_plus S sg_sgS) 
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_CI_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_plus_certs S sg_sgS) 
                           (sg_CI_sg_plus_certs T sg_sgT) 
   ; sg_CI_sg_times_certs := sg_certs_product S T 
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_CI_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_times_certs S sg_sgS)
                           (sg_CI_sg_times_certs T sg_sgT)
   ; sg_CI_sg_certs    := sg_sg_certs_llex_product S T 
                           (eqv_eq S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_eq T (sg_CI_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_plus S sg_sgS)
                           (sg_CI_sg_plus T sg_sgT) 
                           (sg_CI_sg_times T sg_sgT)  
                           (eqv_certs S (sg_CS_sg_eqv S sg_sgS)) 
                           (eqv_certs T (sg_CI_sg_eqv T sg_sgT)) 
                           (sg_CS_sg_times_certs S sg_sgS) 
                           (sg_CI_sg_times_certs T sg_sgT) 
                           (sg_CS_sg_certs S sg_sgS) 
                           (sg_CI_sg_certs T sg_sgT) 
   ; sg_CI_sg_ast := Ast_sg_CI_sg_llex (sg_CS_sg_ast S sg_sgS, sg_CI_sg_ast T sg_sgT)
|}. 

