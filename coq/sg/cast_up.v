Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.

(*
                      1
           sg ------------------------
           |                         |
         2 |                         |
           |                         |
          sg_C                     sg_NC 
         / |  \ 
      4 /  |3  \ 5            (deplicate hierarchy here? but with K, LK, and RK) 
       /   |    \  
  sg_CI sg_CNI  sg_CS 
           | 
           | 6  
           |
         sg_CK


1)  A_sg_proofs_from_sg_NC_proofs    
2)  A_sg_proofs_from_sg_C_proofs     
3)  A_sg_C_proofs_from_sg_CNI_proofs  
4)  A_sg_C_proofs_from_sg_CI_proofs  
5)  A_sg_C_proofs_from_sg_CS_proofs  
6)  A_sg_CNI_proofs_from_sg_CK_proofs  

DERIVED

two hops: 
  A_sg_proofs_from_sg_CI_proofs 
  A_sg_proofs_from_sg_CS_proofs  
  A_sg_proofs_from_sg_CNI_proofs 
  A_sg_C_proofs_from_sg_CK_proofs 

Three hops:
  A_sg_proofs_from_sg_CK_proofs  


1)  A_sg_from_sg_NC
2)  A_sg_from_sg_C
3)  A_sg_C_from_sg_CNI
4)  A_sg_C_from_sg_CI
5)  A_sg_C_from_sg_CS
6)  A_sg_CNI_from_sg_CK

1.id)  A_sg_from_sg_NC_with_id
2.id)  A_sg_from_sg_C_with_id
3.id)  A_sg_C_with_id_from_sg_CNI_with_id
4.id)  A_sg_C_with_id_from_sg_CI_with_id
5.id)  A_sg_C_with_id_from_sg_CS_with_id
6.id)  A_sg_CNI_with_id_from_sg_CK_with_id

1.ann)  A_sg_from_sg_NC_with_ann
2.ann)  A_sg_from_sg_C_with_ann
3.ann)  A_sg_C_with_ann_from_sg_CNI_with_ann
4.ann)  A_sg_C_with_ann_from_sg_CI_with_ann
5.ann)  A_sg_C_with_ann_from_sg_CS_with_ann

1.B)  A_sg_from_sg_BNC
2.B)  A_sg_from_sg_BC
3.B)  A_sg_BC_from_sg_BCNI
4.B)  A_sg_BC_from_sg_BCI
5.B)  A_sg_BC_from_sg_BCS


DERIVED

two hops: 
7)   A_sg_from_sg_CI
8)   A_sg_from_sg_CS
9)   A_sg_from_sg_CNI
10)  A_sg_C_from_sg_CK

7.id)   A_sg_from_sg_CI_with_id
8.id)   A_sg_from_sg_CS_with_id
9.id)   A_sg_from_sg_CNI_with_id
10.id)  A_sg_C_with_id_from_sg_CK_with_id

7.ann)   A_sg_from_sg_CI_with_ann
8.ann)   A_sg_from_sg_CS_with_ann
9.ann)   A_sg_from_sg_CNI_with_ann

7.B)   A_sg_from_sg_BCI
8.B)   A_sg_from_sg_BCS
9.B)   A_sg_from_sg_BCNI


Three hops:
11)     A_sg_from_sg_CK
11.id)  A_sg_from_sg_CK_with_id




*) 

Section ACAS.
 

Section Proofs.

  Variables (S : Type)
            (r : brel S)
            (b : binary_op S)
            (s : S)
            (f : S -> S)
            (Pf : brel_not_trivial S r f)
            (eqvS : eqv_proofs S r)
            (id_d : bop_exists_id_decidable S r b).


(* 1 *)   
Definition A_sg_proofs_from_sg_NC_proofs (sgS : sg_NC_proofs S r b) : sg_proofs S r b := 
{|
  A_sg_associative      := A_sg_NC_associative S r b sgS 
; A_sg_congruence       := A_sg_NC_congruence S r b sgS 
; A_sg_commutative_d    := inr _ (A_sg_NC_not_commutative S r b sgS)
; A_sg_selective_d      := A_sg_NC_selective_d S r b sgS    
; A_sg_is_left_d        := A_sg_NC_is_left_d S r b sgS    
; A_sg_is_right_d       := A_sg_NC_is_right_d S r b sgS    
; A_sg_idempotent_d     := A_sg_NC_idempotent_d S r b sgS    
; A_sg_left_cancel_d    := A_sg_NC_left_cancel_d S r b sgS    
; A_sg_right_cancel_d   := A_sg_NC_right_cancel_d S r b sgS    
; A_sg_left_constant_d  := A_sg_NC_left_constant_d S r b sgS
; A_sg_right_constant_d := A_sg_NC_right_constant_d S r b sgS
; A_sg_anti_left_d      := A_sg_NC_anti_left_d S r b sgS
; A_sg_anti_right_d     := A_sg_NC_anti_right_d S r b sgS
|}. 
  
    
(* 2 *)   
Definition A_sg_proofs_from_sg_C_proofs (sgS : sg_C_proofs S r b) : sg_proofs S r b := 
let commS := A_sg_C_commutative S r b sgS in   
let symS :=  A_eqv_symmetric S r eqvS in 
let tranS := A_eqv_transitive S r eqvS in 
{|
  A_sg_associative      := A_sg_C_associative S r b sgS 
; A_sg_congruence       := A_sg_C_congruence S r b sgS 
; A_sg_commutative_d    := inl _ (A_sg_C_commutative S r b sgS) 
; A_sg_selective_d      := A_sg_C_selective_d S r b sgS    
; A_sg_is_left_d        := inr _ (bop_commutative_implies_not_is_left S r b s f Pf symS tranS commS)
; A_sg_is_right_d       := inr _ (bop_commutative_implies_not_is_right S r b s f Pf symS tranS commS)
; A_sg_idempotent_d     := A_sg_C_idempotent_d S r b sgS    
; A_sg_left_cancel_d    := A_sg_C_cancel_d S r b sgS    
; A_sg_right_cancel_d   := match A_sg_C_cancel_d S r b sgS with 
                           | inl lcanS => inl (bop_commutative_and_left_cancellative_imply_right_cancellative S r b tranS commS lcanS)
                           | inr nlcanS => inr (bop_commutative_and_not_left_cancellative_imply_not_right_cancellative S r b symS tranS commS nlcanS)
                           end 
; A_sg_left_constant_d  := A_sg_C_constant_d S r b sgS
; A_sg_right_constant_d := match A_sg_C_constant_d S r b sgS with
                           | inl conS => inl (bop_commutative_and_left_constant_imply_right_constant S r b tranS commS conS)                             
                           | inr nconS => inr (bop_commutative_and_not_left_constant_imply_not_right_constant S r b symS tranS commS nconS)
                           end                                                         
; A_sg_anti_left_d      := A_sg_C_anti_left_d S r b sgS
; A_sg_anti_right_d     := A_sg_C_anti_right_d S r b sgS
|}.

(* 3 *)
Definition A_sg_C_proofs_from_sg_CNI_proofs (sgS : sg_CNI_proofs S r b) : sg_C_proofs S r b := 
let nidem   := A_sg_CNI_not_idempotent S r b sgS  in
let not_sel := bop_not_idempotent_implies_not_selective _ _ _ nidem in 
{|
  A_sg_C_associative      := A_sg_CNI_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CNI_congruence S r b sgS  
; A_sg_C_commutative      := A_sg_CNI_commutative S r b sgS 
; A_sg_C_selective_d      := inr not_sel
; A_sg_C_idempotent_d     := inr nidem 
; A_sg_C_cancel_d         := A_sg_CNI_cancel_d _ _ _  sgS
; A_sg_C_constant_d       := A_sg_CNI_constant_d _ _ _  sgS
; A_sg_C_anti_left_d      := A_sg_CNI_anti_left_d _ _ _  sgS
; A_sg_C_anti_right_d     := A_sg_CNI_anti_right_d _ _ _  sgS
|}. 

(* 4 *)   
Definition A_sg_C_proofs_from_sg_CI_proofs (sgS : sg_CI_proofs S r b) : sg_C_proofs S r b := 
let assoc := A_sg_CI_associative S r b sgS in
let econg := A_eqv_congruence  S r eqvS  in 
let bcong := A_sg_CI_congruence S r b sgS  in 
let comm  := A_sg_CI_commutative S r b sgS in
let not_sel := A_sg_CI_not_selective S r b sgS   in
let idem  := A_sg_CI_idempotent S r b sgS  in 
let ref   := A_eqv_reflexive S r eqvS in
let sym   := A_eqv_symmetric S r eqvS in
let trn   := A_eqv_transitive S r eqvS in 
{|
  A_sg_C_associative      := assoc 
; A_sg_C_congruence       := bcong 
; A_sg_C_commutative      := comm 
; A_sg_C_selective_d      := inr not_sel
; A_sg_C_idempotent_d     := inl _ idem 
; A_sg_C_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f 
                                       econg Pf ref sym trn assoc bcong idem comm (inr not_sel))
; A_sg_C_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b s f Pf 
                                       econg ref trn idem comm) 
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b s sym idem)
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b s sym idem) 
|}. 

(* 5 *)   
Definition A_sg_C_proofs_from_sg_CS_proofs (sgS : sg_CS_proofs S r b) : sg_C_proofs S r b := 
let assoc := A_sg_CS_associative S r b sgS in
let econg := A_eqv_congruence  S r eqvS  in 
let bcong := A_sg_CS_congruence S r b sgS  in 
let comm  := A_sg_CS_commutative S r b sgS in
let sel   := A_sg_CS_selective S r b sgS   in
let idem  := bop_selective_implies_idempotent S r b  sel in
let ref   := A_eqv_reflexive S r eqvS in
let sym   := A_eqv_symmetric S r eqvS in
let trn   := A_eqv_transitive S r eqvS in 
{|
  A_sg_C_associative      := assoc 
; A_sg_C_congruence       := bcong 
; A_sg_C_commutative      := comm 
; A_sg_C_selective_d      := inl sel 
; A_sg_C_idempotent_d     := inl idem 
; A_sg_C_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f 
                                       econg Pf ref sym trn assoc bcong idem comm (inl sel))
; A_sg_C_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b s f Pf 
                                       econg ref trn idem comm)
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b s sym idem) 
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b s sym idem) 
|}. 

(* 6 *)   
Definition A_sg_CNI_proofs_from_sg_CK_proofs (sgS : sg_CK_proofs S r b) : sg_CNI_proofs S r b := 
let right_cancel := bop_commutative_and_left_cancellative_imply_right_cancellative S r b 
                      (A_eqv_transitive S r eqvS) 
                      (A_sg_CK_commutative S r b sgS)
                      (A_sg_CK_cancel S r b sgS)    
in 
let not_idem := bop_cancellative_implies_not_idempotent S r b s f Pf 
                   (A_eqv_reflexive S r eqvS)  
                   (A_eqv_symmetric S r eqvS) 
                   (A_eqv_transitive S r eqvS) 
                   (A_sg_CK_associative S r b sgS)
                   (A_sg_CK_congruence S r b sgS)
                   (A_sg_CK_cancel S r b sgS)    
                   right_cancel
                   id_d
in 
{|
  A_sg_CNI_associative      := A_sg_CK_associative S r b sgS 
; A_sg_CNI_congruence       := A_sg_CK_congruence S r b sgS 
; A_sg_CNI_commutative      := A_sg_CK_commutative S r b sgS
; A_sg_CNI_not_idempotent   := not_idem 
; A_sg_CNI_cancel_d    := inl _ (A_sg_CK_cancel S r b sgS)    
; A_sg_CNI_constant_d  := inr _ (bop_left_cancellative_implies_not_left_constant S r b s f Pf 
                                       (A_sg_CK_cancel S r b sgS)    
                                   )
; A_sg_CNI_anti_left_d      := A_sg_CK_anti_left_d S r b sgS 
; A_sg_CNI_anti_right_d     := A_sg_CK_anti_right_d S r b sgS
|}. 


(* DERIVED UPCASTS *)


(* two hops 
*) 
Definition A_sg_proofs_from_sg_CI_proofs (sgS : sg_CI_proofs S r b) : sg_proofs S r b := 
   A_sg_proofs_from_sg_C_proofs (A_sg_C_proofs_from_sg_CI_proofs sgS).

Definition A_sg_proofs_from_sg_CS_proofs (sgS : sg_CS_proofs S r b) : sg_proofs S r b := 
   A_sg_proofs_from_sg_C_proofs (A_sg_C_proofs_from_sg_CS_proofs sgS).

Definition A_sg_proofs_from_sg_CNI_proofs (sgS : sg_CNI_proofs S r b) : sg_proofs S r b := 
   A_sg_proofs_from_sg_C_proofs (A_sg_C_proofs_from_sg_CNI_proofs sgS).

Definition A_sg_C_proofs_from_sg_CK_proofs (sgS : sg_CK_proofs S r b) : sg_C_proofs S r b := 
   A_sg_C_proofs_from_sg_CNI_proofs (A_sg_CNI_proofs_from_sg_CK_proofs sgS).

(* three hops *)
Definition A_sg_proofs_from_sg_CK_proofs (sgS : sg_CK_proofs S r b) : sg_proofs S r b := 
   A_sg_proofs_from_sg_C_proofs (A_sg_C_proofs_from_sg_CK_proofs sgS).


End Proofs.
  

Section Combinators. 

(* 1 *)   
Definition A_sg_from_sg_NC (S : Type) (sgS : A_sg_NC S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_NC_eqv _ sgS
   ; A_sg_bop          := A_sg_NC_bop _ sgS
   ; A_sg_exists_id_d  := inr (A_sg_NC_not_exists_id _ sgS)
   ; A_sg_exists_ann_d := inr (A_sg_NC_not_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_NC_proofs _ _ _  (A_sg_NC_proofs _ sgS)
   ; A_sg_ast          := A_sg_NC_ast _ sgS
   |}. 
  
  
(* 2 *)   
Definition A_sg_from_sg_C (S : Type) (sgS : A_sg_C S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_C_eqv _ sgS
   ; A_sg_bop          := A_sg_C_bop _ sgS
   ; A_sg_exists_id_d  := inr (A_sg_C_not_exists_id _ sgS)
   ; A_sg_exists_ann_d := inr (A_sg_C_not_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_C_proofs _ _ _ 
                            (A_eqv_witness _ (A_sg_C_eqv _ sgS))
                            (A_eqv_new _ (A_sg_C_eqv _ sgS))
                            (A_eqv_not_trivial _ (A_sg_C_eqv _ sgS))
                            (A_eqv_proofs _ (A_sg_C_eqv _ sgS)) 
                            (A_sg_C_proofs _ sgS)
   ; A_sg_ast        := A_sg_C_ast _ sgS
   |}. 


(* 3 *)
Definition A_sg_C_from_sg_CNI (S : Type) (sgS : A_sg_CNI S) : A_sg_C S := 
   {| 
     A_sg_C_eqv          := A_sg_CNI_eqv S sgS
   ; A_sg_C_bop          := A_sg_CNI_bop S sgS
   ; A_sg_C_not_exists_id  := A_sg_CNI_not_exists_id S sgS    
   ; A_sg_C_not_exists_ann := A_sg_CNI_not_exists_ann S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CNI_proofs _ _ _ (A_sg_CNI_proofs S sgS)
   ; A_sg_C_ast        := A_sg_CNI_ast S sgS
   |}. 

(* 4 *)   
Definition A_sg_C_from_sg_CI (S : Type) (sgS : A_sg_CI S) : A_sg_C S := 
   {| 
     A_sg_C_eqv          := A_sg_CI_eqv S sgS
   ; A_sg_C_bop          := A_sg_CI_bop S sgS
   ; A_sg_C_not_exists_id  := A_sg_CI_not_exists_id S sgS    
   ; A_sg_C_not_exists_ann := A_sg_CI_not_exists_ann S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_bop S sgS)
                            (A_eqv_witness S (A_sg_CI_eqv S sgS))
                            (A_eqv_new S (A_sg_CI_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CI_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_proofs S sgS)
   ; A_sg_C_ast        := A_sg_CI_ast S sgS
   |}. 

(* 5 *)   
Definition A_sg_C_from_sg_CS (S : Type) (sgS : A_sg_CS S) : A_sg_C S := 
   {| 
     A_sg_C_eqv          := A_sg_CS_eqv S sgS
   ; A_sg_C_bop          := A_sg_CS_bop S sgS
   ; A_sg_C_not_exists_id  := A_sg_CS_not_exists_id S sgS    
   ; A_sg_C_not_exists_ann := A_sg_CS_not_exists_ann S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_bop S sgS)
                            (A_eqv_witness S (A_sg_CS_eqv S sgS))
                            (A_eqv_new S (A_sg_CS_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CS_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_proofs S sgS)
   ; A_sg_C_ast        := A_sg_CS_ast S sgS
   |}. 

(* 6 *)   
Definition A_sg_CNI_from_sg_CK (S : Type) (sgS : A_sg_CK S) : A_sg_CNI S := 
let eqvS := A_sg_CK_eqv S sgS in
let eqvP := A_eqv_proofs S eqvS in
let eq   := A_eqv_eq S eqvS in 
let symS := A_eqv_symmetric S eq eqvP in
let trnS := A_eqv_transitive S eq eqvP in 
let b    := A_sg_CK_bop S sgS in 
let s    := (A_eqv_witness S (A_sg_CK_eqv S sgS)) in
let f    := A_eqv_new S (A_sg_CK_eqv S sgS) in
let Pf   := A_eqv_not_trivial S (A_sg_CK_eqv S sgS) in 
   {| 
     A_sg_CNI_eqv          := eqvS 
   ; A_sg_CNI_bop          := b 
   ; A_sg_CNI_not_exists_id  := A_sg_CK_not_exists_id S sgS
   ; A_sg_CNI_not_exists_ann := (bop_left_cancellative_implies_not_exists_ann S eq b s f symS trnS Pf 
                                    (A_sg_CK_cancel S eq b (A_sg_CK_proofs S sgS)))
   ; A_sg_CNI_proofs     := A_sg_CNI_proofs_from_sg_CK_proofs S eq b s f Pf eqvP (inr (A_sg_CK_not_exists_id S sgS)) (A_sg_CK_proofs S sgS)
   ; A_sg_CNI_ast        := A_sg_CK_ast S sgS
   |}.


(* 1.id *)   
Definition A_sg_from_sg_NC_with_id (S : Type) (sgS : A_sg_NC_with_id S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_NC_wi_eqv _ sgS
   ; A_sg_bop          := A_sg_NC_wi_bop _ sgS
   ; A_sg_exists_id_d  := inl (A_sg_NC_wi_exists_id _ sgS)
   ; A_sg_exists_ann_d := inr (A_sg_NC_wi_not_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_NC_proofs _ _ _  (A_sg_NC_wi_proofs _ sgS)
   ; A_sg_ast          := A_sg_NC_wi_ast _ sgS
   |}. 
  
  
(* 2.id *)   
Definition A_sg_from_sg_C_with_id (S : Type) (sgS : A_sg_C_with_id S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_C_wi_eqv _ sgS
   ; A_sg_bop          := A_sg_C_wi_bop _ sgS
   ; A_sg_exists_id_d  := inl (A_sg_C_wi_exists_id _ sgS)
   ; A_sg_exists_ann_d := inr (A_sg_C_wi_not_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_C_proofs _ _ _ 
                            (A_eqv_witness _ (A_sg_C_wi_eqv _ sgS))
                            (A_eqv_new _ (A_sg_C_wi_eqv _ sgS))
                            (A_eqv_not_trivial _ (A_sg_C_wi_eqv _ sgS))
                            (A_eqv_proofs _ (A_sg_C_wi_eqv _ sgS)) 
                            (A_sg_C_wi_proofs _ sgS)
   ; A_sg_ast        := A_sg_C_wi_ast _ sgS
   |}. 


(* 3.id *)
Definition A_sg_C_with_id_from_sg_CNI_with_id (S : Type) (sgS : A_sg_CNI_with_id S) : A_sg_C_with_id S := 
   {| 
     A_sg_C_wi_eqv            := A_sg_CNI_wi_eqv S sgS
   ; A_sg_C_wi_bop            := A_sg_CNI_wi_bop S sgS
   ; A_sg_C_wi_exists_id      := A_sg_CNI_wi_exists_id S sgS    
   ; A_sg_C_wi_not_exists_ann := A_sg_CNI_wi_not_exists_ann S sgS    
   ; A_sg_C_wi_proofs         := A_sg_C_proofs_from_sg_CNI_proofs _ _ _ (A_sg_CNI_wi_proofs S sgS)
   ; A_sg_C_wi_ast            := A_sg_CNI_wi_ast S sgS
   |}. 

(* 4.id *)   
Definition A_sg_C_with_id_from_sg_CI_with_id (S : Type) (sgS : A_sg_CI_with_id S) : A_sg_C_with_id S := 
   {| 
     A_sg_C_wi_eqv          := A_sg_CI_wi_eqv S sgS
   ; A_sg_C_wi_bop          := A_sg_CI_wi_bop S sgS
   ; A_sg_C_wi_exists_id    := A_sg_CI_wi_exists_id S sgS    
   ; A_sg_C_wi_not_exists_ann := A_sg_CI_wi_not_exists_ann S sgS    
   ; A_sg_C_wi_proofs       := A_sg_C_proofs_from_sg_CI_proofs S 
                                (A_eqv_eq S (A_sg_CI_wi_eqv S sgS)) 
                                (A_sg_CI_wi_bop S sgS)
                                (A_eqv_witness S (A_sg_CI_wi_eqv S sgS))
                                (A_eqv_new S (A_sg_CI_wi_eqv S sgS))
                                (A_eqv_not_trivial S (A_sg_CI_wi_eqv S sgS))    
                                (A_eqv_proofs S (A_sg_CI_wi_eqv S sgS)) 
                                (A_sg_CI_wi_proofs S sgS)
   ; A_sg_C_wi_ast        := A_sg_CI_wi_ast S sgS
   |}. 

(* 5.id *)   
Definition A_sg_C_with_id_from_sg_CS_with_id (S : Type) (sgS : A_sg_CS_with_id S) : A_sg_C_with_id S := 
   {| 
     A_sg_C_wi_eqv          := A_sg_CS_wi_eqv S sgS
   ; A_sg_C_wi_bop          := A_sg_CS_wi_bop S sgS
   ; A_sg_C_wi_exists_id    := A_sg_CS_wi_exists_id S sgS    
   ; A_sg_C_wi_not_exists_ann := A_sg_CS_wi_not_exists_ann S sgS    
   ; A_sg_C_wi_proofs       := A_sg_C_proofs_from_sg_CS_proofs S 
                               (A_eqv_eq S (A_sg_CS_wi_eqv S sgS)) 
                               (A_sg_CS_wi_bop S sgS)
                               (A_eqv_witness S (A_sg_CS_wi_eqv S sgS))
                               (A_eqv_new S (A_sg_CS_wi_eqv S sgS))
                               (A_eqv_not_trivial S (A_sg_CS_wi_eqv S sgS)) 
                               (A_eqv_proofs S (A_sg_CS_wi_eqv S sgS)) 
                               (A_sg_CS_wi_proofs S sgS)
   ; A_sg_C_wi_ast        := A_sg_CS_wi_ast S sgS
   |}. 

(* 6.id *)   
Definition A_sg_CNI_with_id_from_sg_CK_with_id (S : Type) (sgS : A_sg_CK_with_id S) : A_sg_CNI_with_id S := 
let eqvS := A_sg_CK_wi_eqv S sgS in
let eqvP := A_eqv_proofs S eqvS in
let eq   := A_eqv_eq S eqvS in 
let symS := A_eqv_symmetric S eq eqvP in
let trnS := A_eqv_transitive S eq eqvP in 
let b    := A_sg_CK_wi_bop S sgS in 
let s    := (A_eqv_witness S (A_sg_CK_wi_eqv S sgS)) in
let f    := A_eqv_new S (A_sg_CK_wi_eqv S sgS) in
let Pf   := A_eqv_not_trivial S (A_sg_CK_wi_eqv S sgS) in 
   {| 
     A_sg_CNI_wi_eqv          := eqvS 
   ; A_sg_CNI_wi_bop          := b 
   ; A_sg_CNI_wi_exists_id  := A_sg_CK_wi_exists_id S sgS
   ; A_sg_CNI_wi_not_exists_ann := (bop_left_cancellative_implies_not_exists_ann S eq b s f symS trnS Pf 
                                    (A_sg_CK_cancel S eq b (A_sg_CK_wi_proofs S sgS)))
   ; A_sg_CNI_wi_proofs     := A_sg_CNI_proofs_from_sg_CK_proofs S eq b s f Pf eqvP (inl (A_sg_CK_wi_exists_id S sgS)) (A_sg_CK_wi_proofs S sgS)
   ; A_sg_CNI_wi_ast        := A_sg_CK_wi_ast S sgS
   |}.


(* 1.ann *)   
Definition A_sg_from_sg_NC_with_ann (S : Type) (sgS : A_sg_NC_with_ann S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_NC_wa_eqv _ sgS
   ; A_sg_bop          := A_sg_NC_wa_bop _ sgS
   ; A_sg_exists_id_d  := inr (A_sg_NC_wa_not_exists_id _ sgS)
   ; A_sg_exists_ann_d := inl (A_sg_NC_wa_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_NC_proofs _ _ _  (A_sg_NC_wa_proofs _ sgS)
   ; A_sg_ast          := A_sg_NC_wa_ast _ sgS
   |}. 
  
  
(* 2.ann *)   
Definition A_sg_from_sg_C_with_ann (S : Type) (sgS : A_sg_C_with_ann S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_C_wa_eqv _ sgS
   ; A_sg_bop          := A_sg_C_wa_bop _ sgS
   ; A_sg_exists_id_d  := inr (A_sg_C_wa_not_exists_id _ sgS)
   ; A_sg_exists_ann_d := inl (A_sg_C_wa_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_C_proofs _ _ _ 
                            (A_eqv_witness _ (A_sg_C_wa_eqv _ sgS))
                            (A_eqv_new _ (A_sg_C_wa_eqv _ sgS))
                            (A_eqv_not_trivial _ (A_sg_C_wa_eqv _ sgS))
                            (A_eqv_proofs _ (A_sg_C_wa_eqv _ sgS)) 
                            (A_sg_C_wa_proofs _ sgS)
   ; A_sg_ast        := A_sg_C_wa_ast _ sgS
   |}. 


(* 3.ann *)
Definition A_sg_C_with_ann_from_sg_CNI_with_ann (S : Type) (sgS : A_sg_CNI_with_ann S) : A_sg_C_with_ann S := 
   {| 
     A_sg_C_wa_eqv            := A_sg_CNI_wa_eqv S sgS
   ; A_sg_C_wa_bop            := A_sg_CNI_wa_bop S sgS
   ; A_sg_C_wa_not_exists_id  := A_sg_CNI_wa_not_exists_id S sgS    
   ; A_sg_C_wa_exists_ann     := A_sg_CNI_wa_exists_ann S sgS    
   ; A_sg_C_wa_proofs         := A_sg_C_proofs_from_sg_CNI_proofs _ _ _ (A_sg_CNI_wa_proofs S sgS)
   ; A_sg_C_wa_ast            := A_sg_CNI_wa_ast S sgS
   |}. 

(* 4.ann *)   
Definition A_sg_C_with_ann_from_sg_CI_with_ann (S : Type) (sgS : A_sg_CI_with_ann S) : A_sg_C_with_ann S := 
   {| 
     A_sg_C_wa_eqv          := A_sg_CI_wa_eqv S sgS
   ; A_sg_C_wa_bop          := A_sg_CI_wa_bop S sgS
   ; A_sg_C_wa_not_exists_id := A_sg_CI_wa_not_exists_id S sgS    
   ; A_sg_C_wa_exists_ann   := A_sg_CI_wa_exists_ann S sgS    
   ; A_sg_C_wa_proofs       := A_sg_C_proofs_from_sg_CI_proofs S 
                                (A_eqv_eq S (A_sg_CI_wa_eqv S sgS)) 
                                (A_sg_CI_wa_bop S sgS)
                                (A_eqv_witness S (A_sg_CI_wa_eqv S sgS))
                                (A_eqv_new S (A_sg_CI_wa_eqv S sgS))
                                (A_eqv_not_trivial S (A_sg_CI_wa_eqv S sgS))    
                                (A_eqv_proofs S (A_sg_CI_wa_eqv S sgS)) 
                                (A_sg_CI_wa_proofs S sgS)
   ; A_sg_C_wa_ast        := A_sg_CI_wa_ast S sgS
   |}. 

(* 5.ann *)   
Definition A_sg_C_with_ann_from_sg_CS_with_ann (S : Type) (sgS : A_sg_CS_with_ann S) : A_sg_C_with_ann S := 
   {| 
     A_sg_C_wa_eqv          := A_sg_CS_wa_eqv S sgS
   ; A_sg_C_wa_bop          := A_sg_CS_wa_bop S sgS
   ; A_sg_C_wa_not_exists_id    := A_sg_CS_wa_not_exists_id S sgS    
   ; A_sg_C_wa_exists_ann := A_sg_CS_wa_exists_ann S sgS    
   ; A_sg_C_wa_proofs       := A_sg_C_proofs_from_sg_CS_proofs S 
                               (A_eqv_eq S (A_sg_CS_wa_eqv S sgS)) 
                               (A_sg_CS_wa_bop S sgS)
                               (A_eqv_witness S (A_sg_CS_wa_eqv S sgS))
                               (A_eqv_new S (A_sg_CS_wa_eqv S sgS))
                               (A_eqv_not_trivial S (A_sg_CS_wa_eqv S sgS)) 
                               (A_eqv_proofs S (A_sg_CS_wa_eqv S sgS)) 
                               (A_sg_CS_wa_proofs S sgS)
   ; A_sg_C_wa_ast        := A_sg_CS_wa_ast S sgS
   |}. 


(* 1.B *)   
Definition A_sg_from_sg_BNC (S : Type) (sgS : A_sg_BNC S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_BNC_eqv _ sgS
   ; A_sg_bop          := A_sg_BNC_bop _ sgS
   ; A_sg_exists_id_d  := inl (A_sg_BNC_exists_id _ sgS)
   ; A_sg_exists_ann_d := inl (A_sg_BNC_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_NC_proofs _ _ _  (A_sg_BNC_proofs _ sgS)
   ; A_sg_ast          := A_sg_BNC_ast _ sgS
   |}. 
  
  
(* 2.B *)   
Definition A_sg_from_sg_BC (S : Type) (sgS : A_sg_BC S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_BC_eqv _ sgS
   ; A_sg_bop          := A_sg_BC_bop _ sgS
   ; A_sg_exists_id_d  := inl (A_sg_BC_exists_id _ sgS)
   ; A_sg_exists_ann_d := inl (A_sg_BC_exists_ann _ sgS)
   ; A_sg_proofs       := A_sg_proofs_from_sg_C_proofs _ _ _ 
                            (A_eqv_witness _ (A_sg_BC_eqv _ sgS))
                            (A_eqv_new _ (A_sg_BC_eqv _ sgS))
                            (A_eqv_not_trivial _ (A_sg_BC_eqv _ sgS))
                            (A_eqv_proofs _ (A_sg_BC_eqv _ sgS)) 
                            (A_sg_BC_proofs _ sgS)
   ; A_sg_ast        := A_sg_BC_ast _ sgS
   |}. 


(* 3.B *)
Definition A_sg_BC_from_sg_BCNI (S : Type) (sgS : A_sg_BCNI S) : A_sg_BC S := 
   {| 
     A_sg_BC_eqv            := A_sg_BCNI_eqv S sgS
   ; A_sg_BC_bop            := A_sg_BCNI_bop S sgS
   ; A_sg_BC_exists_id      := A_sg_BCNI_exists_id S sgS    
   ; A_sg_BC_exists_ann     := A_sg_BCNI_exists_ann S sgS    
   ; A_sg_BC_proofs         := A_sg_C_proofs_from_sg_CNI_proofs _ _ _ (A_sg_BCNI_proofs S sgS)
   ; A_sg_BC_ast            := A_sg_BCNI_ast S sgS
   |}. 

(* 4.B *)   
Definition A_sg_BC_from_sg_BCI (S : Type) (sgS : A_sg_BCI S) : A_sg_BC S := 
   {| 
     A_sg_BC_eqv          := A_sg_BCI_eqv S sgS
   ; A_sg_BC_bop          := A_sg_BCI_bop S sgS
   ; A_sg_BC_exists_id    := A_sg_BCI_exists_id S sgS    
   ; A_sg_BC_exists_ann   := A_sg_BCI_exists_ann S sgS    
   ; A_sg_BC_proofs       := A_sg_C_proofs_from_sg_CI_proofs S 
                                (A_eqv_eq S (A_sg_BCI_eqv S sgS)) 
                                (A_sg_BCI_bop S sgS)
                                (A_eqv_witness S (A_sg_BCI_eqv S sgS))
                                (A_eqv_new S (A_sg_BCI_eqv S sgS))
                                (A_eqv_not_trivial S (A_sg_BCI_eqv S sgS))    
                                (A_eqv_proofs S (A_sg_BCI_eqv S sgS)) 
                                (A_sg_BCI_proofs S sgS)
   ; A_sg_BC_ast        := A_sg_BCI_ast S sgS
   |}. 

(* 5.B *)   
Definition A_sg_BC_from_sg_BCS (S : Type) (sgS : A_sg_BCS S) : A_sg_BC S := 
   {| 
     A_sg_BC_eqv          := A_sg_BCS_eqv S sgS
   ; A_sg_BC_bop          := A_sg_BCS_bop S sgS
   ; A_sg_BC_exists_id    := A_sg_BCS_exists_id S sgS    
   ; A_sg_BC_exists_ann   := A_sg_BCS_exists_ann S sgS    
   ; A_sg_BC_proofs       := A_sg_C_proofs_from_sg_CS_proofs S 
                               (A_eqv_eq S (A_sg_BCS_eqv S sgS)) 
                               (A_sg_BCS_bop S sgS)
                               (A_eqv_witness S (A_sg_BCS_eqv S sgS))
                               (A_eqv_new S (A_sg_BCS_eqv S sgS))
                               (A_eqv_not_trivial S (A_sg_BCS_eqv S sgS)) 
                               (A_eqv_proofs S (A_sg_BCS_eqv S sgS)) 
                               (A_sg_BCS_proofs S sgS)
   ; A_sg_BC_ast        := A_sg_BCS_ast S sgS
   |}. 



(* DERIVED UPCASTS *)

(* two hops*)

(* 7 *) 
Definition A_sg_from_sg_CI : ∀ (S : Type),  A_sg_CI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CI S sgS).  

(* 8 *) 
Definition A_sg_from_sg_CS : ∀ (S : Type),  A_sg_CS S -> A_sg S 
  := λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CS S sgS).

(* 9 *) 
Definition A_sg_from_sg_CNI : ∀ (S : Type),  A_sg_CNI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CNI S sgS).  

(* 10 *) 
Definition A_sg_C_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg_C S 
  := λ S sgS, A_sg_C_from_sg_CNI S (A_sg_CNI_from_sg_CK S sgS).


(* 7.id *) 
Definition A_sg_from_sg_CI_with_id : ∀ (S : Type),  A_sg_CI_with_id S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C_with_id S (A_sg_C_with_id_from_sg_CI_with_id S sgS).  

(* 8.id *) 
Definition A_sg_from_sg_CS_with_id : ∀ (S : Type),  A_sg_CS_with_id S -> A_sg S 
  := λ S sgS, A_sg_from_sg_C_with_id S (A_sg_C_with_id_from_sg_CS_with_id S sgS).

(* 9.id *) 
Definition A_sg_from_sg_CNI_with_id : ∀ (S : Type),  A_sg_CNI_with_id S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C_with_id S (A_sg_C_with_id_from_sg_CNI_with_id S sgS).  

(* 10.id *) 
Definition A_sg_C_with_id_from_sg_CK_with_id : ∀ (S : Type),  A_sg_CK_with_id S -> A_sg_C_with_id S 
  := λ S sgS, A_sg_C_with_id_from_sg_CNI_with_id S (A_sg_CNI_with_id_from_sg_CK_with_id S sgS).


(* 7.ann *) 
Definition A_sg_from_sg_CI_with_ann : ∀ (S : Type),  A_sg_CI_with_ann S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C_with_ann S (A_sg_C_with_ann_from_sg_CI_with_ann S sgS).  

(* 8.ann *) 
Definition A_sg_from_sg_CS_with_ann : ∀ (S : Type),  A_sg_CS_with_ann S -> A_sg S 
  := λ S sgS, A_sg_from_sg_C_with_ann S (A_sg_C_with_ann_from_sg_CS_with_ann S sgS).

(* 9.ann *) 
Definition A_sg_from_sg_CNI_with_ann : ∀ (S : Type),  A_sg_CNI_with_ann S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C_with_ann S (A_sg_C_with_ann_from_sg_CNI_with_ann S sgS).  


(* 7.B *) 
Definition A_sg_from_sg_BCI : ∀ (S : Type),  A_sg_BCI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_BC S (A_sg_BC_from_sg_BCI S sgS).  

(* 8.B *) 
Definition A_sg_from_sg_BCS : ∀ (S : Type),  A_sg_BCS S -> A_sg S 
  := λ S sgS, A_sg_from_sg_BC S (A_sg_BC_from_sg_BCS S sgS).

(* 9.B *) 
Definition A_sg_from_sg_BCNI : ∀ (S : Type),  A_sg_BCNI S -> A_sg S 
  := λ S sgS, A_sg_from_sg_BC S (A_sg_BC_from_sg_BCNI S sgS).

(* three hops *)

(* 11 *)
Definition A_sg_from_sg_CK : ∀ (S : Type),  A_sg_CK S -> A_sg S 
  := λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CK S sgS).

(* 11.id *)
Definition A_sg_from_sg_CK_with_id : ∀ (S : Type),  A_sg_CK_with_id S -> A_sg S 
  := λ S sgS, A_sg_from_sg_C_with_id S (A_sg_C_with_id_from_sg_CK_with_id S sgS).

End Combinators. 

End ACAS.


Section AMCAS.

Definition A_sg_proofs_mcas_cast_up
           (S : Type)
           (eq : brel S)
           (s : S)
           (f : S -> S)
           (nt : brel_not_trivial S eq f)
           (eqvP : eqv_proofs S eq)
           (bop : binary_op S)
           (id_d : bop_exists_id_decidable S eq bop)
           (A : sg_proofs_mcas S eq bop) : sg_proofs_mcas S eq bop :=
match A with
  | A_MCAS_Proof_sg_Error _ _ _ _ => A
  | A_MCAS_Proof_sg _ _ _ _       => A
  | A_MCAS_Proof_sg_C _ _ _ B     => A_MCAS_Proof_sg _ _ _ (A_sg_proofs_from_sg_C_proofs _ _ _ s f nt eqvP B)
  | A_MCAS_Proof_sg_NC _ _ _ B    => A_MCAS_Proof_sg _ _ _ (A_sg_proofs_from_sg_NC_proofs _ _ _ B) 
  | A_MCAS_Proof_sg_CS _ _ _ B    => A_MCAS_Proof_sg _ _ _ (A_sg_proofs_from_sg_CS_proofs _ _ _ s f nt eqvP B) 
  | A_MCAS_Proof_sg_CI _ _ _ B    => A_MCAS_Proof_sg _ _ _ (A_sg_proofs_from_sg_CI_proofs _ _ _ s f nt eqvP B)  
  | A_MCAS_Proof_sg_CNI _ _ _ B   => A_MCAS_Proof_sg _ _ _ (A_sg_proofs_from_sg_CNI_proofs _ _ _ s f nt eqvP B) 
  | A_MCAS_Proof_sg_CK _ _ _ B    => A_MCAS_Proof_sg _ _ _ (A_sg_proofs_from_sg_CK_proofs _ _ _ s f nt eqvP id_d B)
end.

Definition A_sg_mcas_cast_up (S : Type) (A : A_sg_mcas S) : A_sg_mcas S :=
match A with
  | A_MCAS_sg_Error _ _            => A 
  | A_MCAS_sg _ _                  => A 
  | A_MCAS_sg_C _ B                => A_MCAS_sg _ (A_sg_from_sg_C _ B)
  | A_MCAS_sg_C_with_id _ B        => A_MCAS_sg _ (A_sg_from_sg_C_with_id _ B)
  | A_MCAS_sg_C_with_ann _ B       => A_MCAS_sg _ (A_sg_from_sg_C_with_ann _ B)
  | A_MCAS_sg_BC _ B               => A_MCAS_sg _ (A_sg_from_sg_BC _ B)
  | A_MCAS_sg_NC _ B               => A_MCAS_sg _ (A_sg_from_sg_NC _ B)
  | A_MCAS_sg_NC_with_id _ B       => A_MCAS_sg _ (A_sg_from_sg_NC_with_id _ B)
  | A_MCAS_sg_NC_with_ann _ B      => A_MCAS_sg _ (A_sg_from_sg_NC_with_ann _ B)
  | A_MCAS_sg_BNC _ B              => A_MCAS_sg _ (A_sg_from_sg_BNC _ B)
  | A_MCAS_sg_CS _ B               => A_MCAS_sg _ (A_sg_from_sg_CS _ B)
  | A_MCAS_sg_CS_with_id _ B       => A_MCAS_sg _ (A_sg_from_sg_CS_with_id _ B)
  | A_MCAS_sg_CS_with_ann _ B      => A_MCAS_sg _ (A_sg_from_sg_CS_with_ann _ B)
  | A_MCAS_sg_BCS _ B              => A_MCAS_sg _ (A_sg_from_sg_BCS _ B)
  | A_MCAS_sg_CI _ B               => A_MCAS_sg _ (A_sg_from_sg_CI _ B)
  | A_MCAS_sg_CI_with_id _ B       => A_MCAS_sg _ (A_sg_from_sg_CI_with_id _ B)
  | A_MCAS_sg_CI_with_ann _ B      => A_MCAS_sg _ (A_sg_from_sg_CI_with_ann _ B)
  | A_MCAS_sg_BCI _ B              => A_MCAS_sg _ (A_sg_from_sg_BCI _ B)
  | A_MCAS_sg_CNI _ B              => A_MCAS_sg _ (A_sg_from_sg_CNI _ B)
  | A_MCAS_sg_CNI_with_id _ B      => A_MCAS_sg _ (A_sg_from_sg_CNI_with_id _ B)
  | A_MCAS_sg_CNI_with_ann _ B     => A_MCAS_sg _ (A_sg_from_sg_CNI_with_ann _ B)
  | A_MCAS_sg_BCNI _ B             => A_MCAS_sg _ (A_sg_from_sg_BCNI _ B)
  | A_MCAS_sg_CK _ B               => A_MCAS_sg _ (A_sg_from_sg_CK _ B)
  | A_MCAS_sg_CK_with_id _ B       => A_MCAS_sg _ (A_sg_from_sg_CK_with_id _ B)
end.     

End AMCAS.

Section CAS.

Section Certificates.
    
Variables  (S : Type)
           (r : brel S)
           (b : binary_op S)
           (s : S)
           (f : S -> S)
           (id_d : @check_exists_id S).  

(* 1 *)   
Definition sg_certs_from_sg_NC_certs (sgS : @sg_NC_certificates S) : @sg_certificates S := 
{|
  sg_associative      := sg_NC_associative sgS 
; sg_congruence       := sg_NC_congruence sgS 
; sg_commutative_d    := match sg_NC_not_commutative sgS with
                         | Assert_Not_Commutative p => Certify_Not_Commutative p
                         end 
; sg_selective_d      := sg_NC_selective_d sgS    
; sg_is_left_d        := sg_NC_is_left_d sgS    
; sg_is_right_d       := sg_NC_is_right_d sgS    
; sg_idempotent_d     := sg_NC_idempotent_d sgS    
; sg_left_cancel_d    := sg_NC_left_cancel_d sgS    
; sg_right_cancel_d   := sg_NC_right_cancel_d sgS    
; sg_left_constant_d  := sg_NC_left_constant_d sgS
; sg_right_constant_d := sg_NC_right_constant_d sgS
; sg_anti_left_d      := sg_NC_anti_left_d sgS
; sg_anti_right_d     := sg_NC_anti_right_d sgS
|}. 

(* 2 *)
Definition sg_certs_from_sg_C_certs (sgS : @sg_C_certificates S) : @sg_certificates S := 
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Commutative 
; sg_selective_d      := sg_C_selective_d sgS    
; sg_is_left_d        := Certify_Not_Is_Left (cef_commutative_implies_not_is_left r b s f)
; sg_is_right_d       := Certify_Not_Is_Right (cef_commutative_implies_not_is_right r b s f)
; sg_idempotent_d     := sg_C_idempotent_d sgS    
; sg_left_cancel_d    := sg_C_cancel_d sgS    
; sg_right_cancel_d   := match sg_C_cancel_d sgS with
                         | Certify_Left_Cancellative => Certify_Right_Cancellative
                         | Certify_Not_Left_Cancellative (x, (y, z)) => Certify_Not_Right_Cancellative (x, (y, z))
                         end 
; sg_left_constant_d  := sg_C_constant_d sgS
; sg_right_constant_d := match sg_C_constant_d sgS with
                         | Certify_Left_Constant => Certify_Right_Constant
                         | Certify_Not_Left_Constant (x, (y, z)) => Certify_Not_Right_Constant (x, (y, z))
                         end 
; sg_anti_left_d      := sg_C_anti_left_d sgS
; sg_anti_right_d     := sg_C_anti_right_d sgS
|}.

(* 3 *)
Definition sg_C_certs_from_sg_CNI_certs (sgS : @sg_CNI_certificates S) : @sg_C_certificates S := 
match sg_CNI_not_idempotent sgS  with 
| Assert_Not_Idempotent s => 
{|
  sg_C_associative      := sg_CNI_associative sgS 
; sg_C_congruence       := sg_CNI_congruence sgS  
; sg_C_commutative      := sg_CNI_commutative sgS 
; sg_C_selective_d      := Certify_Not_Selective (s, s)
; sg_C_idempotent_d     := Certify_Not_Idempotent s
; sg_C_cancel_d         := sg_CNI_cancel_d sgS
; sg_C_constant_d       := sg_CNI_constant_d sgS
; sg_C_anti_left_d      := sg_CNI_anti_left_d sgS
; sg_C_anti_right_d     := sg_CNI_anti_right_d sgS
|}
end. 

(* 4 *) 
Definition sg_C_certs_from_sg_CI_certs (sgS : @sg_CI_certificates S): @sg_C_certificates S := 
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative 

; sg_C_idempotent_d     := Certify_Idempotent
; sg_C_selective_d      := match sg_CI_not_selective sgS with
                           | Assert_Not_Selective (s1, s2) => Certify_Not_Selective (s1, s2)
                           end
; sg_C_constant_d       := Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b s f) 
; sg_C_cancel_d         := match sg_CI_not_selective sgS with
                           | Assert_Not_Selective (s1, s2) =>
                               Certify_Not_Left_Cancellative (cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative  b s1 s2) 
                           end
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s) 
|}. 

(* 5 *)
Definition sg_C_certs_from_sg_CS_certs (sgS : @sg_CS_certificates S): @sg_C_certificates S := 
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative 
; sg_C_idempotent_d     := Certify_Idempotent
; sg_C_selective_d      := Certify_Selective 
; sg_C_constant_d       := Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b s f) 
; sg_C_cancel_d         := Certify_Not_Left_Cancellative (cef_selective_and_commutative_imply_not_left_cancellative  r b s f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s) 
|}. 

Definition sg_CNI_certs_from_sg_CK_certs (sgS : @sg_CK_certificates S) : @sg_CNI_certificates S := 
{|
  sg_CNI_associative      := Assert_Associative 
; sg_CNI_congruence       := Assert_Bop_Congruence 
; sg_CNI_commutative      := Assert_Commutative 

; sg_CNI_not_idempotent     := match id_d with
                               | Certify_Exists_Id i => Assert_Not_Idempotent (if r s i then f s else s)
                               | Certify_Not_Exists_Id => Assert_Not_Idempotent s
                               end                          
; sg_CNI_constant_d       := Certify_Not_Left_Constant 
                              (cef_left_cancellative_implies_not_left_constant s f) 
; sg_CNI_cancel_d         := Certify_Left_Cancellative 
; sg_CNI_anti_left_d      := sg_CK_anti_left_d sgS 
; sg_CNI_anti_right_d     := sg_CK_anti_right_d sgS
|}. 

(* DERIVED UPCASTS *)

(* two hops 
*) 
Definition sg_certs_from_sg_CI_certs (sgS : @sg_CI_certificates S) :  @sg_certificates S :=
  sg_certs_from_sg_C_certs (sg_C_certs_from_sg_CI_certs sgS).

Definition sg_certs_from_sg_CS_certs (sgS : @sg_CS_certificates S) : @sg_certificates S := 
  sg_certs_from_sg_C_certs (sg_C_certs_from_sg_CS_certs sgS).

Definition sg_certs_from_sg_CNI_certs (sgS : @sg_CNI_certificates S) : @sg_certificates S := 
  sg_certs_from_sg_C_certs (sg_C_certs_from_sg_CNI_certs sgS).

Definition sg_C_certs_from_sg_CK_certs (sgS : @sg_CK_certificates S) : @sg_C_certificates S := 
  sg_C_certs_from_sg_CNI_certs (sg_CNI_certs_from_sg_CK_certs sgS).

(* three hops *)
Definition sg_certs_from_sg_CK_certs (sgS : @sg_CK_certificates S) :  @sg_certificates S :=
  sg_certs_from_sg_C_certs (sg_C_certs_from_sg_CK_certs sgS).



End Certificates. 

Section Combinators.

(* 1 *)   
Definition sg_from_sg_NC {S : Type} (sgS : @sg_NC S) : @sg S :=
   {| 
     sg_eqv          := sg_NC_eqv sgS
   ; sg_bop          := sg_NC_bop sgS
   ; sg_exists_id_d  := Certify_Not_Exists_Id
   ; sg_exists_ann_d := Certify_Not_Exists_Ann 
   ; sg_certs        := sg_certs_from_sg_NC_certs _ (sg_NC_certs sgS)
   ; sg_ast          := sg_NC_ast sgS
   |}. 
  

(* 2 *)  
Definition sg_from_sg_C {S : Type} (sg_C : @sg_C S) : @sg S := 
   {| 
       sg_eqv    := sg_C_eqv sg_C
     ; sg_bop   := sg_C_bop sg_C
     ; sg_exists_id_d  := Certify_Not_Exists_Id
     ; sg_exists_ann_d := Certify_Not_Exists_Ann 
     ; sg_certs := sg_certs_from_sg_C_certs S
                    (eqv_eq (sg_C_eqv sg_C)) 
                    (sg_C_bop sg_C) 
                    (eqv_witness (sg_C_eqv sg_C))
                    (eqv_new (sg_C_eqv sg_C))                    
                    (sg_C_certs sg_C)
     ; sg_ast   := sg_C_ast sg_C
   |}.


(* 3 *)
Definition sg_C_from_sg_CNI {S : Type} (sgS : @sg_CNI S) : @sg_C S := 
   {| 
     sg_C_eqv          := sg_CNI_eqv sgS
   ; sg_C_bop          := sg_CNI_bop sgS
   ; sg_C_not_exists_id  := Assert_Not_Exists_Id
   ; sg_C_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_C_certs       := sg_C_certs_from_sg_CNI_certs _ (sg_CNI_certs sgS)
   ; sg_C_ast        := sg_CNI_ast sgS
   |}. 


(* 4 *)  
Definition sg_C_from_sg_CI {S : Type} (sg: @sg_CI S) : @sg_C S := 
   {| 
     sg_C_eqv   := sg_CI_eqv sg
   ; sg_C_bop   := sg_CI_bop sg
   ; sg_C_not_exists_id  := Assert_Not_Exists_Id
   ; sg_C_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs S
                     (eqv_eq (sg_CI_eqv sg))
                     (sg_CI_bop sg)                                               
                     (eqv_witness (sg_CI_eqv sg))
                     (eqv_new (sg_CI_eqv sg))
                     (sg_CI_certs sg)
   ; sg_C_ast   := sg_CI_ast sg
   |}. 

(* 5 *) 
Definition sg_C_from_sg_CS {S : Type} (sg : @sg_CS S) : @sg_C S := 
   {| 
     sg_C_eqv   := sg_CS_eqv sg
   ; sg_C_bop   := sg_CS_bop sg
   ; sg_C_not_exists_id  := Assert_Not_Exists_Id
   ; sg_C_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_C_certs := sg_C_certs_from_sg_CS_certs S
                     (eqv_eq (sg_CS_eqv sg))
                     (sg_CS_bop sg)                                               
                     (eqv_witness (sg_CS_eqv sg))
                     (eqv_new (sg_CS_eqv sg))
                     (sg_CS_certs sg)
   ; sg_C_ast   := sg_CS_ast sg
   |}. 

(* 6 *)                                                     
Definition sg_CNI_from_sg_CK {S : Type} (sg : @sg_CK S) : @sg_CNI S := 
   {| 
     sg_CNI_eqv   := sg_CK_eqv sg
   ; sg_CNI_bop   := sg_CK_bop sg
   ; sg_CNI_not_exists_id  := Assert_Not_Exists_Id
   ; sg_CNI_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_CNI_certs := sg_CNI_certs_from_sg_CK_certs S
                      (eqv_eq (sg_CK_eqv sg))                                                   
                      (eqv_witness (sg_CK_eqv sg))
                      (eqv_new (sg_CK_eqv sg))
                      Certify_Not_Exists_Id
                      (sg_CK_certs sg)
   ; sg_CNI_ast   := sg_CK_ast sg
   |}.


(* 1.id *)   
Definition sg_from_sg_NC_with_id {S : Type} (sgS : @sg_NC_with_id S) : @sg S :=
match sg_NC_wi_exists_id sgS with
| Assert_Exists_Id id =>
   {| 
     sg_eqv          := sg_NC_wi_eqv sgS
   ; sg_bop          := sg_NC_wi_bop sgS
   ; sg_exists_id_d  := Certify_Exists_Id id 
   ; sg_exists_ann_d := Certify_Not_Exists_Ann 
   ; sg_certs        := sg_certs_from_sg_NC_certs _ (sg_NC_wi_certs sgS)
   ; sg_ast          := sg_NC_wi_ast sgS
   |}
end. 
  

(* 2.id *)  
Definition sg_from_sg_C_with_id {S : Type} (A : @sg_C_with_id S) : @sg S := 
match sg_C_wi_exists_id A with
| Assert_Exists_Id id =>
  {| 
       sg_eqv    := sg_C_wi_eqv A
     ; sg_bop   := sg_C_wi_bop A
     ; sg_exists_id_d  := Certify_Exists_Id id 
     ; sg_exists_ann_d := Certify_Not_Exists_Ann 
     ; sg_certs := sg_certs_from_sg_C_certs S
                    (eqv_eq (sg_C_wi_eqv A)) 
                    (sg_C_wi_bop A) 
                    (eqv_witness (sg_C_wi_eqv A))
                    (eqv_new (sg_C_wi_eqv A))                    
                    (sg_C_wi_certs A)
     ; sg_ast   := sg_C_wi_ast A
  |}
end.


(* 3.id *)
Definition sg_C_with_id_from_sg_CNI_with_id {S : Type} (sgS : @sg_CNI_with_id S) : @sg_C_with_id S := 
  {| 
     sg_C_wi_eqv            := sg_CNI_wi_eqv sgS
   ; sg_C_wi_bop            := sg_CNI_wi_bop sgS
   ; sg_C_wi_exists_id      := sg_CNI_wi_exists_id sgS
   ; sg_C_wi_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_C_wi_certs          := sg_C_certs_from_sg_CNI_certs _ (sg_CNI_wi_certs sgS)
   ; sg_C_wi_ast            := sg_CNI_wi_ast sgS
  |}. 


(* 4.id *)  
Definition sg_C_with_id_from_sg_CI_with_id {S : Type} (sg: @sg_CI_with_id S) : @sg_C_with_id S := 
   {| 
     sg_C_wi_eqv   := sg_CI_wi_eqv sg
   ; sg_C_wi_bop   := sg_CI_wi_bop sg
   ; sg_C_wi_exists_id  := sg_CI_wi_exists_id sg
   ; sg_C_wi_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_C_wi_certs := sg_C_certs_from_sg_CI_certs S
                     (eqv_eq (sg_CI_wi_eqv sg))
                     (sg_CI_wi_bop sg)                                               
                     (eqv_witness (sg_CI_wi_eqv sg))
                     (eqv_new (sg_CI_wi_eqv sg))
                     (sg_CI_wi_certs sg)
   ; sg_C_wi_ast   := sg_CI_wi_ast sg
   |}. 

(* 5.id *) 
Definition sg_C_with_id_from_sg_CS_with_id {S : Type} (sg : @sg_CS_with_id S) : @sg_C_with_id S := 
   {| 
     sg_C_wi_eqv   := sg_CS_wi_eqv sg
   ; sg_C_wi_bop   := sg_CS_wi_bop sg
   ; sg_C_wi_exists_id  := sg_CS_wi_exists_id sg
   ; sg_C_wi_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_C_wi_certs := sg_C_certs_from_sg_CS_certs S
                     (eqv_eq (sg_CS_wi_eqv sg))
                     (sg_CS_wi_bop sg)                                               
                     (eqv_witness (sg_CS_wi_eqv sg))
                     (eqv_new (sg_CS_wi_eqv sg))
                     (sg_CS_wi_certs sg)
   ; sg_C_wi_ast   := sg_CS_wi_ast sg
   |}. 

(* 6.id *)                                                     
Definition sg_CNI_with_id_from_sg_CK_with_id {S : Type} (sg : @sg_CK_with_id S) : @sg_CNI_with_id S :=
match sg_CK_wi_exists_id sg with
| Assert_Exists_Id id =>     
   {| 
     sg_CNI_wi_eqv   := sg_CK_wi_eqv sg
   ; sg_CNI_wi_bop   := sg_CK_wi_bop sg
   ; sg_CNI_wi_exists_id  := Assert_Exists_Id id
   ; sg_CNI_wi_not_exists_ann := Assert_Not_Exists_Ann 
   ; sg_CNI_wi_certs := sg_CNI_certs_from_sg_CK_certs S
                      (eqv_eq (sg_CK_wi_eqv sg))                                                   
                      (eqv_witness (sg_CK_wi_eqv sg))
                      (eqv_new (sg_CK_wi_eqv sg))
                      (Certify_Exists_Id id)
                      (sg_CK_wi_certs sg)
   ; sg_CNI_wi_ast   := sg_CK_wi_ast sg
   |}
end.

(* 1.ann *)   
Definition sg_from_sg_NC_with_ann {S : Type} (sgS : @sg_NC_with_ann S) : @sg S :=
match sg_NC_wa_exists_ann sgS with
| Assert_Exists_Ann ann =>
   {| 
     sg_eqv          := sg_NC_wa_eqv sgS
   ; sg_bop          := sg_NC_wa_bop sgS
   ; sg_exists_id_d  := Certify_Not_Exists_Id
   ; sg_exists_ann_d := Certify_Exists_Ann ann
   ; sg_certs        := sg_certs_from_sg_NC_certs _ (sg_NC_wa_certs sgS)
   ; sg_ast          := sg_NC_wa_ast sgS
   |}
end. 
  

(* 2.ann *)  
Definition sg_from_sg_C_with_ann {S : Type} (A : @sg_C_with_ann S) : @sg S := 
match sg_C_wa_exists_ann A with
| Assert_Exists_Ann ann =>
  {| 
       sg_eqv    := sg_C_wa_eqv A
     ; sg_bop   := sg_C_wa_bop A
     ; sg_exists_id_d  := Certify_Not_Exists_Id
     ; sg_exists_ann_d := Certify_Exists_Ann ann
     ; sg_certs := sg_certs_from_sg_C_certs S
                    (eqv_eq (sg_C_wa_eqv A)) 
                    (sg_C_wa_bop A) 
                    (eqv_witness (sg_C_wa_eqv A))
                    (eqv_new (sg_C_wa_eqv A))                    
                    (sg_C_wa_certs A)
     ; sg_ast   := sg_C_wa_ast A
  |}
end.


(* 3.ann *)
Definition sg_C_with_ann_from_sg_CNI_with_ann {S : Type} (sgS : @sg_CNI_with_ann S) : @sg_C_with_ann S := 
  {| 
     sg_C_wa_eqv            := sg_CNI_wa_eqv sgS
   ; sg_C_wa_bop            := sg_CNI_wa_bop sgS
   ; sg_C_wa_not_exists_id  := Assert_Not_Exists_Id
   ; sg_C_wa_exists_ann     := sg_CNI_wa_exists_ann sgS
   ; sg_C_wa_certs          := sg_C_certs_from_sg_CNI_certs _ (sg_CNI_wa_certs sgS)
   ; sg_C_wa_ast            := sg_CNI_wa_ast sgS
  |}. 


(* 4.ann *)  
Definition sg_C_with_ann_from_sg_CI_with_ann {S : Type} (sg: @sg_CI_with_ann S) : @sg_C_with_ann S := 
   {| 
     sg_C_wa_eqv            := sg_CI_wa_eqv sg
   ; sg_C_wa_bop            := sg_CI_wa_bop sg
   ; sg_C_wa_not_exists_id  := Assert_Not_Exists_Id 
   ; sg_C_wa_exists_ann     := sg_CI_wa_exists_ann sg
   ; sg_C_wa_certs          := sg_C_certs_from_sg_CI_certs S
                                (eqv_eq (sg_CI_wa_eqv sg))
                                (sg_CI_wa_bop sg)                                               
                                (eqv_witness (sg_CI_wa_eqv sg))
                                (eqv_new (sg_CI_wa_eqv sg))
                                (sg_CI_wa_certs sg)
   ; sg_C_wa_ast            := sg_CI_wa_ast sg
   |}. 

(* 5.ann *) 
Definition sg_C_with_ann_from_sg_CS_with_ann {S : Type} (sg : @sg_CS_with_ann S) : @sg_C_with_ann S := 
   {| 
     sg_C_wa_eqv           := sg_CS_wa_eqv sg
   ; sg_C_wa_bop           := sg_CS_wa_bop sg
   ; sg_C_wa_not_exists_id := Assert_Not_Exists_Id
   ; sg_C_wa_exists_ann    := sg_CS_wa_exists_ann sg
   ; sg_C_wa_certs         := sg_C_certs_from_sg_CS_certs S
                               (eqv_eq (sg_CS_wa_eqv sg))
                               (sg_CS_wa_bop sg)                                               
                               (eqv_witness (sg_CS_wa_eqv sg))
                               (eqv_new (sg_CS_wa_eqv sg))
                               (sg_CS_wa_certs sg)
   ; sg_C_wa_ast           := sg_CS_wa_ast sg
   |}. 



(* 1.B *)   
Definition sg_from_sg_BNC {S : Type} (sgS : @sg_BNC S) : @sg S :=
match sg_BNC_exists_id sgS, sg_BNC_exists_ann sgS with
| Assert_Exists_Id id, Assert_Exists_Ann ann =>
   {| 
     sg_eqv          := sg_BNC_eqv sgS
   ; sg_bop          := sg_BNC_bop sgS
   ; sg_exists_id_d  := Certify_Exists_Id id
   ; sg_exists_ann_d := Certify_Exists_Ann ann 
   ; sg_certs        := sg_certs_from_sg_NC_certs _ (sg_BNC_certs sgS)
   ; sg_ast          := sg_BNC_ast sgS
   |}
end. 
  

(* 2.B *)  
Definition sg_from_sg_BC {S : Type} (A : @sg_BC S) : @sg S :=
match sg_BC_exists_id A, sg_BC_exists_ann A with
| Assert_Exists_Id id, Assert_Exists_Ann ann =>
   {| 
       sg_eqv          := sg_BC_eqv A
     ; sg_bop          := sg_BC_bop A
     ; sg_exists_id_d  := Certify_Exists_Id id
     ; sg_exists_ann_d := Certify_Exists_Ann ann 
     ; sg_certs        := sg_certs_from_sg_C_certs S
                             (eqv_eq (sg_BC_eqv A)) 
                             (sg_BC_bop A) 
                             (eqv_witness (sg_BC_eqv A))
                             (eqv_new (sg_BC_eqv A))                    
                             (sg_BC_certs A)
     ; sg_ast          := sg_BC_ast A
   |}
end.


(* 3.B *)
Definition sg_BC_from_sg_BCNI {S : Type} (sgS : @sg_BCNI S) : @sg_BC S := 
   {| 
     sg_BC_eqv        := sg_BCNI_eqv sgS
   ; sg_BC_bop        := sg_BCNI_bop sgS
   ; sg_BC_exists_id  := sg_BCNI_exists_id sgS
   ; sg_BC_exists_ann := sg_BCNI_exists_ann sgS
   ; sg_BC_certs      := sg_C_certs_from_sg_CNI_certs _ (sg_BCNI_certs sgS)
   ; sg_BC_ast        := sg_BCNI_ast sgS
   |}. 


(* 4.B *)  
Definition sg_BC_from_sg_BCI {S : Type} (sg: @sg_BCI S) : @sg_BC S := 
   {| 
     sg_BC_eqv        := sg_BCI_eqv sg
   ; sg_BC_bop        := sg_BCI_bop sg
   ; sg_BC_exists_id  := sg_BCI_exists_id sg
   ; sg_BC_exists_ann := sg_BCI_exists_ann sg
   ; sg_BC_certs      := sg_C_certs_from_sg_CI_certs S
                          (eqv_eq (sg_BCI_eqv sg))
                          (sg_BCI_bop sg)                                               
                          (eqv_witness (sg_BCI_eqv sg))
                          (eqv_new (sg_BCI_eqv sg))
                          (sg_BCI_certs sg)
   ; sg_BC_ast         := sg_BCI_ast sg
   |}. 

(* 5.B *) 
Definition sg_BC_from_sg_BCS {S : Type} (sg : @sg_BCS S) : @sg_BC S := 
   {| 
     sg_BC_eqv        := sg_BCS_eqv sg
   ; sg_BC_bop        := sg_BCS_bop sg
   ; sg_BC_exists_id  := sg_BCS_exists_id sg
   ; sg_BC_exists_ann := sg_BCS_exists_ann sg
   ; sg_BC_certs      := sg_C_certs_from_sg_CS_certs S
                          (eqv_eq (sg_BCS_eqv sg))
                          (sg_BCS_bop sg)                                               
                          (eqv_witness (sg_BCS_eqv sg))
                          (eqv_new (sg_BCS_eqv sg))
                          (sg_BCS_certs sg)
   ; sg_BC_ast        := sg_BCS_ast sg
   |}. 


(* DERIVED UPCASTS *)

(* 7 *) 
Definition sg_from_sg_CI {S : Type} (sgS : @sg_CI S) : @sg S := 
  sg_from_sg_C (sg_C_from_sg_CI sgS). 

(* 8 *)
Definition sg_from_sg_CS {S : Type} (sgS : @sg_CS S) : @sg S := 
  sg_from_sg_C (sg_C_from_sg_CS sgS).

(* 9 *) 
Definition sg_from_sg_CNI {S : Type} (sgS : @sg_CNI S) : @sg S := 
  sg_from_sg_C (sg_C_from_sg_CNI sgS). 

(* 10 *) 
Definition sg_from_sg_CK {S : Type} (sgS : @sg_CK S) : @sg S := 
   sg_from_sg_CNI (sg_CNI_from_sg_CK sgS).  


(* 7.id *) 
Definition sg_from_sg_CI_with_id {S : Type} (sgS : @sg_CI_with_id S) : @sg S := 
  sg_from_sg_C_with_id (sg_C_with_id_from_sg_CI_with_id sgS). 

(* 8.id *)
Definition sg_from_sg_CS_with_id {S : Type} (sgS : @sg_CS_with_id S) : @sg S := 
  sg_from_sg_C_with_id (sg_C_with_id_from_sg_CS_with_id sgS).

(* 9.id *) 
Definition sg_from_sg_CNI_with_id {S : Type} (sgS : @sg_CNI_with_id S) : @sg S := 
  sg_from_sg_C_with_id (sg_C_with_id_from_sg_CNI_with_id sgS). 

(* 10.id *) 
Definition sg_from_sg_CK_with_id {S : Type} (sgS : @sg_CK_with_id S) : @sg S := 
   sg_from_sg_CNI_with_id (sg_CNI_with_id_from_sg_CK_with_id sgS).  


(* 7.ann *) 
Definition sg_from_sg_CI_with_ann {S : Type} (sgS : @sg_CI_with_ann S) : @sg S := 
  sg_from_sg_C_with_ann (sg_C_with_ann_from_sg_CI_with_ann sgS). 

(* 8.ann *)
Definition sg_from_sg_CS_with_ann {S : Type} (sgS : @sg_CS_with_ann S) : @sg S := 
  sg_from_sg_C_with_ann (sg_C_with_ann_from_sg_CS_with_ann sgS).

(* 9.ann *) 
Definition sg_from_sg_CNI_with_ann {S : Type} (sgS : @sg_CNI_with_ann S) : @sg S := 
  sg_from_sg_C_with_ann (sg_C_with_ann_from_sg_CNI_with_ann sgS). 

(* 7.B *) 
Definition sg_from_sg_BCI {S : Type} (sgS : @sg_BCI S) : @sg S := 
  sg_from_sg_BC (sg_BC_from_sg_BCI sgS). 

(* 8.B *)
Definition sg_from_sg_BCS {S : Type} (sgS : @sg_BCS S) : @sg S := 
  sg_from_sg_BC (sg_BC_from_sg_BCS sgS).

(* 9.B *) 
Definition sg_from_sg_BCNI {S : Type} (sgS : @sg_BCNI S) : @sg S := 
  sg_from_sg_BC (sg_BC_from_sg_BCNI sgS). 


End Combinators. 
End CAS.


Section MCAS.

Definition sg_certs_mcas_cast_up
           (S : Type)
           (eq : brel S)
           (s : S)
           (f : S -> S)
           (bop : binary_op S)
           (id_d : @check_exists_id S)
           (A : @sg_certs_mcas S) : @sg_certs_mcas S :=
match A with
  | MCAS_Cert_sg_Error _ => A
  | MCAS_Cert_sg _       => A
  | MCAS_Cert_sg_C B     => MCAS_Cert_sg (sg_certs_from_sg_C_certs _ eq bop s f B)
  | MCAS_Cert_sg_NC B    => MCAS_Cert_sg (sg_certs_from_sg_NC_certs _ B) 
  | MCAS_Cert_sg_CS B    => MCAS_Cert_sg (sg_certs_from_sg_CS_certs _ eq bop s f B) 
  | MCAS_Cert_sg_CI B    => MCAS_Cert_sg (sg_certs_from_sg_CI_certs _ eq bop s f B)  
  | MCAS_Cert_sg_CNI B   => MCAS_Cert_sg (sg_certs_from_sg_CNI_certs _ eq bop s f B) 
  | MCAS_Cert_sg_CK B    => MCAS_Cert_sg (sg_certs_from_sg_CK_certs _ eq bop s f id_d B)
end.


Definition sg_mcas_cast_up (S : Type) (A : @sg_mcas S) : @sg_mcas S :=
match A with
  | MCAS_sg_Error _            => A 
  | MCAS_sg _                  => A 
  | MCAS_sg_C B                => MCAS_sg (sg_from_sg_C B)
  | MCAS_sg_C_with_id B        => MCAS_sg (sg_from_sg_C_with_id B)
  | MCAS_sg_C_with_ann B       => MCAS_sg (sg_from_sg_C_with_ann B)
  | MCAS_sg_BC B               => MCAS_sg (sg_from_sg_BC B)
  | MCAS_sg_NC B               => MCAS_sg (sg_from_sg_NC B)
  | MCAS_sg_NC_with_id B       => MCAS_sg (sg_from_sg_NC_with_id B)
  | MCAS_sg_NC_with_ann B      => MCAS_sg (sg_from_sg_NC_with_ann B)
  | MCAS_sg_BNC B              => MCAS_sg (sg_from_sg_BNC B)
  | MCAS_sg_CS B               => MCAS_sg (sg_from_sg_CS B)
  | MCAS_sg_CS_with_id B       => MCAS_sg (sg_from_sg_CS_with_id B)
  | MCAS_sg_CS_with_ann B      => MCAS_sg (sg_from_sg_CS_with_ann B)
  | MCAS_sg_BCS B              => MCAS_sg (sg_from_sg_BCS B)
  | MCAS_sg_CI B               => MCAS_sg (sg_from_sg_CI B)
  | MCAS_sg_CI_with_id B       => MCAS_sg (sg_from_sg_CI_with_id B)
  | MCAS_sg_CI_with_ann B      => MCAS_sg (sg_from_sg_CI_with_ann B)
  | MCAS_sg_BCI B              => MCAS_sg (sg_from_sg_BCI B)
  | MCAS_sg_CNI B              => MCAS_sg (sg_from_sg_CNI B)
  | MCAS_sg_CNI_with_id B      => MCAS_sg (sg_from_sg_CNI_with_id B)
  | MCAS_sg_CNI_with_ann B     => MCAS_sg (sg_from_sg_CNI_with_ann B)
  | MCAS_sg_BCNI B             => MCAS_sg (sg_from_sg_BCNI B)
  | MCAS_sg_CK B               => MCAS_sg (sg_from_sg_CK B)
  | MCAS_sg_CK_with_id B       => MCAS_sg (sg_from_sg_CK_with_id B)
end.     

End MCAS.


Section Verify.

Section Certificates.

  Variables (S : Type)
            (r : brel S)
            (b : binary_op S)
            (s : S)
            (f : S -> S)
            (nt : brel_not_trivial S r f)
            (eqvS : eqv_proofs S r)
            (id_d : bop_exists_id_decidable S r b). 


(* 1 *)  
Lemma correct_sg_certs_from_sg_NC_certs (sgS : sg_NC_proofs S r b) : 
       sg_certs_from_sg_NC_certs S (P2C_sg_NC S r b sgS)
       = 
       P2C_sg S r b (A_sg_proofs_from_sg_NC_proofs S r b sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_certs_from_sg_NC_certs, A_sg_proofs_from_sg_NC_proofs, P2C_sg, P2C_sg_NC; simpl.
       reflexivity.
Defined. 

(* 2 *)  
Lemma correct_sg_certs_from_sg_C_certs (sgS : sg_C_proofs S r b) : 
       sg_certs_from_sg_C_certs S r b s f (P2C_sg_C S r b sgS)
       = 
       P2C_sg S r b (A_sg_proofs_from_sg_C_proofs S r b s f nt eqvS sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_certs_from_sg_C_certs, A_sg_proofs_from_sg_C_proofs, P2C_sg, P2C_sg_C; simpl.
       destruct A_sg_C_cancel_d as [ lcanS | [[x [y z]] nlcanS]];
       destruct A_sg_C_constant_d as [ lconS | [[u [v w]] nlconS] ]; simpl; 
       reflexivity.
Defined. 


(* 3 *) 
Lemma correct_sg_C_certs_from_sg_CNI_certs (sgS : sg_CNI_proofs S r b) : 
       sg_C_certs_from_sg_CNI_certs S (P2C_sg_CNI S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CNI_proofs S r b sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CNI_certs, A_sg_C_proofs_from_sg_CNI_proofs, P2C_sg_C, P2C_sg_CNI. simpl. 
       destruct A_sg_CNI_not_idempotent as [s1 A]. 
       simpl. reflexivity.        
Defined.

(* 4 *) 
Lemma correct_sg_C_certs_from_sg_CI_certs (sgS : sg_CI_proofs S r b) : 
       sg_C_certs_from_sg_CI_certs S r b s f (P2C_sg_CI S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CI_proofs S r b s f nt eqvS sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CI_certs, A_sg_C_proofs_from_sg_CI_proofs, P2C_sg_C, P2C_sg_CI. simpl. 
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]. 
       simpl. reflexivity.        
Defined.

(* 5 *) 
Lemma correct_sg_C_certs_from_sg_CS_certs (sgS : sg_CS_proofs S r b) : 
       sg_C_certs_from_sg_CS_certs S r b s f (P2C_sg_CS S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CS_proofs S r b s f nt eqvS sgS). 
Proof.  destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CS_certs, A_sg_C_proofs_from_sg_CS_proofs, P2C_sg_C, P2C_sg_CS; 
       simpl. reflexivity.        
Defined.

(* 6 *) 
Lemma correct_sg_CNI_certs_from_sg_CK_certs (sgS : sg_CK_proofs S r b) :  
       sg_CNI_certs_from_sg_CK_certs S r s f (p2c_exists_id_check _ _ _ id_d) (P2C_sg_CK S r b sgS)
       = 
       P2C_sg_CNI S r b (A_sg_CNI_proofs_from_sg_CK_proofs S r b s f nt eqvS id_d sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_CNI_certs_from_sg_CK_certs, A_sg_CNI_proofs_from_sg_CK_proofs, P2C_sg_CNI, P2C_sg_CK; simpl. 
       destruct id_d as [ [i Pi] | no_id ]; simpl. unfold cef_cancellative_and_exists_id_imply_not_idempotent. 
          reflexivity.                            
          reflexivity.        
Defined. 

End Certificates.

Section Combinators.


(* 1 *)   
Theorem correct_sg_from_sg_NC (S : Type) (P : A_sg_NC S) : 
         sg_from_sg_NC (A2C_sg_NC S P) = A2C_sg S (A_sg_from_sg_NC S P). 
Proof. destruct P.
       destruct A_sg_NC_eqv.        
       unfold sg_from_sg_NC, A_sg_from_sg_NC, A2C_sg_NC, A2C_sg; simpl.
       rewrite <-correct_sg_certs_from_sg_NC_certs; auto.        
Qed. 
  

(* 2 *)   
Theorem correct_sg_from_sg_C (S : Type) (P : A_sg_C S) : 
         sg_from_sg_C (A2C_sg_C S P) = A2C_sg S (A_sg_from_sg_C S P). 
Proof. destruct P.
       unfold sg_from_sg_C, A_sg_from_sg_C, A2C_sg_C, A2C_sg; simpl.
       destruct A_sg_C_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Qed. 

(* 3 *) 
Theorem correct_sg_C_from_sg_CNI (S : Type) (P : A_sg_CNI S) : 
         sg_C_from_sg_CNI (A2C_sg_CNI S P) = A2C_sg_C S (A_sg_C_from_sg_CNI S P). 
Proof. unfold sg_C_from_sg_CNI, A_sg_C_from_sg_CNI, A2C_sg_CNI, A2C_sg_C; simpl.
       destruct P. destruct A_sg_CNI_eqv. 
       rewrite <- correct_sg_C_certs_from_sg_CNI_certs; auto. 
Qed.

(* 4 *) 
Theorem correct_sg_C_from_sg_CI (S : Type) (P : A_sg_CI S) : 
         sg_C_from_sg_CI (A2C_sg_CI S P) = A2C_sg_C S (A_sg_C_from_sg_CI S P). 
Proof. unfold sg_C_from_sg_CI, A_sg_C_from_sg_CI, A2C_sg_CI, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
       
Qed.

(* 5 *) 
Theorem correct_sg_C_from_sg_CS (S : Type) (P : A_sg_CS S) : 
         sg_C_from_sg_CS (A2C_sg_CS S P) = A2C_sg_C S (A_sg_C_from_sg_CS S P). 
Proof. unfold sg_C_from_sg_CS, A_sg_C_from_sg_CS, A2C_sg_CS, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Qed.

(* 6 *) 
Theorem correct_sg_CNI_from_sg_CK (S : Type) (P : A_sg_CK S) : 
  sg_CNI_from_sg_CK  (A2C_sg_CK S P)
  =
  A2C_sg_CNI S (A_sg_CNI_from_sg_CK S P). 
Proof. unfold sg_CNI_from_sg_CK, A_sg_CNI_from_sg_CK, A2C_sg_CK, A2C_sg_CNI; simpl. 
       rewrite <- correct_sg_CNI_certs_from_sg_CK_certs; auto. 
Qed. 



(* 1.id *)   
Theorem correct_sg_from_sg_NC_with_id (S : Type) (P : A_sg_NC_with_id S) : 
         sg_from_sg_NC_with_id (A2C_sg_NC_with_id S P) = A2C_sg S (A_sg_from_sg_NC_with_id S P). 
Proof. destruct P. destruct A_sg_NC_wi_eqv. 
       unfold sg_from_sg_NC_with_id, A_sg_from_sg_NC_with_id, A2C_sg_NC_with_id, A2C_sg; simpl.
       rewrite <-correct_sg_certs_from_sg_NC_certs; auto.        
Qed. 
  

(* 2.id *)   
Theorem correct_sg_from_sg_C_with_id (S : Type) (P : A_sg_C_with_id S) : 
         sg_from_sg_C_with_id (A2C_sg_C_with_id S P) = A2C_sg S (A_sg_from_sg_C_with_id S P). 
Proof. destruct P.
       unfold sg_from_sg_C_with_id, A_sg_from_sg_C_with_id, A2C_sg_C_with_id, A2C_sg; simpl.
       destruct A_sg_C_wi_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Qed. 

(* 3.id *) 
Theorem correct_sg_C_with_id_from_sg_CNI_with_id (S : Type) (P : A_sg_CNI_with_id S) : 
         sg_C_with_id_from_sg_CNI_with_id (A2C_sg_CNI_with_id S P) = A2C_sg_C_with_id S (A_sg_C_with_id_from_sg_CNI_with_id S P). 
Proof. unfold sg_C_with_id_from_sg_CNI_with_id, A_sg_C_with_id_from_sg_CNI_with_id, A2C_sg_CNI_with_id, A2C_sg_C_with_id; simpl.
       destruct P. destruct A_sg_CNI_wi_eqv. 
       rewrite <- correct_sg_C_certs_from_sg_CNI_certs; auto. 
Qed.

(* 4.id *) 
Theorem correct_sg_C_with_id_from_sg_CI_with_id (S : Type) (P : A_sg_CI_with_id S) : 
         sg_C_with_id_from_sg_CI_with_id (A2C_sg_CI_with_id S P) = A2C_sg_C_with_id S (A_sg_C_with_id_from_sg_CI_with_id S P). 
Proof. unfold sg_C_with_id_from_sg_CI_with_id, A_sg_C_with_id_from_sg_CI_with_id, A2C_sg_CI_with_id, A2C_sg_C_with_id; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Qed.

(* 5.id *) 
Theorem correct_sg_C_with_id_from_sg_CS_with_id (S : Type) (P : A_sg_CS_with_id S) : 
         sg_C_with_id_from_sg_CS_with_id (A2C_sg_CS_with_id S P) = A2C_sg_C_with_id S (A_sg_C_with_id_from_sg_CS_with_id S P). 
Proof. unfold sg_C_with_id_from_sg_CS_with_id, A_sg_C_with_id_from_sg_CS_with_id, A2C_sg_CS_with_id, A2C_sg_C_with_id; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Qed.

(* 6.id *) 
Theorem correct_sg_CNI_with_id_from_sg_CK_with_id (S : Type) (P : A_sg_CK_with_id S) : 
  sg_CNI_with_id_from_sg_CK_with_id  (A2C_sg_CK_with_id S P)
  =
  A2C_sg_CNI_with_id S (A_sg_CNI_with_id_from_sg_CK_with_id S P). 
Proof. unfold sg_CNI_with_id_from_sg_CK_with_id, A_sg_CNI_with_id_from_sg_CK_with_id, A2C_sg_CK_with_id, A2C_sg_CNI_with_id; simpl. 
       rewrite <- correct_sg_CNI_certs_from_sg_CK_certs; auto. 
Qed.


(* 1.ann *)   
Theorem correct_sg_from_sg_NC_with_ann (S : Type) (P : A_sg_NC_with_ann S) : 
         sg_from_sg_NC_with_ann (A2C_sg_NC_with_ann S P) = A2C_sg S (A_sg_from_sg_NC_with_ann S P). 
Proof. destruct P. destruct A_sg_NC_wa_eqv. 
       unfold sg_from_sg_NC_with_ann, A_sg_from_sg_NC_with_ann, A2C_sg_NC_with_ann, A2C_sg; simpl.
       rewrite <-correct_sg_certs_from_sg_NC_certs; auto.        
Qed. 
  

(* 2.ann *)   
Theorem correct_sg_from_sg_C_with_ann (S : Type) (P : A_sg_C_with_ann S) : 
         sg_from_sg_C_with_ann (A2C_sg_C_with_ann S P) = A2C_sg S (A_sg_from_sg_C_with_ann S P). 
Proof. destruct P.
       unfold sg_from_sg_C_with_ann, A_sg_from_sg_C_with_ann, A2C_sg_C_with_ann, A2C_sg; simpl.
       destruct A_sg_C_wa_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Qed. 

(* 3.ann *) 
Theorem correct_sg_C_with_ann_from_sg_CNI_with_ann (S : Type) (P : A_sg_CNI_with_ann S) : 
         sg_C_with_ann_from_sg_CNI_with_ann (A2C_sg_CNI_with_ann S P) = A2C_sg_C_with_ann S (A_sg_C_with_ann_from_sg_CNI_with_ann S P). 
Proof. unfold sg_C_with_ann_from_sg_CNI_with_ann, A_sg_C_with_ann_from_sg_CNI_with_ann, A2C_sg_CNI_with_ann, A2C_sg_C_with_ann; simpl.
       destruct P. destruct A_sg_CNI_wa_eqv. 
       rewrite <- correct_sg_C_certs_from_sg_CNI_certs; auto. 
Qed.

(* 4.ann *) 
Theorem correct_sg_C_with_ann_from_sg_CI_with_ann (S : Type) (P : A_sg_CI_with_ann S) : 
         sg_C_with_ann_from_sg_CI_with_ann (A2C_sg_CI_with_ann S P) = A2C_sg_C_with_ann S (A_sg_C_with_ann_from_sg_CI_with_ann S P). 
Proof. unfold sg_C_with_ann_from_sg_CI_with_ann, A_sg_C_with_ann_from_sg_CI_with_ann, A2C_sg_CI_with_ann, A2C_sg_C_with_ann; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Qed.

(* 5.ann *) 
Theorem correct_sg_C_with_ann_from_sg_CS_with_ann (S : Type) (P : A_sg_CS_with_ann S) : 
         sg_C_with_ann_from_sg_CS_with_ann (A2C_sg_CS_with_ann S P) = A2C_sg_C_with_ann S (A_sg_C_with_ann_from_sg_CS_with_ann S P). 
Proof. unfold sg_C_with_ann_from_sg_CS_with_ann, A_sg_C_with_ann_from_sg_CS_with_ann, A2C_sg_CS_with_ann, A2C_sg_C_with_ann; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Qed.



(* 1.B *)   
Theorem correct_sg_from_sg_BNC (S : Type) (P : A_sg_BNC S) : 
         sg_from_sg_BNC (A2C_sg_BNC S P) = A2C_sg S (A_sg_from_sg_BNC S P). 
Proof. destruct P.
       destruct A_sg_BNC_eqv.        
       unfold sg_from_sg_BNC, A_sg_from_sg_BNC, A2C_sg_BNC, A2C_sg; simpl.
       rewrite <-correct_sg_certs_from_sg_NC_certs; auto.        
Qed. 
  

(* 2.B *)   
Theorem correct_sg_from_sg_BC (S : Type) (P : A_sg_BC S) : 
         sg_from_sg_BC (A2C_sg_BC S P) = A2C_sg S (A_sg_from_sg_BC S P). 
Proof. destruct P.
       unfold sg_from_sg_BC, A_sg_from_sg_BC, A2C_sg_BC, A2C_sg; simpl.
       destruct A_sg_BC_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Qed. 

(* 3.B *) 
Theorem correct_sg_BC_from_sg_BCNI (S : Type) (P : A_sg_BCNI S) : 
         sg_BC_from_sg_BCNI (A2C_sg_BCNI S P) = A2C_sg_BC S (A_sg_BC_from_sg_BCNI S P). 
Proof. unfold sg_BC_from_sg_BCNI, A_sg_BC_from_sg_BCNI, A2C_sg_BCNI, A2C_sg_BC; simpl.
       destruct P. destruct A_sg_BCNI_eqv. 
       rewrite <- correct_sg_C_certs_from_sg_CNI_certs; auto. 
Qed.

(* 4.B *) 
Theorem correct_sg_BC_from_sg_BCI (S : Type) (P : A_sg_BCI S) : 
         sg_BC_from_sg_BCI (A2C_sg_BCI S P) = A2C_sg_BC S (A_sg_BC_from_sg_BCI S P). 
Proof. unfold sg_BC_from_sg_BCI, A_sg_BC_from_sg_BCI, A2C_sg_BCI, A2C_sg_BC; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
       
Qed.

(* 5.B *) 
Theorem correct_sg_BC_from_sg_BCS (S : Type) (P : A_sg_BCS S) : 
         sg_BC_from_sg_BCS (A2C_sg_BCS S P) = A2C_sg_BC S (A_sg_BC_from_sg_BCS S P). 
Proof. unfold sg_BC_from_sg_BCS, A_sg_BC_from_sg_BCS, A2C_sg_BCS, A2C_sg_BC; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Qed.

Theorem correct_sg_certs_mcas_cast_up
           (S : Type)
           (eq : brel S)
           (s : S)
           (f : S -> S)
           (nt : brel_not_trivial S eq f)
           (eqvP : eqv_proofs S eq) 
           (bop : binary_op S)
           (id_d : bop_exists_id_decidable S eq bop)
           (P : sg_proofs_mcas S eq bop) : 
  sg_certs_mcas_cast_up S eq s f bop (p2c_exists_id_check _ _ _ id_d) (P2C_proofs_mcas_sg _ _ _ P)
  =
  P2C_proofs_mcas_sg _ _ _  (A_sg_proofs_mcas_cast_up S eq s f nt eqvP bop id_d P).
Proof. destruct P; simpl.
       reflexivity. 
       reflexivity.
       rewrite <- correct_sg_certs_from_sg_C_certs; reflexivity.
       rewrite <- correct_sg_certs_from_sg_NC_certs; auto. 
       unfold sg_certs_from_sg_CS_certs, A_sg_proofs_from_sg_CS_proofs.
          rewrite <- correct_sg_certs_from_sg_C_certs. 
          rewrite <- correct_sg_C_certs_from_sg_CS_certs. reflexivity.
       unfold sg_certs_from_sg_CI_certs, A_sg_proofs_from_sg_CI_proofs.
          rewrite <- correct_sg_certs_from_sg_C_certs. 
          rewrite <- correct_sg_C_certs_from_sg_CI_certs. reflexivity.
       unfold sg_certs_from_sg_CNI_certs, A_sg_proofs_from_sg_CNI_proofs.
          rewrite <- correct_sg_certs_from_sg_C_certs. 
          rewrite <- correct_sg_C_certs_from_sg_CNI_certs; auto. 
       unfold sg_certs_from_sg_CK_certs, A_sg_proofs_from_sg_CK_proofs.
       unfold sg_C_certs_from_sg_CK_certs, A_sg_C_proofs_from_sg_CK_proofs.          
          rewrite <- correct_sg_certs_from_sg_C_certs. 
          rewrite <- correct_sg_C_certs_from_sg_CNI_certs. 
          rewrite <- correct_sg_CNI_certs_from_sg_CK_certs. reflexivity. 
          exact eqvP. 
Qed. 


       
Theorem correct_sg_mcas_cast_up (S : Type) (P : A_sg_mcas S) : 
         sg_mcas_cast_up S (A2C_mcas_sg  S P) = A2C_mcas_sg  S (A_sg_mcas_cast_up S P).
Proof. destruct P; simpl.
       reflexivity.
       reflexivity.        
       rewrite correct_sg_from_sg_C; reflexivity. 
       rewrite correct_sg_from_sg_C_with_id; reflexivity.
       rewrite correct_sg_from_sg_C_with_ann; reflexivity.
       rewrite correct_sg_from_sg_BC; reflexivity. 
       rewrite correct_sg_from_sg_NC; reflexivity. 
       rewrite correct_sg_from_sg_NC_with_id; reflexivity. 
       rewrite correct_sg_from_sg_NC_with_ann; reflexivity. 
       rewrite correct_sg_from_sg_BNC; reflexivity. 
       unfold sg_from_sg_CS, A_sg_from_sg_CS.
          rewrite correct_sg_C_from_sg_CS.
          rewrite correct_sg_from_sg_C; reflexivity. 
       unfold sg_from_sg_CS_with_id, A_sg_from_sg_CS_with_id.
          rewrite correct_sg_C_with_id_from_sg_CS_with_id.
          rewrite correct_sg_from_sg_C_with_id; reflexivity. 
       unfold sg_from_sg_CS_with_ann, A_sg_from_sg_CS_with_ann.
          rewrite correct_sg_C_with_ann_from_sg_CS_with_ann.
          rewrite correct_sg_from_sg_C_with_ann; reflexivity. 
       unfold sg_from_sg_BCS, A_sg_from_sg_BCS.
          rewrite correct_sg_BC_from_sg_BCS.
          rewrite correct_sg_from_sg_BC; reflexivity. 
       unfold sg_from_sg_CI, A_sg_from_sg_CI.
          rewrite correct_sg_C_from_sg_CI.
          rewrite correct_sg_from_sg_C; reflexivity. 
       unfold sg_from_sg_CI_with_id, A_sg_from_sg_CI_with_id.
          rewrite correct_sg_C_with_id_from_sg_CI_with_id.
          rewrite correct_sg_from_sg_C_with_id; reflexivity. 
       unfold sg_from_sg_CI_with_ann, A_sg_from_sg_CI_with_ann.
          rewrite correct_sg_C_with_ann_from_sg_CI_with_ann.
          rewrite correct_sg_from_sg_C_with_ann; reflexivity. 
       unfold sg_from_sg_BCI, A_sg_from_sg_BCI.
          rewrite correct_sg_BC_from_sg_BCI.
          rewrite correct_sg_from_sg_BC; reflexivity. 
       unfold sg_from_sg_CNI, A_sg_from_sg_CNI.
          rewrite correct_sg_C_from_sg_CNI.
          rewrite correct_sg_from_sg_C; reflexivity. 
       unfold sg_from_sg_CNI_with_id, A_sg_from_sg_CNI_with_id.
          rewrite correct_sg_C_with_id_from_sg_CNI_with_id.
          rewrite correct_sg_from_sg_C_with_id; reflexivity. 
       unfold sg_from_sg_CNI_with_ann, A_sg_from_sg_CNI_with_ann.
          rewrite correct_sg_C_with_ann_from_sg_CNI_with_ann.
          rewrite correct_sg_from_sg_C_with_ann; reflexivity. 
       unfold sg_from_sg_BCNI, A_sg_from_sg_BCNI.
          rewrite correct_sg_BC_from_sg_BCNI.
          rewrite correct_sg_from_sg_BC; reflexivity.
       unfold sg_from_sg_CK, A_sg_from_sg_CK.
       unfold sg_from_sg_CNI, A_sg_C_from_sg_CK. 
          rewrite <- correct_sg_from_sg_C. 
          rewrite <- correct_sg_C_from_sg_CNI. 
          rewrite <- correct_sg_CNI_from_sg_CK.
          reflexivity. 
       unfold sg_from_sg_CK_with_id, A_sg_from_sg_CK_with_id.
       unfold sg_from_sg_CNI_with_id, A_sg_C_with_id_from_sg_CK_with_id. 
          rewrite <- correct_sg_from_sg_C_with_id. 
          rewrite <- correct_sg_C_with_id_from_sg_CNI_with_id. 
          rewrite <- correct_sg_CNI_with_id_from_sg_CK_with_id.
          reflexivity. 
Qed.


Theorem A_sg_cas_up_is_error_or_sg (S : Type) (P : A_sg_mcas S) :
  {l : list string & P = A_MCAS_sg_Error _ l} + 
  {A : A_sg S & A_sg_mcas_cast_up S P = A_MCAS_sg _ A}. 
Proof. destruct P; simpl. 
       + left. exists l. reflexivity.
       + right. exists a. reflexivity.
       + right. exists (A_sg_from_sg_C S a). reflexivity.
       + right. exists (A_sg_from_sg_C_with_id S a). reflexivity.
       + right. exists (A_sg_from_sg_C_with_ann S a). reflexivity.
       + right. exists (A_sg_from_sg_BC S a). reflexivity.
       + right. exists (A_sg_from_sg_NC S a). reflexivity.
       + right. exists (A_sg_from_sg_NC_with_id S a). reflexivity.
       + right. exists (A_sg_from_sg_NC_with_ann S a). reflexivity.
       + right. exists (A_sg_from_sg_BNC S a). reflexivity.
       + right. exists (A_sg_from_sg_CS S a). reflexivity.
       + right. exists (A_sg_from_sg_CS_with_id S a). reflexivity.
       + right. exists (A_sg_from_sg_CS_with_ann S a). reflexivity.
       + right. exists (A_sg_from_sg_BCS S a). reflexivity.
       + right. exists (A_sg_from_sg_CI S a). reflexivity.
       + right. exists (A_sg_from_sg_CI_with_id S a). reflexivity.
       + right. exists (A_sg_from_sg_CI_with_ann S a). reflexivity.
       + right. exists (A_sg_from_sg_BCI S a). reflexivity.
       + right. exists (A_sg_from_sg_CNI S a). reflexivity.
       + right. exists (A_sg_from_sg_CNI_with_id S a). reflexivity.
       + right. exists (A_sg_from_sg_CNI_with_ann S a). reflexivity.
       + right. exists (A_sg_from_sg_BCNI S a). reflexivity.
       + right. exists (A_sg_from_sg_CK S a). reflexivity.
       + right. exists (A_sg_from_sg_CK_with_id S a). reflexivity.
Qed. 






       
End Combinators.  
End Verify.   
