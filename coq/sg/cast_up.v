Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.

(*

ACAS 

  A_asg_proofs_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_C_proofs S r b -> asg_proofs S r b
  A_msg_proofs_from_sg_proofs   : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_proofs S r b -> msg_proofs S r b

  A_sg_proofs_from_sg_C_proofs     : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
                                       brel_not_trivial S r f -> eqv_proofs S r -> sg_C_proofs S r b -> sg_proofs S r b 
  A_sg_C_proofs_from_sg_CI_proofs  : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
                                       brel_not_trivial S r f -> eqv_proofs S r -> sg_CI_proofs S r b -> sg_C_proofs S r b 
  A_sg_C_proofs_from_sg_CS_proofs  : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
                                       brel_not_trivial S r f -> eqv_proofs S r -> sg_CS_proofs S r b -> sg_C_proofs S r b 
  A_sg_C_proofs_from_sg_CK_proofs  : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
                                       brel_not_trivial S r f -> eqv_proofs S r -> sg_CI_proofs S r b -> sg_C_proofs S r b 

  A_sg_from_sg_C     : ∀ (S : Type),  A_sg_C S -> A_sg S 
  A_msg_from_sg      : ∀ (S : Type),  A_sg S -> A_msg S
  A_sg_C_from_sg_CI  : ∀ (S : Type),  A_sg_CI S -> A_sg_C S
  A_sg_C_from_sg_CS  : ∀ (S : Type),  A_sg_CS S -> A_sg_C S
  A_sg_C_from_sg_CK  : ∀ (S : Type),  A_sg_CK S -> A_sg_C S

DERIVED
  A_asg_proofs_from_sg_CI_proofs  : ∀ (S : Type) (r : brel S) (b : binary_op S)  (s : S) (f : S -> S),
                                     brel_not_trivial S r f -> eqv_proofs S r -> sg_CI_proofs S r b -> asg_proofs S r b 

  A_sg_proofs_from_sg_CI_proofs   : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
                                     brel_not_trivial S r f -> eqv_proofs S r ->  sg_CI_proofs S r b -> sg_proofs S r b 
  A_sg_proofs_from_sg_CS_proofs   : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
                                     brel_not_trivial S r f -> eqv_proofs S r ->  sg_CS_proofs S r b -> sg_proofs S r b 

  A_sg_from_sg_CI   : ∀ (S : Type),  A_sg_CI S -> A_sg S 
  A_sg_from_sg_CS   : ∀ (S : Type),  A_sg_CS S -> A_sg S 
  A_sg_from_sg_CK   : ∀ (S : Type),  A_sg_CK S -> A_sg S 

CAS 

  asg_certs_from_sg_C_certs : ∀ {S : Type}, @sg_C_certificates S -> @asg_certificates S 
  msg_certs_from_sg_certs : ∀ {S : Type}, @sg_certificates S -> @msg_certificates S 
  sg_certs_from_sg_C_certs     : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @sg_C_certificates S -> @sg_certificates S
  sg_C_certs_from_sg_CI_certs     : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @sg_CI_certificates S -> @sg_C_certificates S
  sg_C_certs_from_sg_CS_certs     : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @sg_CS_certificates S -> @sg_C_certificates S
  sg_C_certs_from_sg_CK_certs  : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @sg_CK_certificates S -> @sg_C_certificates S

  sg_from_sg_C     : ∀ {S : Type},  @sg_C S -> @sg S
  msg_from_sg      : ∀ {S : Type},  @sg S -> @msg S
  sg_C_from_sg_CI  : ∀ {S : Type},  @sg_CI S -> @sg_C S  
  sg_C_from_sg_CS  : ∀ {S : Type},  @sg_CS S -> @sg_C S  
  sg_C_from_sg_CK  : ∀ {S : Type},  @sg_CK S -> @sg_C S  

DERIVED 

  asg_certs_from_sg_CI_certs : ∀ (S : Type) (r : brel S) (b : binary_op S)  (s : S) (f : S -> S), @sg_CI_certificates S -> @asg_certificates S 
  sg_certs_from_sg_CI_certs   : ∀ {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S),  @sg_CI_certificates S -> @sg_certificates S
  sg_certs_from_sg_CS_certs   : ∀ {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S),  @sg_CS_certificates S -> @sg_certificates S

  sg_from_sg_CI   : ∀ {S : Type},  @sg_CI S -> @sg S  
  sg_from_sg_CS   : ∀ {S : Type},  @sg_CS S -> @sg S
  sg_from_sg_CK   : ∀ {S : Type},  @sg_CK S -> @sg S

*) 

Section Theory.

End Theory.

Section ACAS.
 

Definition A_asg_proofs_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_C_proofs S r b -> asg_proofs S r b 
:= λ S r b sgS,
{|
  A_asg_associative      := A_sg_C_associative S r b sgS 
; A_asg_congruence       := A_sg_C_congruence S r b sgS 
; A_asg_commutative      := A_sg_C_commutative S r b sgS
; A_asg_selective_d      := A_sg_C_selective_d S r b sgS    
; A_asg_idempotent_d     := A_sg_C_idempotent_d S r b sgS
|}. 

Definition A_msg_proofs_from_sg_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S),  sg_proofs S r b -> msg_proofs S r b
:= λ S r b sgS,                                                                                                                     
{|
  A_msg_associative      := A_sg_associative S r b sgS 
; A_msg_congruence       := A_sg_congruence S r b sgS 
; A_msg_commutative_d    := A_sg_commutative_d S r b sgS
; A_msg_is_left_d        := A_sg_is_left_d S r b sgS
; A_msg_is_right_d       := A_sg_is_right_d S r b sgS
; A_msg_left_cancel_d    := A_sg_left_cancel_d S r b sgS
; A_msg_right_cancel_d   := A_sg_right_cancel_d S r b sgS
; A_msg_left_constant_d  := A_sg_left_constant_d S r b sgS
; A_msg_right_constant_d := A_sg_right_constant_d S r b sgS
; A_msg_anti_left_d      := A_sg_anti_left_d S r b sgS
; A_msg_anti_right_d     := A_sg_anti_right_d S r b sgS
|}. 
       
Definition A_sg_proofs_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> sg_C_proofs S r b -> sg_proofs S r b 
:= λ S r b s f Pf eqvS sgS,
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

Definition A_sg_C_proofs_from_sg_CI_proofs (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S)
    (Pf : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CI_proofs S r b) : sg_C_proofs S r b := 
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



Definition A_sg_C_proofs_from_sg_CS_proofs (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S)
    (Pf : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CS_proofs S r b) : sg_C_proofs S r b := 
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





Definition A_sg_C_proofs_from_sg_CK_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> bop_exists_id_decidable S r b -> sg_CK_proofs S r b -> sg_C_proofs S r b 
:= λ S r b s f Pf eqvS id_decidable sgS, 
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
                   id_decidable
in 
{|
  A_sg_C_associative      := A_sg_CK_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CK_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CK_commutative S r b sgS
; A_sg_C_selective_d      := inr _ (bop_not_idempotent_implies_not_selective S r b not_idem)
; A_sg_C_idempotent_d     := inr _ not_idem 
; A_sg_C_cancel_d    := inl _ (A_sg_CK_cancel S r b sgS)    
; A_sg_C_constant_d  := inr _ (bop_left_cancellative_implies_not_left_constant S r b s f Pf 
                                       (A_sg_CK_cancel S r b sgS)    
                                   )
; A_sg_C_anti_left_d      := A_sg_CK_anti_left_d S r b sgS 
; A_sg_C_anti_right_d     := A_sg_CK_anti_right_d S r b sgS
|}. 


Definition A_sg_from_sg_C : ∀ (S : Type),  A_sg_C S -> A_sg S 
:= λ S sgS,
  let b  := A_sg_C_bop S sgS in
  let eq := A_eqv_eq S (A_sg_C_eqv S sgS) in 
   {| 
     A_sg_eq           := A_sg_C_eqv S sgS
   ; A_sg_bop          := b
   ; A_sg_exists_id_d  := A_sg_C_exists_id_d S sgS    
   ; A_sg_exists_ann_d := A_sg_C_exists_ann_d S sgS    
   ; A_sg_proofs       := A_sg_proofs_from_sg_C_proofs S eq b 
                            (A_eqv_witness S (A_sg_C_eqv S sgS))
                            (A_eqv_new S (A_sg_C_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_C_eqv S sgS))
                            (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_proofs S sgS)
   ; A_sg_ast        := Ast_sg_from_sg_C (A_sg_C_ast S sgS)
   |}. 



Definition A_msg_from_sg : ∀ (S : Type),  A_sg S -> A_msg S 
:= λ S sgS, 
   {| 
     A_msg_eq          := A_sg_eq S sgS
   ; A_msg_bop         := A_sg_bop S sgS
   ; A_msg_exists_id_d  := A_sg_exists_id_d S sgS    
   ; A_msg_exists_ann_d := A_sg_exists_ann_d S sgS    
   ; A_msg_proofs      := A_msg_proofs_from_sg_proofs S 
                            (A_eqv_eq S (A_sg_eq S sgS)) 
                            (A_sg_bop S sgS)
                            (A_sg_proofs S sgS)
   ; A_msg_ast        := Ast_msg_from_sg (A_sg_ast S sgS)
   |}. 



Definition A_sg_C_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv          := A_sg_CI_eqv S sgS
   ; A_sg_C_bop          := A_sg_CI_bop S sgS
   ; A_sg_C_exists_id_d  := A_sg_CI_exists_id_d S sgS    
   ; A_sg_C_exists_ann_d := A_sg_CI_exists_ann_d S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_bop S sgS)
                            (A_eqv_witness S (A_sg_CI_eqv S sgS))
                            (A_eqv_new S (A_sg_CI_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CI_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_proofs S sgS)
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CI (A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_C_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv          := A_sg_CS_eqv S sgS
   ; A_sg_C_bop          := A_sg_CS_bop S sgS
   ; A_sg_C_exists_id_d  := A_sg_CS_exists_id_d S sgS    
   ; A_sg_C_exists_ann_d := A_sg_CS_exists_ann_d S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_bop S sgS)
                            (A_eqv_witness S (A_sg_CS_eqv S sgS))
                            (A_eqv_new S (A_sg_CS_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CS_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_proofs S sgS)
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CI (A_sg_CS_ast S sgS) (* fix *) 
   |}. 

Definition A_sg_C_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg_C S 
  := λ S sgS,
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
     A_sg_C_eqv          := eqvS 
   ; A_sg_C_bop          := b 
   ; A_sg_C_exists_id_d  := A_sg_CK_exists_id_d S sgS
   ; A_sg_C_exists_ann_d := inr (bop_left_cancellative_implies_not_exists_ann S eq b s f symS trnS Pf 
                                    (A_sg_CK_cancel S eq b (A_sg_CK_proofs S sgS)))
   ; A_sg_C_proofs     := A_sg_C_proofs_from_sg_CK_proofs S eq b s f Pf eqvP (A_sg_CK_exists_id_d S sgS) (A_sg_CK_proofs S sgS)
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CK (A_sg_CK_ast S sgS)
   |}. 


(* DERIVED UPCASTS *)

Definition A_asg_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S)  (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> sg_CI_proofs S r b -> asg_proofs S r b 
:= λ S r b s f nt eqv sgS,
   A_asg_proofs_from_sg_C_proofs S r b (A_sg_C_proofs_from_sg_CI_proofs S r b s f nt eqv sgS). 

Definition A_sg_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r ->  sg_CI_proofs S r b -> sg_proofs S r b 
  := λ S r b s f Pf eqv sg_CS, A_sg_proofs_from_sg_C_proofs S r b s f Pf eqv (A_sg_C_proofs_from_sg_CI_proofs S r b s f Pf eqv sg_CS).

Definition A_sg_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r ->  sg_CS_proofs S r b -> sg_proofs S r b 
:= λ S r b s f Pf eqv sg_CS, A_sg_proofs_from_sg_C_proofs S r b s f Pf eqv (A_sg_C_proofs_from_sg_CS_proofs S r b s f Pf eqv sg_CS).

Definition A_sg_from_sg_CI : ∀ (S : Type),  A_sg_CI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CI S sgS).  

Definition A_sg_from_sg_CS : ∀ (S : Type),  A_sg_CS S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CS S sgS).  

Definition A_sg_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CK S sgS).  

End ACAS.

Section CAS.


Definition asg_certs_from_sg_C_certs : ∀ {S : Type}, @sg_C_certificates S -> @asg_certificates S 
:= λ {S} sgS,
{|
  asg_associative      := sg_C_associative sgS 
; asg_congruence       := sg_C_congruence sgS 
; asg_commutative      := sg_C_commutative sgS
; asg_selective_d      := sg_C_selective_d sgS    
; asg_idempotent_d     := sg_C_idempotent_d sgS
|}. 


Definition msg_certs_from_sg_certs : ∀ {S : Type}, @sg_certificates S -> @msg_certificates S 
:= λ {S} sgS,
{|
  msg_associative      := sg_associative sgS 
; msg_congruence       := sg_congruence sgS 
; msg_commutative_d    := sg_commutative_d sgS
; msg_is_left_d        := sg_is_left_d sgS
; msg_is_right_d       := sg_is_right_d sgS
; msg_left_cancel_d    := sg_left_cancel_d sgS
; msg_right_cancel_d   := sg_right_cancel_d sgS
; msg_left_constant_d  := sg_left_constant_d sgS
; msg_right_constant_d := sg_right_constant_d sgS
; msg_anti_left_d      := sg_anti_left_d sgS
; msg_anti_right_d     := sg_anti_right_d sgS
|}. 
  

Definition sg_certs_from_sg_C_certs : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @sg_C_certificates S -> @sg_certificates S
:= λ {S} r b s f sgS, 
{|
  sg_associative      := Assert_Associative (S := S) 
; sg_congruence       := Assert_Bop_Congruence (S := S) 
; sg_commutative_d    := Certify_Commutative (S := S)  
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



Definition sg_C_certs_from_sg_CI_certs {S : Type} (wS : S) (r : brel S) (f : S -> S)
           (b : binary_op S) (sgS : @sg_CI_certificates S): @sg_C_certificates S := 
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative 

; sg_C_idempotent_d     := Certify_Idempotent
; sg_C_selective_d      := match sg_CI_not_selective sgS with
                           | Assert_Not_Selective (s1, s2) => Certify_Not_Selective (s1, s2)
                           end
; sg_C_constant_d       := Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b wS f) 
; sg_C_cancel_d         := match sg_CI_not_selective sgS with
                           | Assert_Not_Selective (s1, s2) =>
                               Certify_Not_Left_Cancellative (cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative  b s1 s2) 
                           end
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left wS) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right wS) 
|}. 


Definition sg_C_certs_from_sg_CS_certs {S : Type} (wS : S) (r : brel S) (f : S -> S)
           (b : binary_op S) (sgS : @sg_CS_certificates S): @sg_C_certificates S := 
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative 

; sg_C_idempotent_d     := Certify_Idempotent
; sg_C_selective_d      := Certify_Selective 
; sg_C_constant_d       := Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b wS f) 
; sg_C_cancel_d         := Certify_Not_Left_Cancellative (cef_selective_and_commutative_imply_not_left_cancellative  r b wS f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left wS) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right wS) 
|}. 

Definition sg_C_certs_from_sg_CK_certs : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @check_exists_id S -> @sg_CK_certificates S -> @sg_C_certificates S
:= λ {S} r b s f exists_id_d sgS, 
let ni := match exists_id_d with 
          | Certify_Exists_Id i => cef_cancellative_and_exists_id_imply_not_idempotent r s i f
          | Certify_Not_Exists_Id => s 
          end 
in 
{|
  sg_C_associative      := Assert_Associative (S := S) 
; sg_C_congruence       := Assert_Bop_Congruence (S := S) 
; sg_C_commutative      := Assert_Commutative (S := S) 

; sg_C_idempotent_d     := Certify_Not_Idempotent (S := S) ni 
; sg_C_selective_d      := Certify_Not_Selective (S := S) 
                              (cef_not_idempotent_implies_not_selective ni) 
; sg_C_constant_d       := Certify_Not_Left_Constant (S := S) 
                              (cef_left_cancellative_implies_not_left_constant s f) 
; sg_C_cancel_d         := Certify_Left_Cancellative (S := S) 
; sg_C_anti_left_d      := sg_CK_anti_left_d sgS 
; sg_C_anti_right_d     := sg_CK_anti_right_d sgS
|}. 

Definition sg_from_sg_C: ∀ {S : Type},  @sg_C S -> @sg S
:= λ {S} sg_C, 
   {| 
       sg_eq    := sg_C_eqv sg_C
     ; sg_bop   := sg_C_bop sg_C
     ; sg_exists_id_d  := sg_C_exists_id_d sg_C
     ; sg_exists_ann_d := sg_C_exists_ann_d sg_C
     ; sg_certs := sg_certs_from_sg_C_certs 
                    (eqv_eq (sg_C_eqv sg_C)) 
                    (sg_C_bop sg_C) 
                    (eqv_witness (sg_C_eqv sg_C))
                    (eqv_new (sg_C_eqv sg_C))                    
                    (sg_C_certs sg_C)
     ; sg_ast   := Ast_sg_from_sg_C (sg_C_ast sg_C)
   |}. 

Definition msg_from_sg : ∀ {S : Type},  @sg S -> @msg S 
:= λ S sgS, 
   {| 
     msg_eq        := sg_eq sgS
   ; msg_bop       := sg_bop sgS
   ; msg_exists_id_d  := sg_exists_id_d sgS
   ; msg_exists_ann_d := sg_exists_ann_d sgS                               
   ; msg_certs     := msg_certs_from_sg_certs (sg_certs sgS)
   ; msg_ast       := Ast_msg_from_sg (sg_ast sgS)
   |}. 



Definition sg_C_from_sg_CI: ∀ {S : Type},  @sg_CI S -> @sg_C S  
:= λ {S} sg, 
   {| 
     sg_C_eqv   := sg_CI_eqv sg
   ; sg_C_bop   := sg_CI_bop sg
   ; sg_C_exists_id_d  := sg_CI_exists_id_d sg
   ; sg_C_exists_ann_d := sg_CI_exists_ann_d sg
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs
                     (eqv_witness (sg_CI_eqv sg))
                     (eqv_eq (sg_CI_eqv sg))
                     (eqv_new (sg_CI_eqv sg))
                     (sg_CI_bop sg)
                     (sg_CI_certs sg)
   ; sg_C_ast   := Ast_sg_C_from_sg_CI (sg_CI_ast sg)
   |}. 


Definition sg_C_from_sg_CS: ∀ {S : Type},  @sg_CS S -> @sg_C S  
:= λ {S} sg, 
   {| 
     sg_C_eqv   := sg_CS_eqv sg
   ; sg_C_bop   := sg_CS_bop sg
   ; sg_C_exists_id_d  := sg_CS_exists_id_d sg
   ; sg_C_exists_ann_d := sg_CS_exists_ann_d sg
   ; sg_C_certs := sg_C_certs_from_sg_CS_certs
                     (eqv_witness (sg_CS_eqv sg))
                     (eqv_eq (sg_CS_eqv sg))
                     (eqv_new (sg_CS_eqv sg))
                     (sg_CS_bop sg)
                     (sg_CS_certs sg)
   ; sg_C_ast   := Ast_sg_C_from_sg_CI (sg_CS_ast sg) (* fix *) 
   |}. 


                                                    
Definition sg_C_from_sg_CK: ∀ {S : Type},  @sg_CK S -> @sg_C S  
:= λ {S} sg, 
   {| 
     sg_C_eqv   := sg_CK_eqv sg
   ; sg_C_bop   := sg_CK_bop sg
   ; sg_C_exists_id_d  := sg_CK_exists_id_d sg
   ; sg_C_exists_ann_d := @Certify_Not_Exists_Ann S 
   ; sg_C_certs := sg_C_certs_from_sg_CK_certs 
                      (eqv_eq (sg_CK_eqv sg))
                      (sg_CK_bop sg)
                      (eqv_witness (sg_CK_eqv sg))
                      (eqv_new (sg_CK_eqv sg))
                      (sg_CK_exists_id_d sg)
                      (sg_CK_certs sg)
   ; sg_C_ast   := Ast_sg_C_from_sg_CK (sg_CK_ast sg)
   |}. 


(* DERIVED UPCASTS *)


Definition asg_certs_from_sg_CI_certs : ∀ {S : Type} (r : brel S) (b : binary_op S)  (s : S) (f : S -> S), @sg_CI_certificates S -> @asg_certificates S 
:= λ {S} r b s f sgS,
   asg_certs_from_sg_C_certs (sg_C_certs_from_sg_CI_certs s r f b sgS). 

Definition sg_certs_from_sg_CI_certs : ∀ {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
            @sg_CI_certificates S -> @sg_certificates S
:= λ {S} r b s f sg_CI, sg_certs_from_sg_C_certs r b s f (sg_C_certs_from_sg_CI_certs s r f b sg_CI).

Definition sg_certs_from_sg_CS_certs : ∀ {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
            @sg_CS_certificates S -> @sg_certificates S
:= λ {S} r b s f sg_CI, sg_certs_from_sg_C_certs r b s f (sg_C_certs_from_sg_CS_certs s r f b sg_CI).

Definition sg_from_sg_CI: ∀ {S : Type},  @sg_CI S -> @sg S
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CI sgS ). 

Definition sg_from_sg_CS: ∀ {S : Type},  @sg_CS S -> @sg S
  := λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CS sgS).

Definition sg_from_sg_CK: ∀ {S : Type},  @sg_CK S -> @sg S
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CK sgS).  


End CAS.

Section Verify.

Lemma correct_asg_certs_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_C_proofs S r b), 
       asg_certs_from_sg_C_certs (P2C_sg_C S r b sgS)
       = 
       P2C_asg S r b (A_asg_proofs_from_sg_C_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold asg_certs_from_sg_C_certs, A_asg_proofs_from_sg_C_proofs, P2C_asg, P2C_sg_C; simpl.
       reflexivity.
Defined. 


Lemma correct_msg_certs_from_sg_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_proofs S r b), 
       msg_certs_from_sg_certs (P2C_sg S r b sgS)
       = 
       P2C_msg S r b (A_msg_proofs_from_sg_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold msg_certs_from_sg_certs, A_msg_proofs_from_sg_proofs, P2C_msg, P2C_sg; simpl.
       reflexivity.
Defined. 


Lemma correct_sg_certs_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_C_proofs S r b), 
       sg_certs_from_sg_C_certs r b s f (P2C_sg_C S r b sgS)
       = 
       P2C_sg S r b (A_sg_proofs_from_sg_C_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. destruct sgS. destruct eqvS. 
       unfold sg_certs_from_sg_C_certs, A_sg_proofs_from_sg_C_proofs, P2C_sg, P2C_sg_C; simpl.
       destruct A_sg_C_cancel_d as [ lcanS | [[x [y z]] nlcanS]];
       destruct A_sg_C_constant_d as [ lconS | [[u [v w]] nlconS] ]; simpl; 
       reflexivity.
Defined. 


Lemma correct_sg_C_certs_from_sg_CI_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CI_proofs S r b), 
       sg_C_certs_from_sg_CI_certs s r f b (P2C_sg_CI S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CI_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CI_certs, A_sg_C_proofs_from_sg_CI_proofs, P2C_sg_C, P2C_sg_CI. simpl. 
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]. 
       simpl. reflexivity.        
       
Defined.


Lemma correct_sg_C_certs_from_sg_CS_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CS_proofs S r b), 
       sg_C_certs_from_sg_CS_certs s r f b (P2C_sg_CS S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CS_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CS_certs, A_sg_C_proofs_from_sg_CS_proofs, P2C_sg_C, P2C_sg_CS; 
       simpl. reflexivity.        
Defined.

Lemma correct_sg_C_certs_from_sg_CK_certs : 
  ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S)
     (nt : brel_not_trivial S r f)  (eqvS : eqv_proofs S r) (exists_id_d : bop_exists_id_decidable S r b) (sgS : sg_CK_proofs S r b), 
       sg_C_certs_from_sg_CK_certs r b s f (p2c_exists_id_check S r b exists_id_d) (P2C_sg_CK S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CK_proofs S r b s f nt eqvS exists_id_d sgS). 
Proof. intros S r b s f nt eqvS exists_id_d sgS. destruct sgS. destruct eqvS. 
       destruct exists_id_d as [ [i Pi] | no_id ]; 
       unfold sg_C_certs_from_sg_CK_certs, A_sg_C_proofs_from_sg_CK_proofs, P2C_sg_C, P2C_sg_CK; 
       simpl. 
          reflexivity.        
          compute. reflexivity.        
Defined. 

Theorem correct_sg_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
         sg_from_sg_C (A2C_sg_C S P) = A2C_sg S (A_sg_from_sg_C S P). 
Proof. intros S P. destruct P.
       unfold sg_from_sg_C, A_sg_from_sg_C, A2C_sg_C, A2C_sg; simpl.
       destruct A_sg_C_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Defined. 

Theorem correct_msg_from_sg : ∀ (S : Type) (P : A_sg S),  
         msg_from_sg (A2C_sg S P) = A2C_msg S (A_msg_from_sg S P). 
Proof. intros S P. destruct P.
       unfold msg_from_sg, A_msg_from_sg, A2C_sg, A2C_msg; simpl.
       rewrite <-correct_msg_certs_from_sg_certs; auto. 
Defined. 

Theorem correct_sg_C_from_sg_CI : ∀ (S : Type) (P : A_sg_CI S),  
         sg_C_from_sg_CI (A2C_sg_CI S P) = A2C_sg_C S (A_sg_C_from_sg_CI S P). 
Proof. intros S P. unfold sg_C_from_sg_CI, A_sg_C_from_sg_CI, A2C_sg_CI, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Defined.

Theorem correct_sg_C_from_sg_CS : ∀ (S : Type) (P : A_sg_CS S),  
         sg_C_from_sg_CS (A2C_sg_CS S P) = A2C_sg_C S (A_sg_C_from_sg_CS S P). 
Proof. intros S P. unfold sg_C_from_sg_CS, A_sg_C_from_sg_CS, A2C_sg_CS, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Defined.

Theorem correct_sg_C_from_sg_CK : ∀ (S : Type) (P : A_sg_CK S),  
         sg_C_from_sg_CK  (A2C_sg_CK S P) = A2C_sg_C S (A_sg_C_from_sg_CK S P). 
Proof. intros S P. unfold sg_C_from_sg_CK, A_sg_C_from_sg_CK, A2C_sg_CK, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CK_certs; auto. 
Defined. 
 
End Verify.   
