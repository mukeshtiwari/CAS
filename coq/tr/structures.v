Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.tr.properties.

Section ACAS. 

Record ltr_proofs (L S : Type) (eqS : brel S) (eqL : brel L) (ltr : L -> (S -> S)) := 
{
  A_ltr_congruence          : ltr_congruence L S eqL eqS ltr    
; A_ltr_is_right_d          : ltr_is_right_decidable L S eqS ltr
(* ; A_ltr_exists_id_d         : ltr_exists_id_decidable L S eqS ltr *) 
; A_ltr_left_cancellative_d : ltr_left_cancellative_decidable L S eqS ltr
}.


Record A_ltr (L S : Type) :=
{
  A_ltr_carrier : A_eqv S
; A_ltr_label   : A_eqv L                                                       
; A_ltr_ltr   : left_transform L S (* T -> (S -> S) *) 
; A_ltr_proofs  : ltr_proofs L S (A_eqv_eq S A_ltr_carrier) (A_eqv_eq L A_ltr_label)  A_ltr_ltr
; A_ltr_ast     : cas_ltr_ast
}.

End ACAS. 

Section CAS. 


Record ltr_certificates {L S : Type} := 
{
   ltr_congruence_a          : @assert_ltr_congruence L S 
;  ltr_is_right_d          : @check_ltr_is_right L S 
(* ; ltr_exists_id_d         : @check_ltr_exists_id L S *) 
; ltr_left_cancellative_d : @check_ltr_left_cancellative L S 
}.

Record ltr (L S : Type) :=
{
  ltr_carrier : @eqv S
; ltr_label   : @eqv L                                                       
; ltr_ltr     : @left_transform L S (* T -> (S -> S) *) 
; ltr_certs   : @ltr_certificates L S
; ltr_ast     : cas_ltr_ast
}.

End CAS.

Section Translate.

Definition P2C_ltr : ∀ (L S : Type) (eqS : brel S) (eqL : brel L) (ltr : L -> (S -> S)), 
         ltr_proofs L S eqS eqL ltr -> @ltr_certificates L S 
:= λ L S eqS eqL ltr P,
{|
  ltr_congruence_a          := @Assert_Ltr_Congruence L S 
; ltr_is_right_d          := p2c_ltr_is_right L S eqS ltr (A_ltr_is_right_d L S eqS eqL ltr P)
(* ; ltr_exists_id_d         := p2c_ltr_exists_id L S eqS ltr (A_ltr_exists_id_d L S eqS eqL ltr P) *) 
; ltr_left_cancellative_d := p2c_ltr_left_cancellative L S eqS ltr (A_ltr_left_cancellative_d L S eqS eqL ltr P)
|}. 

Definition A2C_ltr : ∀ (L S : Type), A_ltr L S -> @ltr L S 
  := λ L S R,
let ltr := A_ltr_ltr L S R in 
let eqvS := A_ltr_carrier L S R in
let eqvL := A_ltr_label L S R in
let eqS := A_eqv_eq S eqvS in
let eqL := A_eqv_eq L eqvL in 
{|

  ltr_carrier := A2C_eqv S eqvS
; ltr_label   := A2C_eqv L eqvL
; ltr_ltr     := ltr 
; ltr_certs   := P2C_ltr L S eqS eqL ltr (A_ltr_proofs L S R)
; ltr_ast     := A_ltr_ast L S R
|}.   

End Translate.   
