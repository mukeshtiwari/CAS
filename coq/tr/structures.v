Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.tr.properties.

Section ACAS. 

Record left_transform_proofs (L S : Type) (eqS : brel S) (eqL : brel L) (ltr : ltr_type L S) := 
{
  A_left_transform_congruence          : ltr_congruence L S eqL eqS ltr    
; A_left_transform_is_right_d          : ltr_is_right_decidable L S eqS ltr
; A_left_transform_left_constant_d     : ltr_left_constant_decidable L S eqS ltr                                                       
; A_left_transform_left_cancellative_d : ltr_left_cancellative_decidable L S eqS ltr
}.


Record A_left_transform (L S : Type) :=
{
  A_left_transform_carrier      : A_eqv S
; A_left_transform_label        : A_eqv L                                                       
; A_left_transform_ltr          : ltr_type L S (* T -> (S -> S) *)
; A_left_transform_exists_id_d  : ltr_exists_id_decidable L S  (A_eqv_eq S A_left_transform_carrier) A_left_transform_ltr 
; A_left_transform_exists_ann_d : ltr_exists_ann_decidable L S (A_eqv_eq S A_left_transform_carrier) A_left_transform_ltr 
; A_left_transform_proofs       : left_transform_proofs L S (A_eqv_eq S A_left_transform_carrier) (A_eqv_eq L A_left_transform_label)  A_left_transform_ltr
; A_left_transform_ast          : cas_ast (* cas_ltr_ast *)
}.

End ACAS.


Section MACAS.

Inductive A_ltr_mcas (L S : Type) := 
| A_MCAS_ltr_Error        : list string             -> A_ltr_mcas L S
| A_MCAS_ltr              : A_left_transform L S    -> A_ltr_mcas L S
.  

End MACAS.   

Section CAS. 

Record left_transform_certificates {L S : Type} := 
{
  left_transform_congruence          : @assert_ltr_congruence L S 
; left_transform_is_right_d          : @check_ltr_is_right L S
; left_transform_left_constant_d     : @check_ltr_left_constant L S                   
; left_transform_left_cancellative_d : @check_ltr_left_cancellative L S 
}.

Record left_transform (L S : Type) :=
{
  left_transform_carrier      : @eqv S
; left_transform_label        : @eqv L                                                       
; left_transform_ltr          : @ltr_type L S
; left_transform_exists_id_d  : @check_ltr_exists_id L S  
; left_transform_exists_ann_d : @check_ltr_exists_ann L S 
; left_transform_certs        : @left_transform_certificates L S
; left_transform_ast          : cas_ast (* cas_ltr_ast *)
}.

End CAS.

Section MCAS.

Inductive ltr_mcas {L S : Type} := 
| MCAS_ltr_Error        : list string             -> @ltr_mcas L S
| MCAS_ltr              : @left_transform L S    -> @ltr_mcas L S
.  

End MCAS.   


Section Translate.

Definition P2C_left_transform : ∀ (L S : Type) (eqS : brel S) (eqL : brel L) (ltr : L -> (S -> S)), 
         left_transform_proofs L S eqS eqL ltr -> @left_transform_certificates L S 
:= λ L S eqS eqL ltr P,
{|
  left_transform_congruence          := @Assert_Ltr_Congruence L S 
; left_transform_is_right_d          := p2c_ltr_is_right L S eqS ltr (A_left_transform_is_right_d L S eqS eqL ltr P)
; left_transform_left_constant_d     := p2c_ltr_left_constant L S eqS ltr (A_left_transform_left_constant_d L S eqS eqL ltr P)                                                
; left_transform_left_cancellative_d := p2c_ltr_left_cancellative L S eqS ltr (A_left_transform_left_cancellative_d L S eqS eqL ltr P)
|}.


Definition A2C_left_transform (L S : Type) (R : A_left_transform L S) : @left_transform L S := 
let ltr := A_left_transform_ltr L S R in 
let eqvS := A_left_transform_carrier L S R in
let eqvL := A_left_transform_label L S R in
let eqS := A_eqv_eq S eqvS in
let eqL := A_eqv_eq L eqvL in 
{|
  left_transform_carrier      := A2C_eqv S eqvS
; left_transform_label        := A2C_eqv L eqvL
; left_transform_ltr          := ltr
; left_transform_exists_id_d  := p2c_ltr_exists_id _ _ _ _ (A_left_transform_exists_id_d L S R)
; left_transform_exists_ann_d := p2c_ltr_exists_ann _ _ _ _ (A_left_transform_exists_ann_d L S R)
; left_transform_certs        := P2C_left_transform L S eqS eqL ltr (A_left_transform_proofs L S R)
; left_transform_ast          := A_left_transform_ast L S R
|}.

Definition A2C_mcas_ltr (L S : Type) (A : A_ltr_mcas L S) : @ltr_mcas L S :=
match A with
| A_MCAS_ltr_Error _ _ s        => MCAS_ltr_Error s
| A_MCAS_ltr _ _ B              => MCAS_ltr (A2C_left_transform _ _ B)
end. 

End Translate.   

