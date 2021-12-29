Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.theory. 

Section ACAS.

Record os_bottom_top_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bottom_top_bottom_id_d : os_exists_bottom_id_decidable S eq lte times 
; A_bottom_top_top_ann_d   : os_exists_top_ann_decidable S eq lte times 
}.

Record os_bottom_is_id_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bottom_is_id           : A_os_exists_bottom_id_equal eq lte times 
; A_bottom_is_id_top_ann_d : os_exists_top_ann_decidable S eq lte times 
}.

Record os_top_is_ann_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_top_is_ann_bottom_id_d : os_exists_bottom_id_decidable S eq lte times 
; A_top_is_ann             : A_os_exists_top_ann_equal eq lte times 
}.


Record os_bounded_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bounded_bottom_id : A_os_exists_bottom_id_equal eq lte times 
; A_bounded_top_ann   : A_os_exists_top_ann_equal eq lte times 
}.


Record os_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_posg_left_monotonic_d            : os_left_monotone_decidable lte times 
; A_posg_right_monotonic_d           : os_right_monotone_decidable lte times 

; A_posg_left_increasing_d           : os_left_increasing_decidable lte times 
; A_posg_right_increasing_d          : os_right_increasing_decidable lte times 

; A_posg_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_posg_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
}.


Record os_monotone_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_left_monotonic              : os_left_monotone lte times 
; A_mono_right_monotonic             : os_right_monotone lte times 

; A_mono_left_increasing_d           : os_left_increasing_decidable lte times 
; A_mono_right_increasing_d          : os_right_increasing_decidable lte times 

(* not yet                                                                      
; A_mono_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_mono_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
*) 
}. 


Record os_monotone_increasing_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_inc_left_monotonic              : os_left_monotone lte times 
; A_mono_inc_right_monotonic             : os_right_monotone lte times 

; A_mono_inc_left_increasing             : os_left_increasing lte times 
; A_mono_inc_right_increasing            : os_right_increasing lte times 

(*  Not yet 
; A_mono_inc_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_mono_inc_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
*) 
}. 

(*
Record os_monotone_strictly_increasing_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_sinc_left_monotonic              : os_left_monotone lte times 
; A_mono_sinc_right_monotonic             : os_right_monotone lte times 

; A_mono_sinc_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_mono_sinc_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
}. 
*) 


Record A_posg (S : Type) := {
  A_posg_eqv               : A_eqv S 
; A_posg_lte               : brel S 
; A_posg_times             : binary_op S 
; A_posg_lte_proofs        : po_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte
; A_posg_times_proofs      : msg_proofs S (A_eqv_eq S A_posg_eqv) A_posg_times
; A_posg_bottom_top_proofs : os_bottom_top_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte A_posg_times
; A_posg_proofs            : os_proofs S A_posg_lte A_posg_times 
; A_posg_ast               : cas_ast
}.

Record A_monotone_posg (S : Type) := {
  A_mposg_eqv          : A_eqv S 
; A_mposg_lte          : brel S 
; A_mposg_times        : binary_op S 
; A_mposg_lte_proofs   : po_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte
; A_mposg_times_proofs : msg_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_times
; A_mposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte A_mposg_times                                    
; A_mposg_proofs       : os_monotone_proofs S A_mposg_lte A_mposg_times 
; A_mposg_ast          : cas_ast
}.

Record A_monotone_increasing_posg (S : Type) := {
  A_miposg_eqv          : A_eqv S 
; A_miposg_lte          : brel S 
; A_miposg_times        : binary_op S 
; A_miposg_lte_proofs   : po_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_lte
; A_miposg_times_proofs : msg_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_times
; A_miposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_lte A_miposg_times                                    
; A_miposg_proofs       : os_monotone_increasing_proofs S A_miposg_lte A_miposg_times 
; A_miposg_ast          : cas_ast
}.

Record A_bounded_monotone_increasing_posg (S : Type) := {
  A_bmiposg_eqv          : A_eqv S 
; A_bmiposg_lte          : brel S 
; A_bmiposg_times        : binary_op S 
; A_bmiposg_lte_proofs   : po_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_lte
; A_bmiposg_times_proofs : msg_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_times
; A_bmiposg_top_bottom   : os_bounded_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_lte A_bmiposg_times                                    
; A_bmiposg_proofs       : os_monotone_increasing_proofs S A_bmiposg_lte A_bmiposg_times 
; A_bmiposg_ast          : cas_ast
}.

Record A_bounded_monotone_increasing_posg_CI (S : Type) := {
  A_bmiposg_CI_eqv          : A_eqv S 
; A_bmiposg_CI_lte          : brel S 
; A_bmiposg_CI_times        : binary_op S 
; A_bmiposg_CI_lte_proofs   : po_proofs S (A_eqv_eq S A_bmiposg_CI_eqv) A_bmiposg_CI_lte
; A_bmiposg_CI_times_proofs : sg_CI_proofs S (A_eqv_eq S A_bmiposg_CI_eqv) A_bmiposg_CI_times
; A_bmiposg_CI_top_bottom   : os_bounded_proofs S (A_eqv_eq S A_bmiposg_CI_eqv) A_bmiposg_CI_lte A_bmiposg_CI_times                                    
; A_bmiposg_CI_proofs       : os_monotone_increasing_proofs S A_bmiposg_CI_lte A_bmiposg_CI_times 
; A_bmiposg_CI_ast          : cas_ast
}.

Record A_meet_semilattice (S : Type) := {
  A_msl_eqv           : A_eqv S 
; A_msl_lte           : brel S 
; A_msl_meet          : binary_op S
; A_msl_lte_proofs    : po_proofs S (A_eqv_eq _ A_msl_eqv) A_msl_lte 
; A_msl_meet_proofs   : sg_CI_proofs S (A_eqv_eq _ A_msl_eqv) A_msl_meet
; A_msl_top_bottom    : os_bottom_top_proofs S (A_eqv_eq S A_msl_eqv) A_msl_lte A_msl_meet
; A_msl_proofs        : bop_is_glb A_msl_lte A_msl_meet
; A_msl_ast           : cas_ast
}.

Record A_join_semilattice (S : Type) := {
  A_jsl_eqv           : A_eqv S 
; A_jsl_lte           : brel S 
; A_jsl_join          : binary_op S 
; A_jsl_lte_proofs    : po_proofs S (A_eqv_eq _ A_jsl_eqv) A_jsl_lte 
; A_jsl_join_proofs   : sg_CI_proofs S (A_eqv_eq _ A_jsl_eqv) A_jsl_join
; A_jsl_top_bottom    : os_bottom_top_proofs S (A_eqv_eq S A_jsl_eqv) A_jsl_lte A_jsl_join
; A_jsl_proofs        : bop_is_lub A_jsl_lte A_jsl_join
; A_jsl_ast           : cas_ast
}.

Record A_bounded_join_semilattice (S : Type) := {
  A_bjsl_eqv           : A_eqv S 
; A_bjsl_lte           : brel S 
; A_bjsl_join          : binary_op S 
; A_bjsl_lte_proofs    : po_proofs S (A_eqv_eq _ A_bjsl_eqv) A_bjsl_lte 
; A_bjsl_join_proofs   : sg_CI_proofs S (A_eqv_eq _ A_bjsl_eqv) A_bjsl_join
; A_bjsl_top_bottom    : os_bounded_proofs S (A_eqv_eq S A_bjsl_eqv) A_bjsl_lte A_bjsl_join
; A_bjsl_proofs        : bop_is_lub A_bjsl_lte A_bjsl_join
; A_bjsl_ast           : cas_ast
}.


Section Projections.
  
Definition A_po_from_bounded_monotone_increasing_posg
           (S : Type)
           (P : A_bounded_monotone_increasing_posg S) : A_po S :=
let B := A_bmiposg_top_bottom _ P in 
let bot_id := A_bounded_bottom_id _ _ _ _ B in
let top_ann := A_bounded_top_ann _ _ _ _ B in 
{|
  A_po_eqv           := A_bmiposg_eqv _ P 
; A_po_lte           := A_bmiposg_lte _ P 
; A_po_exists_top_d  := inl (A_extract_exist_top_from_exists_top_ann_equal _ _ _ _ top_ann ) 
; A_po_exists_bottom := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bot_id 
; A_po_proofs        := A_bmiposg_lte_proofs _ P 
; A_po_ast           := A_bmiposg_ast _ P (* FIX *)
|}.  
  

Definition A_po_from_bounded_monotone_increasing_posg_CI
           (S : Type)
           (P : A_bounded_monotone_increasing_posg_CI S) : A_po S :=
let B := A_bmiposg_CI_top_bottom _ P in 
let bot_id := A_bounded_bottom_id _ _ _ _ B in
let top_ann := A_bounded_top_ann _ _ _ _ B in 
{|
  A_po_eqv           := A_bmiposg_CI_eqv _ P 
; A_po_lte           := A_bmiposg_CI_lte _ P 
; A_po_exists_top_d  := inl (A_extract_exist_top_from_exists_top_ann_equal _ _ _ _ top_ann ) 
; A_po_exists_bottom := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bot_id 
; A_po_proofs        := A_bmiposg_CI_lte_proofs _ P 
; A_po_ast           := A_bmiposg_CI_ast _ P (* FIX *)
|}.  

Definition A_po_from_bounded_join_semilattice
           (S : Type)
           (P : A_bounded_join_semilattice S) : A_po S :=
let B := A_bjsl_top_bottom _ P in 
let bot_id := A_bounded_bottom_id _ _ _ _ B in
let top_ann := A_bounded_top_ann _ _ _ _ B in 
{|
  A_po_eqv           := A_bjsl_eqv _ P 
; A_po_lte           := A_bjsl_lte _ P 
; A_po_exists_top_d  := inl (A_extract_exist_top_from_exists_top_ann_equal _ _ _ _ top_ann ) 
; A_po_exists_bottom := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bot_id 
; A_po_proofs        := A_bjsl_lte_proofs _ P 
; A_po_ast           := A_bjsl_ast _ P (* FIX *)
|}.  
  

End Projections.   
  
End ACAS.

Section AMCAS.

Inductive A_os_mcas S : Type :=
| A_OS_Error                            : string                               -> A_os_mcas S
| A_OS_posg                             : A_posg S                             -> A_os_mcas S
| A_OS_monotone_posg                    : A_monotone_posg S                    -> A_os_mcas S
| A_OS_monotone_increasing_posg         : A_monotone_increasing_posg S         -> A_os_mcas S
| A_OS_bounded_monotone_increasing_posg : A_bounded_monotone_increasing_posg S -> A_os_mcas S
.

Definition A_os_classify_bounded_monotone_increasing_posg (S : Type) (A : A_bounded_monotone_increasing_posg S) : A_os_mcas S :=
  A_OS_bounded_monotone_increasing_posg _ A.  


Definition A_os_classify_monotone_increasing_posg (S : Type) (A : A_monotone_increasing_posg S) : A_os_mcas S :=
  match A_bottom_top_bottom_id_d _ _ _ _ (A_miposg_top_bottom _ A),
        A_bottom_top_top_ann_d _ _ _ _ (A_miposg_top_bottom _ A) 
  with 
  | Bottom_Id_Proof_Equal _ _ _ _ P, Top_Ann_Proof_Equal _ _ _ _ Q =>
    A_os_classify_bounded_monotone_increasing_posg _
     {|
         A_bmiposg_eqv          := A_miposg_eqv _ A 
       ; A_bmiposg_lte          := A_miposg_lte _ A 
       ; A_bmiposg_times        := A_miposg_times _ A 
       ; A_bmiposg_lte_proofs   := A_miposg_lte_proofs _ A 
       ; A_bmiposg_times_proofs := A_miposg_times_proofs _ A 
       ; A_bmiposg_top_bottom   := {| A_bounded_bottom_id := P; A_bounded_top_ann := Q|}
       ; A_bmiposg_proofs       := A_miposg_proofs _ A 
       ; A_bmiposg_ast          := A_miposg_ast _ A 
     |}
  | _ , _ => A_OS_monotone_increasing_posg _ A
  end. 

Definition A_os_classify_monotone_posg (S : Type) (A : A_monotone_posg S) : A_os_mcas S :=
  let P := A_mposg_proofs _ A in 
  match A_mono_left_increasing_d _ _ _ P, A_mono_right_increasing_d _ _ _ P 
  with 
  | inl LI, inl RI =>
    A_os_classify_monotone_increasing_posg _ 
     {|
         A_miposg_eqv          := A_mposg_eqv _ A 
       ; A_miposg_lte          := A_mposg_lte _ A 
       ; A_miposg_times        := A_mposg_times _ A 
       ; A_miposg_lte_proofs   := A_mposg_lte_proofs _ A 
       ; A_miposg_times_proofs := A_mposg_times_proofs _ A 
       ; A_miposg_top_bottom   := A_mposg_top_bottom _ A 
       ; A_miposg_proofs       := {|
                                     A_mono_inc_left_monotonic   := A_mono_left_monotonic _ _ _ P 
                                   ; A_mono_inc_right_monotonic  := A_mono_right_monotonic _ _ _ P 
                                   ; A_mono_inc_left_increasing  := LI 
                                   ; A_mono_inc_right_increasing := RI 
                                   |} 
       ; A_miposg_ast          := A_mposg_ast _ A 
     |}
  | _ , _ => A_OS_monotone_posg _ A
  end. 


Definition A_os_classify_posg (S : Type) (A : A_posg S) : A_os_mcas S :=
  let P := A_posg_proofs _ A in 
  match A_posg_left_monotonic_d _ _ _ P, A_posg_right_monotonic_d _ _ _ P 
  with 
  | inl LM, inl RM =>
    A_os_classify_monotone_posg _     
     {|
         A_mposg_eqv          := A_posg_eqv _ A 
       ; A_mposg_lte          := A_posg_lte _ A 
       ; A_mposg_times        := A_posg_times _ A 
       ; A_mposg_lte_proofs   := A_posg_lte_proofs _ A 
       ; A_mposg_times_proofs := A_posg_times_proofs _ A 
       ; A_mposg_top_bottom   := A_posg_bottom_top_proofs _ A 
       ; A_mposg_proofs       := {|
                                     A_mono_left_monotonic   := LM 
                                   ; A_mono_right_monotonic  := RM 
                                   ; A_mono_left_increasing_d  := A_posg_left_increasing_d _ _ _ P 
                                   ; A_mono_right_increasing_d := A_posg_right_increasing_d _ _ _ P 
                                   |} 
       ; A_mposg_ast          := A_posg_ast _ A 
     |}
  | _ , _ => A_OS_posg _ A
  end. 


Definition A_os_classify (S : Type) (A : A_os_mcas S) : A_os_mcas S :=
match A with
| A_OS_Error _ _                            => A 
| A_OS_posg _ B                             => A_os_classify_posg _ B 
| A_OS_monotone_posg _ B                    => A_os_classify_monotone_posg _ B 
| A_OS_monotone_increasing_posg _ B         => A_os_classify_monotone_increasing_posg _ B 
| A_OS_bounded_monotone_increasing_posg _ B => A_os_classify_bounded_monotone_increasing_posg _ B 
end.     


End AMCAS.                                                   



Section CAS.


Record os_bottom_top_certs {S: Type} :=
{
  bottom_top_bottom_id_d : @os_exists_bottom_id_certificate S
; bottom_top_top_ann_d   : @os_exists_top_ann_certificate S
}.

Record os_bottom_is_id_certs {S: Type}  :=
{
  bottom_is_id           : @os_exists_bottom_id_equal S
; bottom_is_id_top_ann_d : @os_exists_top_ann_certificate S
}.

Record os_top_is_ann_certs {S: Type}  :=
{
  top_is_ann_bottom_id_d : @os_exists_bottom_id_certificate S
; top_is_ann             : @os_exists_top_ann_equal S
}.

Record os_bounded_certs {S: Type}  :=
{
  bounded_bottom_id : @os_exists_bottom_id_equal S
; bounded_top_ann   : @os_exists_top_ann_equal S
}.

Record os_certificates {S: Type} := 
{
  posg_left_monotonic_d            : @check_left_monotone S 
; posg_right_monotonic_d           : @check_right_monotone S

; posg_left_increasing_d           : @check_left_increasing S
; posg_right_increasing_d          : @check_right_increasing S

; posg_left_strictly_increasing_d  : @check_left_strictly_increasing S
; posg_right_strictly_increasing_d : @check_right_strictly_increasing S
}.


Record os_monotone_certificates (S: Type) := 
{
  mono_left_monotonic              : @assert_left_monotone S
; mono_right_monotonic             : @assert_right_monotone S

; mono_left_increasing_d           : @check_left_increasing S
; mono_right_increasing_d          : @check_right_increasing S

}. 

Record os_monotone_increasing_certificates {S: Type} := 
{
  mono_inc_left_monotonic              : @assert_left_monotone S
; mono_inc_right_monotonic             : @assert_right_monotone S 
; mono_inc_left_increasing             : @assert_left_increasing S
; mono_inc_right_increasing            : @assert_right_increasing S
}.


Record posg {S : Type} := {
  posg_eqv              : @eqv S 
; posg_lte              : @brel S 
; posg_times            : @binary_op S 
; posg_lte_certs        : @po_certificates S 
; posg_times_certs      : @msg_certificates S 
; posg_bottom_top_certs : @os_bottom_top_certs S 
; posg_certs            : @os_certificates S 
; posg_ast              : cas_ast
}.

Record monotone_posg {S : Type} := {
  mposg_eqv          : @eqv S 
; mposg_lte          : @brel S 
; mposg_times        : @binary_op S 
; mposg_lte_certs    : @po_certificates S 
; mposg_times_certs  : @msg_certificates S 
; mposg_top_bottom   : @os_bottom_top_certs S 
; mposg_certs        : @os_monotone_certificates S 
; mposg_ast          : cas_ast
}.

Record monotone_increasing_posg (S : Type) := {
  miposg_eqv          : @eqv S 
; miposg_lte          : @brel S 
; miposg_times        : @binary_op S 
; miposg_lte_certs    : @po_certificates S 
; miposg_times_certs  : @msg_certificates S 
; miposg_top_bottom   : @os_bottom_top_certs S 
; miposg_certs        : @os_monotone_increasing_certificates S 
; miposg_ast          : cas_ast
}.


Record bounded_monotone_increasing_posg {S : Type} :=
{
  bmiposg_eqv         : @eqv S 
; bmiposg_lte         : @brel S 
; bmiposg_times       : @binary_op S 
; bmiposg_lte_certs   : @po_certificates S 
; bmiposg_times_certs : @msg_certificates S 
; bmiposg_top_bottom  : @os_bounded_certs S 
; bmiposg_certs       : @os_monotone_increasing_certificates S 
; bmiposg_ast         : cas_ast 
}.

Record bounded_monotone_increasing_posg_CI {S : Type} := {
  bmiposg_CI_eqv          : @eqv S 
; bmiposg_CI_lte          : @brel S 
; bmiposg_CI_times        : @binary_op S 
; bmiposg_CI_lte_certs    : @po_certificates S 
; bmiposg_CI_times_certs  : @sg_CI_certificates S 
; bmiposg_CI_top_bottom   : @os_bounded_certs S
; bmiposg_CI_certs        : @os_monotone_increasing_certificates S
; bmiposg_CI_ast          : cas_ast
}.


Section Projections.
Definition po_from_bounded_monotone_increasing_posg
           {S : Type}
           (P : @bounded_monotone_increasing_posg S) : @po S :=
let B := bmiposg_top_bottom P in 
{|
  po_eqv           := bmiposg_eqv P 
; po_lte           := bmiposg_lte P 
; po_exists_top_d  := match bounded_bottom_id B with
                      | Assert_Os_Exists_Bottom_Id_Equal bot_id => Certify_Exists_Top bot_id
                      end
; po_exists_bottom := match bounded_top_ann B with 
                      | Assert_Os_Exists_Top_Ann_Equal top_ann => Assert_Exists_Bottom top_ann
                      end
; po_certs         := bmiposg_lte_certs P 
; po_ast           := bmiposg_ast P (* FIX *)
|}.  




End Projections.   

End CAS.

Section MCAS.

Inductive os_mcas {S : Type} :=
| OS_Error                            : string                              -> @os_mcas S
| OS_posg                             : @posg S                             -> @os_mcas S
| OS_monotone_posg                    : @monotone_posg S                    -> @os_mcas S
| OS_monotone_increasing_posg         : @monotone_increasing_posg S         -> @os_mcas S
| OS_bounded_monotone_increasing_posg : @bounded_monotone_increasing_posg S -> @os_mcas S
| OS_bounded_monotone_increasing_posg_CI : @bounded_monotone_increasing_posg_CI S -> @os_mcas S 
.

(* HELP : how to classify OS_bounded_monotone_increasing_posg_CI ??? *)

Definition os_classify_bounded_monotone_increasing_posg {S : Type} (A : @bounded_monotone_increasing_posg S) : @os_mcas S :=
  OS_bounded_monotone_increasing_posg A.  


Definition os_classify_monotone_increasing_posg {S : Type} (A : @monotone_increasing_posg S) : @os_mcas S :=
  match bottom_top_bottom_id_d (miposg_top_bottom _ A),
        bottom_top_top_ann_d (miposg_top_bottom _ A) 
  with 
  | Bottom_Id_Cert_Equal P, Top_Ann_Cert_Equal Q =>
    os_classify_bounded_monotone_increasing_posg 
     {|
         bmiposg_eqv          := miposg_eqv _ A 
       ; bmiposg_lte          := miposg_lte _ A 
       ; bmiposg_times        := miposg_times _ A 
       ; bmiposg_lte_certs    := miposg_lte_certs _ A 
       ; bmiposg_times_certs  := miposg_times_certs _ A 
       ; bmiposg_top_bottom   := {| bounded_bottom_id := Assert_Os_Exists_Bottom_Id_Equal P;
                                    bounded_top_ann := Assert_Os_Exists_Top_Ann_Equal Q|}
       ; bmiposg_certs        := miposg_certs _ A 
       ; bmiposg_ast          := miposg_ast _ A 
     |}
  | _ , _ => OS_monotone_increasing_posg A
  end. 

Definition os_classify_monotone_posg {S : Type} (A : @monotone_posg S) : @os_mcas S :=
  let P := mposg_certs A in 
  match mono_left_increasing_d _ P, mono_right_increasing_d _ P 
  with 
  | Certify_Left_Increasing, Certify_Right_Increasing => 
    os_classify_monotone_increasing_posg 
     {|
         miposg_eqv          := mposg_eqv A 
       ; miposg_lte          := mposg_lte A 
       ; miposg_times        := mposg_times A 
       ; miposg_lte_certs   := mposg_lte_certs A 
       ; miposg_times_certs := mposg_times_certs A 
       ; miposg_top_bottom   := mposg_top_bottom A 
       ; miposg_certs       := {|
                                     mono_inc_left_monotonic   := mono_left_monotonic _ P 
                                   ; mono_inc_right_monotonic  := mono_right_monotonic _ P 
                                   ; mono_inc_left_increasing  := Assert_Left_Increasing
                                   ; mono_inc_right_increasing := Assert_Right_Increasing
                                   |} 
       ; miposg_ast          := mposg_ast A 
     |}
  | _ , _ => OS_monotone_posg A
  end. 


Definition os_classify_posg {S : Type} (A : @posg S) : @os_mcas S :=
  let P := posg_certs A in 
  match posg_left_monotonic_d P, posg_right_monotonic_d P 
  with 
  | Certify_Left_Monotone, Certify_Right_Monotone => 
    os_classify_monotone_posg 
     {|
         mposg_eqv          := posg_eqv A 
       ; mposg_lte          := posg_lte A 
       ; mposg_times        := posg_times A 
       ; mposg_lte_certs   := posg_lte_certs A 
       ; mposg_times_certs := posg_times_certs A 
       ; mposg_top_bottom   := posg_bottom_top_certs A 
       ; mposg_certs       := {|
                                     mono_left_monotonic   := Assert_Left_Monotone 
                                   ; mono_right_monotonic  := Assert_Right_Monotone 
                                   ; mono_left_increasing_d  := posg_left_increasing_d P 
                                   ; mono_right_increasing_d := posg_right_increasing_d P 
                                   |} 
       ; mposg_ast          := posg_ast A 
     |}
  | _ , _ => OS_posg A
  end. 


Definition os_classify {S : Type} (A : @os_mcas S) : @os_mcas S :=
match A with
| OS_Error _                            => A 
| OS_posg B                             => os_classify_posg B 
| OS_monotone_posg B                    => os_classify_monotone_posg B 
| OS_monotone_increasing_posg B         => os_classify_monotone_increasing_posg B 
| OS_bounded_monotone_increasing_posg B => os_classify_bounded_monotone_increasing_posg B
| OS_bounded_monotone_increasing_posg_CI B => A 
end.     


End MCAS. 
  
Section Translation.

End Translation.   

Section Verify.
End Verify.   
