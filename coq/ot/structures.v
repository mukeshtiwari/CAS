Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties. 
Require Import CAS.coq.po.structures. 
Require Import CAS.coq.tr.structures. 
Require Import CAS.coq.ot.properties.

Section ACAS.


Record with_bottom_proofs (S: Type) (eq lte : brel S) := 
{
  A_with_bottom_exists_top_d       : brel_exists_qo_top_decidable S eq lte
; A_with_bottom_exists             : brel_exists_qo_bottom S eq lte 
}.
  
  
Record qoltr_msi_proofs (L S : Type) (lte : brel S) (ltr : L -> (S -> S)) :=
{
  A_qoltr_msi_monotone  : olt_monotone L S lte ltr 
; A_qoltr_msi_strictly_increasing  : olt_strictly_increasing L S lte ltr
}.


Record A_qoltr_monotone_strictly_increasing (L S : Type) :=
{
  A_qoltr_msi_carrier      : A_eqv S
; A_qoltr_msi_label        : A_eqv L
; A_qoltr_msi_lte          : brel S                                               
; A_qoltr_msi_ltr          : left_transform L S (* L -> (S -> S) *)
; A_qoltr_msi_lte_proofs   : qo_proofs S (A_eqv_eq S A_qoltr_msi_carrier) A_qoltr_msi_lte                                 
; A_qoltr_msi_ltr_proofs   : ltr_proofs L S (A_eqv_eq S A_qoltr_msi_carrier) (A_eqv_eq L A_qoltr_msi_label)  A_qoltr_msi_ltr
; A_qoltr_msi_bottom_proofs : with_bottom_proofs S (A_eqv_eq S A_qoltr_msi_carrier) A_qoltr_msi_lte                                           
; A_qoltr_msi_proofs       : qoltr_msi_proofs L S A_qoltr_msi_lte A_qoltr_msi_ltr                                  
; A_qoltr_msi_ast          : cas_ast 
}.



Record A_wpltr_monotone_strictly_increasing (L S : Type) :=
{
  A_wpltr_msi_carrier      : A_eqv S
; A_wpltr_msi_label        : A_eqv L
; A_wpltr_msi_lte          : brel S                                               
; A_wpltr_msi_ltr          : left_transform L S (* L -> (S -> S) *)
; A_wpltr_msi_lte_proofs   : wp_proofs S (A_eqv_eq S A_wpltr_msi_carrier) A_wpltr_msi_lte                                 
; A_wpltr_msi_ltr_proofs   : ltr_proofs L S (A_eqv_eq S A_wpltr_msi_carrier) (A_eqv_eq L A_wpltr_msi_label)  A_wpltr_msi_ltr
; A_wpltr_msi_bottom_proofs : with_bottom_proofs S (A_eqv_eq S A_wpltr_msi_carrier) A_wpltr_msi_lte                                           
; A_wpltr_msi_proofs       : qoltr_msi_proofs L S A_wpltr_msi_lte A_wpltr_msi_ltr                                  
; A_wpltr_msi_ast          : cas_ast 
}.



Record poltr_mi_proofs (L S : Type) (lte : brel S) (ltr : L -> (S -> S)) :=
{
  A_poltr_mi_monotone    : olt_monotone L S lte ltr 
; A_poltr_mi_increasing  : olt_increasing L S lte ltr
}.


Record A_poltr_monotone_increasing (L S : Type) :=
{
  A_poltr_mi_carrier      : A_eqv S
; A_poltr_mi_label        : A_eqv L
; A_poltr_mi_lte          : brel S                                               
; A_poltr_mi_ltr          : left_transform L S (* L -> (S -> S) *)
; A_poltr_mi_lte_proofs   : po_proofs S (A_eqv_eq S A_poltr_mi_carrier) A_poltr_mi_lte                                 
; A_poltr_mi_ltr_proofs   : ltr_proofs L S (A_eqv_eq S A_poltr_mi_carrier) (A_eqv_eq L A_poltr_mi_label)  A_poltr_mi_ltr
; A_poltr_mi_bottom_proofs : with_bottom_proofs S (A_eqv_eq S A_poltr_mi_carrier) A_poltr_mi_lte                                 
; A_poltr_mi_proofs       : poltr_mi_proofs L S A_poltr_mi_lte A_poltr_mi_ltr                                  
; A_poltr_mi_ast          : cas_ast 
}.



End ACAS. 


Section CAS.


Record with_bottom_certs {S: Type} := 
{
  with_bottom_exists_top_d  : @check_exists_qo_top S 
; with_bottom_exists        : @assert_exists_qo_bottom S 
}.
  

Record qoltr_msi_certificates {L S : Type} :=
{
  qoltr_msi_monotone             : @assert_olt_monotone L S 
; qoltr_msi_strictly_increasing  : @assert_olt_strictly_increasing L S 
}.



Record qoltr_monotone_strictly_increasing {L S : Type} :=
{
  qoltr_msi_carrier      : @eqv S
; qoltr_msi_label        : @eqv L
; qoltr_msi_lte          : @brel S                                               
; qoltr_msi_ltr          : @left_transform L S 
; qoltr_msi_lte_certs    : @qo_certificates S 
; qoltr_msi_ltr_certs    : @ltr_certificates L S
; qoltr_msi_bottom_certs : @with_bottom_certs S                                                                                          
; qoltr_msi_certs        : @qoltr_msi_certificates L S
; qoltr_msi_ast          : cas_ast 
}.



Record wpltr_monotone_strictly_increasing {L S : Type} :=
{
  wpltr_msi_carrier      : @eqv S
; wpltr_msi_label        : @eqv L
; wpltr_msi_lte          : @brel S                                               
; wpltr_msi_ltr          : @left_transform L S 
; wpltr_msi_lte_certs    : @wp_certificates S
; wpltr_msi_ltr_certs    : @ltr_certificates L S
; wpltr_msi_bottom_certs : @with_bottom_certs S                                             
; wpltr_msi_certs        : @qoltr_msi_certificates L S
; wpltr_msi_ast          : cas_ast 
}.

Record poltr_mi_certificates {L S : Type} := 
{
  poltr_mi_monotone    : @assert_olt_monotone L S 
; poltr_mi_increasing  : @assert_olt_increasing L S 
}.


Record poltr_monotone_increasing {L S : Type} :=
{
  poltr_mi_carrier      : @eqv S
; poltr_mi_label        : @eqv L
; poltr_mi_lte          : @brel S                                               
; poltr_mi_ltr          : @left_transform L S 
; poltr_mi_lte_certs    : @po_certificates S 
; poltr_mi_ltr_certs    : @ltr_certificates L S
; poltr_mi_bottom_certs : @with_bottom_certs S                                                                                         
; poltr_mi_certs        : @poltr_mi_certificates L S 
; poltr_mi_ast          : cas_ast 
}.

End CAS.


Section Translate.

Definition P2C_with_bottom  (S: Type) (eq lte : brel S) (P : with_bottom_proofs S eq lte) := 
{|
  with_bottom_exists_top_d       := p2c_exists_qo_top_check _ _ _ (A_with_bottom_exists_top_d _ _ _ P)
; with_bottom_exists             := p2c_exists_qo_bottom_assert _ _ _ (A_with_bottom_exists _ _ _ P)
|}.
  


Definition P2C_qoltr_msi (L S : Type) (lte : brel S) (ltr : left_transform L S) (P : qoltr_msi_proofs L S lte ltr) :=
{|
  qoltr_msi_monotone             := @Assert_Olt_Monotone L S 
; qoltr_msi_strictly_increasing  := @Assert_Olt_Strictly_Increasing L S 
|}.



    
Definition A2C_qoltr_monotone_strictly_increasing (L S : Type) (Q : A_qoltr_monotone_strictly_increasing L S) := 
{|
  qoltr_msi_carrier      := A2C_eqv S (A_qoltr_msi_carrier L S Q) 
; qoltr_msi_label        := A2C_eqv L (A_qoltr_msi_label L S Q) 
; qoltr_msi_lte          := A_qoltr_msi_lte L S Q
; qoltr_msi_ltr          := A_qoltr_msi_ltr L S Q
; qoltr_msi_lte_certs    := P2C_qo S _ _ (A_qoltr_msi_lte_proofs L S Q)
; qoltr_msi_ltr_certs    := P2C_ltr L S _ _ _ (A_qoltr_msi_ltr_proofs L S Q)
; qoltr_msi_bottom_certs := P2C_with_bottom _ _ _ (A_qoltr_msi_bottom_proofs L S Q)
; qoltr_msi_certs        := P2C_qoltr_msi L S _ _ (A_qoltr_msi_proofs L S Q)
; qoltr_msi_ast          := A_qoltr_msi_ast L S Q
|}.


Definition A2C_wpltr_monotone_strictly_increasing (L S : Type) (Q : A_wpltr_monotone_strictly_increasing L S) := 
{|
  wpltr_msi_carrier      := A2C_eqv S (A_wpltr_msi_carrier L S Q) 
; wpltr_msi_label        := A2C_eqv L (A_wpltr_msi_label L S Q) 
; wpltr_msi_lte          := A_wpltr_msi_lte L S Q
; wpltr_msi_ltr          := A_wpltr_msi_ltr L S Q
; wpltr_msi_lte_certs    := P2C_wp S _ _ (A_wpltr_msi_lte_proofs L S Q)
; wpltr_msi_ltr_certs    := P2C_ltr L S _ _ _ (A_wpltr_msi_ltr_proofs L S Q)
; wpltr_msi_bottom_certs := P2C_with_bottom _ _ _ (A_wpltr_msi_bottom_proofs L S Q)                                    
; wpltr_msi_certs        := P2C_qoltr_msi L S _ _ (A_wpltr_msi_proofs L S Q)
; wpltr_msi_ast          := A_wpltr_msi_ast L S Q
|}.

Definition P2C_poltr_mi (L S : Type) (lte : brel S) (ltr : L -> (S -> S)) (P : poltr_mi_proofs L S lte ltr) := 
{|
  poltr_mi_monotone    := @Assert_Olt_Monotone L S 
; poltr_mi_increasing  := @Assert_Olt_Increasing L S 
|}.
  
Definition A2C_poltr_monotone_increasing (L S : Type) (P : A_poltr_monotone_increasing L S) :=
{|
  poltr_mi_carrier     := A2C_eqv S (A_poltr_mi_carrier L S P) 
; poltr_mi_label       := A2C_eqv L (A_poltr_mi_label L S P) 
; poltr_mi_lte         := A_poltr_mi_lte L S P 
; poltr_mi_ltr         := A_poltr_mi_ltr L S P 
; poltr_mi_lte_certs   := P2C_po S _ _  (A_poltr_mi_lte_proofs L S P)
; poltr_mi_ltr_certs   := P2C_ltr L S _ _  _ (A_poltr_mi_ltr_proofs L S P)
; poltr_mi_bottom_certs := P2C_with_bottom _ _ _ (A_poltr_mi_bottom_proofs L S P)                                                                      
; poltr_mi_certs       := P2C_poltr_mi L S _ _ (A_poltr_mi_proofs L S P) 
; poltr_mi_ast         := A_poltr_mi_ast L S P 
|}.


End Translate.