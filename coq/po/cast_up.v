Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory. 
Require Import CAS.coq.po.structures.

Section ACAS.
 

Section Proofs.

Variables (S : Type)
          (eq lte : brel S)
          (wS : S)
          (f : S -> S) 
          (nt : brel_not_trivial S eq f). 


Definition or_proofs_from_po_proofs (d : po_proofs S eq lte) :=
let anti := (A_po_antisymmetric _ _ _ d ) in   
{|  
  A_or_congruence      := A_po_congruence _ _ _ d 
; A_or_reflexive       := A_po_reflexive _ _ _ d 
; A_or_transitive      := A_po_transitive _ _ _ d 
; A_or_antisymmetric_d := inl anti 
; A_or_total_d         := inr (A_po_not_total _ _ _ d )
; A_or_trivial_d       := inr (antisymmetric_implies_order_not_trivial S eq lte wS f nt anti)                              
|}.


Definition or_proofs_from_to_proofs (d : to_proofs S eq lte) :=
let anti := (A_to_antisymmetric _ _ _ d ) in     
{|  
  A_or_congruence      := A_to_congruence _ _ _ d 
; A_or_reflexive       := A_to_reflexive _ _ _ d 
; A_or_transitive      := A_to_transitive _ _ _ d 
; A_or_antisymmetric_d := inl anti
; A_or_total_d         := inl (A_to_total _ _ _ d )
; A_or_trivial_d       := inr (antisymmetric_implies_order_not_trivial S eq lte wS f nt anti)                                                            
|}.


Definition or_proofs_from_qo_proofs (d : qo_proofs S eq lte) :=
let ntot := A_qo_not_total _ _ _ d in 
{|  
  A_or_congruence      := A_qo_congruence _ _ _ d 
; A_or_reflexive       := A_qo_reflexive _ _ _ d 
; A_or_transitive      := A_qo_transitive _ _ _ d 
; A_or_antisymmetric_d := inr (A_qo_not_antisymmetric _ _ _ d )
; A_or_total_d         := inr ntot 
; A_or_trivial_d       := inr (order_not_total_implies_not_trivial S lte ntot)
|}.

Definition or_proofs_from_wo_proofs (d : wo_proofs S eq lte) :=
{|  
  A_or_congruence      := A_wo_congruence _ _ _ d 
; A_or_reflexive       := A_wo_reflexive _ _ _ d 
; A_or_transitive      := A_wo_transitive _ _ _ d 
; A_or_antisymmetric_d := inr (A_wo_not_antisymmetric _ _ _ d )
; A_or_total_d         := inl (A_wo_total _ _ _ d )
; A_or_trivial_d       := A_wo_trivial_d  _ _ _ d 
|}.

End Proofs.
  

Section Combinators.


Definition A_or_from_po {S : Type} (A : A_po S) :=
let eqv := A_po_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
{|    
  A_or_eqv             := eqv 
; A_or_lte             := A_po_lte _ A 
; A_or_exists_top_d    := inr (brel_not_exists_qo_top_from_brel_not_exists_top _ _ _ (A_po_not_exists_top _ A))
; A_or_exists_bottom_d := inr (brel_not_exists_qo_bottom_from_brel_not_exists_bottom _ _ _ (A_po_not_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_po_proofs _ _ _ wS f nt (A_po_proofs _ A) 
; A_or_ast             := A_po_ast _ A 
|}.

Definition A_or_from_po_with_bottom {S : Type} (A : A_po_with_bottom S) :=
let eqv := A_po_wb_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
let anti := A_po_antisymmetric _ _ _ (A_po_wb_proofs _ A) in       
{|    
  A_or_eqv             := A_po_wb_eqv _ A 
; A_or_lte             := A_po_wb_lte _ A 
; A_or_exists_top_d    := inr (brel_not_exists_qo_top_from_brel_not_exists_top _ _ _ (A_po_wb_not_exists_top _ A))
; A_or_exists_bottom_d := inl (brel_exists_qo_bottom_from_brel_exists_bottom _ _ _ anti (A_po_wb_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_po_proofs _ _ _ wS f nt (A_po_wb_proofs _ A) 
; A_or_ast             := A_po_wb_ast _ A 
|}.


Definition A_or_from_po_with_top {S : Type} (A : A_po_with_top S) :=
let eqv := A_po_wt_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
let anti := A_po_antisymmetric _ _ _ (A_po_wt_proofs _ A) in       
{|    
  A_or_eqv             := A_po_wt_eqv _ A 
; A_or_lte             := A_po_wt_lte _ A 
; A_or_exists_top_d    := inl (brel_exists_qo_top_from_brel_exists_top _ _ _ anti (A_po_wt_exists_top _ A))
; A_or_exists_bottom_d := inr (brel_not_exists_qo_bottom_from_brel_not_exists_bottom _ _ _ (A_po_wt_not_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_po_proofs _ _ _ wS f nt (A_po_wt_proofs _ A) 
; A_or_ast             := A_po_wt_ast _ A 
|}.

Definition A_or_from_po_bounded {S : Type} (A : A_po_bounded S) :=
let eqv := A_po_bd_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
let anti := A_po_antisymmetric _ _ _ (A_po_bd_proofs _ A) in       
{|    
  A_or_eqv             := A_po_bd_eqv _ A 
; A_or_lte             := A_po_bd_lte _ A 
; A_or_exists_top_d    := inl (brel_exists_qo_top_from_brel_exists_top _ _ _ anti (A_po_bd_exists_top _ A))
; A_or_exists_bottom_d := inl (brel_exists_qo_bottom_from_brel_exists_bottom _ _ _ anti (A_po_bd_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_po_proofs _ _ _ wS f nt (A_po_bd_proofs _ A) 
; A_or_ast             := A_po_bd_ast _ A 
|}.

Definition A_or_from_to {S : Type} (A : A_to S) :=
let eqv := A_to_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
{|    
  A_or_eqv             := A_to_eqv _ A 
; A_or_lte             := A_to_lte _ A 
; A_or_exists_top_d    := inr (brel_not_exists_qo_top_from_brel_not_exists_top _ _ _ (A_to_not_exists_top _ A))
; A_or_exists_bottom_d := inr (brel_not_exists_qo_bottom_from_brel_not_exists_bottom _ _ _ (A_to_not_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_to_proofs _ _ _ wS f nt (A_to_proofs _ A) 
; A_or_ast             := A_to_ast _ A 
|}.

Definition A_or_from_to_with_bottom {S : Type} (A : A_to_with_bottom S) :=
let eqv := A_to_wb_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in  
let anti := A_to_antisymmetric _ _ _ (A_to_wb_proofs _ A) in       
{|    
  A_or_eqv             := A_to_wb_eqv _ A 
; A_or_lte             := A_to_wb_lte _ A 
; A_or_exists_top_d    := inr (brel_not_exists_qo_top_from_brel_not_exists_top _ _ _ (A_to_wb_not_exists_top _ A))
; A_or_exists_bottom_d := inl (brel_exists_qo_bottom_from_brel_exists_bottom _ _ _ anti (A_to_wb_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_to_proofs _ _ _ wS f nt (A_to_wb_proofs _ A) 
; A_or_ast             := A_to_wb_ast _ A 
|}.


Definition A_or_from_to_with_top {S : Type} (A : A_to_with_top S) :=
let eqv := A_to_wt_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in  
let anti := A_to_antisymmetric _ _ _ (A_to_wt_proofs _ A) in       
{|    
  A_or_eqv             := A_to_wt_eqv _ A 
; A_or_lte             := A_to_wt_lte _ A 
; A_or_exists_top_d    := inl (brel_exists_qo_top_from_brel_exists_top _ _ _ anti (A_to_wt_exists_top _ A))
; A_or_exists_bottom_d := inr (brel_not_exists_qo_bottom_from_brel_not_exists_bottom _ _ _ (A_to_wt_not_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_to_proofs _ _ _ wS f nt (A_to_wt_proofs _ A) 
; A_or_ast             := A_to_wt_ast _ A 
|}.

Definition A_or_from_to_bounded {S : Type} (A : A_to_bounded S) :=
let eqv := A_to_bd_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in  
let anti := A_to_antisymmetric _ _ _ (A_to_bd_proofs _ A) in       
{|    
  A_or_eqv             := A_to_bd_eqv _ A 
; A_or_lte             := A_to_bd_lte _ A 
; A_or_exists_top_d    := inl (brel_exists_qo_top_from_brel_exists_top _ _ _ anti (A_to_bd_exists_top _ A))
; A_or_exists_bottom_d := inl (brel_exists_qo_bottom_from_brel_exists_bottom _ _ _ anti (A_to_bd_exists_bottom _ A))
; A_or_proofs          := or_proofs_from_to_proofs _ _ _ wS f nt (A_to_bd_proofs _ A) 
; A_or_ast             := A_to_bd_ast _ A 
|}.


Definition A_or_from_qo {S : Type} (A : A_qo S) :=
{|    
  A_or_eqv             := A_qo_eqv _ A 
; A_or_lte             := A_qo_lte _ A 
; A_or_exists_top_d    := inr (A_qo_not_exists_top _ A)
; A_or_exists_bottom_d := inr (A_qo_not_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_qo_proofs _ _ _ (A_qo_proofs _ A) 
; A_or_ast             := A_qo_ast _ A 
|}.

Definition A_or_from_qo_with_bottom {S : Type} (A : A_qo_with_bottom S) :=
{|    
  A_or_eqv             := A_qo_wb_eqv _ A 
; A_or_lte             := A_qo_wb_lte _ A 
; A_or_exists_top_d    := inr (A_qo_wb_not_exists_top _ A)
; A_or_exists_bottom_d := inl (A_qo_wb_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_qo_proofs _ _ _ (A_qo_wb_proofs _ A) 
; A_or_ast             := A_qo_wb_ast _ A 
|}.


Definition A_or_from_qo_with_top {S : Type} (A : A_qo_with_top S) :=
{|    
  A_or_eqv             := A_qo_wt_eqv _ A 
; A_or_lte             := A_qo_wt_lte _ A 
; A_or_exists_top_d    := inl (A_qo_wt_exists_top _ A)
; A_or_exists_bottom_d := inr (A_qo_wt_not_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_qo_proofs _ _ _ (A_qo_wt_proofs _ A) 
; A_or_ast             := A_qo_wt_ast _ A 
|}.

Definition A_or_from_qo_bounded {S : Type} (A : A_qo_bounded S) :=
{|    
  A_or_eqv             := A_qo_bd_eqv _ A 
; A_or_lte             := A_qo_bd_lte _ A 
; A_or_exists_top_d    := inl (A_qo_bd_exists_top _ A)
; A_or_exists_bottom_d := inl (A_qo_bd_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_qo_proofs _ _ _ (A_qo_bd_proofs _ A) 
; A_or_ast             := A_qo_bd_ast _ A 
|}.


Definition A_or_from_wo {S : Type} (A : A_wo S) :=
{|    
  A_or_eqv             := A_wo_eqv _ A 
; A_or_lte             := A_wo_lte _ A 
; A_or_exists_top_d    := inr (A_wo_not_exists_top _ A)
; A_or_exists_bottom_d := inr (A_wo_not_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_wo_proofs _ _ _ (A_wo_proofs _ A) 
; A_or_ast             := A_wo_ast _ A 
|}.

Definition A_or_from_wo_with_bottom {S : Type} (A : A_wo_with_bottom S) :=
{|    
  A_or_eqv             := A_wo_wb_eqv _ A 
; A_or_lte             := A_wo_wb_lte _ A 
; A_or_exists_top_d    := inr (A_wo_wb_not_exists_top _ A)
; A_or_exists_bottom_d := inl (A_wo_wb_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_wo_proofs _ _ _ (A_wo_wb_proofs _ A) 
; A_or_ast             := A_wo_wb_ast _ A 
|}.


Definition A_or_from_wo_with_top {S : Type} (A : A_wo_with_top S) :=
{|    
  A_or_eqv             := A_wo_wt_eqv _ A 
; A_or_lte             := A_wo_wt_lte _ A 
; A_or_exists_top_d    := inl (A_wo_wt_exists_top _ A)
; A_or_exists_bottom_d := inr (A_wo_wt_not_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_wo_proofs _ _ _ (A_wo_wt_proofs _ A) 
; A_or_ast             := A_wo_wt_ast _ A 
|}.

Definition A_or_from_wo_bounded {S : Type} (A : A_wo_bounded S) :=
{|    
  A_or_eqv             := A_wo_bd_eqv _ A 
; A_or_lte             := A_wo_bd_lte _ A 
; A_or_exists_top_d    := inl (A_wo_bd_exists_top _ A)
; A_or_exists_bottom_d := inl (A_wo_bd_exists_bottom _ A)
; A_or_proofs          := or_proofs_from_wo_proofs _ _ _ (A_wo_bd_proofs _ A) 
; A_or_ast             := A_wo_bd_ast _ A 
|}.
  

End Combinators. 

End ACAS.


Section AMCAS.
  
Definition A_or_mcas_cast_up {S : Type} (A : @A_or_mcas S) : @A_or_mcas S :=
match A with
  | A_OR_Error          _ => A 
  | A_OR_or             _ => A
  | A_OR_po             B => A_OR_or(A_or_from_po B)
  | A_OR_po_with_bottom B => A_OR_or(A_or_from_po_with_bottom B)
  | A_OR_po_with_top    B => A_OR_or(A_or_from_po_with_top B)
  | A_OR_po_bounded     B => A_OR_or(A_or_from_po_bounded B)
  | A_OR_to             B => A_OR_or(A_or_from_to B)
  | A_OR_to_with_bottom B => A_OR_or(A_or_from_to_with_bottom B)
  | A_OR_to_with_top    B => A_OR_or(A_or_from_to_with_top B)
  | A_OR_to_bounded     B => A_OR_or(A_or_from_to_bounded B)
  | A_OR_qo             B => A_OR_or(A_or_from_qo B)
  | A_OR_qo_with_bottom B => A_OR_or(A_or_from_qo_with_bottom B)
  | A_OR_qo_with_top    B => A_OR_or(A_or_from_qo_with_top B)
  | A_OR_qo_bounded     B => A_OR_or(A_or_from_qo_bounded B)
  | A_OR_wo             B => A_OR_or(A_or_from_wo B)
  | A_OR_wo_with_bottom B => A_OR_or(A_or_from_wo_with_bottom B)
  | A_OR_wo_with_top    B => A_OR_or(A_or_from_wo_with_top B)
  | A_OR_wo_bounded     B => A_OR_or(A_or_from_wo_bounded B)
end.    
End AMCAS.

Section CAS.

Section Certificates.

Definition or_certs_from_po_certs {S : Type} (wS : S) (f : S -> S) (lte : brel S) (d : @po_certificates S) :=
{|  
  or_congruence      := po_congruence d 
; or_reflexive       := po_reflexive d 
; or_transitive      := po_transitive d 
; or_antisymmetric_d := match po_antisymmetric d with
                        | Assert_Antisymmetric => Certify_Antisymmetric
                        end 
; or_total_d         := match po_not_total d with
                        | Assert_Not_Total p => Certify_Not_Total p 
                        end
; or_trivial_d       := Certify_Order_Not_Trivial (witness_antisymmetric_implies_order_not_trivial _ lte wS f)                          
|}.

Definition or_certs_from_to_certs {S : Type} (wS : S) (f : S -> S) (lte : brel S) (d : @to_certificates S) :=
{|  
  or_congruence      := to_congruence d 
; or_reflexive       := to_reflexive d 
; or_transitive      := to_transitive d 
; or_antisymmetric_d := match to_antisymmetric d with
                        | Assert_Antisymmetric => Certify_Antisymmetric
                        end 
; or_total_d         := match to_total d with
                        | Assert_Total => Certify_Total
                        end
; or_trivial_d       := Certify_Order_Not_Trivial (witness_antisymmetric_implies_order_not_trivial _ lte wS f)                           
|}.

Definition or_certs_from_qo_certs {S : Type} (d : @qo_certificates S) :=
{|  
  or_congruence      := qo_congruence d 
; or_reflexive       := qo_reflexive d 
; or_transitive      := qo_transitive d 
; or_antisymmetric_d := match qo_not_antisymmetric d with
                        | Assert_Not_Antisymmetric p => Certify_Not_Antisymmetric p
                        end 
; or_total_d         := match qo_not_total d with
                        | Assert_Not_Total p => Certify_Not_Total p 
                        end
; or_trivial_d       := match qo_not_total d with
                        | Assert_Not_Total p => Certify_Order_Not_Trivial p 
                        end                          
|}.

Definition or_certs_from_wo_certs {S : Type} (d : @wo_certificates S) :=
{|  
  or_congruence      := wo_congruence d 
; or_reflexive       := wo_reflexive d 
; or_transitive      := wo_transitive d 
; or_antisymmetric_d := match wo_not_antisymmetric d with
                        | Assert_Not_Antisymmetric p => Certify_Not_Antisymmetric p
                        end 
; or_total_d         := match wo_total d with
                        | Assert_Total => Certify_Total
                        end
; or_trivial_d       := wo_trivial_d d
|}.

End Certificates. 

Section Combinators.

Definition or_from_po {S : Type} (A : @po S) :=
let lte  := po_lte A in
let eqv  := po_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in
{|    
  or_eqv             := po_eqv A 
; or_lte             := po_lte A 
; or_exists_top_d    := match po_not_exists_top A with
                        | Assert_Not_Exists_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match po_not_exists_bottom A with
                        | Assert_Not_Exists_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs           := or_certs_from_po_certs wS f lte (po_certs A) 
; or_ast             := po_ast A 
|}.

Definition or_from_po_with_bottom {S : Type} (A : @po_with_bottom S) :=
let lte  := po_wb_lte A in
let eqv  := po_wb_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in
{|    
  or_eqv             := po_wb_eqv A 
; or_lte             := po_wb_lte A 
; or_exists_top_d    := match po_wb_not_exists_top A with
                        | Assert_Not_Exists_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match po_wb_exists_bottom A with
                        | Assert_Exists_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_po_certs wS f lte (po_wb_certs A) 
; or_ast             := po_wb_ast A 
|}.


Definition or_from_po_with_top {S : Type} (A : @po_with_top S) :=
let lte  := po_wt_lte A in
let eqv  := po_wt_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in
let anti := po_antisymmetric  (po_wt_certs A) in       
{|    
  or_eqv             := po_wt_eqv A 
; or_lte             := po_wt_lte A 
; or_exists_top_d    := match po_wt_exists_top A with
                        | Assert_Exists_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match po_wt_not_exists_bottom A with
                        | Assert_Not_Exists_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs           := or_certs_from_po_certs wS f lte (po_wt_certs A) 
; or_ast             := po_wt_ast A 
|}.

Definition or_from_po_bounded {S : Type} (A : @po_bounded S) :=
let lte  := po_bd_lte A in
let eqv  := po_bd_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in
{|    
  or_eqv             := po_bd_eqv A 
; or_lte             := po_bd_lte A 
; or_exists_top_d    := match po_bd_exists_top A with
                        | Assert_Exists_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match po_bd_exists_bottom A with
                        | Assert_Exists_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_po_certs  wS f lte (po_bd_certs A) 
; or_ast             := po_bd_ast A 
|}.

Definition or_from_to {S : Type} (A : @to S) :=
let lte  := to_lte A in
let eqv  := to_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in  
{|    
  or_eqv             := to_eqv A 
; or_lte             := to_lte A 
; or_exists_top_d    := match to_not_exists_top A with
                        | Assert_Not_Exists_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match to_not_exists_bottom A with
                        | Assert_Not_Exists_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs           := or_certs_from_to_certs wS f lte (to_certs A) 
; or_ast             := to_ast A 
|}.

Definition or_from_to_with_bottom {S : Type} (A : @to_with_bottom S) :=
let lte  := to_wb_lte A in
let eqv  := to_wb_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in    
let anti := to_antisymmetric  (to_wb_certs A) in       
{|    
  or_eqv             := to_wb_eqv A 
; or_lte             := to_wb_lte A 
; or_exists_top_d    := match to_wb_not_exists_top A with
                        | Assert_Not_Exists_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match to_wb_exists_bottom A with
                        | Assert_Exists_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_to_certs wS f lte (to_wb_certs A) 
; or_ast             := to_wb_ast A 
|}.


Definition or_from_to_with_top {S : Type} (A : @to_with_top S) :=
let lte  := to_wt_lte A in
let eqv  := to_wt_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in    
let anti := to_antisymmetric  (to_wt_certs A) in       
{|    
  or_eqv             := to_wt_eqv A 
; or_lte             := to_wt_lte A 
; or_exists_top_d    := match to_wt_exists_top A with
                        | Assert_Exists_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match to_wt_not_exists_bottom A with
                        | Assert_Not_Exists_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs          := or_certs_from_to_certs wS f lte (to_wt_certs A) 
; or_ast             := to_wt_ast A 
|}.

Definition or_from_to_bounded {S : Type} (A : @to_bounded S) :=
let lte  := to_bd_lte A in
let eqv  := to_bd_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in    
let anti := to_antisymmetric  (to_bd_certs A) in       
{|    
  or_eqv             := to_bd_eqv A 
; or_lte             := to_bd_lte A 
; or_exists_top_d    := match to_bd_exists_top A with
                        | Assert_Exists_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match to_bd_exists_bottom A with
                        | Assert_Exists_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs          := or_certs_from_to_certs wS f lte  (to_bd_certs A) 
; or_ast             := to_bd_ast A 
|}.


Definition or_from_qo {S : Type} (A : @qo S) :=
{|    
  or_eqv             := qo_eqv A 
; or_lte             := qo_lte A 
; or_exists_top_d    := match qo_not_exists_top A with
                        | Assert_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match qo_not_exists_bottom A with
                        | Assert_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs          := or_certs_from_qo_certs  (qo_certs A) 
; or_ast             := qo_ast A 
|}.

Definition or_from_qo_with_bottom {S : Type} (A : @qo_with_bottom S) :=
{|    
  or_eqv             := qo_wb_eqv A 
; or_lte             := qo_wb_lte A 
; or_exists_top_d    := match qo_wb_not_exists_top A with
                        | Assert_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match qo_wb_exists_bottom A with
                        | Assert_Exists_Qo_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_qo_certs  (qo_wb_certs A) 
; or_ast             := qo_wb_ast A 
|}.


Definition or_from_qo_with_top {S : Type} (A : @qo_with_top S) :=
{|    
  or_eqv             := qo_wt_eqv A 
; or_lte             := qo_wt_lte A 
; or_exists_top_d    := match qo_wt_exists_top A with
                        | Assert_Exists_Qo_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match qo_wt_not_exists_bottom A with
                        | Assert_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs           := or_certs_from_qo_certs  (qo_wt_certs A) 
; or_ast             := qo_wt_ast A 
|}.

Definition or_from_qo_bounded {S : Type} (A : @qo_bounded S) :=
{|    
  or_eqv             := qo_bd_eqv A 
; or_lte             := qo_bd_lte A 
; or_exists_top_d    := match qo_bd_exists_top A with
                        | Assert_Exists_Qo_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match qo_bd_exists_bottom A with
                        | Assert_Exists_Qo_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_qo_certs  (qo_bd_certs A) 
; or_ast             := qo_bd_ast A 
|}.


Definition or_from_wo {S : Type} (A : @wo S) :=
{|    
  or_eqv             := wo_eqv A 
; or_lte             := wo_lte A 
; or_exists_top_d    := match wo_not_exists_top A with
                        | Assert_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match wo_not_exists_bottom A with
                        | Assert_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs           := or_certs_from_wo_certs  (wo_certs A) 
; or_ast             := wo_ast A 
|}.

Definition or_from_wo_with_bottom {S : Type} (A : @wo_with_bottom S) :=
{|    
  or_eqv             := wo_wb_eqv A 
; or_lte             := wo_wb_lte A 
; or_exists_top_d    := match wo_wb_not_exists_top A with
                        | Assert_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
                        end 
; or_exists_bottom_d := match wo_wb_exists_bottom A with
                        | Assert_Exists_Qo_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_wo_certs  (wo_wb_certs A) 
; or_ast             := wo_wb_ast A 
|}.


Definition or_from_wo_with_top {S : Type} (A : @wo_with_top S) :=
{|    
  or_eqv             := wo_wt_eqv A 
; or_lte             := wo_wt_lte A 
; or_exists_top_d    := match wo_wt_exists_top A with
                        | Assert_Exists_Qo_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match wo_wt_not_exists_bottom A with
                        | Assert_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; or_certs           := or_certs_from_wo_certs  (wo_wt_certs A) 
; or_ast             := wo_wt_ast A 
|}.

Definition or_from_wo_bounded {S : Type} (A : @wo_bounded S) :=
{|    
  or_eqv             := wo_bd_eqv A 
; or_lte             := wo_bd_lte A 
; or_exists_top_d    := match wo_bd_exists_top A with
                        | Assert_Exists_Qo_Top top => Certify_Exists_Qo_Top top
                        end 
; or_exists_bottom_d := match wo_bd_exists_bottom A with
                        | Assert_Exists_Qo_Bottom bot => Certify_Exists_Qo_Bottom bot
                        end 
; or_certs           := or_certs_from_wo_certs (wo_bd_certs A) 
; or_ast             := wo_bd_ast A 
|}.

End Combinators. 
End CAS.


Section MCAS.

Definition or_mcas_cast_up {S : Type} (A : @or_mcas S) : @or_mcas S :=
match A with
  | OR_Error          _ => A 
  | OR_or             _ => A
  | OR_po             B => OR_or(or_from_po B)
  | OR_po_with_bottom B => OR_or(or_from_po_with_bottom B)
  | OR_po_with_top    B => OR_or(or_from_po_with_top B)
  | OR_po_bounded     B => OR_or(or_from_po_bounded B)
  | OR_to             B => OR_or(or_from_to B)
  | OR_to_with_bottom B => OR_or(or_from_to_with_bottom B)
  | OR_to_with_top    B => OR_or(or_from_to_with_top B)
  | OR_to_bounded     B => OR_or(or_from_to_bounded B)
  | OR_qo             B => OR_or(or_from_qo B)
  | OR_qo_with_bottom B => OR_or(or_from_qo_with_bottom B)
  | OR_qo_with_top    B => OR_or(or_from_qo_with_top B)
  | OR_qo_bounded     B => OR_or(or_from_qo_bounded B)
  | OR_wo             B => OR_or(or_from_wo B)
  | OR_wo_with_bottom B => OR_or(or_from_wo_with_bottom B)
  | OR_wo_with_top    B => OR_or(or_from_wo_with_top B)
  | OR_wo_bounded     B => OR_or(or_from_wo_bounded B)
end.     

End MCAS.


Section Verify.

Section Certificates.

Variables (S : Type) (eq lte : brel S) (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f).       

Lemma correct_or_certs_from_po_certs (P : po_proofs S eq lte) :
 P2C_or eq lte (or_proofs_from_po_proofs S eq lte wS f nt P)
 =
 or_certs_from_po_certs wS f lte (P2C_po eq lte P).
Proof. destruct P; unfold or_proofs_from_po_proofs, or_certs_from_po_certs,
                   P2C_or, P2C_po; simpl.
       reflexivity. 
Qed.

Lemma correct_or_certs_from_to_certs (P : to_proofs S eq lte) :
 P2C_or eq lte (or_proofs_from_to_proofs S eq lte wS f nt P)
 =
 or_certs_from_to_certs wS f lte (P2C_to eq lte P).
Proof. destruct P; unfold or_proofs_from_to_proofs, or_certs_from_to_certs,
                   P2C_or, P2C_to; simpl.
       reflexivity. 
Qed.

Lemma correct_or_certs_from_qo_certs (P : qo_proofs S eq lte) :
 P2C_or eq lte (or_proofs_from_qo_proofs S eq lte P)
 =
 or_certs_from_qo_certs (P2C_qo eq lte P).
Proof. destruct P; unfold or_proofs_from_qo_proofs, or_certs_from_qo_certs,
                   P2C_or, P2C_qo; simpl.
       destruct A_qo_not_total as [[s1 s2] [A B]]; simpl. 
       reflexivity. 
Qed.


Lemma correct_or_certs_from_wo_certs (P : wo_proofs S eq lte) :
 P2C_or eq lte (or_proofs_from_wo_proofs S eq lte P)
 =
 or_certs_from_wo_certs (P2C_wo eq lte P).
Proof. destruct P; unfold or_proofs_from_wo_proofs, or_certs_from_wo_certs,
                   P2C_or, P2C_wo; simpl.
       reflexivity. 
Qed.


End Certificates.

Section Combinators.

Variable (S : Type).   

Lemma correct_or_from_po (a : A_po S) : 
  or_from_po (A2C_po a) = A2C_or (A_or_from_po a).
Proof. destruct a; unfold or_from_po, A_or_from_po, A2C_or, A2C_po; simpl.
       rewrite correct_or_certs_from_po_certs.
       reflexivity. 
Qed.

Lemma correct_or_from_po_with_bottom (a : A_po_with_bottom S) : 
  or_from_po_with_bottom (A2C_po_with_bottom a) = A2C_or (A_or_from_po_with_bottom a).
Proof. destruct a; unfold or_from_po_with_bottom, A_or_from_po_with_bottom, A2C_or, A2C_po_with_bottom; simpl.
       rewrite correct_or_certs_from_po_certs.
       destruct A_po_wb_exists_bottom as [bot botP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_po_with_top (a : A_po_with_top S) : 
  or_from_po_with_top (A2C_po_with_top a) = A2C_or (A_or_from_po_with_top a).
Proof. destruct a; unfold or_from_po_with_top, A_or_from_po_with_top, A2C_or, A2C_po_with_top; simpl.
       rewrite correct_or_certs_from_po_certs.
       destruct A_po_wt_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_po_bounded (a : A_po_bounded S) : 
  or_from_po_bounded (A2C_po_bounded a) = A2C_or (A_or_from_po_bounded a).
Proof. destruct a; unfold or_from_po_bounded, A_or_from_po_bounded, A2C_or, A2C_po_bounded; simpl.
       rewrite correct_or_certs_from_po_certs.
       destruct A_po_bd_exists_bottom as [bot botP]; 
       destruct A_po_bd_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_to (a : A_to S) : 
  or_from_to (A2C_to a) = A2C_or (A_or_from_to a).
Proof. destruct a; unfold or_from_to, A_or_from_to, A2C_or, A2C_to; simpl.
       rewrite correct_or_certs_from_to_certs.
       reflexivity. 
Qed.

Lemma correct_or_from_to_with_bottom (a : A_to_with_bottom S) : 
  or_from_to_with_bottom (A2C_to_with_bottom a) = A2C_or (A_or_from_to_with_bottom a).
Proof. destruct a; unfold or_from_to_with_bottom, A_or_from_to_with_bottom, A2C_or, A2C_to_with_bottom; simpl.
       rewrite correct_or_certs_from_to_certs.
       destruct A_to_wb_exists_bottom as [bot botP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_to_with_top (a : A_to_with_top S) : 
  or_from_to_with_top (A2C_to_with_top a) = A2C_or (A_or_from_to_with_top a).
Proof. destruct a; unfold or_from_to_with_top, A_or_from_to_with_top, A2C_or, A2C_to_with_top; simpl.
       rewrite correct_or_certs_from_to_certs.
       destruct A_to_wt_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_to_bounded (a : A_to_bounded S) : 
  or_from_to_bounded (A2C_to_bounded a) = A2C_or (A_or_from_to_bounded a).
Proof. destruct a; unfold or_from_to_bounded, A_or_from_to_bounded, A2C_or, A2C_to_bounded; simpl.
       rewrite correct_or_certs_from_to_certs.
       destruct A_to_bd_exists_bottom as [bot botP]; 
       destruct A_to_bd_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_qo (a : A_qo S) : 
  or_from_qo (A2C_qo a) = A2C_or (A_or_from_qo a).
Proof. destruct a; unfold or_from_qo, A_or_from_qo, A2C_or, A2C_qo; simpl.
       rewrite correct_or_certs_from_qo_certs.
       reflexivity. 
Qed.

Lemma correct_or_from_qo_with_bottom (a : A_qo_with_bottom S) : 
  or_from_qo_with_bottom (A2C_qo_with_bottom a) = A2C_or (A_or_from_qo_with_bottom a).
Proof. destruct a; unfold or_from_qo_with_bottom, A_or_from_qo_with_bottom, A2C_or, A2C_qo_with_bottom; simpl.
       rewrite correct_or_certs_from_qo_certs.
       destruct A_qo_wb_exists_bottom as [bot botP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_qo_with_top (a : A_qo_with_top S) : 
  or_from_qo_with_top (A2C_qo_with_top a) = A2C_or (A_or_from_qo_with_top a).
Proof. destruct a; unfold or_from_qo_with_top, A_or_from_qo_with_top, A2C_or, A2C_qo_with_top; simpl.
       rewrite correct_or_certs_from_qo_certs.
       destruct A_qo_wt_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_qo_bounded (a : A_qo_bounded S) : 
  or_from_qo_bounded (A2C_qo_bounded a) = A2C_or (A_or_from_qo_bounded a).
Proof. destruct a; unfold or_from_qo_bounded, A_or_from_qo_bounded, A2C_or, A2C_qo_bounded; simpl.
       rewrite correct_or_certs_from_qo_certs.
       destruct A_qo_bd_exists_bottom as [bot botP]; 
       destruct A_qo_bd_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_wo (a : A_wo S) : 
  or_from_wo (A2C_wo a) = A2C_or (A_or_from_wo a).
Proof. destruct a; unfold or_from_wo, A_or_from_wo, A2C_or, A2C_wo; simpl.
       rewrite correct_or_certs_from_wo_certs.
       reflexivity. 
Qed.

Lemma correct_or_from_wo_with_bottom (a : A_wo_with_bottom S) : 
  or_from_wo_with_bottom (A2C_wo_with_bottom a) = A2C_or (A_or_from_wo_with_bottom a).
Proof. destruct a; unfold or_from_wo_with_bottom, A_or_from_wo_with_bottom, A2C_or, A2C_wo_with_bottom; simpl.
       rewrite correct_or_certs_from_wo_certs.
       destruct A_wo_wb_exists_bottom as [bot botP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_wo_with_top (a : A_wo_with_top S) : 
  or_from_wo_with_top (A2C_wo_with_top a) = A2C_or (A_or_from_wo_with_top a).
Proof. destruct a; unfold or_from_wo_with_top, A_or_from_wo_with_top, A2C_or, A2C_wo_with_top; simpl.
       rewrite correct_or_certs_from_wo_certs.
       destruct A_wo_wt_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

Lemma correct_or_from_wo_bounded (a : A_wo_bounded S) : 
  or_from_wo_bounded (A2C_wo_bounded a) = A2C_or (A_or_from_wo_bounded a).
Proof. destruct a; unfold or_from_wo_bounded, A_or_from_wo_bounded, A2C_or, A2C_wo_bounded; simpl.
       rewrite correct_or_certs_from_wo_certs.
       destruct A_wo_bd_exists_bottom as [bot botP]; 
       destruct A_wo_bd_exists_top as [top topP]; simpl. 
       reflexivity. 
Qed.

       
Theorem correct_or_mcas_cast_up (P : @A_or_mcas S) : 
         or_mcas_cast_up (A2C_mcas_or P) = A2C_mcas_or (A_or_mcas_cast_up P).
Proof. destruct P; simpl.
       reflexivity.
       reflexivity.
       rewrite correct_or_from_po; reflexivity. 
       rewrite correct_or_from_po_with_bottom; reflexivity.
       rewrite correct_or_from_po_with_top; reflexivity.        
       rewrite correct_or_from_po_bounded; reflexivity. 
       rewrite correct_or_from_to; reflexivity. 
       rewrite correct_or_from_to_with_bottom; reflexivity.
       rewrite correct_or_from_to_with_top; reflexivity.        
       rewrite correct_or_from_to_bounded; reflexivity. 
       rewrite correct_or_from_qo; reflexivity. 
       rewrite correct_or_from_qo_with_bottom; reflexivity.
       rewrite correct_or_from_qo_with_top; reflexivity.        
       rewrite correct_or_from_qo_bounded; reflexivity. 
       rewrite correct_or_from_wo; reflexivity. 
       rewrite correct_or_from_wo_with_bottom; reflexivity.
       rewrite correct_or_from_wo_with_top; reflexivity.        
       rewrite correct_or_from_wo_bounded; reflexivity. 
Qed.


Theorem A_or_cast_up_is_error_or_or (P : @A_or_mcas S) :
  {l : list string & P = A_OR_Error l} + 
  {A : A_or S & A_or_mcas_cast_up P = A_OR_or A}. 
Proof. destruct P; simpl. 
       + left. exists l. reflexivity.
       + right. exists a. reflexivity.
       + right. exists (A_or_from_po a). reflexivity.
       + right. exists (A_or_from_po_with_bottom a). reflexivity.
       + right. exists (A_or_from_po_with_top a). reflexivity.
       + right. exists (A_or_from_po_bounded a). reflexivity.
       + right. exists (A_or_from_to a). reflexivity.
       + right. exists (A_or_from_to_with_bottom a). reflexivity.
       + right. exists (A_or_from_to_with_top a). reflexivity.
       + right. exists (A_or_from_to_bounded a). reflexivity.         
       + right. exists (A_or_from_qo a). reflexivity.
       + right. exists (A_or_from_qo_with_bottom a). reflexivity.
       + right. exists (A_or_from_qo_with_top a). reflexivity.
       + right. exists (A_or_from_qo_bounded a). reflexivity.
       + right. exists (A_or_from_wo a). reflexivity.
       + right. exists (A_or_from_wo_with_bottom a). reflexivity.
       + right. exists (A_or_from_wo_with_top a). reflexivity.
       + right. exists (A_or_from_wo_bounded a). reflexivity.         
Qed. 
       
End Combinators.  
End Verify.   
