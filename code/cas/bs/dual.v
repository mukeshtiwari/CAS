Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop.
Require Import CAS.code.bs_certificates. 
Require Import CAS.code.bs_cert_records.
Require Import CAS.code.bs_records.


Definition lattice_certs_dual {S: Type} : @lattice_certificates S  -> @lattice_certificates S 
:= λ pfs,
{|
   lattice_absorptive          := Assert_Left_Left_Absorptive
 ; lattice_absorptive_dual     := Assert_Left_Left_Absorptive_Dual
 ; lattice_distributive_d      := match lattice_distributive_dual_d pfs with
                                  | Certify_Left_Distributive_Dual => Certify_Left_Distributive
                                  | Certify_Not_Left_Distributive_Dual p => Certify_Not_Left_Distributive p                   
                                  end 
 ; lattice_distributive_dual_d := match lattice_distributive_d pfs with
                                  | Certify_Left_Distributive => Certify_Left_Distributive_Dual
                                  | Certify_Not_Left_Distributive p => Certify_Not_Left_Distributive_Dual p                   
                                  end                                     
|}. 


Definition lattice_dual : ∀ {S : Type}, @lattice S -> @lattice S
:= λ {S} lat,
{|  
  lattice_eqv          := lattice_eqv lat 
; lattice_join         := lattice_meet lat 
; lattice_meet         := lattice_join lat 
; lattice_join_certs   := lattice_meet_certs lat 
; lattice_meet_certs   := lattice_join_certs lat 
; lattice_certs        := lattice_certs_dual (lattice_certs lat)   
; lattice_ast          := Ast_lattice_dual (lattice_ast lat) 
|}.


Definition distributive_lattice_certs_dual {S: Type} :
  @distributive_lattice_certificates S -> @distributive_lattice_certificates S 
:= λ dlc,
{|
   distributive_lattice_absorptive        := Assert_Left_Left_Absorptive 
 ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
 ; distributive_lattice_distributive      := Assert_Left_Distributive
|}.

Definition distributive_lattice_dual : ∀ {S : Type}, @distributive_lattice S -> @distributive_lattice S
:= λ {S} lat,
{|  
  distributive_lattice_eqv          := distributive_lattice_eqv lat 
; distributive_lattice_join         := distributive_lattice_meet lat 
; distributive_lattice_meet         := distributive_lattice_join lat 
; distributive_lattice_join_certs   := distributive_lattice_meet_certs lat 
; distributive_lattice_meet_certs   := distributive_lattice_join_certs lat 
; distributive_lattice_certs        := distributive_lattice_certs_dual (distributive_lattice_certs lat)
; distributive_lattice_ast          := Ast_distributive_lattice_dual (distributive_lattice_ast lat) 
|}.
