
Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.bs_certificates.
Require Import CAS.code.bs_cert_records.
Require Import CAS.code.bs_records.
Require Import CAS.code.ast.

Require Import CAS.code.cas.eqv.add_constant.
Require Import CAS.code.cas.sg.add_ann.
Require Import CAS.code.cas.sg.add_id.

Definition bops_add_zero_left_distributive_check : 
   ∀ {S : Type},  
     check_left_distributive (S := S) -> 
     check_left_distributive (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Left_Distributive => Certify_Left_Distributive (S := (with_constant S)) 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (S := (with_constant S)) (inr s1, (inr s2, inr _ s3))
   end. 

Definition bops_add_zero_right_distributive_check : 
   ∀ {S : Type},  
     check_right_distributive (S := S) -> 
     check_right_distributive (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Right_Distributive => Certify_Right_Distributive (S := (with_constant S)) 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (S := (with_constant S)) (inr _ s1, (inr _ s2, inr _ s3))
   end.

Definition bops_add_zero_distributive_dual_check : 
   ∀ {S : Type},  @check_left_distributive_dual S -> @check_left_distributive_dual (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Left_Distributive_Dual               => Certify_Left_Distributive_Dual 
   | Certify_Not_Left_Distributive_Dual (s1, (s2, s3)) => Certify_Not_Left_Distributive_Dual (inr s1, (inr s2, inr _ s3))
   end. 


Definition bops_add_zero_left_left_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive (S := (with_constant S))
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
     Certify_Not_Left_Left_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 


Definition bops_add_zero_left_right_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive (S := (with_constant S))
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
     Certify_Not_Left_Right_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_left_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive (S := (with_constant S))
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
     Certify_Not_Right_Left_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_right_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive (S := (with_constant S))
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
     Certify_Not_Right_Right_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end.


Definition bops_add_zero_times_id_is_plus_ann_check : 
   ∀ {S : Type}, @check_times_id_equals_plus_ann S-> @check_times_id_equals_plus_ann (with_constant S)
:= λ {S} dS,  
  match dS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann  
  end . 


Definition bs_certs_add_zero : 
  ∀ {S : Type} (s : S), bs_certificates (S := S) -> bs_certificates (S := (with_constant S))
:= λ {S} s pS, 
{|
  bs_left_distributive_d    := 
     bops_add_zero_left_distributive_check (bs_left_distributive_d pS) 
; bs_right_distributive_d   := 
     bops_add_zero_right_distributive_check (bs_right_distributive_d pS) 

; bs_left_left_absorptive_d      := 
     bops_add_zero_left_left_absorptive_check s (bs_left_left_absorptive_d pS)
; bs_left_right_absorptive_d      := 
     bops_add_zero_left_right_absorptive_check s (bs_left_right_absorptive_d pS)
; bs_right_left_absorptive_d     := 
     bops_add_zero_right_left_absorptive_check s (bs_right_left_absorptive_d pS)
; bs_right_right_absorptive_d     := 
     bops_add_zero_right_right_absorptive_check s (bs_right_right_absorptive_d pS)

; bs_plus_id_is_times_ann_d :=  Certify_Plus_Id_Equals_Times_Ann  
; bs_times_id_is_plus_ann_d :=  bops_add_zero_times_id_is_plus_ann_check (bs_times_id_is_plus_ann_d pS)
|}. 


Definition bs_add_zero : ∀ {S : Type},  @bs S -> cas_constant -> @bs (with_constant S)
  := λ {S} bsS c,
let s :=   eqv_witness (bs_eqv bsS) in
let f :=   eqv_new (bs_eqv bsS) in   
{| 
     bs_eqv         := eqv_add_constant (bs_eqv bsS) c 
   ; bs_plus        := bop_add_id (bs_plus bsS) c
   ; bs_times       := bop_add_ann (bs_times bsS) c
   ; bs_plus_certs  := sg_certs_add_id c s f (bs_plus_certs bsS) 
   ; bs_times_certs := sg_certs_add_ann c s f (bs_times_certs bsS) 
   ; bs_certs       := bs_certs_add_zero s (bs_certs bsS)
   ; bs_ast         := Ast_bs_add_zero (c, bs_ast bsS)
|}. 


Definition semiring_certs_add_zero : 
  ∀ {S : Type} (s : S), @semiring_certificates S  -> @semiring_certificates (with_constant S) 
:= λ S s pS, 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann  
; semiring_times_id_is_plus_ann_d   :=
  match semiring_times_id_is_plus_ann_d pS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann  
  end 
; semiring_left_left_absorptive_d   := bops_add_zero_left_left_absorptive_check s (semiring_left_left_absorptive_d pS)
; semiring_left_right_absorptive_d  := bops_add_zero_left_right_absorptive_check s (semiring_left_right_absorptive_d pS)
|}.

Definition dioid_add_zero : ∀ (S : Type),  @dioid S -> cas_constant -> @dioid (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (dioid_eqv bsS) in
let f :=   eqv_new (dioid_eqv bsS) in   
{| 
     dioid_eqv         := eqv_add_constant (dioid_eqv bsS) c 
   ; dioid_plus        := bop_add_id (dioid_plus bsS) c
   ; dioid_times       := bop_add_ann (dioid_times bsS) c
   ; dioid_plus_certs  := sg_CI_certs_add_id c (dioid_plus_certs bsS)
   ; dioid_times_certs := sg_certs_add_ann c s f (dioid_times_certs bsS)
   ; dioid_certs       := semiring_certs_add_zero s (dioid_certs bsS)
   ; dioid_ast         := Ast_dioid_add_zero (c, dioid_ast bsS)
|}. 

Definition semiring_add_zero : ∀ (S : Type),  @semiring S -> cas_constant -> @semiring (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (semiring_eqv bsS) in
let f :=   eqv_new (semiring_eqv bsS) in   
{| 
     semiring_eqv         := eqv_add_constant (semiring_eqv bsS) c 
   ; semiring_plus        := bop_add_id (semiring_plus bsS) c
   ; semiring_times       := bop_add_ann (semiring_times bsS) c
   ; semiring_plus_certs  := sg_C_certs_add_id c s f (semiring_plus_certs bsS)
   ; semiring_times_certs := sg_certs_add_ann c s f (semiring_times_certs bsS)
   ; semiring_certs       := semiring_certs_add_zero s (semiring_certs bsS)
   ; semiring_ast         := Ast_semiring_add_zero (c, semiring_ast bsS)
|}. 

Definition distributive_lattice_certs_add_zero : 
  ∀ {S : Type} (c : cas_constant), @distributive_lattice_certificates S -> @distributive_lattice_certificates (with_constant S) 
:= λ {S} c dlc ,
{|
  distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
; distributive_lattice_distributive      := Assert_Left_Distributive 
|}.

Definition distributive_lattice_add_zero : ∀ (S : Type),  @distributive_lattice S -> cas_constant -> @distributive_lattice (with_constant S) 
:= λ S bsS c,
{| 
     distributive_lattice_eqv         := eqv_add_constant (distributive_lattice_eqv bsS) c 
   ; distributive_lattice_join        := bop_add_id (distributive_lattice_join bsS) c
   ; distributive_lattice_meet        := bop_add_ann (distributive_lattice_meet bsS) c
   ; distributive_lattice_join_certs  := sg_CI_certs_add_id c (distributive_lattice_join_certs bsS)
   ; distributive_lattice_meet_certs  := sg_CI_certs_add_ann c (distributive_lattice_meet_certs bsS)
   ; distributive_lattice_certs       := distributive_lattice_certs_add_zero c (distributive_lattice_certs bsS )
   ; distributive_lattice_ast         := Ast_distributive_lattice_add_zero (c, distributive_lattice_ast bsS)
|}. 


Definition lattice_certs_add_zero : 
  ∀ {S : Type}, @lattice_certificates S -> @lattice_certificates (with_constant S) 
:= λ {S} pS, 
{|
  lattice_absorptive          := Assert_Left_Left_Absorptive
; lattice_absorptive_dual     := Assert_Left_Left_Absorptive_Dual
; lattice_distributive_d      := bops_add_zero_left_distributive_check (lattice_distributive_d pS) 
; lattice_distributive_dual_d := bops_add_zero_distributive_dual_check (lattice_distributive_dual_d pS) 
|}.

Definition lattice_add_zero : ∀ (S : Type),  @lattice S -> cas_constant -> @lattice (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (lattice_eqv bsS) in
let f :=   eqv_new (lattice_eqv bsS) in   
{| 
     lattice_eqv         := eqv_add_constant (lattice_eqv bsS) c 
   ; lattice_join        := bop_add_id (lattice_join bsS) c
   ; lattice_meet        := bop_add_ann (lattice_meet bsS) c
   ; lattice_join_certs  := sg_CI_certs_add_id c (lattice_join_certs bsS)
   ; lattice_meet_certs  := sg_CI_certs_add_ann c (lattice_meet_certs bsS)
   ; lattice_certs       := lattice_certs_add_zero (lattice_certs bsS)
   ; lattice_ast         := Ast_lattice_add_zero (c, lattice_ast bsS)
|}. 



 
