
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

Require Import CAS.code.cas.eqv.product.
Require Import CAS.code.cas.sg.product. 


Definition bop_product_left_distributive_check : 
   ∀ {S T : Type},  
     S -> 
     T -> 
     @check_left_distributive S -> 
     @check_left_distributive T -> 
     @check_left_distributive (S * T) 
:= λ {S T} s t dS dT,  
   match dS with 
   | Certify_Left_Distributive => 
     match dT with 
     | Certify_Left_Distributive => Certify_Left_Distributive 
     | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive ((s1, t), ((s2, t), (s3, t)))
   end.

Definition bop_product_right_distributive_check : 
   ∀ {S T : Type},  
     S -> 
     T -> 
     @check_right_distributive S -> 
     @check_right_distributive T -> 
     @check_right_distributive (S * T) 
:= λ {S T} s t dS dT,  
   match dS with 
   | Certify_Right_Distributive => 
     match dT with 
     | Certify_Right_Distributive => Certify_Right_Distributive  
     | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, t), ((s2, t), (s3, t)))
   end.

Definition bop_product_plus_id_is_times_ann_check : 
   ∀ {S T : Type},  
     @check_plus_id_equals_times_ann S -> 
     @check_plus_id_equals_times_ann T -> 
     @check_plus_id_equals_times_ann (S * T) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann  
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann  
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 

Definition bop_product_times_id_equals_plus_ann_check : 
   ∀ {S T : Type},  
     @check_times_id_equals_plus_ann S -> 
     @check_times_id_equals_plus_ann T -> 
     @check_times_id_equals_plus_ann (S * T) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann  
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann 
   end. 



Definition bop_product_left_left_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_left_left_absorptive S -> 
     @check_left_left_absorptive T -> 
     @check_left_left_absorptive (S * T) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive  
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
          Certify_Not_Left_Left_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_left_right_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_left_right_absorptive S -> 
     @check_left_right_absorptive T -> 
     @check_left_right_absorptive (S * T)
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive  
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
          Certify_Not_Left_Right_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_right_left_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_right_left_absorptive S -> 
     @check_right_left_absorptive T -> 
     @check_right_left_absorptive (S * T)
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive  
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
          Certify_Not_Right_Left_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_right_right_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_right_right_absorptive S -> 
     @check_right_right_absorptive T -> 
     @check_right_right_absorptive (S * T) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive  
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
          Certify_Not_Right_Right_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive  ((s1, t), (s2, t))
end. 

Definition bs_certs_product : 
  ∀ {S T : Type}, 
        S -> T -> @bs_certificates S -> @bs_certificates T -> @bs_certificates (S * T) 
:= λ {S T} s t bsS bsT, 
{|
  bs_left_distributive_d      := bop_product_left_distributive_check s t
                                     (bs_left_distributive_d bsS)
                                     (bs_left_distributive_d bsT)
; bs_right_distributive_d     := bop_product_right_distributive_check s t
                                     (bs_right_distributive_d bsS)
                                     (bs_right_distributive_d bsT)
; bs_plus_id_is_times_ann_d   := bop_product_plus_id_is_times_ann_check 
                                     (bs_plus_id_is_times_ann_d bsS)
                                     (bs_plus_id_is_times_ann_d bsT)
; bs_times_id_is_plus_ann_d   := bop_product_times_id_equals_plus_ann_check 
                                     (bs_times_id_is_plus_ann_d bsS)
                                     (bs_times_id_is_plus_ann_d bsT)
; bs_left_left_absorptive_d   := bop_product_left_left_absorptive_check s t 
                                     (bs_left_left_absorptive_d bsS)
                                     (bs_left_left_absorptive_d bsT)
; bs_left_right_absorptive_d  := bop_product_left_right_absorptive_check s t 
                                     (bs_left_right_absorptive_d bsS)
                                     (bs_left_right_absorptive_d bsT)
; bs_right_left_absorptive_d  := bop_product_right_left_absorptive_check s t
                                     (bs_right_left_absorptive_d bsS)
                                     (bs_right_left_absorptive_d bsT)
; bs_right_right_absorptive_d := bop_product_right_right_absorptive_check s t
                                     (bs_right_right_absorptive_d bsS)
                                     (bs_right_right_absorptive_d bsT)

|}.

Definition bs_product : ∀ {S T : Type},  @bs S -> @bs T -> @bs (S * T)
:= λ {S T} bsS bsT, 
   {| 
     bs_eqv         := eqv_product (bs_eqv bsS) (bs_eqv bsT) 
   ; bs_plus        := bop_product (bs_plus bsS) (bs_plus bsT) 
   ; bs_times       := bop_product (bs_times bsS) (bs_times bsT) 
   ; bs_plus_certs  := sg_certs_product
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_plus_certs bsS) 
                           (bs_plus_certs bsT) 
   ; bs_times_certs := sg_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_times_certs bsS) 
                           (bs_times_certs bsT) 
   ; bs_certs       := bs_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_certs bsS) 
                           (bs_certs bsT) 
   ; bs_ast         := Ast_bs_product(bs_ast bsS, bs_ast bsT)
   |}. 


Definition semiring_certs_product : 
  ∀ {S T : Type}, S -> T -> @semiring_certificates S -> @semiring_certificates T ->  @semiring_certificates (S * T)
:= λ {S T} s t srS srT, 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_plus_id_is_times_ann_d   := bop_product_plus_id_is_times_ann_check 
                                         (semiring_plus_id_is_times_ann_d srS)
                                         (semiring_plus_id_is_times_ann_d srT)                                         
; semiring_times_id_is_plus_ann_d   := bop_product_times_id_equals_plus_ann_check 
                                         (semiring_times_id_is_plus_ann_d srS)
                                         (semiring_times_id_is_plus_ann_d srT)                                         
; semiring_left_left_absorptive_d   := bop_product_left_left_absorptive_check s t
                                         (semiring_left_left_absorptive_d srS)
                                         (semiring_left_left_absorptive_d srT)
; semiring_left_right_absorptive_d  := bop_product_left_right_absorptive_check s t 
                                         (semiring_left_right_absorptive_d srS)
                                         (semiring_left_right_absorptive_d srT)   
|}.

Definition semiring_product : ∀ {S T : Type},  @semiring S ->  @semiring T -> @semiring (S * T)
:= λ S T s1 s2,
let wS := eqv_witness (semiring_eqv s1) in
let wT := eqv_witness (semiring_eqv s2) in
let fS := eqv_new (semiring_eqv s1) in
let fT := eqv_new (semiring_eqv s2) in
let eqS := eqv_eq (semiring_eqv s1) in
let eqT := eqv_eq (semiring_eqv s2) in
let addS := semiring_plus s1 in
let mulS := semiring_times s1 in
let addT := semiring_plus s2 in
let mulT := semiring_times s2 in 
{| 
     semiring_eqv          := eqv_product (semiring_eqv s1) (semiring_eqv s2) 
   ; semiring_plus         := bop_product addS addT
   ; semiring_times        := bop_product mulS mulT
   ; semiring_plus_certs   := sg_C_certs_product eqS eqT addS addT wS fS wT fT (semiring_plus_certs s1) (semiring_plus_certs s2) 
   ; semiring_times_certs  := sg_certs_product wS wT (semiring_times_certs s1) (semiring_times_certs s2) 
   ; semiring_certs        := semiring_certs_product wS wT (semiring_certs s1) (semiring_certs s2) 
   ; semiring_ast          := Ast_semiring_product (semiring_ast s1, semiring_ast s2)
|}.

Definition dioid_product : ∀ (S T : Type),  @dioid S ->  @dioid T -> @dioid (S * T) 
:= λ S T sr1 sr2,
let eqvS   := dioid_eqv sr1   in
let eqvT   := dioid_eqv sr2   in
let rS     := eqv_eq eqvS  in 
let rT     := eqv_eq eqvT  in
let s      := eqv_witness eqvS in
let f      := eqv_new eqvS in
let t      := eqv_witness eqvT in
let g      := eqv_new eqvT in
let plusS  := dioid_plus sr1  in 
let plusT  := dioid_plus sr2  in
let timesS := dioid_times sr1 in 
let timesT := dioid_times sr2 in 
{| 
     dioid_eqv         := eqv_product eqvS eqvT 
   ; dioid_plus        := bop_product plusS plusT 
   ; dioid_times       := bop_product timesS timesT 
   ; dioid_plus_certs  := sg_CI_certs_product rS rT plusS plusT s f t g (dioid_plus_certs sr1)(dioid_plus_certs sr2)
   ; dioid_times_certs := sg_certs_product s t (dioid_times_certs sr1) (dioid_times_certs sr2)
   ; dioid_certs       := semiring_certs_product s t (dioid_certs sr1) (dioid_certs sr2) 
   ; dioid_ast         := Ast_dioid_product (dioid_ast sr1, dioid_ast sr2)
|}.
