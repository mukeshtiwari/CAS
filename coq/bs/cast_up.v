Require Import CAS.coq.common.base. 
Require Import CAS.code.cas.sg.cast_up. 
Require Import CAS.coq.theory.facts. 
Section Theory.

End Theory.

Section ACAS.





Definition A_bs_from_bs_C : ∀ (S : Type),  A_bs_C S -> A_bs S 
:= λ S s, 
{| 
  A_bs_eqv          := A_bs_C_eqv S s
; A_bs_plus         := A_bs_C_plus S s
; A_bs_times        := A_bs_C_times S s
; A_bs_plus_proofs  := A_sg_proofs_from_sg_C_proofs S 
                            (A_eqv_eq S (A_bs_C_eqv S s))
                            (A_bs_C_plus S s)
                            (A_eqv_proofs S (A_bs_C_eqv S s)) 
                            (A_bs_C_plus_proofs S s)  
; A_bs_times_proofs := A_bs_C_times_proofs S s
; A_bs_proofs       := A_bs_C_proofs S s 
; A_bs_ast          := Ast_bs_from_bs_C (A_bs_C_ast S s)
|}. 



Definition A_bs_from_bs_CS : ∀ (S : Type),  A_bs_CS S -> A_bs S 
:= λ S s, 
{| 
  A_bs_eqv          := A_bs_CS_eqv S s
; A_bs_plus         := A_bs_CS_plus S s
; A_bs_times        := A_bs_CS_times S s
; A_bs_plus_proofs  := A_sg_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_bs_CS_eqv S s))
                            (A_bs_CS_plus S s)
                            (A_eqv_proofs S (A_bs_CS_eqv S s)) 
                            (A_bs_CS_plus_proofs S s)  
; A_bs_times_proofs := A_bs_CS_times_proofs S s
; A_bs_proofs       := A_bs_CS_proofs S s 
; A_bs_ast          := Ast_bs_from_bs_CS (A_bs_CS_ast S s)
|}. 




(* UPCAST 

Definition A_sg_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CS_proofs S r b -> sg_proofs S r b 
:= λ S r b eqvS sgS,  
    A_sg_proofs_from_sg_C_proofs S r b eqvS
      (A_sg_C_proofs_from_sg_CI_proofs S r b eqvS 
         (A_sg_CI_proofs_from_sg_CS_proofs S r b sgS)).  


Definition A_sg_proofs_from_sg_CK_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CK_proofs S r b -> sg_proofs S r b 
:= λ S r b eqvS sgS,  
    A_sg_proofs_from_sg_C_proofs S r b eqvS
         (A_sg_C_proofs_from_sg_CK_proofs S r b eqvS sgS).  


Definition A_sg_C_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), eqv_proofs S r -> sg_CS_proofs S r b -> sg_C_proofs S r b 
:= λ S r b eqvS sgS,  
      A_sg_C_proofs_from_sg_CI_proofs S r b eqvS 
         (A_sg_CI_proofs_from_sg_CS_proofs S r b sgS).  

Definition A_bs_C_from_sg_CS_sg : ∀ (S : Type),  A_sg_CS_sg S -> A_bs_C S 
:= λ S s, 
{| 
  A_bs_C_eqv          := A_sg_CS_sg_eqv S s
; A_bs_C_plus         := A_sg_CS_sg_plus S s
; A_bs_C_times        := A_sg_CS_sg_times S s
; A_bs_C_plus_proofs  := A_sg_C_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_sg_eqv S s))
                            (A_sg_CS_sg_plus S s)
                            (A_eqv_proofs S (A_sg_CS_sg_eqv S s)) 
                            (A_sg_CS_sg_plus_proofs S s)  
; A_bs_C_times_proofs := A_sg_CS_sg_times_proofs S s
; A_bs_C_proofs       := A_sg_CS_sg_proofs S s 
; A_bs_C_ast          := Ast_bs_C_from_sg_CS_sg (A_sg_CS_sg_ast S s)
|}. 


Definition A_bs_from_sg_CS_sg : ∀ (S : Type),  A_sg_CS_sg S -> A_bs S 
:= λ S s, A_bs_from_bs_C S (A_bs_C_from_sg_CS_sg S s). 

Definition A_bs_proofs_from_bs_LD_proofs : 
   ∀ (S : Type) (eq : brel S) (plus : binary_op S) (times : binary_op S), 
        brel_transitive S eq -> 
        bop_congruence S eq plus -> 
        bop_commutative S eq plus -> 
        bop_commutative S eq times -> 
       bs_LD_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times transS congP commP commT s,  
{|
  A_bs_left_distributive_d    := inl _ (A_bs_LD_left_distributive S eq plus times s) 
; A_bs_right_distributive_d   := inl _ (bop_left_distributive_implies_right S eq plus times
                                              transS congP commP commT
                                              (A_bs_LD_left_distributive S eq plus times s))

; A_bs_left_absorption_d      := A_bs_LD_left_absorption_d S eq plus times s
; A_bs_right_absorption_d     := A_bs_LD_right_absorption_d S eq plus times s

; A_bs_plus_id_is_times_ann_d := A_bs_LD_plus_id_is_times_ann_d S eq plus times s
; A_bs_times_id_is_plus_ann_d := A_bs_LD_times_id_is_plus_ann_d S eq plus times s
|}. 


Definition A_bs_proofs_from_bs_LA_proofs : 
   ∀ (S : Type) (eq : brel S) (plus : binary_op S) (times : binary_op S), 
        brel_reflexive S eq -> 
        brel_transitive S eq -> 
        bop_congruence S eq plus -> 
        bop_commutative S eq times -> 
       bs_LA_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times refS transS congP commT s,  
{|
  A_bs_left_distributive_d    := A_bs_LA_left_distributive_d S eq plus times s 
; A_bs_right_distributive_d   := A_bs_LA_right_distributive_d S eq plus times s

; A_bs_left_absorption_d      := inl _ (A_bs_LA_left_absorption S eq plus times s)
; A_bs_right_absorption_d     := inl _ (bops_left_absorption_and_times_commutative_imply_right_absorption S eq plus times
                                              refS transS congP commT
                                              (A_bs_LA_left_absorption S eq plus times s))

; A_bs_plus_id_is_times_ann_d := A_bs_LA_plus_id_is_times_ann_d S eq plus times s
; A_bs_times_id_is_plus_ann_d := A_bs_LA_times_id_is_plus_ann_d S eq plus times s
|}. 


Definition A_bs_proofs_from_bs_LALD_proofs : 
   ∀ (S : Type) (eq : brel S) (plus : binary_op S) (times : binary_op S), 
        brel_reflexive S eq -> 
        brel_transitive S eq -> 
        bop_congruence S eq plus -> 
        bop_commutative S eq plus -> 
        bop_commutative S eq times -> 
       bs_LALD_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times refS transS congP commP commT s,  
{|
  A_bs_left_distributive_d    := inl _ (A_bs_LALD_left_distributive S eq plus times s) 
; A_bs_right_distributive_d   := inl _ (bop_left_distributive_implies_right S eq plus times
                                              transS congP commP commT
                                              (A_bs_LALD_left_distributive S eq plus times s))


; A_bs_left_absorption_d      := inl _ (A_bs_LALD_left_absorption S eq plus times s)
; A_bs_right_absorption_d     := inl _ (bops_left_absorption_and_times_commutative_imply_right_absorption S eq plus times
                                              refS transS congP commT
                                              (A_bs_LALD_left_absorption S eq plus times s))

; A_bs_plus_id_is_times_ann_d := A_bs_LALD_plus_id_is_times_ann_d S eq plus times s
; A_bs_times_id_is_plus_ann_d := A_bs_LALD_times_id_is_plus_ann_d S eq plus times s
|}. 





Definition A_sg_CS_sg_from_sg_CS_sg_CK_AD : ∀ (S : Type),  A_sg_CS_sg_CK_AD S -> A_sg_CS_sg S 
:= λ S s,  
{|
  A_sg_CS_sg_eqv          := A_sg_CS_sg_CK_AD_eqv S s 
; A_sg_CS_sg_plus         := A_sg_CS_sg_CK_AD_plus S s 
; A_sg_CS_sg_times        := A_sg_CS_sg_CK_AD_times S s 
; A_sg_CS_sg_plus_proofs  := A_sg_CS_sg_CK_AD_plus_proofs S s  
; A_sg_CS_sg_times_proofs := A_sg_proofs_from_sg_CK_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                (A_sg_CS_sg_CK_AD_times S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CK_AD_eqv S s))
                                (A_sg_CS_sg_CK_AD_times_proofs S s) 
; A_sg_CS_sg_proofs       := A_bs_proofs_from_bs_LALD_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                (A_sg_CS_sg_CK_AD_plus S s)
                                (A_sg_CS_sg_CK_AD_times S s)
                                (A_eqv_reflexive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CK_AD_eqv S s))) 
                                (A_eqv_transitive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CK_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CK_AD_eqv S s))) 
                                (A_sg_CS_congruence S _ _ (A_sg_CS_sg_CK_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CK_AD_plus_proofs S s)) 
                                (A_sg_CK_commutative S _ _ (A_sg_CS_sg_CK_AD_times_proofs S s))
                                (A_sg_CS_sg_CK_AD_proofs S s)  
; A_sg_CS_sg_ast          :=  Ast_sg_CS_sg_from_sg_CS_sg_CK_AD (A_sg_CS_sg_CK_AD_ast S s)  
|}.




Definition A_bs_C_from_sg_CS_sg_CS_AD : ∀ (S : Type),  A_sg_CS_sg_CS_AD S -> A_bs_C S 
:= λ S s,  
{|
  A_bs_C_eqv          := A_sg_CS_sg_CS_AD_eqv S s 
; A_bs_C_plus         := A_sg_CS_sg_CS_AD_plus S s 
; A_bs_C_times        := A_sg_CS_sg_CS_AD_times S s 
; A_bs_C_plus_proofs  := A_sg_C_proofs_from_sg_CS_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus_proofs S s)  
; A_bs_C_times_proofs := A_sg_proofs_from_sg_CS_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_times S s)
                                (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_times_proofs S s) 
; A_bs_C_proofs       := A_bs_proofs_from_bs_LALD_proofs S 
                                (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                (A_sg_CS_sg_CS_AD_plus S s)
                                (A_sg_CS_sg_CS_AD_times S s)
                                (A_eqv_reflexive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s)))
                                (A_eqv_transitive S  
                                   (A_eqv_eq S (A_sg_CS_sg_CS_AD_eqv S s))
                                   (A_eqv_proofs S (A_sg_CS_sg_CS_AD_eqv S s)))
                                (A_sg_CS_congruence S _ _ (A_sg_CS_sg_CS_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CS_AD_plus_proofs S s)) 
                                (A_sg_CS_commutative S _ _ (A_sg_CS_sg_CS_AD_times_proofs S s))
                                (A_sg_CS_sg_CS_AD_proofs S s)  
; A_bs_C_ast          :=  Ast_bs_C_from_sg_CS_sg_CS_AD (A_sg_CS_sg_CS_AD_ast S s)  
|}.



 *)

Definition semiring_proofs_to_bs_proofs :
  ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
       eqv_proofs S eq -> sg_C_proofs S eq plus -> semiring_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times eqv sg sr,
let tranS := A_eqv_transitive S eq eqv   in 
let plus_comm := A_sg_C_commutative S eq plus sg in   
{|
  A_bs_left_distributive_d      := inl _ (A_semiring_left_distributive S eq plus times sr)
; A_bs_right_distributive_d     := inl _ (A_semiring_right_distributive S eq plus times sr)

; A_bs_plus_id_is_times_ann_d   := A_semiring_plus_id_is_times_ann_d S eq plus times sr
; A_bs_times_id_is_plus_ann_d   := A_semiring_times_id_is_plus_ann_d S eq plus times sr

; A_bs_left_left_absorptive_d   := A_semiring_left_left_absorptive_d S eq plus times sr
; A_bs_left_right_absorptive_d  := A_semiring_left_right_absorptive_d S eq plus times sr
; A_bs_right_left_absorptive_d  := bops_left_left_absorptive_implies_right_left S eq plus times tranS plus_comm 
                                     (A_semiring_left_left_absorptive_d S eq plus times sr)
; A_bs_right_right_absorptive_d := bops_left_right_absorptive_implies_right_right S eq plus times tranS plus_comm 
                                     (A_semiring_left_right_absorptive_d S eq plus times sr)
|}.

Definition lattice_proofs_to_bs_proofs :
     ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
       lattice_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times lp,                                                    
{|
  A_bs_left_distributive_d      := 
; A_bs_right_distributive_d     :=

; A_bs_plus_id_is_times_ann_d   :=
; A_bs_times_id_is_plus_ann_d   := 

; A_bs_left_left_absorptive_d   := 
; A_bs_left_right_absorptive_d  := 
; A_bs_right_left_absorptive_d  := 
; A_bs_right_right_absorptive_d := 
|}.

Definition distributive_lattice_proofs_to_lattice_proofs :
     ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
             distributive_lattice_proofs S eq plus times -> lattice_proofs S eq plus times
:= λ S eq plus times dlp,                                                      
{|
  A_lattice_absorptive           :=
; A_lattice_absorptive_dual      :=
 
; A_lattice_distributive_d       := 
; A_lattice_distributive_dual_d  :=
|}. 


Definition distributive_lattice_proofs_to_semiring_proofs :
     ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
             distributive_lattice_proofs S eq plus times -> semiring_proofs S eq plus times
:= λ S eq plus times dlp,                                                        
{|
  A_semiring_left_distributive        := A_distributive_lattice_distributive S eq plus times dlp 
; A_semiring_right_distributive       := left_distributive_implies_right_distributive S eq plus times times_comm
                                              (A_distributive_lattice_distributive S eq plus times dlp)

; A_semiring_plus_id_is_times_ann_d   := 
; A_semiring_times_id_is_plus_ann_d   := 
                                                                     
; A_semiring_left_left_absorptive_d   := 
; A_semiring_left_right_absorptive_d  := 
|}.





End ACAS.

Section CAS.
Definition bs_from_bs_C : ∀ {S : Type},  bs_C (S := S) -> bs (S := S)
:= λ {S} s, 
{| 
  bs_eqv          := bs_C_eqv s
; bs_plus         := bs_C_plus s
; bs_times        := bs_C_times s
; bs_plus_certs  := sg_certs_from_sg_C_certs 
                            (eqv_eq (bs_C_eqv s))
                            (bs_C_plus s)
                            (eqv_witness (bs_C_eqv s))
                            (eqv_new (bs_C_eqv s))                             
                            (bs_C_plus_certs s)  
; bs_times_certs := bs_C_times_certs s
; bs_certs       := bs_C_certs  s 
; bs_ast          := Ast_bs_from_bs_C (bs_C_ast s)
|}. 


Definition bs_from_bs_CS : ∀ {S : Type},  bs_CS (S := S) -> bs (S := S)
:= λ {S} s, 
{| 
  bs_eqv          := bs_CS_eqv s
; bs_plus         := bs_CS_plus s
; bs_times        := bs_CS_times s
; bs_plus_certs  := sg_certs_from_sg_CS_certs 
                      (eqv_eq  (bs_CS_eqv s))
                      (bs_CS_plus s)                      
                      (eqv_witness (bs_CS_eqv s))
                      (eqv_new (bs_CS_eqv s))                             
                      (bs_CS_plus_certs s)  
; bs_times_certs := bs_CS_times_certs s
; bs_certs       := bs_CS_certs s 
; bs_ast         := Ast_bs_from_bs_CS (bs_CS_ast s)
|}.

(* needs verification *) 
Definition bs_certs_from_semiring_certs : ∀ {S : Type},  @semiring_certificates S -> @bs_certificates S
:= λ {S} s,                                                                                                       
{|
  bs_left_distributive_d      := @Certify_Left_Distributive S
; bs_right_distributive_d     := @Certify_Right_Distributive S
; bs_plus_id_is_times_ann_d   := @semiring_plus_id_is_times_ann_d S s
; bs_times_id_is_plus_ann_d   := @semiring_times_id_is_plus_ann_d S s
; bs_left_left_absorptive_d   := @semiring_left_left_absorptive_d S s
; bs_left_right_absorptive_d  := @semiring_left_right_absorptive_d S s
; bs_right_left_absorptive_d  := match @semiring_left_left_absorptive_d S s with
                                 | Certify_Left_Left_Absorptive => @Certify_Right_Left_Absorptive S
                                 | Certify_Not_Left_Left_Absorptive p => @Certify_Not_Right_Left_Absorptive S p
                                 end 
; bs_right_right_absorptive_d := match @semiring_left_right_absorptive_d S s with
                                 | Certify_Left_Right_Absorptive => @Certify_Right_Right_Absorptive S
                                 | Certify_Not_Left_Right_Absorptive p => @Certify_Not_Right_Right_Absorptive S p
                                 end 
|}. 


Definition bs_C_from_semiring : ∀ {S : Type},  @semiring S -> @bs_C S
:= λ {S} s, 
{| 
  bs_C_eqv          := @semiring_eqv S s
; bs_C_plus         := @semiring_plus S s
; bs_C_times        := @semiring_times S s
; bs_C_plus_certs  :=  @semiring_plus_certs S s
; bs_C_times_certs := @semiring_times_certs S s
; bs_C_certs       := @bs_certs_from_semiring_certs S (semiring_certs s) 
; bs_C_ast         := Ast_bs_C_from_semiring (semiring_ast s)
|}. 



End CAS.

Section Verify.
 
End Verify.   
  