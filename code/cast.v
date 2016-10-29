Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.  
Require Import CAS.code.cef.  
Require Import CAS.code.ast. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.cas_records. 


(*CC*) (* proved correct in verify/cas_correct.v *) 
(*!!*) (* NOT (yet) proved correct in verify/cas_correct.v *) 



(* UPCASTS *) 

(*CC*)
Definition sg_certs_from_sg_C_certs : ∀ (S : Type), brel S -> binary_op S -> eqv_certificates S -> sg_C_certificates S -> sg_certificates S 
:= λ S r b eqvS sgS, 
let ntS := eqv_nontrivial S eqvS in 
match certify_nontrivial_witness S ntS, certify_nontrivial_negate S ntS with 
| Certify_Witness _ s, Certify_Negate _ f => 
{|
  sg_associative      := Assert_Associative S 
; sg_congruence       := Assert_Bop_Congruence S 
; sg_commutative_d    := Certify_Commutative S 
; sg_selective_d      := sg_C_selective_d S sgS    
; sg_is_left_d        := Certify_Not_Is_Left S (cef_commutative_implies_not_is_left S r b s f)
; sg_is_right_d       := Certify_Not_Is_Right S (cef_commutative_implies_not_is_right S r b s f)
; sg_idempotent_d     := sg_C_idempotent_d S sgS    
; sg_exists_id_d      := sg_C_exists_id_d S sgS    
; sg_exists_ann_d     := sg_C_exists_ann_d S sgS    
; sg_left_cancel_d    := sg_C_left_cancel_d S sgS    
; sg_right_cancel_d   := sg_C_right_cancel_d S sgS    
; sg_left_constant_d  := sg_C_left_constant_d S sgS
; sg_right_constant_d := sg_C_right_constant_d S sgS
; sg_anti_left_d      := sg_C_anti_left_d S sgS
; sg_anti_right_d     := sg_C_anti_right_d S sgS
|}
end. 


Definition sg_from_sg_C: ∀ (S : Type),  sg_C S -> sg S 
:= λ S sg_CS, 
   {| 
     sg_eq    := sg_C_eqv S sg_CS
   ; sg_bop   := sg_C_bop S sg_CS
   ; sg_certs := sg_certs_from_sg_C_certs S 
                    (eqv_eq S (sg_C_eqv S sg_CS)) 
                    (sg_C_bop S sg_CS) 
                    (eqv_certs S (sg_C_eqv S sg_CS))
                    (sg_C_certs S sg_CS) 
   ; sg_ast   := Ast_sg_from_sg_C (sg_C_ast S sg_CS)
   |}. 



(*CC*)
Definition sg_C_certs_from_sg_CI_certs : ∀ (S : Type), brel S -> binary_op S -> eqv_certificates S -> sg_CI_certificates S -> sg_C_certificates S 
:= λ S r b eqvS sgS, 
let ntS := eqv_nontrivial S eqvS in 
match certify_nontrivial_witness S ntS, certify_nontrivial_negate S ntS with 
| Certify_Witness _ s, Certify_Negate _ f => 
{|
  sg_C_associative      := Assert_Associative S 
; sg_C_congruence       := Assert_Bop_Congruence S 
; sg_C_commutative      := Assert_Commutative S 
; sg_C_selective_d      := sg_CI_selective_d S sgS    
; sg_C_idempotent_d     := Certify_Idempotent S 
; sg_C_exists_id_d      := sg_CI_exists_id_d S sgS    
; sg_C_exists_ann_d     := sg_CI_exists_ann_d S sgS    
; sg_C_left_cancel_d    := 
     Certify_Not_Left_Cancellative S 
        (match sg_CI_selective_d S sgS with 
        | Certify_Selective _ => 
             cef_selective_and_commutative_imply_not_left_cancellative S r b s f
        | Certify_Not_Selective _ (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative S b s1 s2
        end) 
; sg_C_right_cancel_d   := 
     Certify_Not_Right_Cancellative S 
        (match sg_CI_selective_d S sgS with 
        | Certify_Selective _ => 
             cef_selective_and_commutative_imply_not_right_cancellative S r b s f
        | Certify_Not_Selective _ (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative S b s1 s2
        end) 
; sg_C_left_constant_d  := 
     Certify_Not_Left_Constant S (cef_idempotent_and_commutative_imply_not_left_constant S r b s f)
; sg_C_right_constant_d := 
     Certify_Not_Right_Constant S (cef_idempotent_and_commutative_imply_not_right_constant S r b s f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left S (cef_idempotent_implies_not_anti_left S s)
; sg_C_anti_right_d     := Certify_Not_Anti_Right S (cef_idempotent_implies_not_anti_right S s)
|}
end. 

(*CC*)
Definition sg_C_from_sg_CI: ∀ (S : Type),  sg_CI S -> sg_C S 
:= λ S sgS, 
   {| 
     sg_C_eqv   := sg_CI_eqv S sgS
   ; sg_C_bop   := sg_CI_bop S sgS
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs S 
                      (eqv_eq S (sg_CI_eqv S sgS)) 
                      (sg_CI_bop S sgS) 
                      (eqv_certs S (sg_CI_eqv S sgS))
                      (sg_CI_certs S sgS) 
   ; sg_C_ast   := Ast_sg_C_from_sg_CI (sg_CI_ast S sgS)
   |}. 




(*CC*)
Definition sg_CI_certs_from_sg_CS_certs : ∀ (S : Type), sg_CS_certificates S -> sg_CI_certificates S 
:= λ S sgS, 
{|
  sg_CI_associative        := Assert_Associative S 
; sg_CI_congruence         := Assert_Bop_Congruence S 
; sg_CI_commutative        := Assert_Commutative S 
; sg_CI_idempotent         := Assert_Idempotent S 
; sg_CI_selective_d        := Certify_Selective S 
; sg_CI_exists_id_d        := sg_CS_exists_id_d S sgS    
; sg_CI_exists_ann_d       := sg_CS_exists_ann_d S sgS    
|}. 

(*CC*)
Definition sg_CI_from_sg_CS: ∀ (S : Type),  sg_CS S -> sg_CI S 
:= λ S sgS, 
   {| 
     sg_CI_eqv   := sg_CS_eqv S sgS
   ; sg_CI_bop   := sg_CS_bop S sgS
   ; sg_CI_certs := sg_CI_certs_from_sg_CS_certs S (sg_CS_certs S sgS) 
   ; sg_CI_ast   := Ast_sg_CI_from_sg_CS (sg_CS_ast S sgS)
   |}. 

(*CC*)
Definition sg_C_certs_from_sg_CK_certs : ∀ (S : Type), brel S -> binary_op S -> eqv_certificates S -> sg_CK_certificates S -> sg_C_certificates S 
:= λ S r b eqvS sgS, 
let ntS := eqv_nontrivial S eqvS in 
match certify_nontrivial_witness S ntS, certify_nontrivial_negate S ntS with 
| Certify_Witness _ s, Certify_Negate _ f => 
let ni := match sg_CK_exists_id_d S sgS with 
          | Certify_Exists_Id _ i => cef_cancellative_and_exists_id_imply_not_idempotent S r s i f
          | Certify_Not_Exists_Id _ => s 
          end 
in 
{|
  sg_C_associative      := Assert_Associative S 
; sg_C_congruence       := Assert_Bop_Congruence S 
; sg_C_commutative      := Assert_Commutative S 

; sg_C_idempotent_d     := Certify_Not_Idempotent S ni 
; sg_C_selective_d      := Certify_Not_Selective S 
                              (cef_not_idempotent_implies_not_selective S ni) 

; sg_C_exists_id_d      := sg_CK_exists_id_d S sgS
; sg_C_exists_ann_d     := Certify_Not_Exists_Ann S 

; sg_C_left_constant_d  := Certify_Not_Left_Constant S 
                              (cef_left_cancellative_implies_not_left_constant S s f) 
; sg_C_right_constant_d := Certify_Not_Right_Constant S 
                              (cef_right_cancellative_implies_not_right_constant S s f) 

; sg_C_left_cancel_d    := Certify_Left_Cancellative S 
; sg_C_right_cancel_d   := Certify_Right_Cancellative S 
; sg_C_anti_left_d      := sg_CK_anti_left_d S sgS 
; sg_C_anti_right_d     := sg_CK_anti_right_d S sgS 
|}
end. 



(*CC*)
Definition sg_C_from_sg_CK: ∀ (S : Type),  sg_CK S -> sg_C S 
:= λ S sg, 
   {| 
     sg_C_eqv   := sg_CK_eqv S sg
   ; sg_C_bop   := sg_CK_bop S sg
   ; sg_C_certs := sg_C_certs_from_sg_CK_certs S 
                      (eqv_eq S (sg_CK_eqv S sg))
                      (sg_CK_bop S sg)
                      (eqv_certs S (sg_CK_eqv S sg)) 
                      (sg_CK_certs S sg) 
   ; sg_C_ast   := Ast_sg_C_from_sg_CK (sg_CK_ast S sg)
   |}. 




(* DERIVED UPCASTS *) 

Definition sg_from_sg_CI: ∀ (S : Type),  sg_CI S -> sg S 
:= λ S sgS, sg_from_sg_C S (sg_C_from_sg_CI S sgS).  

Definition sg_from_sg_CK: ∀ (S : Type),  sg_CK S -> sg S 
:= λ S sgS, sg_from_sg_C S (sg_C_from_sg_CK S sgS).  

Definition sg_C_from_sg_CS: ∀ (S : Type),  sg_CS S -> sg_C S 
:= λ S sgS, sg_C_from_sg_CI S (sg_CI_from_sg_CS S sgS ). 

Definition sg_from_sg_CS: ∀ (S : Type),  sg_CS S -> sg S 
:= λ S sgS, sg_from_sg_C S (sg_C_from_sg_CS S sgS).  


Definition sg_certs_from_sg_CI_certs : ∀ (S : Type) (r : brel S) (eqv : eqv_certificates S) (b : binary_op S),
            sg_CI_certificates S -> sg_certificates S 
:= λ S r eqv b sg_CI, sg_certs_from_sg_C_certs S r b eqv (sg_C_certs_from_sg_CI_certs S r b eqv sg_CI).

Definition sg_certs_from_sg_CS_certs : ∀ (S : Type) (r : brel S) (eqv : eqv_certificates S) (b : binary_op S),
            sg_CS_certificates S -> sg_certificates S 
:= λ S r eqv b sg_CI, sg_certs_from_sg_CI_certs S r eqv b (sg_CI_certs_from_sg_CS_certs S sg_CI).




(* DOWNCASTS *) 

(*CC*)
Definition sg_C_certs_option_from_sg_certs : ∀ (S : Type), sg_certificates S -> option (sg_C_certificates S) 
:= λ S sgS, 
   match sg_commutative_d S sgS with 
   | Certify_Commutative _ => Some
      {|
        sg_C_associative      := Assert_Associative S 
      ; sg_C_congruence       := Assert_Bop_Congruence S 
      ; sg_C_commutative      := Assert_Commutative S 
      ; sg_C_selective_d      := sg_selective_d S sgS    
      ; sg_C_idempotent_d     := sg_idempotent_d S sgS    
      ; sg_C_exists_id_d      := sg_exists_id_d S sgS    
      ; sg_C_exists_ann_d     := sg_exists_ann_d S sgS   
      ; sg_C_left_cancel_d    := sg_left_cancel_d S sgS    
      ; sg_C_right_cancel_d   := sg_right_cancel_d S sgS    
      ; sg_C_left_constant_d  := sg_left_constant_d S sgS
      ; sg_C_right_constant_d := sg_right_constant_d S sgS
      ; sg_C_anti_left_d      := sg_anti_left_d  S sgS
      ; sg_C_anti_right_d     := sg_anti_right_d S sgS
     |}
   | _ => None
   end . 

(*CC*)
Definition sg_C_option_from_sg: ∀ (S : Type),  sg S -> option (sg_C S) 
:= λ S sgS, 
   match sg_C_certs_option_from_sg_certs S (sg_certs S sgS) with 
   | None => None
   | Some c => Some
      {| 
        sg_C_eqv   := sg_eq S sgS
      ; sg_C_bop   := sg_bop S sgS
      ; sg_C_certs := c 
      ; sg_C_ast   := Ast_sg_C_from_sg (sg_ast S sgS)
      |}
   end. 


(*CC*)
Definition sg_CI_certs_option_from_sg_C_certs : ∀ (S : Type), sg_C_certificates S -> option (sg_CI_certificates S) 
:= λ S sg_CS, 
   match sg_C_idempotent_d S sg_CS with 
   | Certify_Idempotent _ => Some
      {|
        sg_CI_associative        := Assert_Associative S 
      ; sg_CI_congruence         := Assert_Bop_Congruence S 
      ; sg_CI_commutative        := Assert_Commutative S 
      ; sg_CI_idempotent         := Assert_Idempotent S 
      ; sg_CI_selective_d        := sg_C_selective_d S sg_CS    
      ; sg_CI_exists_id_d        := sg_C_exists_id_d S sg_CS    
      ; sg_CI_exists_ann_d       := sg_C_exists_ann_d S sg_CS    
     |}
   | _ => None
   end. 

(*CC*)
Definition sg_CI_option_from_sg_C: ∀ (S : Type),  sg_C S -> option (sg_CI S) 
:= λ S sg_CS, 
   match sg_CI_certs_option_from_sg_C_certs S (sg_C_certs S sg_CS) with 
   | None => None
   | Some certs => Some
      {| 
        sg_CI_eqv   := sg_C_eqv S sg_CS
      ; sg_CI_bop   := sg_C_bop S sg_CS
      ; sg_CI_certs := certs 
      ; sg_CI_ast   := Ast_sg_CI_from_sg_C (sg_C_ast S sg_CS)
      |}
   end. 

(*CC*)
Definition sg_CS_certs_option_from_sg_CI_certs : ∀ (S : Type), sg_CI_certificates S -> option (sg_CS_certificates S) 
:= λ S sg_CIS, 
   match sg_CI_selective_d S sg_CIS with 
   | Certify_Selective _ => Some
      {|
        sg_CS_associative        := Assert_Associative S 
      ; sg_CS_congruence         := Assert_Bop_Congruence S 
      ; sg_CS_commutative        := Assert_Commutative S 
      ; sg_CS_selective          := Assert_Selective S 
      ; sg_CS_exists_id_d        := sg_CI_exists_id_d S sg_CIS    
      ; sg_CS_exists_ann_d       := sg_CI_exists_ann_d S sg_CIS    
     |}
   | _ => None
   end . 


(*CC*)
Definition sg_CS_option_from_sg_CI: ∀ (S : Type),  sg_CI S -> option (sg_CS S) 
:= λ S sg_CIS, 
   match sg_CS_certs_option_from_sg_CI_certs S (sg_CI_certs S sg_CIS) with 
   | None => None
   | Some certs => Some
      {| 
        sg_CS_eqv   := sg_CI_eqv S sg_CIS
      ; sg_CS_bop   := sg_CI_bop S sg_CIS
      ; sg_CS_certs := certs 
      ; sg_CS_ast   := Ast_sg_CS_from_sg_CI (sg_CI_ast S sg_CIS)
      |}
   end. 

(*CC*)
Definition sg_CK_certs_option_from_sg_C_certs : ∀ (S : Type), sg_C_certificates S -> option (sg_CK_certificates S) 
:= λ S sgS, 
   match sg_C_left_cancel_d S sgS with 
   | Certify_Left_Cancellative _ => Some
      {|
        sg_CK_associative        := sg_C_associative S sgS    
      ; sg_CK_congruence         := sg_C_congruence S sgS    
      ; sg_CK_commutative        := sg_C_commutative S sgS    
      ; sg_CK_left_cancel        := Assert_Left_Cancellative S
      ; sg_CK_exists_id_d        := sg_C_exists_id_d S sgS    
      ; sg_CK_anti_left_d        := sg_C_anti_left_d S sgS   
      ; sg_CK_anti_right_d       := sg_C_anti_right_d S sgS   
     |}
   |  _ => None
   end . 

(*CC*)
Definition sg_CK_option_from_sg_C: ∀ (S : Type),  sg_C S -> option (sg_CK S) 
:= λ S sgS, 
   match sg_CK_certs_option_from_sg_C_certs S (sg_C_certs S sgS) with 
   | None => None
   | Some c => Some
      {| 
        sg_CK_eqv         := sg_C_eqv S sgS
      ; sg_CK_bop         := sg_C_bop S sgS
      ; sg_CK_certs       := c
      ; sg_CK_ast         := Ast_sg_CK_from_sg_C (sg_C_ast S sgS)
      |}
   end. 


(*!!*)
Definition sg_CS_certs_option_from_sg_certs : ∀ (S : Type),  sg_certificates S -> option (sg_CS_certificates S) 
:= λ S sgS, 
   match sg_C_certs_option_from_sg_certs S sgS with 
   | None => None
   | Some sgC => 
      match sg_CI_certs_option_from_sg_C_certs S sgC with 
      | None => None
      | Some sgCI => sg_CS_certs_option_from_sg_CI_certs S sgCI 
      end 
   end. 

(* DERIVED DOWNCASTS *) 

Definition sg_CI_option_from_sg: ∀ (S : Type),  sg S -> option (sg_CI S) 
:= λ S sgS, 
   match sg_C_option_from_sg S sgS with 
   | None => None
   | Some sgS => sg_CI_option_from_sg_C S sgS 
   end. 


Definition sg_CK_option_from_sg: ∀ (S : Type),  sg S -> option (sg_CK S) 
:= λ S sgS, 
   match sg_C_option_from_sg S sgS with 
   | None => None
   | Some sgS => sg_CK_option_from_sg_C S sgS 
   end. 


Definition sg_CS_option_from_sg_C : ∀ (S : Type),  sg_C S -> option (sg_CS S) 
:= λ S sgS, 
   match sg_CI_option_from_sg_C S sgS with 
   | None => None
   | Some sgS => sg_CS_option_from_sg_CI S sgS 
   end. 


Definition sg_CS_option_from_sg: ∀ (S : Type),  sg S -> option (sg_CS S) 
:= λ S sgS, 
   match sg_CI_option_from_sg S sgS with 
   | None => None
   | Some sgS => sg_CS_option_from_sg_CI S sgS 
   end. 



(* ******************************************************************

BS 

****************************************************************** *) 

(*!!*)
Definition bs_from_bs_C : ∀ (S : Type),  bs_C S -> bs S 
:= λ S s, 
{| 
  bs_eqv          := bs_C_eqv S s
; bs_plus         := bs_C_plus S s
; bs_times        := bs_C_times S s
; bs_plus_certs  := sg_certs_from_sg_C_certs S 
                            (eqv_eq S (bs_C_eqv S s))
                            (bs_C_plus S s)
                            (eqv_certs S (bs_C_eqv S s)) 
                            (bs_C_plus_certs S s)  
; bs_times_certs := bs_C_times_certs S s
; bs_certs       := bs_C_certs S s 
; bs_ast          := Ast_bs_from_bs_C (bs_C_ast S s)
|}. 



(*!!*)
Definition bs_from_bs_CS : ∀ (S : Type),  bs_CS S -> bs S 
:= λ S s, 
{| 
  bs_eqv          := bs_CS_eqv S s
; bs_plus         := bs_CS_plus S s
; bs_times        := bs_CS_times S s
; bs_plus_certs  := sg_certs_from_sg_CS_certs S 
                            (eqv_eq S (bs_CS_eqv S s))
                            (eqv_certs S (bs_CS_eqv S s)) (bs_CS_plus S s)
                            (bs_CS_plus_certs S s)  
; bs_times_certs := bs_CS_times_certs S s
; bs_certs       := bs_CS_certs S s 
; bs_ast         := Ast_bs_from_bs_CS (bs_CS_ast S s)
|}. 


(*!!*)
Definition bs_C_option_from_bs : ∀ (S : Type),  bs S -> option (bs_C S) 
:= λ S s, 
   match sg_C_certs_option_from_sg_certs _ (bs_plus_certs S s) with 
   | None => None
   | Some sg_C_p => Some (
     {| 
         bs_C_eqv          := bs_eqv S s
       ; bs_C_plus         := bs_plus S s
       ; bs_C_times        := bs_times S s
       ; bs_C_plus_certs  := sg_C_p
       ; bs_C_times_certs := bs_times_certs S s
       ; bs_C_certs       := bs_certs S s 
       ; bs_C_ast          := Ast_bs_C_from_bs (bs_ast S s)
    |})
   end. 


(*!!*)
Definition bs_CS_option_from_bs : ∀ (S : Type),  bs S -> option (bs_CS S) 
:= λ S s, 
   match sg_CS_certs_option_from_sg_certs _ (bs_plus_certs S s) with 
   | None => None
   | Some sg_CS_p => Some (
     {| 
         bs_CS_eqv          := bs_eqv S s
       ; bs_CS_plus         := bs_plus S s
       ; bs_CS_times        := bs_times S s
       ; bs_CS_plus_certs  := sg_CS_p
       ; bs_CS_times_certs := bs_times_certs S s
       ; bs_CS_certs       := bs_certs S s 
       ; bs_CS_ast          := Ast_bs_CS_from_bs (bs_ast S s)
    |})
   end. 

