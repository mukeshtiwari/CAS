Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.

Section Theory.

End Theory.

Section ACAS.

Definition A_sg_proofs_from_sg_C_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> sg_C_proofs S r b -> sg_proofs S r b 
  := λ S r b s f Pf eqvS sgS,
{|
  A_sg_associative      := A_sg_C_associative S r b sgS 
; A_sg_congruence       := A_sg_C_congruence S r b sgS 
; A_sg_commutative_d    := inl _ (A_sg_C_commutative S r b sgS) 
; A_sg_selective_d      := A_sg_C_selective_d S r b sgS    
; A_sg_is_left_d        := inr _ (bop_commutative_implies_not_is_left S r b s f Pf
                                     (A_eqv_symmetric S r eqvS) 
                                     (A_eqv_transitive S r eqvS) 
                                     (A_sg_C_commutative S r b sgS))
; A_sg_is_right_d       := inr _ (bop_commutative_implies_not_is_right S r b s f Pf 
                                     (A_eqv_symmetric S r eqvS) 
                                     (A_eqv_transitive S r eqvS) 
                                     (A_sg_C_commutative S r b sgS))
; A_sg_idempotent_d     := A_sg_C_idempotent_d S r b sgS    
; A_sg_exists_id_d      := A_sg_C_exists_id_d S r b sgS    
; A_sg_exists_ann_d     := A_sg_C_exists_ann_d S r b sgS    
; A_sg_left_cancel_d    := A_sg_C_left_cancel_d S r b sgS    
; A_sg_right_cancel_d   := A_sg_C_right_cancel_d S r b sgS    
; A_sg_left_constant_d  := A_sg_C_left_constant_d S r b sgS
; A_sg_right_constant_d := A_sg_C_right_constant_d S r b sgS
; A_sg_anti_left_d      := A_sg_C_anti_left_d S r b sgS
; A_sg_anti_right_d     := A_sg_C_anti_right_d S r b sgS
|}. 

Definition A_sg_from_sg_C : ∀ (S : Type),  A_sg_C S -> A_sg S 
:= λ S sgS, 
   {| 
     A_sg_eq          := A_sg_C_eqv S sgS
   ; A_sg_bop         := A_sg_C_bop S sgS
   ; A_sg_proofs      := A_sg_proofs_from_sg_C_proofs S 
                            (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_bop S sgS)
                            (A_eqv_witness S (A_sg_C_eqv S sgS))
                            (A_eqv_new S (A_sg_C_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_C_eqv S sgS))
                            (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                            (A_sg_C_proofs S sgS)
   ; A_sg_bop_ast    := A_sg_C_bop_ast S sgS                                                                                                    
   ; A_sg_ast        := Ast_sg_from_sg_C (A_sg_C_ast S sgS)
   |}. 


Definition A_sg_C_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> sg_CI_proofs S r b -> sg_C_proofs S r b 
:= λ S r b s f Pf eqvS sgS, 
{|
  A_sg_C_associative      := A_sg_CI_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CI_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CI_commutative S r b sgS
; A_sg_C_selective_d      := A_sg_CI_selective_d S r b sgS    
; A_sg_C_idempotent_d     := inl _ (A_sg_CI_idempotent S r b sgS) 
; A_sg_C_exists_id_d      := A_sg_CI_exists_id_d S r b sgS    
; A_sg_C_exists_ann_d     := A_sg_CI_exists_ann_d S r b sgS    
; A_sg_C_left_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f 
                                       (A_eqv_congruence  S r eqvS) 
                                       Pf 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_associative S r b sgS)
                                       (A_sg_CI_congruence S r b sgS)
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                       (A_sg_CI_selective_d S r b sgS)
                                   )
; A_sg_C_right_cancel_d   := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative S r b s f
                                       (A_eqv_congruence  S r eqvS) 
                                       Pf 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_associative S r b sgS)
                                       (A_sg_CI_congruence S r b sgS)
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                       (A_sg_CI_selective_d S r b sgS)
                                   )
; A_sg_C_left_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b s f Pf 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                   ) 
; A_sg_C_right_constant_d := inr _ (bop_idempotent_and_commutative_imply_not_right_constant S r b s f Pf 
                                       (A_eqv_congruence  S r eqvS) 
                                       (A_eqv_reflexive S r eqvS) 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_eqv_transitive S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                       (A_sg_CI_commutative S r b sgS)
                                   ) 
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b s
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                   )
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b s 
                                       (A_eqv_symmetric S r eqvS) 
                                       (A_sg_CI_idempotent S r b sgS)
                                   )
|}. 


Definition A_sg_C_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv         := A_sg_CI_eqv S sgS
   ; A_sg_C_bop         := A_sg_CI_bop S sgS
   ; A_sg_C_proofs      := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_bop S sgS)
                            (A_eqv_witness S (A_sg_CI_eqv S sgS))
                            (A_eqv_new S (A_sg_CI_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CI_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_proofs S sgS)
   ; A_sg_C_bop_ast    := A_sg_CI_bop_ast S sgS 
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CI (A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CI_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S), sg_CS_proofs S r b -> sg_CI_proofs S r b 
:= λ S r b sg_CSS, 
{|
  A_sg_CI_associative        := A_sg_CS_associative S r b sg_CSS 
; A_sg_CI_congruence         := A_sg_CS_congruence S r b sg_CSS 
; A_sg_CI_commutative        := A_sg_CS_commutative S r b sg_CSS
; A_sg_CI_idempotent         := bop_selective_implies_idempotent S r b (A_sg_CS_selective S r b sg_CSS)
; A_sg_CI_selective_d        := inl _ (A_sg_CS_selective S r b sg_CSS) 
; A_sg_CI_exists_id_d        := A_sg_CS_exists_id_d S r b sg_CSS    
; A_sg_CI_exists_ann_d       := A_sg_CS_exists_ann_d S r b sg_CSS    
|}. 


Definition A_sg_CI_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_CI S 
:= λ S sgS, 
   {| 
     A_sg_CI_eqv         := A_sg_CS_eqv S sgS
   ; A_sg_CI_bop         := A_sg_CS_bop S sgS
   ; A_sg_CI_proofs      := A_sg_CI_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_bop S sgS) 
                            (A_sg_CS_proofs S sgS)
   ; A_sg_CI_bop_ast    := A_sg_CS_bop_ast S sgS                             
   ; A_sg_CI_ast        := Ast_sg_CI_from_sg_CS (A_sg_CS_ast S sgS)
   |}. 



Definition A_sg_C_proofs_from_sg_CK_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> sg_CK_proofs S r b -> sg_C_proofs S r b 
:= λ S r b s f Pf eqvS sgS, 
let right_cancel := bop_commutative_and_left_cancellative_imply_right_cancellative S r b 
                      (A_eqv_transitive S r eqvS) 
                      (A_sg_CK_commutative S r b sgS)
                      (A_sg_CK_left_cancel S r b sgS)    
in 
let not_idem := bop_cancellative_implies_not_idempotent S r b s f Pf 
                   (A_eqv_reflexive S r eqvS)  
                   (A_eqv_symmetric S r eqvS) 
                   (A_eqv_transitive S r eqvS) 
                   (A_sg_CK_associative S r b sgS)
                   (A_sg_CK_congruence S r b sgS)
                   (A_sg_CK_left_cancel S r b sgS)    
                   right_cancel 
                   (A_sg_CK_exists_id_d S r b sgS)
in 
{|
  A_sg_C_associative      := A_sg_CK_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CK_congruence S r b sgS 
; A_sg_C_commutative      := A_sg_CK_commutative S r b sgS
; A_sg_C_selective_d      := inr _ (bop_not_idempotent_implies_not_selective S r b not_idem)
; A_sg_C_idempotent_d     := inr _ not_idem 
; A_sg_C_exists_id_d      := A_sg_CK_exists_id_d S r b sgS    
; A_sg_C_exists_ann_d     := inr (bop_left_cancellative_implies_not_exists_ann S r b s f 
                                    (A_eqv_symmetric S r eqvS) 
                                    (A_eqv_transitive S r eqvS) 
                                    Pf 
                                    (A_sg_CK_left_cancel S r b sgS)    
                                 )
; A_sg_C_left_cancel_d    := inl _ (A_sg_CK_left_cancel S r b sgS)    
; A_sg_C_right_cancel_d   := inl _ right_cancel 
; A_sg_C_left_constant_d  := inr _ (bop_left_cancellative_implies_not_left_constant S r b s f Pf 
                                       (A_sg_CK_left_cancel S r b sgS)    
                                   )
; A_sg_C_right_constant_d := inr _ (bop_right_cancellative_implies_not_right_constant S r b s f Pf 
                                       right_cancel    
                                   )
; A_sg_C_anti_left_d      := A_sg_CK_anti_left_d S r b sgS 
; A_sg_C_anti_right_d     := A_sg_CK_anti_right_d S r b sgS
|}. 



Definition A_sg_C_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg_C S 
:= λ S sgS, 
   {| 
     A_sg_C_eqv         := A_sg_CK_eqv S sgS
   ; A_sg_C_bop         := A_sg_CK_bop S sgS
   ; A_sg_C_proofs      := A_sg_C_proofs_from_sg_CK_proofs S 
                            (A_eqv_eq S (A_sg_CK_eqv S sgS)) 
                            (A_sg_CK_bop S sgS)  
                            (A_eqv_witness S (A_sg_CK_eqv S sgS))
                            (A_eqv_new S (A_sg_CK_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CK_eqv S sgS))
                            (A_eqv_proofs S (A_sg_CK_eqv S sgS))                             
                            (A_sg_CK_proofs S sgS)
   ; A_sg_C_bop_ast    := A_sg_CK_bop_ast S sgS                                                         
   ; A_sg_C_ast        := Ast_sg_C_from_sg_CK (A_sg_CK_ast S sgS)
   |}. 




(* DERIVED UPCASTS *)

Definition A_sg_C_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r -> sg_CS_proofs S r b -> sg_C_proofs S r b
:= λ S r b s f Pf eqv sg_CS, A_sg_C_proofs_from_sg_CI_proofs S r b s f Pf eqv 
                     (A_sg_CI_proofs_from_sg_CS_proofs S r b sg_CS ). 


Definition A_sg_proofs_from_sg_CS_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r ->  sg_CS_proofs S r b -> sg_proofs S r b 
:= λ S r b s f Pf eqv sg_CS, A_sg_proofs_from_sg_C_proofs S r b s f Pf eqv (A_sg_C_proofs_from_sg_CS_proofs S r b s f Pf eqv sg_CS).

Definition A_sg_proofs_from_sg_CI_proofs : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
    brel_not_trivial S r f -> eqv_proofs S r ->  sg_CI_proofs S r b -> sg_proofs S r b 
:= λ S r b s f Pf eqv sg_CS, A_sg_proofs_from_sg_C_proofs S r b s f Pf eqv (A_sg_C_proofs_from_sg_CI_proofs S r b s f Pf eqv sg_CS).

Definition A_sg_from_sg_CI: ∀ (S : Type),  A_sg_CI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CI S sgS).  

Definition A_sg_from_sg_CK: ∀ (S : Type),  A_sg_CK S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CK S sgS).  

Definition A_sg_C_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg_C S 
:= λ S sgS, A_sg_C_from_sg_CI S (A_sg_CI_from_sg_CS S sgS ). 

Definition A_sg_from_sg_CS: ∀ (S : Type),  A_sg_CS S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CS S sgS).  


End ACAS.

Section CAS.

Definition sg_certs_from_sg_C_certs : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> sg_C_certificates (S := S) -> sg_certificates (S := S)  
:= λ {S} r b s f sgS, 
{|
  sg_associative      := Assert_Associative (S := S) 
; sg_congruence       := Assert_Bop_Congruence (S := S) 
; sg_commutative_d    := Certify_Commutative (S := S)  
; sg_selective_d      := sg_C_selective_d sgS    
; sg_is_left_d        := Certify_Not_Is_Left (cef_commutative_implies_not_is_left r b s f)
; sg_is_right_d       := Certify_Not_Is_Right (cef_commutative_implies_not_is_right r b s f)
; sg_idempotent_d     := sg_C_idempotent_d sgS    
; sg_exists_id_d      := sg_C_exists_id_d sgS    
; sg_exists_ann_d     := sg_C_exists_ann_d sgS    
; sg_left_cancel_d    := sg_C_left_cancel_d sgS    
; sg_right_cancel_d   := sg_C_right_cancel_d sgS    
; sg_left_constant_d  := sg_C_left_constant_d sgS
; sg_right_constant_d := sg_C_right_constant_d sgS
; sg_anti_left_d      := sg_C_anti_left_d sgS
; sg_anti_right_d     := sg_C_anti_right_d sgS
|}.


Definition sg_from_sg_C: ∀ {S : Type},  sg_C (S := S) -> sg (S := S)  
:= λ {S} sg_C, 
   {| 
     sg_eq    := sg_C_eqv sg_C
   ; sg_bop   := sg_C_bop sg_C
   ; sg_certs := sg_certs_from_sg_C_certs 
                    (eqv_eq (sg_C_eqv sg_C)) 
                    (sg_C_bop sg_C) 
                    (eqv_witness (sg_C_eqv sg_C))
                    (eqv_new (sg_C_eqv sg_C))                    
                    (sg_C_certs sg_C)
   ; sg_bop_ast    := sg_C_bop_ast sg_C                                                                                                    
   ; sg_ast   := Ast_sg_from_sg_C (sg_C_ast sg_C)
   |}. 


Definition sg_C_certs_from_sg_CI_certs : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> sg_CI_certificates (S := S) -> sg_C_certificates (S := S)  
:= λ {S} r b s f sgS, 
{|
  sg_C_associative      := Assert_Associative (S := S) 
; sg_C_congruence       := Assert_Bop_Congruence (S := S) 
; sg_C_commutative      := Assert_Commutative (S := S) 
; sg_C_selective_d      := sg_CI_selective_d sgS    
; sg_C_idempotent_d     := Certify_Idempotent (S := S)  
; sg_C_exists_id_d      := sg_CI_exists_id_d sgS    
; sg_C_exists_ann_d     := sg_CI_exists_ann_d sgS    
; sg_C_left_cancel_d    := 
     Certify_Not_Left_Cancellative 
        (match sg_CI_selective_d sgS with 
        | Certify_Selective => 
             cef_selective_and_commutative_imply_not_left_cancellative r b s f
        | Certify_Not_Selective (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative b s1 s2
        end) 
; sg_C_right_cancel_d   := 
     Certify_Not_Right_Cancellative 
        (match sg_CI_selective_d sgS with 
        | Certify_Selective => 
             cef_selective_and_commutative_imply_not_right_cancellative r b s f
        | Certify_Not_Selective (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative b s1 s2
        end) 
; sg_C_left_constant_d  := 
     Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b s f)
; sg_C_right_constant_d := 
     Certify_Not_Right_Constant (cef_idempotent_and_commutative_imply_not_right_constant r b s f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left s)
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s)
|}.


Definition sg_C_from_sg_CI: ∀ {S : Type},  sg_CI (S := S) -> sg_C (S := S)  
:= λ {S} sgS, 
   {| 
     sg_C_eqv   := sg_CI_eqv sgS
   ; sg_C_bop   := sg_CI_bop sgS
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs  
                      (eqv_eq  (sg_CI_eqv  sgS)) 
                      (sg_CI_bop sgS) 
                      (eqv_witness (sg_CI_eqv sgS))
                      (eqv_new (sg_CI_eqv sgS))                      
                      (sg_CI_certs sgS)
   ; sg_C_bop_ast    := sg_CI_bop_ast sgS 
   ; sg_C_ast   := Ast_sg_C_from_sg_CI (sg_CI_ast sgS)
   |}. 



Definition sg_CI_certs_from_sg_CS_certs : ∀ {S : Type}, sg_CS_certificates (S := S) -> sg_CI_certificates (S := S) 
:= λ {S} sgS, 
{|
  sg_CI_associative        := Assert_Associative (S := S) 
; sg_CI_congruence         := Assert_Bop_Congruence (S := S) 
; sg_CI_commutative        := Assert_Commutative (S := S) 
; sg_CI_idempotent         := Assert_Idempotent (S := S) 
; sg_CI_selective_d        := Certify_Selective (S := S) 
; sg_CI_exists_id_d        := sg_CS_exists_id_d sgS    
; sg_CI_exists_ann_d       := sg_CS_exists_ann_d sgS    
|}.

Definition sg_C_certs_from_sg_CS_certs: ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> @sg_CS_certificates S -> @sg_C_certificates S 
:= λ {S} eq b s f sgS, sg_C_certs_from_sg_CI_certs eq b s f (sg_CI_certs_from_sg_CS_certs sgS). 


Definition sg_CI_from_sg_CS: ∀ {S : Type},  sg_CS (S := S) -> sg_CI (S := S) 
:= λ {S} sgS, 
   {| 
     sg_CI_eqv   := sg_CS_eqv sgS
   ; sg_CI_bop   := sg_CS_bop sgS
   ; sg_CI_certs := sg_CI_certs_from_sg_CS_certs (sg_CS_certs sgS)
   ; sg_CI_bop_ast := sg_CS_bop_ast sgS                             
   ; sg_CI_ast   := Ast_sg_CI_from_sg_CS (sg_CS_ast sgS)
   |}. 

Definition sg_C_certs_from_sg_CK_certs : ∀ {S : Type}, brel S -> binary_op S -> S -> (S -> S) -> sg_CK_certificates (S := S) -> sg_C_certificates (S := S) 
:= λ {S} r b s f sgS, 
let ni := match sg_CK_exists_id_d sgS with 
          | Certify_Exists_Id i => cef_cancellative_and_exists_id_imply_not_idempotent r s i f
          | Certify_Not_Exists_Id => s 
          end 
in 
{|
  sg_C_associative      := Assert_Associative (S := S) 
; sg_C_congruence       := Assert_Bop_Congruence (S := S) 
; sg_C_commutative      := Assert_Commutative (S := S) 

; sg_C_idempotent_d     := Certify_Not_Idempotent (S := S) ni 
; sg_C_selective_d      := Certify_Not_Selective (S := S) 
                              (cef_not_idempotent_implies_not_selective ni) 

; sg_C_exists_id_d      := sg_CK_exists_id_d sgS
; sg_C_exists_ann_d     := Certify_Not_Exists_Ann (S := S) 

; sg_C_left_constant_d  := Certify_Not_Left_Constant (S := S) 
                              (cef_left_cancellative_implies_not_left_constant s f) 
; sg_C_right_constant_d := Certify_Not_Right_Constant (S := S) 
                              (cef_right_cancellative_implies_not_right_constant  s f) 

; sg_C_left_cancel_d    := Certify_Left_Cancellative (S := S) 
; sg_C_right_cancel_d   := Certify_Right_Cancellative (S := S) 
; sg_C_anti_left_d      := sg_CK_anti_left_d sgS 
; sg_C_anti_right_d     := sg_CK_anti_right_d sgS 
|}. 


Definition sg_C_from_sg_CK: ∀ {S : Type},  sg_CK (S := S) -> sg_C (S := S)  
:= λ {S} sg, 
   {| 
     sg_C_eqv   := sg_CK_eqv sg
   ; sg_C_bop   := sg_CK_bop sg
   ; sg_C_certs := sg_C_certs_from_sg_CK_certs 
                      (eqv_eq (sg_CK_eqv sg))
                      (sg_CK_bop sg)
                      (eqv_witness (sg_CK_eqv sg))
                      (eqv_new (sg_CK_eqv sg)) 
                      (sg_CK_certs sg)
   ; sg_C_bop_ast    := sg_CK_bop_ast sg                                                         
   ; sg_C_ast   := Ast_sg_C_from_sg_CK (sg_CK_ast sg)
   |}. 




(* DERIVED UPCASTS *) 

Definition sg_from_sg_CI: ∀ {S : Type},  sg_CI (S := S) -> sg (S := S)  
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CI sgS).  

Definition sg_from_sg_CK: ∀ {S : Type},  sg_CK (S := S) -> sg (S := S)
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CK sgS).  

Definition sg_C_from_sg_CS: ∀ {S : Type},  sg_CS (S := S) -> sg_C (S := S)
:= λ {S} sgS, sg_C_from_sg_CI (sg_CI_from_sg_CS sgS ). 

Definition sg_from_sg_CS: ∀ {S : Type},  sg_CS (S := S) -> sg (S := S)
:= λ {S} sgS, sg_from_sg_C (sg_C_from_sg_CS sgS).  


Definition sg_certs_from_sg_CI_certs : ∀ {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
            sg_CI_certificates (S := S) -> sg_certificates (S := S)
:= λ {S} r b s f sg_CI, sg_certs_from_sg_C_certs r b s f (sg_C_certs_from_sg_CI_certs r b s f sg_CI).

Definition sg_certs_from_sg_CS_certs : ∀ {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
            sg_CS_certificates (S := S) -> sg_certificates (S := S)
:= λ {S} r b s f sg_CI, sg_certs_from_sg_CI_certs r b s f (sg_CI_certs_from_sg_CS_certs sg_CI).

  

End CAS.

Section Verify.

Lemma correct_sg_certs_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_C_proofs S r b), 
       sg_certs_from_sg_C_certs r b s f (P2C_sg_C S r b sgS)
       = 
       P2C_sg S r b (A_sg_proofs_from_sg_C_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. destruct sgS. destruct eqvS. 
       unfold sg_certs_from_sg_C_certs, A_sg_proofs_from_sg_C_proofs, P2C_sg, P2C_sg_C; simpl. 
       reflexivity.        
Defined. 


Lemma correct_sg_C_certs_from_sg_CI_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CI_proofs S r b), 
       sg_C_certs_from_sg_CI_certs r b s f (P2C_sg_CI S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CI_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CI_certs, A_sg_C_proofs_from_sg_CI_proofs, P2C_sg_C, P2C_sg_CI; 
       simpl. 
       destruct A_sg_CI_selective_d as [ selS | [ [s1 s2] [P1 P2] ] ]; simpl. 
       reflexivity.        
       reflexivity.        
Defined. 

Lemma correct_sg_CI_certs_from_sg_CS_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_CS_proofs S r b), 
       sg_CI_certs_from_sg_CS_certs (P2C_sg_CS S r b sgS)
       = 
       P2C_sg_CI S r b (A_sg_CI_proofs_from_sg_CS_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CI_certs_from_sg_CS_certs, 
              A_sg_CI_proofs_from_sg_CS_proofs, P2C_sg_CI, P2C_sg_CS; simpl. 
       reflexivity.        
Defined. 

Lemma correct_sg_C_certs_from_sg_CS_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CS_proofs S r b), 
       sg_C_certs_from_sg_CS_certs r b s f (P2C_sg_CS S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CS_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. 
       unfold sg_C_certs_from_sg_CS_certs, A_sg_C_proofs_from_sg_CS_proofs.
       rewrite correct_sg_CI_certs_from_sg_CS_certs.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Defined.


Lemma correct_sg_certs_from_sg_CI_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f) (eqvS : eqv_proofs S r) (sgS : sg_CI_proofs S r b), 
       sg_certs_from_sg_CI_certs r b s f (P2C_sg_CI S r b sgS)
       = 
       P2C_sg S r b (A_sg_proofs_from_sg_CI_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. 
       unfold sg_certs_from_sg_CI_certs, A_sg_proofs_from_sg_CI_proofs.
       rewrite (correct_sg_C_certs_from_sg_CI_certs S r b s f nt eqvS).
       rewrite <- correct_sg_certs_from_sg_C_certs; auto. 
Qed. 


Lemma correct_sg_C_certs_from_sg_CK_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (nt : brel_not_trivial S r f)  (eqvS : eqv_proofs S r) (sgS : sg_CK_proofs S r b), 
       sg_C_certs_from_sg_CK_certs r b s f (P2C_sg_CK S r b sgS)
       = 
       P2C_sg_C S r b (A_sg_C_proofs_from_sg_CK_proofs S r b s f nt eqvS sgS). 
Proof. intros S r b s f nt eqvS sgS. destruct sgS. destruct eqvS. 
       destruct A_sg_CK_exists_id_d as [ [i Pi] | no_id ]; 
       unfold sg_C_certs_from_sg_CK_certs, A_sg_C_proofs_from_sg_CK_proofs, P2C_sg_C, P2C_sg_CK; 
       simpl. 
          reflexivity.        
          compute. reflexivity.        
Defined. 


Theorem correct_sg_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
         sg_from_sg_C (A2C_sg_C S P) = A2C_sg S (A_sg_from_sg_C S P). 
Proof. intros S P. destruct P.
       unfold sg_from_sg_C, A_sg_from_sg_C, A2C_sg_C, A2C_sg; simpl.
       destruct A_sg_C_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Defined. 
 

Theorem correct_sg_C_from_sg_CI : ∀ (S : Type) (P : A_sg_CI S),  
         sg_C_from_sg_CI (A2C_sg_CI S P) = A2C_sg_C S (A_sg_C_from_sg_CI S P). 
Proof. intros S P. unfold sg_C_from_sg_CI, A_sg_C_from_sg_CI, A2C_sg_CI, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Defined. 

Theorem correct_sg_CI_from_sg_CS : ∀ (S : Type) (P : A_sg_CS S),  
         sg_CI_from_sg_CS (A2C_sg_CS S P) = A2C_sg_CI S (A_sg_CI_from_sg_CS S P). 
Proof. intros S P. unfold sg_CI_from_sg_CS, A_sg_CI_from_sg_CS, A2C_sg_CI, A2C_sg_CS; simpl. 
       rewrite correct_sg_CI_certs_from_sg_CS_certs. reflexivity. 
Defined. 

Theorem correct_sg_C_from_sg_CK : ∀ (S : Type) (P : A_sg_CK S),  
         sg_C_from_sg_CK  (A2C_sg_CK S P) = A2C_sg_C S (A_sg_C_from_sg_CK S P). 
Proof. intros S P. unfold sg_C_from_sg_CK, A_sg_C_from_sg_CK, A2C_sg_CK, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CK_certs; auto. 
Defined. 


(* derived up casts. just a sanity check ... *)

Theorem correct_sg_from_sg_CI : ∀ (S : Type) (P : A_sg_CI S),  
         sg_from_sg_CI  (A2C_sg_CI S P) = A2C_sg S (A_sg_from_sg_CI S P). 
Proof. intros S P. unfold sg_from_sg_CI, A_sg_from_sg_CI. 
       rewrite correct_sg_C_from_sg_CI. rewrite correct_sg_from_sg_C. reflexivity. 
Defined. 

Theorem correct_sg_from_sg_CK : ∀ (S : Type) (P : A_sg_CK S),  
         sg_from_sg_CK  (A2C_sg_CK S P) = A2C_sg S (A_sg_from_sg_CK S P). 
Proof. intros S P. unfold sg_from_sg_CK, A_sg_from_sg_CK. 
       rewrite correct_sg_C_from_sg_CK. rewrite correct_sg_from_sg_C. reflexivity. 
Defined. 

Theorem correct_sg_C_from_sg_CS : ∀ (S : Type) (P : A_sg_CS S),  
    sg_C_from_sg_CS  (A2C_sg_CS S P) = A2C_sg_C S (A_sg_C_from_sg_CS S P).
Proof. intros S P. unfold sg_C_from_sg_CS, A_sg_C_from_sg_CS. 
       rewrite correct_sg_CI_from_sg_CS. rewrite correct_sg_C_from_sg_CI. reflexivity. 
Defined. 

Theorem correct_sg_from_sg_CS : ∀ (S : Type) (P : A_sg_CS S),  
         sg_from_sg_CS  (A2C_sg_CS S P) = A2C_sg S (A_sg_from_sg_CS S P). 
Proof. intros S P. unfold sg_from_sg_CS, A_sg_from_sg_CS. 
       rewrite correct_sg_C_from_sg_CS. rewrite correct_sg_from_sg_C. reflexivity. 
Defined. 

 
End Verify.   
  