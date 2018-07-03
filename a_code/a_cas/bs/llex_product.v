Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel.
Require Import CAS.code.bop.
Require Import CAS.code.combined.
Require Import CAS.code.cef. 

Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.product.
Require Import CAS.a_code.a_cas.sg.llex. 
Require Import CAS.a_code.a_cas.sg.product.
Require Import CAS.a_code.a_cas.sg.cast_up.

Require Import CAS.theory.bs.llex_product. 
Require Import CAS.theory.brel_properties. (* abstractions broken? *) 
Require Import CAS.theory.facts.

Definition bs_proofs_llex : 
  ∀ (S T: Type) (rS : brel S) (rT : brel T) (plusS timesS : binary_op S) (plusT timesT : binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 

     sg_CS_proofs S rS plusS ->          (*NB*) 
     sg_proofs S rS timesS ->            
     sg_C_proofs T rT plusT ->           (*NB*) 
     sg_proofs T rT timesT ->            

     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 

        bs_proofs (S * T) 
           (brel_product rS rT) 
           (bop_llex rS plusS plusT)
           (bop_product timesS timesT)

:= λ S T rS rT plusS timesS plusT timesT s t eqvS eqvT sg_CS_S sg_S sg_C_T sg_T pS pT,
let refS   := A_eqv_reflexive S rS eqvS in 
let symS   := A_eqv_symmetric S rS eqvS in 
let transS := A_eqv_transitive S rS eqvS in 
let refT   := A_eqv_reflexive T rT eqvT in 
let symT   := A_eqv_symmetric T rT eqvT in 
let transT := A_eqv_transitive T rT eqvT in 
let selS := A_sg_CS_selective S rS plusS sg_CS_S in 
let comS := A_sg_CS_commutative S rS plusS sg_CS_S in 
let comT := A_sg_C_commutative T rT plusT sg_C_T in   
let c_timesS := A_sg_congruence S rS timesS sg_S in 
{|
  A_bs_left_distributive_d    := 
   bops_llex_product_left_distributive_decide S T rS rT s t plusS timesS plusT timesT refS symS transS refT symT transT c_timesS selS comS comT
     (A_sg_left_cancel_d S rS timesS  sg_S) 
     (A_sg_left_constant_d T rT timesT sg_T)
     (A_bs_left_distributive_d S rS plusS timesS pS)
     (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d   := 
   bops_llex_product_right_distributive_decide S T rS rT s t plusS timesS plusT timesT refS symS transS refT symT transT c_timesS selS comS comT
     (A_sg_right_cancel_d S rS timesS  sg_S) 
     (A_sg_right_constant_d T rT timesT sg_T)
     (A_bs_right_distributive_d S rS plusS timesS pS)
     (A_bs_right_distributive_d T rT plusT timesT pT)
; A_bs_plus_id_is_times_ann_d :=  
    bops_llex_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS transS refT comS 
     (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)
     (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)
; A_bs_times_id_is_plus_ann_d :=  
   bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS transS refT comS 
   (bop_selective_implies_idempotent S rS plusS (A_sg_CS_selective S rS plusS sg_CS_S))
   (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
   (A_bs_times_id_is_plus_ann_d T rT plusT timesT pT)
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T rS rT t plusS timesS plusT timesT refT
    (A_bs_left_left_absorptive_d S rS plusS timesS pS)
    (A_bs_left_left_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_left_d S rS timesS sg_S)
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T rS rT t plusS timesS plusT timesT refT 
    (A_bs_left_right_absorptive_d S rS plusS timesS pS)
    (A_bs_left_right_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_right_d S rS timesS sg_S)
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T rS rT t plusS timesS plusT timesT symS transS refT 
       (A_bs_right_left_absorptive_d S rS plusS timesS pS)
       (A_bs_right_left_absorptive_d T rT plusT timesT pT)
       (A_sg_anti_left_d S rS timesS sg_S)
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T rS rT t plusS timesS plusT timesT symS transS refT
       (A_bs_right_right_absorptive_d S rS plusS timesS pS)
       (A_bs_right_right_absorptive_d T rT plusT timesT pT)
       (A_sg_anti_right_d S rS timesS sg_S)
|}. 


Definition A_bs_C_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_C T -> A_bs_C (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_bs_CS_eqv S bsS   in
let eqvT   := A_bs_C_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_bs_CS_plus S bsS  in 
let plusT  := A_bs_C_plus T bsT  in
let timesS := A_bs_CS_times S bsS in 
let timesT := A_bs_C_times T bsT in 
{| 
     A_bs_C_eqv         := A_eqv_product S T eqvS eqvT 
   ; A_bs_C_plus        := bop_llex rS plusS plusT 
   ; A_bs_C_times       := bop_product timesS timesT 
   ; A_bs_C_plus_proofs := sg_C_proofs_llex S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_C_plus_proofs T bsT) 
   ; A_bs_C_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_C_times_proofs T bsT)
   ; A_bs_C_proofs    := bs_proofs_llex S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_times_proofs S bsS) 
                           (A_bs_C_plus_proofs T bsT) 
                           (A_bs_C_times_proofs T bsT) 
                           (A_bs_CS_proofs S bsS) 
                           (A_bs_C_proofs T bsT) 
   ; A_bs_C_ast        := Ast_bs_C_llex (A_bs_CS_ast S bsS, A_bs_C_ast T bsT)
|}. 



Definition A_bs_CS_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_CS T -> A_bs_CS (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_bs_CS_eqv S bsS   in
let eqvT   := A_bs_CS_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_bs_CS_plus S bsS  in 
let plusT  := A_bs_CS_plus T bsT  in
let timesS := A_bs_CS_times S bsS in 
let timesT := A_bs_CS_times T bsT in 
{| 
     A_bs_CS_eqv         := A_eqv_product S T eqvS eqvT 
   ; A_bs_CS_plus        := bop_llex rS plusS plusT 
   ; A_bs_CS_times       := bop_product timesS timesT 
   ; A_bs_CS_plus_proofs := sg_CS_proofs_llex S T rS rT plusS plusT peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_plus_proofs T bsT) 
   ; A_bs_CS_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_CS_times_proofs T bsT)
   ; A_bs_CS_proofs    := bs_proofs_llex S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_times_proofs S bsS) 
                           (A_sg_C_proofs_from_sg_CS_proofs T _ _ t g Pg (A_eqv_proofs T (A_bs_CS_eqv T bsT)) (A_bs_CS_plus_proofs T bsT))
                           (A_bs_CS_times_proofs T bsT)
                           (A_bs_CS_proofs S bsS) 
                           (A_bs_CS_proofs T bsT) 
   ; A_bs_CS_ast        := Ast_bs_CS_llex (A_bs_CS_ast S bsS, A_bs_CS_ast T bsT)
|}. 

