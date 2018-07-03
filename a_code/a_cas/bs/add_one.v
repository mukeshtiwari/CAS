Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.

Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.a_code.proof_records.
Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.eqv.add_constant. 
Require Import CAS.a_code.a_cas.sg.add_id.
Require Import CAS.a_code.a_cas.sg.add_ann.

Require Import CAS.theory.bs.add_ann_add_id.
Require Import CAS.theory.bs.add_id_add_ann.

Require Import CAS.theory.facts.

Definition bs_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S) (s : S), 
     eqv_proofs S rS -> 
     sg_proofs S rS plusS -> 
     bs_proofs S rS plusS timesS -> 
        bs_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_ann plusS c)
           (bop_add_id timesS c)
:= λ S rS c plusS timesS s eqvS ppS pS, 
{|
  A_bs_left_distributive_d    := 
     bops_add_one_left_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d S rS plusS timesS pS) 
; A_bs_right_distributive_d   := 
     bops_add_one_right_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d S rS plusS timesS pS) 
; A_bs_left_left_absorptive_d      := 
     bops_add_one_left_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
; A_bs_left_right_absorptive_d      := 
     bops_add_one_left_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
; A_bs_right_left_absorptive_d     := 
     bops_add_one_right_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
; A_bs_right_right_absorptive_d     := 
     bops_add_one_right_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_sg_idempotent_d S rS plusS ppS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
; A_bs_plus_id_is_times_ann_d := 
    bops_add_one_id_equals_ann_decide S rS c plusS timesS s (A_eqv_reflexive S rS eqvS) 
      (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)
; A_bs_times_id_is_plus_ann_d :=  
     inl _ (bops_add_id_add_ann_id_equals_ann S rS c timesS plusS (A_eqv_reflexive S rS eqvS))

|}. 

Definition A_bs_add_one : ∀ (S : Type),  A_bs S -> cas_constant -> A_bs (with_constant S) 
:= λ S bsS c,
let eqvS  := A_bs_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_plus S bsS in
let times := A_bs_times S bsS in
let pproofs := A_bs_plus_proofs S bsS in
let tproofs := A_bs_times_proofs S bsS in 
{| 
     A_bs_eqv          := A_eqv_add_constant S eqvS c 
   ; A_bs_plus         := bop_add_ann plus c
   ; A_bs_times        := bop_add_id times c
   ; A_bs_plus_proofs  := sg_proofs_add_ann S rS c plus s f Pf peqvS pproofs 
   ; A_bs_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs 
   ; A_bs_proofs       := bs_proofs_add_one S rS c plus times s peqvS pproofs (A_bs_proofs S bsS)
   ; A_bs_ast          := Ast_bs_add_one (c, A_bs_ast S bsS)
|}.





Definition lattice_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS join ->
     sg_CI_proofs S rS meet ->      
     lattice_proofs S rS join meet -> 
        lattice_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_ann join c)
           (bop_add_id meet c)
:= λ S rS c join meet eqvS p_join p_meet pl, 
{|
  A_lattice_absorptive        := 
    bops_add_ann_add_id_left_left_absorptive S rS c join meet
       (A_eqv_symmetric S rS eqvS)
       (A_sg_CI_idempotent S rS join p_join)
       (A_lattice_absorptive S rS join meet pl)
; A_lattice_absorptive_dual   := 
    bops_add_id_add_ann_left_left_absorptive S rS c meet join 
      (A_eqv_reflexive S rS eqvS)
      (A_lattice_absorptive_dual S rS join meet pl)                                                                        
; A_lattice_distributive_d      :=
     bops_add_one_left_distributive_decide S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (inl _ (A_sg_CI_idempotent S rS join p_join))        
        (inl _ (A_lattice_absorptive S rS join meet pl))
        (inl _ (bops_left_right_absorptive_implies_right_left S rS join meet
                 (A_eqv_reflexive S rS eqvS)                                                       
                 (A_eqv_transitive S rS eqvS)
                 (A_sg_CI_congruence S rS join p_join)
                 (A_sg_CI_commutative S rS join p_join)
                 (A_sg_CI_commutative S rS meet p_meet)
                 (bops_left_left_absorptive_implies_left_right S rS join meet
                    (A_eqv_reflexive S rS eqvS)                                                          
                    (A_eqv_transitive S rS eqvS)
                    (A_sg_CI_congruence S rS join p_join)
                    (A_sg_CI_commutative S rS meet p_meet)
                    (A_lattice_absorptive S rS join meet pl)
                 )                                          
               )
        )
        (A_lattice_distributive_d S rS join meet pl) 
; A_lattice_distributive_dual_d :=
   bops_add_zero_left_distributive_decide S rS c meet join
        (A_eqv_reflexive S rS eqvS)
        (A_lattice_distributive_dual_d S rS join meet pl) 
|}.


Definition A_lattice_add_one : ∀ (S : Type),  A_lattice S -> cas_constant -> A_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_lattice_eqv          := A_eqv_add_constant S (A_lattice_eqv S bsS) c 
   ; A_lattice_join         := bop_add_ann (A_lattice_join S bsS) c
   ; A_lattice_meet        := bop_add_id (A_lattice_meet S bsS) c
   ; A_lattice_join_proofs  := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_join S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_proofs S bsS) 
   ; A_lattice_meet_proofs := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_meet S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))                                
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_meet_proofs S bsS) 
   ; A_lattice_proofs       := lattice_proofs_add_one S _ c 
                                (A_lattice_join S bsS) 
                                (A_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_proofs S bsS)
                                (A_lattice_meet_proofs S bsS)                                 
                                (A_lattice_proofs S bsS)
   ; A_lattice_ast         :=  Ast_lattice_add_one (c, A_lattice_ast S bsS)
|}. 



Definition distributive_lattice_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS join ->
     sg_CI_proofs S rS meet ->      
     distributive_lattice_proofs S rS join meet -> 
        distributive_lattice_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_ann join c)
           (bop_add_id meet c)
:= λ S rS c join meet eqvS p_join p_meet p_dl, 
{|
  A_distributive_lattice_absorptive        := 
    bops_add_ann_add_id_left_left_absorptive S rS c join meet
       (A_eqv_symmetric S rS eqvS)
       (A_sg_CI_idempotent S rS join p_join)
       (A_distributive_lattice_absorptive S rS join meet p_dl)
; A_distributive_lattice_absorptive_dual   := 
    bops_add_id_add_ann_left_left_absorptive S rS c meet join 
      (A_eqv_reflexive S rS eqvS)
      (A_distributive_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_distributive_lattice_distributive      := 
    bops_add_ann_add_id_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_CI_idempotent S rS join p_join)
        (A_distributive_lattice_absorptive S rS join meet p_dl)
        (bops_left_right_absorptive_implies_right_left S rS join meet
            (A_eqv_reflexive S rS eqvS)                                                       
            (A_eqv_transitive S rS eqvS)
            (A_sg_CI_congruence S rS join p_join)
            (A_sg_CI_commutative S rS join p_join)
            (A_sg_CI_commutative S rS meet p_meet)
            (bops_left_left_absorptive_implies_left_right S rS join meet
                (A_eqv_reflexive S rS eqvS)                                                          
                (A_eqv_transitive S rS eqvS)
                (A_sg_CI_congruence S rS join p_join)
                (A_sg_CI_commutative S rS meet p_meet)
                (A_distributive_lattice_absorptive S rS join meet p_dl)
            )                                          
        )
        (A_distributive_lattice_distributive S rS join meet p_dl)
(*        
; A_distributive_lattice_distributive_dual := 
    bops_add_id_add_ann_left_distributive S rS c meet join 
        (A_eqv_reflexive S rS eqvS)
        (A_distributive_lattice_distributive_dual S rS join meet p_dl)        
*) 
|}.

Definition A_distributive_lattice_add_one : ∀ (S : Type),  A_distributive_lattice S -> cas_constant -> A_distributive_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_distributive_lattice_eqv          := A_eqv_add_constant S (A_distributive_lattice_eqv S bsS) c 
   ; A_distributive_lattice_join         := bop_add_ann (A_distributive_lattice_join S bsS) c
   ; A_distributive_lattice_meet        := bop_add_id (A_distributive_lattice_meet S bsS) c
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_join S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_proofs S bsS) 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_meet S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                                                
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_proofs S bsS) 
   ; A_distributive_lattice_proofs       := distributive_lattice_proofs_add_one S _ c 
                                (A_distributive_lattice_join S bsS) 
                                (A_distributive_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_proofs S bsS)
                                (A_distributive_lattice_meet_proofs S bsS)                                 
                                (A_distributive_lattice_proofs S bsS)
   ; A_distributive_lattice_ast         := Ast_distributive_lattice_add_one (c, A_distributive_lattice_ast S bsS)
|}. 



(* Note: This is another example (like llex) where we can combine semirings and obtain 
   something that is not a semiring 

bops_add_ann_add_id_left_distributive
     : ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
       brel_properties.brel_reflexive S r
       → brel_properties.brel_symmetric S r
         → bop_properties.bop_idempotent S r b1
ll         → bs_properties.bops_left_left_absorptive S r b1 b2
rl           → bs_properties.bops_right_left_absorptive S r b1 b2
               → bs_properties.bop_left_distributive S r b1 b2
                 → bs_properties.bop_left_distributive (with_constant S) (brel_add_constant r c) (bop_add_ann b1 c) (bop_add_id b2 c)

bops_add_ann_add_id_right_distributive
     : ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
       brel_properties.brel_reflexive S r
       → brel_properties.brel_symmetric S r
         → bop_properties.bop_idempotent S r b1
lr         → bs_properties.bops_left_right_absorptive S r b1 b2
rr           → bs_properties.bops_right_right_absorptive S r b1 b2
               → bs_properties.bop_right_distributive S r b1 b2
                 → bs_properties.bop_right_distributive (with_constant S) (brel_add_constant r c) (bop_add_ann b1 c) (bop_add_id b2 c)

so we cannot use add_one to map dioids to dioids or semirings to semirings. 

BUT, what if structures are commutative, and we can derive one of the absorptions? (from 0-stable?) 

Definition bops_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 s t) s) = true.

Definition bops_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.

comutative(b1) -> 
    lr <-> rr 
    ll <-> rl 
commutative(b2) -> 
    ll <-> lr 
    lr <-> rl 

so comutative(b1) -> commutative(b2) -> ll <-> lr <-> rl <-> rr 

So only need one to get them all 

 *)


