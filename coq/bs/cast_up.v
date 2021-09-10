Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 
Require Import CAS.coq.bs.dual. 

Require Import CAS.coq.theory.lattice_theory. 

(*                         1
                                  bs ---------------------------------------------------- 
                                  |                                                      \                         
                                  | 3                                                     \       2 
                                  |                12                                     bs_CI ----
    ----------------------------- presemiring  ------------                               |         \
   /                /             |                        \                              |         bs_CS 
   |                |             | 5                      selective_presemiring          |
   | 15             | 13          |                            |                          |
   |                |             semiring ----------------    |                          | 4
selective           |             |                        \   |                          |
distributive    distributive      | 6                      selective_semiring             |
prelattice        prelattice      |                            |                          |
                    |             dioid -------------------    |                          |
                    |             |            11          \   |                          |
                    | 14          |                        selective_dioid                lattice
                    |             | 7                          |                          |
                    |             |                            |                          |
                    |             |                   -------------------------------------
                    |             |                  /         |               8
                    \ ----------- distributive_lattice ----    | 9
                                       10  \   |
                                           selective_distributive_lattice 

1  A_bs_from_bs_CI
2  A_bs_CI_from_bs_CS
3  A_bs_from_presemiring
4  A_bs_CI_from_lattice
5  A_presemiring_from_semiring              
6  A_semiring_from_dioid
7  A_dioid_from_distributive_lattice
8  A_lattice_from_distributive_lattice
9  A_selective_dioid_from_selective_distributive_lattice
10 A_distributive_lattice_from_selective_distributive_lattice
11 A_dioid_from_selective_dioid
12 A_presemiring_from_selective_presemiring
13 A_presemiring_from_distributive_prelattice
14 
15 A_presemiring_from_selective_distributive_prelattice

Derived 
A_bs_from_semiring
A_bs_from_selective_presemiring
A_bs_from_dioid
A_bs_from_selective_dioid 
A_bs_from_distributive_lattice 
A_bs_from_selective_distributive_lattice 
A_bs_from_distributive_prelattice
A_bs_from_selective_distributive_prelattice

*) 



Section Theory.

End Theory.

Section ACAS. 
Section Proofs.

Variable S: Type. 
Variable eq : brel S.     
Variable plus times : binary_op S.


Definition bs_proofs_from_semiring_proofs :
    eqv_proofs S eq -> sg_C_proofs S eq plus ->
        semiring_proofs S eq plus times -> bs_proofs S eq plus times
:= λ eqv sg sr,
let tranS := A_eqv_transitive S eq eqv   in 
let plusS_comm := A_sg_C_commutative S eq plus sg in
{|
  A_bs_left_distributive_d      := inl _ (A_semiring_left_distributive S eq plus times sr)
; A_bs_right_distributive_d     := inl _ (A_semiring_right_distributive S eq plus times sr)

; A_bs_left_left_absorptive_d   := A_semiring_left_left_absorptive_d S eq plus times sr
; A_bs_left_right_absorptive_d  := A_semiring_left_right_absorptive_d S eq plus times sr
                                                                      
; A_bs_right_left_absorptive_d  := bops_right_left_absorptive_decide_I S eq plus times tranS plusS_comm (A_semiring_left_left_absorptive_d S eq plus times sr)
; A_bs_right_right_absorptive_d := bops_right_right_absorptive_decide_I S eq plus times tranS plusS_comm (A_semiring_left_right_absorptive_d S eq plus times sr)
|}.


Definition bounded_to_zero_one_proofs : bounded_proofs S eq plus times -> zero_one_proofs S eq plus times
:= λ bp,
   match A_bounded_times_id_is_plus_ann S eq plus times bp with 
   | existT _ one (idP, annP)  => 
    {|
        A_zero_one_exists_plus_ann_d      := inl (existT (λ a, bop_is_ann S eq plus a) one annP)
      ; A_zero_one_exists_times_id        := existT (λ a, bop_is_id S eq times a) one idP 
      ; A_zero_one_plus_id_is_times_ann   := A_bounded_plus_id_is_times_ann S eq plus times bp 
      ; A_zero_one_times_id_is_plus_ann_d := inl (A_bounded_times_id_is_plus_ann S eq plus times bp)
    |}
   end.


Definition zero_one_to_id_ann_proofs : zero_one_proofs S eq plus times -> id_ann_proofs S eq plus times
:= λ zop,
   match A_zero_one_plus_id_is_times_ann S eq plus times zop with 
   | existT _ zero (idP, annP)  => 
     {|
        A_id_ann_exists_plus_id_d       := inl(existT (λ a, bop_is_id S eq plus a) zero idP)
      ; A_id_ann_exists_plus_ann_d      := A_zero_one_exists_plus_ann_d _ _ _ _ zop 
      ; A_id_ann_exists_times_id_d      := inl(A_zero_one_exists_times_id _ _ _ _ zop)
      ; A_id_ann_exists_times_ann_d     := inl(existT (λ a, bop_is_ann S eq times a) zero annP)                                                  
      ; A_id_ann_plus_id_is_times_ann_d := inl (A_zero_one_plus_id_is_times_ann _ _ _ _ zop) 
      ; A_id_ann_times_id_is_plus_ann_d := A_zero_one_times_id_is_plus_ann_d _ _ _ _ zop 
    |}
   end.

Definition selective_distributive_lattice_proofs_to_semiring_proofs :
       eqv_proofs S eq -> 
       sg_CS_proofs S eq plus -> sg_CS_proofs S eq times -> 
             distributive_lattice_proofs S eq plus times -> semiring_proofs S eq plus times
:= λ eqvP plusP timesP dlp,
let refS  := A_eqv_reflexive S eq eqvP in
let symS  := A_eqv_symmetric S eq eqvP in     
let tranS := A_eqv_transitive S eq eqvP in
let cong_plus  := A_sg_CS_congruence S eq plus plusP in   
let comm_plus  := A_sg_CS_commutative S eq plus plusP in
let comm_times := A_sg_CS_commutative S eq times timesP in   
let ld  := A_distributive_lattice_distributive S eq plus times dlp in   
let la  := A_distributive_lattice_absorptive S eq plus times dlp in
{|
  A_semiring_left_distributive        := ld 
; A_semiring_right_distributive       := bop_left_distributive_implies_right S eq plus times tranS cong_plus comm_plus comm_times ld
; A_semiring_left_left_absorptive_d   := inl la 
; A_semiring_left_right_absorptive_d  := inl (bops_left_left_absorptive_implies_left_right S eq plus times refS tranS cong_plus comm_times la)
|}.





Definition distributive_lattice_proofs_to_semiring_proofs :
       eqv_proofs S eq -> 
       sg_CI_proofs S eq plus -> sg_CI_proofs S eq times -> 
             distributive_lattice_proofs S eq plus times -> semiring_proofs S eq plus times
:= λ eqvP plusP timesP dlp,
let refS  := A_eqv_reflexive S eq eqvP in
let symS  := A_eqv_symmetric S eq eqvP in     
let tranS := A_eqv_transitive S eq eqvP in
let cong_plus  := A_sg_CI_congruence S eq plus plusP in   
let comm_plus  := A_sg_CI_commutative S eq plus plusP in
let comm_times := A_sg_CI_commutative S eq times timesP in   
let ld  := A_distributive_lattice_distributive S eq plus times dlp in   
let la  := A_distributive_lattice_absorptive S eq plus times dlp in
{|
  A_semiring_left_distributive        := ld 
; A_semiring_right_distributive       := bop_left_distributive_implies_right S eq plus times tranS cong_plus comm_plus comm_times ld
; A_semiring_left_left_absorptive_d   := inl la 
; A_semiring_left_right_absorptive_d  := inl (bops_left_left_absorptive_implies_left_right S eq plus times refS tranS cong_plus comm_times la)
|}.

  
Definition lattice_proofs_from_distributive_lattice_proofs (eqv : A_eqv S) :
            sg_CI_proofs S (A_eqv_eq S eqv) plus -> sg_CI_proofs S (A_eqv_eq S eqv) times ->
            distributive_lattice_proofs S (A_eqv_eq S eqv) plus times ->  lattice_proofs S (A_eqv_eq S eqv) plus times
:= λ jP mP dP,
  let eq       := A_eqv_eq S eqv in
  let eqvP     := A_eqv_proofs S eqv in   
  let refS     := A_eqv_reflexive S eq eqvP in
  let symS     := A_eqv_symmetric S eq eqvP in
  let trnS     := A_eqv_transitive S eq eqvP in 
  let j_cong   := A_sg_CI_congruence S eq plus jP in
  let j_assoc  := A_sg_CI_associative S eq plus jP in
  let m_com    := A_sg_CI_commutative S eq times mP in
  let abs_j_m  := A_distributive_lattice_absorptive S eq plus times dP in
  let abs_m_j  := A_distributive_lattice_absorptive_dual S eq plus times dP in
  let dist_j_m := A_distributive_lattice_distributive S eq plus times dP in
   {|
      A_lattice_absorptive          := A_distributive_lattice_absorptive _ _ _ _ dP 
    ; A_lattice_absorptive_dual     := A_distributive_lattice_absorptive_dual _ _ _ _ dP 
    ; A_lattice_distributive_d      := inl (A_distributive_lattice_distributive _ _ _ _ dP)
    ; A_lattice_distributive_dual_d := inl (lattice_distributive_implies_distributive_dual S eq refS symS trnS
                                             plus times j_cong j_assoc m_com abs_j_m abs_m_j dist_j_m)
   |}.

Definition lattice_to_bs_proofs 
           (eqvP : eqv_proofs S eq)
           (plusP : sg_CI_proofs S eq plus)
           (timesP : sg_CI_proofs S eq times)            
           (lP : lattice_proofs S eq plus times) : bs_proofs S eq plus times 
:=
let refS := A_eqv_reflexive S eq eqvP in     
let trnS := A_eqv_transitive S eq eqvP in     
let plus_cong := A_sg_CI_congruence S eq plus plusP in 
let plus_comm := A_sg_CI_commutative S eq plus plusP in 
let times_comm := A_sg_CI_commutative S eq times timesP in 
let l_dist_d := A_lattice_distributive_d S eq plus times lP in 
let r_dist_d := bop_left_distributive_decidable_implies_right_decidable S eq plus times trnS plus_cong plus_comm times_comm l_dist_d in 
let ll_abs := A_lattice_absorptive S eq plus times lP in     
let lr_abs := bops_left_left_absorptive_implies_left_right S eq plus times refS trnS plus_cong times_comm ll_abs in
let rl_abs := bops_left_left_absorptive_implies_right_left S eq plus times trnS plus_comm ll_abs in 
let rr_abs := bops_left_right_absorptive_implies_right_right S eq plus times trnS plus_comm lr_abs  in     
{|
   A_bs_left_distributive_d      := l_dist_d 
 ; A_bs_right_distributive_d     := r_dist_d 
 ; A_bs_left_left_absorptive_d   := inl ll_abs 
 ; A_bs_left_right_absorptive_d  := inl lr_abs 
 ; A_bs_right_left_absorptive_d  := inl rl_abs 
 ; A_bs_right_right_absorptive_d := inl rr_abs 
|}.           

End Proofs.   


Definition A_bs_from_bs_CI : ∀ (S : Type),  A_bs_CI S -> A_bs S 
:= λ S bs, 
{| 
  A_bs_eqv          := A_bs_CI_eqv S bs
; A_bs_plus         := A_bs_CI_plus S bs
; A_bs_times        := A_bs_CI_times S bs
; A_bs_plus_proofs  := A_asg_proofs_from_sg_CI_proofs S
                         (A_eqv_eq S (A_bs_CI_eqv S bs))
                         (A_bs_CI_plus S bs)
                         (A_eqv_witness S (A_bs_CI_eqv S bs))
                         (A_eqv_new S (A_bs_CI_eqv S bs))
                         (A_eqv_not_trivial S (A_bs_CI_eqv S bs))                         
                         (A_eqv_proofs S (A_bs_CI_eqv S bs))
                         (A_bs_CI_plus_proofs S bs)  
; A_bs_times_proofs := A_bs_CI_times_proofs S bs
; A_bs_id_ann_proofs := A_bs_CI_id_ann_proofs S bs                                            
; A_bs_proofs       := A_bs_CI_proofs S bs
; A_bs_ast          := Ast_bs_from_bs_CI (A_bs_CI_ast S bs)
|}. 

Definition A_bs_CI_from_bs_CS : ∀ (S : Type),  A_bs_CS S -> A_bs_CI S 
:= λ S bs, 
{| 
  A_bs_CI_eqv          := A_bs_CS_eqv S bs
; A_bs_CI_plus         := A_bs_CS_plus S bs
; A_bs_CI_times        := A_bs_CS_times S bs
; A_bs_CI_plus_proofs  := A_sg_CI_proofs_from_sg_CS_proofs S
                         (A_eqv_eq S (A_bs_CS_eqv S bs))
                         (A_bs_CS_plus S bs)
                         (A_bs_CS_plus_proofs S bs)  
; A_bs_CI_times_proofs  := A_bs_CS_times_proofs S bs
; A_bs_CI_id_ann_proofs := A_bs_CS_id_ann_proofs S bs                                            
; A_bs_CI_proofs        := A_bs_CS_proofs S bs
; A_bs_CI_ast           := Ast_bs_CI_from_bs_CS (A_bs_CS_ast S bs)
|}. 


Definition A_bs_from_presemiring :∀ (S: Type), A_presemiring S -> A_bs S 
:= λ S s,
let eqv      := A_presemiring_eqv S s in
let eqvP     := A_eqv_proofs S eqv in
let eq       := A_eqv_eq S eqv in
let plus     := A_presemiring_plus S s in
let times    := A_presemiring_times S s in
let sg_plusP := A_presemiring_plus_proofs S s in 
{| 
  A_bs_eqv           := eqv 
; A_bs_plus          := plus 
; A_bs_times         := times 
; A_bs_plus_proofs   := A_asg_proofs_from_sg_C_proofs S eq plus sg_plusP  
; A_bs_times_proofs  := A_presemiring_times_proofs S s
; A_bs_id_ann_proofs := A_presemiring_id_ann_proofs S s
; A_bs_proofs        := bs_proofs_from_semiring_proofs S eq plus times eqvP sg_plusP (A_presemiring_proofs S s)
; A_bs_ast           := Ast_bs_from_presemiring (A_presemiring_ast S s)
|}.


Definition A_presemiring_from_selective_presemiring :∀ (S: Type), A_selective_presemiring S -> A_presemiring S
  := λ S dS,
let eqvS  := A_selective_presemiring_eqv S dS in
let eqvP  := A_eqv_proofs S eqvS in     
let eq    := A_eqv_eq S eqvS in
let wS    := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let ntS   := A_eqv_not_trivial S eqvS in
let plus  := A_selective_presemiring_plus S dS in
let times := A_selective_presemiring_times S dS in 
{|
  A_presemiring_eqv           := eqvS 
; A_presemiring_plus          := plus
; A_presemiring_times         := times 
; A_presemiring_plus_proofs   := A_sg_C_proofs_from_sg_CS_proofs S eq plus wS f ntS eqvP (A_selective_presemiring_plus_proofs S dS)
; A_presemiring_times_proofs  := A_selective_presemiring_times_proofs S dS 
; A_presemiring_id_ann_proofs := A_selective_presemiring_id_ann_proofs S dS
; A_presemiring_proofs        := A_selective_presemiring_proofs S dS 
; A_presemiring_ast           := Ast_presemiring_from_selective_presemiring(A_selective_presemiring_ast S dS)
|}.     


Definition A_presemiring_from_semiring :∀ (S: Type), A_semiring S -> A_presemiring S
  := λ S dS,
let eqvS  := A_semiring_eqv S dS in
let eq    := A_eqv_eq S eqvS in
let plus  := A_semiring_plus S dS in
let times := A_semiring_times S dS in 
{|
  A_presemiring_eqv           := eqvS 
; A_presemiring_plus          := plus
; A_presemiring_times         := times 
; A_presemiring_plus_proofs   := A_semiring_plus_proofs S dS 
; A_presemiring_times_proofs  := A_semiring_times_proofs S dS 
; A_presemiring_id_ann_proofs := zero_one_to_id_ann_proofs S eq plus times (A_semiring_id_ann_proofs S dS)
; A_presemiring_proofs        := A_semiring_proofs S dS 
; A_presemiring_ast           := Ast_presemiring_from_semiring(A_semiring_ast S dS)
|}.



Definition A_presemiring_from_distributive_prelattice :∀ (S: Type), A_distributive_prelattice S -> A_presemiring S
  := λ S dS,
let eqvS   := A_distributive_prelattice_eqv S dS in
let eqvP   := A_eqv_proofs S eqvS      in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let ntS    := A_eqv_not_trivial S eqvS in
let eq     := A_eqv_eq S eqvS in
let plus   := A_distributive_prelattice_join S dS in
let times  := A_distributive_prelattice_meet S dS in
let plusP  := A_distributive_prelattice_join_proofs S dS in
let timesP := A_distributive_prelattice_meet_proofs S dS in
{|
  A_presemiring_eqv           := eqvS 
; A_presemiring_plus          := plus
; A_presemiring_times         := times 
; A_presemiring_plus_proofs   := A_sg_C_proofs_from_sg_CI_proofs S eq plus s f ntS eqvP plusP
; A_presemiring_times_proofs  := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CI_proofs S eq times s f ntS eqvP timesP)
; A_presemiring_id_ann_proofs := A_distributive_prelattice_id_ann_proofs S dS
; A_presemiring_proofs        := distributive_lattice_proofs_to_semiring_proofs S eq plus times eqvP plusP timesP  (A_distributive_prelattice_proofs S dS)
; A_presemiring_ast           := Ast_presemiring_from_distributive_prelattice (A_distributive_prelattice_ast S dS)
|}.     



Definition A_presemiring_from_selective_distributive_prelattice :∀ (S: Type), A_selective_distributive_prelattice S -> A_presemiring S
  := λ S dS,
let eqvS   := A_selective_distributive_prelattice_eqv S dS in
let eqvP   := A_eqv_proofs S eqvS      in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let ntS    := A_eqv_not_trivial S eqvS in
let eq     := A_eqv_eq S eqvS in
let plus   := A_selective_distributive_prelattice_join S dS in
let times  := A_selective_distributive_prelattice_meet S dS in
let plusP  := A_selective_distributive_prelattice_join_proofs S dS in
let timesP := A_selective_distributive_prelattice_meet_proofs S dS in
let plP    := A_selective_distributive_prelattice_proofs S dS in 
{|
  A_presemiring_eqv           := eqvS 
; A_presemiring_plus          := plus
; A_presemiring_times         := times 
; A_presemiring_plus_proofs   := A_sg_C_proofs_from_sg_CS_proofs S eq plus s f ntS eqvP plusP
; A_presemiring_times_proofs  := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CS_proofs S eq times s f ntS eqvP timesP)
; A_presemiring_id_ann_proofs := A_selective_distributive_prelattice_id_ann_proofs S dS
; A_presemiring_proofs        := selective_distributive_lattice_proofs_to_semiring_proofs S eq plus times eqvP plusP timesP plP
; A_presemiring_ast           := Ast_presemiring_from_selective_distributive_prelattice (A_selective_distributive_prelattice_ast S dS)
|}.     



Definition A_semiring_from_dioid :∀ (S: Type), A_dioid S -> A_semiring S
:= λ S dS,
let eqv := A_dioid_eqv S dS in
let eqvP := A_eqv_proofs S eqv in
let eq := A_eqv_eq S eqv in
let plus := A_dioid_plus S dS in
let w := A_eqv_witness S eqv in
let f := A_eqv_new S eqv in
let nt := A_eqv_not_trivial S eqv in
{|
  A_semiring_eqv          := eqv 
; A_semiring_plus         := plus
; A_semiring_times        := A_dioid_times S dS
; A_semiring_plus_proofs  := A_sg_C_proofs_from_sg_CI_proofs S eq plus w f nt eqvP (A_dioid_plus_proofs S dS)
; A_semiring_times_proofs := A_dioid_times_proofs S dS
; A_semiring_id_ann_proofs := bounded_to_zero_one_proofs S _ _ _ (A_dioid_id_ann_proofs S dS)                                                  
; A_semiring_proofs       := A_dioid_proofs S dS
; A_semiring_ast          := Ast_semiring_from_dioid (A_dioid_ast S dS)
|}.  



Definition A_lattice_from_distributive_lattice :∀ (S: Type), A_distributive_lattice S -> A_lattice S
:= λ S dS,
let eqv   := A_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let join  := A_distributive_lattice_join S dS in
let joinP := A_distributive_lattice_join_proofs S dS in
let meet  := A_distributive_lattice_meet S dS in
let meetP := A_distributive_lattice_meet_proofs S dS in
let dPS   := A_distributive_lattice_proofs S dS in 
{|
      A_lattice_eqv           := eqv 
    ; A_lattice_join          := join 
    ; A_lattice_meet          := meet
    ; A_lattice_join_proofs   := joinP 
    ; A_lattice_meet_proofs   := meetP
    ; A_lattice_id_ann_proofs := A_distributive_lattice_id_ann_proofs S dS 
    ; A_lattice_proofs        := lattice_proofs_from_distributive_lattice_proofs S join meet eqv  joinP meetP dPS
    ; A_lattice_ast           := Ast_lattice_from_distributive_lattice (A_distributive_lattice_ast S dS)
|}.

                                
Definition A_bs_CI_from_lattice :∀ (S: Type), A_lattice S -> A_bs_CI S
  := λ S lP,
  let eqv  := A_lattice_eqv S lP     in               
  let eq   := A_eqv_eq S eqv      in 
  let wS   := A_eqv_witness S eqv in 
  let f    := A_eqv_new S eqv     in
  let ntf  := A_eqv_not_trivial S eqv     in   
  let eqvP := A_eqv_proofs S eqv  in 
  let join := A_lattice_join S lP    in
  let joinP := A_lattice_join_proofs S lP in 
  let meet := A_lattice_meet S lP    in
  let meetP := A_lattice_meet_proofs S lP in   
  {|
     A_bs_CI_eqv           := eqv 
   ; A_bs_CI_plus          := join 
   ; A_bs_CI_times         := meet 
   ; A_bs_CI_plus_proofs   := joinP 
   ; A_bs_CI_times_proofs  := A_msg_proofs_from_sg_proofs S eq meet (A_sg_proofs_from_sg_CI_proofs S eq meet wS f ntf eqvP meetP)
   ; A_bs_CI_id_ann_proofs := zero_one_to_id_ann_proofs S eq join meet (bounded_to_zero_one_proofs S eq join meet (A_lattice_id_ann_proofs S lP))
   ; A_bs_CI_proofs        := lattice_to_bs_proofs S eq join meet eqvP joinP meetP (A_lattice_proofs S lP) 
   ; A_bs_CI_ast           := Ast_bs_CI_from_lattice (A_lattice_ast S lP)
  |}.

Definition A_dioid_from_distributive_lattice :∀ (S: Type), A_distributive_lattice S -> A_dioid S
:= λ S dS,
let eqv   := A_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let plus  := A_distributive_lattice_join S dS in
let plusP := A_distributive_lattice_join_proofs S dS in
let times := A_distributive_lattice_meet S dS in
let timesP:= A_distributive_lattice_meet_proofs S dS in
let dPS   := A_distributive_lattice_proofs S dS in 
let w     := A_eqv_witness S eqv in
let f     := A_eqv_new S eqv in
let nt    := A_eqv_not_trivial S eqv in
{|
  A_dioid_eqv          := eqv 
; A_dioid_plus         := plus
; A_dioid_times        := times 
; A_dioid_plus_proofs  := plusP 
; A_dioid_times_proofs := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CI_proofs S eq times w f nt eqvP timesP)
; A_dioid_id_ann_proofs := A_distributive_lattice_id_ann_proofs S dS 
; A_dioid_proofs       := distributive_lattice_proofs_to_semiring_proofs S eq plus times eqvP plusP timesP dPS
; A_dioid_ast          := Ast_dioid_from_distributive_lattice (A_distributive_lattice_ast S dS)
|}.



Definition A_selective_dioid_from_selective_distributive_lattice :∀ (S: Type), A_selective_distributive_lattice S -> A_selective_dioid S
:= λ S dS,
let eqv   := A_selective_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let plus  := A_selective_distributive_lattice_join S dS in
let plusP := A_selective_distributive_lattice_join_proofs S dS in
let times := A_selective_distributive_lattice_meet S dS in
let timesP:= A_selective_distributive_lattice_meet_proofs S dS in
let dPS   := A_selective_distributive_lattice_proofs S dS in 
let w     := A_eqv_witness S eqv in
let f     := A_eqv_new S eqv in
let nt    := A_eqv_not_trivial S eqv in
{|
  A_selective_dioid_eqv           := eqv 
; A_selective_dioid_plus          := plus
; A_selective_dioid_times         := times 
; A_selective_dioid_plus_proofs   := plusP 
; A_selective_dioid_times_proofs  := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CS_proofs S eq times w f nt eqvP timesP)
; A_selective_dioid_id_ann_proofs := A_selective_distributive_lattice_id_ann_proofs S dS 
; A_selective_dioid_proofs        := distributive_lattice_proofs_to_semiring_proofs S eq plus times eqvP (A_sg_CI_proofs_from_sg_CS_proofs _ _ _ plusP) (A_sg_CI_proofs_from_sg_CS_proofs _ _ _ timesP) dPS
; A_selective_dioid_ast           := Ast_selective_dioid_from_selective_distributive_lattice (A_selective_distributive_lattice_ast S dS)
|}.  


Definition A_dioid_from_selective_dioid :∀ (S: Type), A_selective_dioid S -> A_dioid S
:= λ S dS,
{|
  A_dioid_eqv           := A_selective_dioid_eqv S dS
; A_dioid_plus          := A_selective_dioid_plus S dS
; A_dioid_times         := A_selective_dioid_times S dS
; A_dioid_plus_proofs   := A_sg_CI_proofs_from_sg_CS_proofs S
                             (A_eqv_eq S (A_selective_dioid_eqv S dS))
                             (A_selective_dioid_plus S dS)
                             (A_selective_dioid_plus_proofs S dS)
; A_dioid_id_ann_proofs := A_selective_dioid_id_ann_proofs S dS                              
; A_dioid_times_proofs  := A_selective_dioid_times_proofs S dS
; A_dioid_proofs        := A_selective_dioid_proofs S dS
; A_dioid_ast          := Ast_dioid_from_selective_dioid (A_selective_dioid_ast S dS)
|}.


Definition A_distributive_lattice_from_selective_distributive_lattice : ∀ (S : Type), A_selective_distributive_lattice S -> A_distributive_lattice S
:= λ S lat,
{|  
  A_distributive_lattice_eqv          := A_selective_distributive_lattice_eqv S lat 
; A_distributive_lattice_join         := A_selective_distributive_lattice_join S lat
; A_distributive_lattice_meet         := A_selective_distributive_lattice_meet S lat 
; A_distributive_lattice_join_proofs  := A_sg_CI_proofs_from_sg_CS_proofs S
                                              (A_eqv_eq S (A_selective_distributive_lattice_eqv S lat))
                                              (A_selective_distributive_lattice_join S lat)                                
                                              (A_selective_distributive_lattice_join_proofs S lat)
; A_distributive_lattice_meet_proofs  := A_sg_CI_proofs_from_sg_CS_proofs S
                                              (A_eqv_eq S (A_selective_distributive_lattice_eqv S lat))
                                              (A_selective_distributive_lattice_meet S lat)
                                              (A_selective_distributive_lattice_meet_proofs S lat)
; A_distributive_lattice_id_ann_proofs := A_selective_distributive_lattice_id_ann_proofs S lat  
; A_distributive_lattice_proofs       := A_selective_distributive_lattice_proofs S lat
; A_distributive_lattice_ast          := Ast_distributive_lattice_from_selective_distributive_lattice (A_selective_distributive_lattice_ast S lat) 
|}.  


Definition A_bs_from_semiring :∀ (S: Type), A_semiring S -> A_bs S 
  := λ S sS,  A_bs_from_presemiring S (A_presemiring_from_semiring S sS).

Definition A_bs_from_selective_presemiring :∀ (S: Type), A_selective_presemiring S -> A_bs S 
  := λ S sS,  A_bs_from_presemiring S (A_presemiring_from_selective_presemiring S sS).


Definition A_bs_from_dioid :∀ (S: Type), A_dioid S -> A_bs S 
  := λ S sS,  A_bs_from_semiring S (A_semiring_from_dioid S sS).

Definition A_bs_from_selective_dioid :∀ (S: Type), A_selective_dioid S -> A_bs S 
  := λ S sS,  A_bs_from_dioid S (A_dioid_from_selective_dioid S sS).

Definition A_bs_from_distributive_lattice :∀ (S: Type), A_distributive_lattice S -> A_bs S 
  := λ S sS,  A_bs_from_dioid S (A_dioid_from_distributive_lattice S sS). 

Definition A_bs_from_distributive_prelattice :∀ (S: Type), A_distributive_prelattice S -> A_bs S 
  := λ S sS,  A_bs_from_presemiring S (A_presemiring_from_distributive_prelattice S sS). 


Definition A_bs_from_selective_distributive_prelattice :∀ (S: Type), A_selective_distributive_prelattice S -> A_bs S 
  := λ S sS,  A_bs_from_presemiring S (A_presemiring_from_selective_distributive_prelattice S sS). 


Definition A_bs_from_selective_distributive_lattice :∀ (S: Type), A_selective_distributive_lattice S -> A_bs S 
  := λ S sS,  A_bs_from_distributive_lattice S (A_distributive_lattice_from_selective_distributive_lattice S sS). 

End ACAS.

Section CAS.
  
Definition bs_from_bs_CI : ∀ {S : Type},  @bs_CI S -> @bs S
:= λ {S} bs, 
{| 
  bs_eqv          := bs_CI_eqv bs
; bs_plus         := bs_CI_plus bs
; bs_times        := bs_CI_times bs
; bs_plus_certs  := asg_certs_from_sg_CI_certs
                      (eqv_eq (bs_CI_eqv bs))
                      (bs_CI_plus bs)
                      (eqv_witness (bs_CI_eqv bs))
                      (eqv_new (bs_CI_eqv bs))
                      (bs_CI_plus_certs bs)  
; bs_times_certs := bs_CI_times_certs bs
; bs_id_ann_certs := bs_CI_id_ann_certs bs                                      
; bs_certs       := bs_CI_certs bs
; bs_ast         := Ast_bs_from_bs_CI (bs_CI_ast bs)
|}.

Definition bs_certs_from_semiring_certs :
  ∀ {S: Type},  @semiring_certificates S -> @bs_certificates S 
:= λ S sr,
{|
  bs_left_distributive_d      := Certify_Left_Distributive
; bs_right_distributive_d     := Certify_Right_Distributive

; bs_left_left_absorptive_d   := semiring_left_left_absorptive_d sr
; bs_left_right_absorptive_d  := semiring_left_right_absorptive_d sr
                                                                      
; bs_right_left_absorptive_d  := match semiring_left_left_absorptive_d sr with
                                 | Certify_Left_Left_Absorptive => Certify_Right_Left_Absorptive 
                                 | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive (s1, s2) 
                                 end 
; bs_right_right_absorptive_d := match semiring_left_right_absorptive_d sr with
                                 | Certify_Left_Right_Absorptive => Certify_Right_Right_Absorptive
                                 | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive (s1, s2) 
                                 end 
|}.


Definition bs_from_presemiring {S: Type} (s : @presemiring S): @bs S := 
{| 
  bs_eqv           := presemiring_eqv s 
; bs_plus          := presemiring_plus s 
; bs_times         := presemiring_times s 
; bs_plus_certs    := asg_certs_from_sg_C_certs (presemiring_plus_certs s)
; bs_times_certs   := presemiring_times_certs s
; bs_id_ann_certs  := presemiring_id_ann_certs s
; bs_certs         := bs_certs_from_semiring_certs (presemiring_certs s)
; bs_ast           := Ast_bs_from_presemiring (presemiring_ast s)
|}. 

Definition bs_CI_from_bs_CS {S : Type} (bs : @bs_CS S) : @bs_CI S := 
{| 
  bs_CI_eqv          := bs_CS_eqv bs
; bs_CI_plus         := bs_CS_plus bs
; bs_CI_times        := bs_CS_times bs
; bs_CI_plus_certs   := sg_CI_certs_from_sg_CS_certs (bs_CS_plus_certs bs)  
; bs_CI_times_certs  := bs_CS_times_certs bs
; bs_CI_id_ann_certs := bs_CS_id_ann_certs bs                                            
; bs_CI_certs        := bs_CS_certs bs
; bs_CI_ast          := Ast_bs_CI_from_bs_CS (bs_CS_ast bs)
|}. 

Definition zero_one_to_id_ann_certs {S : Type} : @zero_one_certificates S  -> @id_ann_certificates S 
:= λ zop,
   match zero_one_plus_id_is_times_ann zop , zero_one_exists_times_id zop with 
   | Assert_Plus_Id_Equals_Times_Ann zero, Assert_Exists_Id one => 
     {|
        id_ann_exists_plus_id_d       := Certify_Exists_Id zero 
      ; id_ann_exists_plus_ann_d      := zero_one_exists_plus_ann_d zop 
      ; id_ann_exists_times_id_d      := Certify_Exists_Id one 
      ; id_ann_exists_times_ann_d     := Certify_Exists_Ann zero 
      ; id_ann_plus_id_is_times_ann_d := Certify_Plus_Id_Equals_Times_Ann zero 
      ; id_ann_times_id_is_plus_ann_d := zero_one_times_id_is_plus_ann_d zop 
    |}
   end.

Definition presemiring_from_selective_presemiring :∀ {S: Type}, @selective_presemiring S -> @presemiring S
  := λ S dS,
let eqvS  := selective_presemiring_eqv dS in
let eq    := eqv_eq eqvS      in
let wS    := eqv_witness eqvS in
let f     := eqv_new eqvS     in
let plus  := selective_presemiring_plus dS in
{|
  presemiring_eqv           := eqvS 
; presemiring_plus          := plus
; presemiring_times         := selective_presemiring_times dS 
; presemiring_plus_certs    := sg_C_certs_from_sg_CS_certs eq plus wS f (selective_presemiring_plus_certs dS)
; presemiring_times_certs   := selective_presemiring_times_certs dS 
; presemiring_id_ann_certs  := selective_presemiring_id_ann_certs dS
; presemiring_certs         := selective_presemiring_certs dS 
; presemiring_ast           := Ast_presemiring_from_selective_presemiring(selective_presemiring_ast dS)
|}.     


Definition presemiring_from_semiring  {S: Type} (bS : @semiring S) : @presemiring S := 
{|
  presemiring_eqv          := semiring_eqv bS 
; presemiring_plus         := semiring_plus bS 
; presemiring_times        := semiring_times bS 
; presemiring_plus_certs   := semiring_plus_certs bS 
; presemiring_times_certs  := semiring_times_certs bS 
; presemiring_id_ann_certs := zero_one_to_id_ann_certs (semiring_id_ann_certs bS)
; presemiring_certs        := semiring_certs bS 
; presemiring_ast          := Ast_presemiring_from_semiring(semiring_ast bS)
|}.     


Definition bounded_to_zero_one_certs {S : Type} : 
                     @bounded_certificates S -> @zero_one_certificates S 
:= λ bp,
   match bounded_times_id_is_plus_ann bp with 
   | Assert_Times_Id_Equals_Plus_Ann one  => 
    {|
        zero_one_exists_plus_ann_d      := Certify_Exists_Ann one 
      ; zero_one_exists_times_id        := Assert_Exists_Id one 
      ; zero_one_plus_id_is_times_ann   := bounded_plus_id_is_times_ann bp 
      ; zero_one_times_id_is_plus_ann_d := Certify_Times_Id_Equals_Plus_Ann one 
    |}
   end.


Definition selective_distributive_lattice_certs_to_semiring_certs {S: Type} :
       @sg_CS_certificates S  -> @sg_CS_certificates S-> @distributive_lattice_certificates S -> @semiring_certificates S
:= λ plusC timesC dlp,
{|
  semiring_left_distributive        := Assert_Left_Distributive   
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
; semiring_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
|}.


Definition distributive_lattice_certs_to_semiring_certs :
  ∀ {S: Type}, @sg_CI_certificates S  -> @sg_CI_certificates S-> @distributive_lattice_certificates S -> @semiring_certificates S 
:= λ S plusP timesP dlp,
{|
   semiring_left_distributive        := Assert_Left_Distributive   
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
; semiring_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
|}.

Definition presemiring_from_distributive_prelattice :∀ {S: Type}, @distributive_prelattice S -> @presemiring S
  := λ S dS,
let eqvS   := distributive_prelattice_eqv dS in
let s      := eqv_witness eqvS in
let f      := eqv_new eqvS in
let eq     := eqv_eq eqvS in
let plus   := distributive_prelattice_join dS in
let times  := distributive_prelattice_meet dS in
let plusP  := distributive_prelattice_join_certs dS in
let timesP := distributive_prelattice_meet_certs dS in
{|
  presemiring_eqv          := eqvS 
; presemiring_plus         := plus
; presemiring_times        := times 
; presemiring_plus_certs   := sg_C_certs_from_sg_CI_certs eq plus s f plusP
; presemiring_times_certs  := msg_certs_from_sg_certs (sg_certs_from_sg_CI_certs eq times s f timesP)
; presemiring_id_ann_certs := distributive_prelattice_id_ann_certs dS
; presemiring_certs        := distributive_lattice_certs_to_semiring_certs plusP timesP  (distributive_prelattice_certs dS)
; presemiring_ast          := Ast_presemiring_from_distributive_prelattice (distributive_prelattice_ast dS)
|}.     


Definition presemiring_from_selective_distributive_prelattice :∀ {S: Type}, @selective_distributive_prelattice S -> @presemiring S
  := λ S dS,
let eqvS   := selective_distributive_prelattice_eqv dS in
let s      := eqv_witness eqvS in
let f      := eqv_new eqvS in
let eq     := eqv_eq eqvS in
let plus   := selective_distributive_prelattice_join dS in
let times  := selective_distributive_prelattice_meet dS in
let plusP  := selective_distributive_prelattice_join_certs dS in
let timesP := selective_distributive_prelattice_meet_certs dS in
let plP    := selective_distributive_prelattice_certs dS in 
{|
  presemiring_eqv          := eqvS 
; presemiring_plus         := plus
; presemiring_times        := times 
; presemiring_plus_certs   := sg_C_certs_from_sg_CS_certs eq plus s f plusP
; presemiring_times_certs  := msg_certs_from_sg_certs (sg_certs_from_sg_CS_certs eq times s f timesP)
; presemiring_id_ann_certs := selective_distributive_prelattice_id_ann_certs dS
; presemiring_certs        := selective_distributive_lattice_certs_to_semiring_certs plusP timesP plP
; presemiring_ast          := Ast_presemiring_from_selective_distributive_prelattice (selective_distributive_prelattice_ast dS)
|}.     

Definition semiring_from_dioid :∀ {S: Type}, @dioid S -> @semiring S
:= λ S dS,
{|
  semiring_eqv          := dioid_eqv dS 
; semiring_plus         := dioid_plus dS
; semiring_times        := dioid_times dS
; semiring_plus_certs   := sg_C_certs_from_sg_CI_certs (eqv_eq (dioid_eqv dS))
                                                       (dioid_plus dS)
                                                       (eqv_witness (dioid_eqv dS))
                                                       (eqv_new (dioid_eqv dS))
                                                       (dioid_plus_certs dS)                                                       
; semiring_times_certs  := dioid_times_certs dS
; semiring_id_ann_certs := bounded_to_zero_one_certs (dioid_id_ann_certs dS)
; semiring_certs        := dioid_certs dS
; semiring_ast          := Ast_semiring_from_dioid (dioid_ast dS)
|}.


Definition dioid_from_selective_dioid :∀ {S: Type}, @selective_dioid S -> @dioid S
:= λ S dS,
{|
  dioid_eqv          := selective_dioid_eqv dS
; dioid_plus         := selective_dioid_plus dS
; dioid_times        := selective_dioid_times dS
; dioid_plus_certs   := sg_CI_certs_from_sg_CS_certs (selective_dioid_plus_certs dS)
; dioid_times_certs  := selective_dioid_times_certs dS
; dioid_id_ann_certs   := selective_dioid_id_ann_certs dS                                                    
; dioid_certs        := selective_dioid_certs dS
; dioid_ast          := Ast_dioid_from_selective_dioid (selective_dioid_ast dS)
|}.  


Definition distributive_lattice_from_selective_distributive_lattice : ∀ {S : Type}, @selective_distributive_lattice S -> @distributive_lattice S
:= λ S lat,
{|  
  distributive_lattice_eqv          := selective_distributive_lattice_eqv lat 
; distributive_lattice_join         := selective_distributive_lattice_join lat
; distributive_lattice_meet         := selective_distributive_lattice_meet lat 
; distributive_lattice_join_certs   := sg_CI_certs_from_sg_CS_certs (selective_distributive_lattice_join_certs lat)
; distributive_lattice_meet_certs   := sg_CI_certs_from_sg_CS_certs (selective_distributive_lattice_meet_certs lat)
; distributive_lattice_id_ann_certs := selective_distributive_lattice_id_ann_certs lat                                          
; distributive_lattice_certs        := selective_distributive_lattice_certs lat
; distributive_lattice_ast          := Ast_distributive_lattice_from_selective_distributive_lattice (selective_distributive_lattice_ast lat) 
|}.  

Definition dioid_from_distributive_lattice {S: Type} (dS : @distributive_lattice S) : @dioid S :=
let eqv   := distributive_lattice_eqv dS in  
let eq    := eqv_eq eqv in
let plusC := distributive_lattice_join_certs dS in
let times := distributive_lattice_meet dS in
let timesC:= distributive_lattice_meet_certs dS in
let wS    := eqv_witness eqv in
let f     := eqv_new eqv in
{|
  dioid_eqv          := distributive_lattice_eqv dS
; dioid_plus         := distributive_lattice_join dS 
; dioid_times        := distributive_lattice_meet dS
; dioid_plus_certs   := distributive_lattice_join_certs dS 
; dioid_times_certs  := msg_certs_from_sg_certs (sg_certs_from_sg_CI_certs eq times wS f (distributive_lattice_meet_certs dS))
; dioid_id_ann_certs := distributive_lattice_id_ann_certs dS 
; dioid_certs        := distributive_lattice_certs_to_semiring_certs plusC timesC (distributive_lattice_certs dS)
; dioid_ast          := Ast_dioid_from_distributive_lattice (distributive_lattice_ast dS)
|}.


Definition lattice_certs_from_distributive_lattice_certs {S : Type} : @distributive_lattice_certificates S ->  @lattice_certificates S 
:= λ dP,
   {|
      lattice_absorptive          := distributive_lattice_absorptive dP 
    ; lattice_absorptive_dual     := distributive_lattice_absorptive_dual dP 
    ; lattice_distributive_d      := Certify_Left_Distributive
    ; lattice_distributive_dual_d := Certify_Left_Distributive_Dual
   |}.



Definition lattice_from_distributive_lattice {S: Type} (dS : @distributive_lattice S ) : @lattice S := 
{|
      lattice_eqv           := distributive_lattice_eqv dS
    ; lattice_join          := distributive_lattice_join dS 
    ; lattice_meet          := distributive_lattice_meet dS
    ; lattice_join_certs    := distributive_lattice_join_certs dS 
    ; lattice_meet_certs    := distributive_lattice_meet_certs dS 
    ; lattice_id_ann_certs  := distributive_lattice_id_ann_certs dS 
    ; lattice_certs         := lattice_certs_from_distributive_lattice_certs (distributive_lattice_certs dS)
    ; lattice_ast           := Ast_lattice_from_distributive_lattice (distributive_lattice_ast dS)
|}.


Definition lattice_to_bs_certs {S : Type} (lP : @lattice_certificates S ) : @bs_certificates S :=
{|
   bs_left_distributive_d      := lattice_distributive_d lP 
 ; bs_right_distributive_d     := match lattice_distributive_d lP with
                                    | Certify_Left_Distributive       => Certify_Right_Distributive
                                    | Certify_Not_Left_Distributive t => Certify_Not_Right_Distributive t
                                  end 
 ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
 ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
 ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive
 ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive
|}.           


Definition bs_CI_from_lattice {S: Type} (lP : @lattice S) :  @bs_CI S := 
  let eqv  := lattice_eqv lP      in 
  let eq   := eqv_eq eqv          in 
  let wS   := eqv_witness eqv     in 
  let f    := eqv_new  eqv        in
  let meet := lattice_meet lP     in 
  {|
     bs_CI_eqv           := eqv
   ; bs_CI_plus          := lattice_join lP 
   ; bs_CI_times         := meet 
   ; bs_CI_plus_certs    := lattice_join_certs lP
   ; bs_CI_times_certs   := msg_certs_from_sg_certs (sg_certs_from_sg_CI_certs eq meet wS f (lattice_meet_certs lP))
   ; bs_CI_id_ann_certs  := zero_one_to_id_ann_certs (bounded_to_zero_one_certs (lattice_id_ann_certs lP))
   ; bs_CI_certs         := lattice_to_bs_certs (lattice_certs lP) 
   ; bs_CI_ast           := Ast_bs_CI_from_lattice (lattice_ast lP)
  |}.

Definition selective_dioid_from_selective_distributive_lattice {S: Type} (dS : @selective_distributive_lattice S) : @selective_dioid S := 
let eqv   := selective_distributive_lattice_eqv dS in
let eq    := eqv_eq eqv in
let plus  := selective_distributive_lattice_join dS in
let plusP := selective_distributive_lattice_join_certs dS in
let times := selective_distributive_lattice_meet dS in
let timesP:= selective_distributive_lattice_meet_certs dS in
let dPS   := selective_distributive_lattice_certs dS in 
let w     := eqv_witness eqv in
let f     := eqv_new eqv in
{|
  selective_dioid_eqv          := eqv 
; selective_dioid_plus         := plus
; selective_dioid_times        := times 
; selective_dioid_plus_certs   := plusP 
; selective_dioid_times_certs  := msg_certs_from_sg_certs (sg_certs_from_sg_CS_certs eq times w f timesP)
; selective_dioid_id_ann_certs := selective_distributive_lattice_id_ann_certs dS 
; selective_dioid_certs        := distributive_lattice_certs_to_semiring_certs (sg_CI_certs_from_sg_CS_certs plusP) (sg_CI_certs_from_sg_CS_certs timesP) dPS
; selective_dioid_ast          := Ast_selective_dioid_from_selective_distributive_lattice (selective_distributive_lattice_ast dS)
|}.  



Definition bs_from_semiring :∀ {S: Type}, @semiring S -> @bs S 
  := λ S sS,  bs_from_presemiring (presemiring_from_semiring sS).

Definition bs_from_selective_presemiring :∀ {S: Type}, @selective_presemiring S -> @bs S 
  := λ S sS,  bs_from_presemiring (presemiring_from_selective_presemiring sS).

Definition bs_from_dioid :∀ {S: Type}, @dioid S -> @bs S 
  := λ S sS,  bs_from_semiring (semiring_from_dioid sS).

Definition bs_from_selective_dioid :∀ {S: Type}, @selective_dioid S -> @bs S 
  := λ S sS,  bs_from_dioid (dioid_from_selective_dioid sS).

Definition bs_from_distributive_lattice :∀ {S: Type}, @distributive_lattice S ->@bs S 
  := λ S sS,  bs_from_dioid (dioid_from_distributive_lattice sS). 


Definition bs_from_distributive_prelattice :∀ {S: Type}, @distributive_prelattice S -> @bs S 
  := λ {S} sS,  bs_from_presemiring (presemiring_from_distributive_prelattice sS). 

Definition bs_from_selective_distributive_prelattice :∀ {S: Type}, @selective_distributive_prelattice S -> @bs S 
  := λ {S} sS,  bs_from_presemiring (presemiring_from_selective_distributive_prelattice sS). 

Definition bs_from_selective_distributive_lattice :∀ {S: Type}, @selective_distributive_lattice S -> @bs S 
  := λ S sS,  bs_from_distributive_lattice (distributive_lattice_from_selective_distributive_lattice sS). 


(*
bs_from_selective_distributive_lattice

Definition bs_from_dioid :∀ {S: Type}, @dioid S -> @bs S 
  := λ S sS,  bs_from_semiring (semiring_from_dioid sS).

Definition bs_from_selective_dioid :∀ {S: Type}, @selective_dioid S -> @bs S 
:= λ S sS,  bs_from_dioid (dioid_from_selective_dioid sS). 
*) 

End CAS.

Section Verify.

Section Lemmas.

Variable S : Type. 
Variable eq : brel S.     
Variable eqvP : eqv_proofs S eq.
Variable plus times : binary_op S.

Lemma correct_bs_certs_from_semiring_certs (plusP : sg_C_proofs S eq plus) (srP : semiring_proofs S eq plus times):
  P2C_bs S eq plus times (bs_proofs_from_semiring_proofs S eq plus times eqvP plusP srP)
  = 
  bs_certs_from_semiring_certs (P2C_semiring S eq plus times srP). 
Proof. destruct srP. 
       unfold bs_certs_from_semiring_certs, bs_proofs_from_semiring_proofs, P2C_semiring; simpl.
       destruct A_semiring_left_left_absorptive_d as [lla | [[s1 s2] nlla]];
       destruct A_semiring_left_right_absorptive_d as [X | [[s3 s4] nlra]]; 
       unfold bops_right_left_absorptive_decide_I, bops_right_right_absorptive_decide_I; compute; auto.
Qed.

Lemma correct_lattice_to_bs_certs (plusP : sg_CI_proofs S eq plus) (timesP : sg_CI_proofs S eq times) (lP : lattice_proofs S eq plus times) : 
  P2C_bs S eq plus times (lattice_to_bs_proofs S eq plus times eqvP plusP timesP lP)
  =                                      
  lattice_to_bs_certs (P2C_lattice S eq plus times lP). 
Proof. destruct lP. unfold lattice_to_bs_proofs, P2C_lattice, lattice_to_bs_certs, P2C_bs; simpl.
       destruct A_lattice_distributive_d as [LD | [[a [b c]] NLD] ]; simpl; auto. 
Qed.                    
  
Lemma correct_distributive_lattice_certs_to_semiring_certs 
  (plusP : sg_CI_proofs S eq plus)
  (timesP : sg_CI_proofs S eq times)
  (dP : distributive_lattice_proofs S eq plus times): 
  P2C_semiring S eq plus times (distributive_lattice_proofs_to_semiring_proofs S eq plus times eqvP plusP timesP dP)
  =                                      
  distributive_lattice_certs_to_semiring_certs
                   (P2C_sg_CI S eq plus plusP)
                   (P2C_sg_CI S eq times timesP)
                   (P2C_distributive_lattice S eq plus times dP). 
Proof. destruct dP. destruct plusP, timesP. 
       unfold distributive_lattice_proofs_to_semiring_proofs,
            distributive_lattice_certs_to_semiring_certs, P2C_sg_CI, P2C_distributive_lattice, P2C_semiring; simpl; auto. 
Qed.

Lemma correct_zero_one_to_id_ann_certs (zop : zero_one_proofs S eq plus times): 
   zero_one_to_id_ann_certs (P2C_zero_one S eq plus times zop)
   =
   P2C_id_ann S eq plus times (zero_one_to_id_ann_proofs S eq plus times zop).
Proof. destruct zop.
       destruct A_zero_one_plus_id_is_times_ann as [zero [idP annP]].              
       destruct A_zero_one_exists_times_id as [one oneP].
       unfold zero_one_to_id_ann_proofs, zero_one_to_id_ann_certs, P2C_zero_one, P2C_id_ann; simpl.
       reflexivity. 
Qed.

Lemma correct_bounded_to_zero_one_certs (bp : bounded_proofs S eq plus times): 
   bounded_to_zero_one_certs (P2C_bounded S eq plus times bp)
   =
   P2C_zero_one S eq plus times (bounded_to_zero_one_proofs S eq plus times bp).
Proof. destruct bp.
       destruct A_bounded_times_id_is_plus_ann as [one [oidP oannP]].                     
       destruct A_bounded_plus_id_is_times_ann as [zero [zidP zannP]].
       unfold bounded_to_zero_one_proofs, bounded_to_zero_one_certs, P2C_zero_one, P2C_bounded; simpl.
       reflexivity. 
Qed.

Lemma correct_lattice_certs_from_distributive_lattice_certs
      (eqv : A_eqv S)
      (plusP : sg_CI_proofs S (A_eqv_eq S eqv) plus)
      (timesP : sg_CI_proofs S (A_eqv_eq S eqv) times)
      (bp : distributive_lattice_proofs S (A_eqv_eq S eqv) plus times): 
   lattice_certs_from_distributive_lattice_certs (P2C_distributive_lattice S (A_eqv_eq S eqv) plus times bp)
   =
   P2C_lattice S (A_eqv_eq S eqv) plus times (lattice_proofs_from_distributive_lattice_proofs S plus times eqv plusP timesP bp).
Proof. destruct bp.
       unfold P2C_distributive_lattice, lattice_proofs_from_distributive_lattice_proofs, P2C_lattice.  
       unfold lattice_certs_from_distributive_lattice_certs; simpl. 
       reflexivity. 
Qed.

End Lemmas. 


Section Theorems.



Theorem correct_bs_from_presemiring : ∀ (S : Type) (P : A_presemiring S),  
    bs_from_presemiring (A2C_presemiring S P) = A2C_bs S (A_bs_from_presemiring S P).
Proof. intros S P. destruct P.
       unfold bs_from_presemiring, A_bs_from_presemiring, A2C_presemiring, A2C_bs; simpl.
       rewrite correct_bs_certs_from_semiring_certs.
       reflexivity. 
Qed.

Theorem correct_bs_from_bs_CI : ∀ (S : Type) (P : A_bs_CI S),  
    bs_from_bs_CI (A2C_bs_CI S P) = A2C_bs S (A_bs_from_bs_CI S P).
Proof. intros S P. destruct P.
       unfold bs_from_bs_CI, A_bs_from_bs_CI, A2C_bs_CI, A2C_bs; simpl.
       reflexivity. 
Qed.

Theorem correct_bs_CI_from_bs_CS : ∀ (S : Type) (P : A_bs_CS S),  
    bs_CI_from_bs_CS (A2C_bs_CS S P) = A2C_bs_CI S (A_bs_CI_from_bs_CS S P).
Proof. intros S P. destruct P.
       unfold bs_CI_from_bs_CS, A_bs_CI_from_bs_CS, A2C_bs_CI, A2C_bs_CS; simpl.
       reflexivity. 
Qed.


Theorem correct_bs_CI_from_lattice : ∀ (S : Type) (P : A_lattice S),  
    bs_CI_from_lattice (A2C_lattice S P) = A2C_bs_CI S (A_bs_CI_from_lattice S P).
Proof. intros S P. destruct P.
       unfold bs_CI_from_lattice, A_bs_CI_from_lattice, A2C_bs_CI, A2C_lattice; simpl.
       rewrite <- correct_msg_certs_from_sg_certs. 
       rewrite <- correct_sg_certs_from_sg_CI_certs. 
       rewrite <- correct_zero_one_to_id_ann_certs.
       rewrite <- correct_bounded_to_zero_one_certs.
       rewrite correct_lattice_to_bs_certs. 
       reflexivity. 
Qed.



Theorem correct_semiring_from_dioid : ∀ (S : Type) (P : A_dioid S),  
    semiring_from_dioid (A2C_dioid S P) = A2C_semiring S (A_semiring_from_dioid S P).
Proof. intros S P. destruct P.
       unfold semiring_from_dioid, A_semiring_from_dioid, A2C_semiring, A2C_dioid; simpl.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       rewrite correct_bounded_to_zero_one_certs; auto.        
Qed. 


Theorem correct_dioid_from_selective_dioid : ∀ (S : Type) (P : A_selective_dioid S),  
    dioid_from_selective_dioid (A2C_selective_dioid S P) = A2C_dioid S (A_dioid_from_selective_dioid S P).
Proof. intros S P. destruct P.
       unfold dioid_from_selective_dioid, A_dioid_from_selective_dioid.
       unfold A2C_selective_dioid, A2C_dioid. simpl.
       rewrite <- correct_sg_CI_certs_from_sg_CS_certs.
       reflexivity. 
Qed. 


Theorem correct_selective_dioid_from_selective_distributed_lattice : ∀ (S : Type) (P : A_selective_distributive_lattice S),  
    selective_dioid_from_selective_distributive_lattice (A2C_selective_distributive_lattice S P)
    =
    A2C_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S P).
Proof. intros S P. destruct P.
       unfold selective_dioid_from_selective_distributive_lattice, A_selective_dioid_from_selective_distributive_lattice. 
       unfold A2C_selective_dioid, A2C_selective_distributive_lattice; simpl.
       rewrite correct_distributive_lattice_certs_to_semiring_certs.
       rewrite <- correct_sg_CI_certs_from_sg_CS_certs.
       rewrite <- correct_sg_CI_certs_from_sg_CS_certs.
       rewrite <- correct_msg_certs_from_sg_certs.
       rewrite <- correct_sg_certs_from_sg_CS_certs. 
       reflexivity. 
Qed. 

Theorem correct_dioid_from_distributive_lattice : ∀ (S : Type) (P : A_distributive_lattice S),  
    dioid_from_distributive_lattice (A2C_distributive_lattice S P) = A2C_dioid S (A_dioid_from_distributive_lattice S P).
Proof. intros S P. destruct P.
       unfold dioid_from_distributive_lattice, A_dioid_from_distributive_lattice.
       unfold A2C_distributive_lattice, A2C_dioid. simpl.
       rewrite correct_distributive_lattice_certs_to_semiring_certs.
       rewrite <- correct_msg_certs_from_sg_certs.
       rewrite <- correct_sg_certs_from_sg_CI_certs. 
       reflexivity. 
Qed. 

Theorem correct_distributive_lattice_from_selective_distributive_lattice : ∀ (S : Type) (P : A_selective_distributive_lattice S),  
    distributive_lattice_from_selective_distributive_lattice (A2C_selective_distributive_lattice S P)
    =
    A2C_distributive_lattice S (A_distributive_lattice_from_selective_distributive_lattice S P).
Proof. intros S P. destruct P.
       unfold distributive_lattice_from_selective_distributive_lattice, A_distributive_lattice_from_selective_distributive_lattice.
       unfold A2C_distributive_lattice, A2C_selective_distributive_lattice. simpl.
       rewrite <- correct_sg_CI_certs_from_sg_CS_certs.
       reflexivity. 
Qed. 


Theorem correct_lattice_from_distributive_lattice : ∀ (S : Type) (P : A_distributive_lattice S),  
    lattice_from_distributive_lattice (A2C_distributive_lattice S P)
    =
    A2C_lattice S (A_lattice_from_distributive_lattice S P).
Proof. intros S P. destruct P.
       unfold lattice_from_distributive_lattice, A_lattice_from_distributive_lattice.
       unfold A2C_distributive_lattice, A2C_lattice. simpl.
       rewrite <- correct_lattice_certs_from_distributive_lattice_certs. 
       reflexivity. 
Qed. 

End Theorems. 
End Verify.   



                       
