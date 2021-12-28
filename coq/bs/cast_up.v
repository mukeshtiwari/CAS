Require Import Coq.Strings.String.

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

(**) 

Section Theory.

End Theory.

Section ACAS. 
Section Proofs.

Variable S: Type. 
Variable eq : brel S.     
Variable plus times : binary_op S.

(*  Note: Someday, after the CAS design has settled down a bit, it should be possible to generate 
    this (very tedious) file from a high-level specification. 


                        id_ann_proofs
                   1 /                \ 2
  pid_is_tann_proofs                   pann_is_tid_proofs
                 3  \                   / 4
                   dually_bounded_proofs
*)


(* 1 *)
Definition id_ann_proofs_from_pid_is_tann_proofs (P : pid_is_tann_proofs S eq plus times) : id_ann_proofs S eq plus times := 
{|
  A_id_ann_plus_times_d := Id_Ann_Proof_Equal _ _ _ _ (A_pid_is_tann_plus_times _ _ _ _ P)
; A_id_ann_times_plus_d := A_pid_is_tann_times_plus_d _ _ _ _ P
|}.

(* 2 *)
Definition id_ann_proofs_from_pann_is_tid_proofs (P : pann_is_tid_proofs S eq plus times) : id_ann_proofs S eq plus times := 
{|
  A_id_ann_plus_times_d := A_pann_is_tid_plus_times_d _ _ _ _ P
; A_id_ann_times_plus_d := Id_Ann_Proof_Equal _ _ _ _ (A_pann_is_tid_times_plus _ _ _ _ P)
|}.

(* 3 *)
Definition pid_is_tann_proofs_from_dually_bounded_proofs (P : dually_bounded_proofs S eq plus times) : pid_is_tann_proofs S eq plus times := 
{|
  A_pid_is_tann_plus_times   := A_bounded_plus_id_is_times_ann  _ _ _ _ P
; A_pid_is_tann_times_plus_d := Id_Ann_Proof_Equal _ _ _ _ (A_bounded_times_id_is_plus_ann _ _ _ _ P)
|}.

(* 4 *)
Definition pann_is_tid_proofs_from_dually_bounded_proofs (P : dually_bounded_proofs S eq plus times) : pann_is_tid_proofs S eq plus times := 
{|
  A_pann_is_tid_plus_times_d   := Id_Ann_Proof_Equal _ _ _ _ (A_bounded_plus_id_is_times_ann _ _ _ _ P)
; A_pann_is_tid_times_plus     := A_bounded_times_id_is_plus_ann  _ _ _ _ P
|}.


(* Derived *) 
Definition id_ann_proofs_from_dually_bounded_proofs (P : dually_bounded_proofs S eq plus times) : id_ann_proofs S eq plus times := 
             id_ann_proofs_from_pann_is_tid_proofs (pann_is_tid_proofs_from_dually_bounded_proofs P). 

(*

                           bs_proofs                 
                         1 /        \ 5 
              semiring_proofs     lattice_proofs
                 2 |                 |
              dioid_proofs           | 4
                 3 |                 | 
                distributive_lattice_proofs
*) 


(* 1 *)
Definition bs_proofs_from_semiring_proofs 
           (eqv : eqv_proofs S eq)
           (sg : sg_C_proofs S eq plus) 
           (sr : semiring_proofs S eq plus times) : bs_proofs S eq plus times := 
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

(* 2 *)
Definition semiring_proofs_from_dioid_proofs
       (dlp : dioid_proofs S eq plus times) : semiring_proofs S eq plus times := 
{|
  A_semiring_left_distributive        := A_dioid_left_distributive S eq plus times dlp
; A_semiring_right_distributive       := A_dioid_right_distributive S eq plus times dlp
; A_semiring_left_left_absorptive_d   := inl (A_dioid_left_left_absorptive S eq plus times dlp)
; A_semiring_left_right_absorptive_d  := inl (A_dioid_left_right_absorptive S eq plus times dlp) 
|}.

(* 3 *)
Definition dioid_proofs_from_distributive_lattice_proofs
       (eqvP : eqv_proofs S eq)
       (cong_plus : bop_congruence S eq plus)
       (comm_plus : bop_commutative S eq plus)
       (comm_times : bop_commutative S eq times)                  
(*     (plusP : sg_CI_proofs S eq plus)
       (timesP : sg_CI_proofs S eq times) *) 
       (dlp : distributive_lattice_proofs S eq plus times) : dioid_proofs S eq plus times := 
let refS  := A_eqv_reflexive S eq eqvP in
let tranS := A_eqv_transitive S eq eqvP in
(*let cong_plus  := A_sg_CI_congruence S eq plus plusP in   
let comm_plus  := A_sg_CI_commutative S eq plus plusP in
let comm_times := A_sg_CI_commutative S eq times timesP in   *) 
let ld  := A_distributive_lattice_distributive S eq plus times dlp in   
let la  := A_distributive_lattice_absorptive S eq plus times dlp in
{|
  A_dioid_left_distributive     := ld 
; A_dioid_right_distributive    := bop_left_distributive_implies_right S eq plus times tranS cong_plus comm_plus comm_times ld
; A_dioid_left_left_absorptive  := la 
; A_dioid_left_right_absorptive := bops_left_left_absorptive_implies_left_right S eq plus times refS tranS cong_plus comm_times la
|}.

(* 4 *)  
Definition lattice_proofs_from_distributive_lattice_proofs
           (eqvP : eqv_proofs S eq)
           (jP   : sg_CI_proofs S eq plus)
           (mP   : sg_CI_proofs S eq times) 
           (dP : distributive_lattice_proofs S eq plus times): lattice_proofs S eq plus times := 
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

(* 5 *)  
Definition bs_proofs_from_lattice_proofs 
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


(* Derived *)

Definition bs_proofs_from_dioid_proofs 
           (eqv : eqv_proofs S eq)
           (sg : sg_C_proofs S eq plus) 
           (di : dioid_proofs S eq plus times) : bs_proofs S eq plus times := 
  bs_proofs_from_semiring_proofs eqv sg (semiring_proofs_from_dioid_proofs di).

Definition bs_proofs_from_distributive_lattice_proofs 
           (eqvP : eqv_proofs S eq)
           (plusP : sg_CI_proofs S eq plus)
           (timesP : sg_CI_proofs S eq times)            
           (dP : distributive_lattice_proofs S eq plus times) : bs_proofs S eq plus times := 
  bs_proofs_from_lattice_proofs eqvP plusP timesP (lattice_proofs_from_distributive_lattice_proofs eqvP plusP timesP dP). 


Definition semiring_proofs_from_distributive_lattice_proofs
       (eqvP : eqv_proofs S eq) 
       (plusP : sg_CI_proofs S eq plus)
       (timesP : sg_CI_proofs S eq times) 
       (dlp : distributive_lattice_proofs S eq plus times) : semiring_proofs S eq plus times :=
         let cong_plus := A_sg_CI_congruence _ _ _ plusP in
         let comm_plus := A_sg_CI_commutative _ _ _ plusP in
         let comm_times := A_sg_CI_commutative _ _ _ timesP in
          semiring_proofs_from_dioid_proofs (dioid_proofs_from_distributive_lattice_proofs eqvP cong_plus comm_plus comm_times dlp). 

End Proofs.

Section Combinators.

(*            

Need to add idempotent_semiring, idempotent_pre_semiring 


        ---------------bs
        |               |
      2 |             1 |
        |               |             5
   pre_semiring       bs_CI <---------------- pre_lattice 
      3 |             |                       /15     |
     semiring       7 |                      /        |
        |             |                lattice         | 13
      4 |       pre_dioid                |             |
        |      8 /  \ 9                  | 6           | 
pre_dioid_with_zero  pre_dioid_with_one  |    ---- distributive_prelattice
              10 \   / 11                |   /
                 dioid                   |  / 14 
                     |                   | /
                  12 |                   / 
                     distributive_lattice

 *)

(* 1 *) 
Definition A_bs_from_bs_CI (S : Type) (bs : A_bs_CI S) : A_bs S := 
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

(* 2 *) 
Definition A_bs_from_presemiring (S: Type) (s: A_presemiring S) : A_bs S := 
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

(* 3 *) 
Definition A_presemiring_from_semiring (S: Type) (dS : A_semiring S) : A_presemiring S := 
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
; A_presemiring_id_ann_proofs := id_ann_proofs_from_pid_is_tann_proofs S eq plus times (A_semiring_id_ann_proofs S dS)
; A_presemiring_proofs        := A_semiring_proofs S dS 
; A_presemiring_ast           := Ast_presemiring_from_semiring(A_semiring_ast S dS)
|}.

(* 4 *) 
Definition A_semiring_from_pre_dioid_with_zero (S: Type) (dS : A_pre_dioid_with_zero S) : A_semiring S := 
let eqv := A_pre_dioid_with_zero_eqv S dS in
let eqvP := A_eqv_proofs S eqv in
let eq := A_eqv_eq S eqv in
let plus := A_pre_dioid_with_zero_plus S dS in
let times := A_pre_dioid_with_zero_times S dS in 
let w := A_eqv_witness S eqv in
let f := A_eqv_new S eqv in
let nt := A_eqv_not_trivial S eqv in
{|
  A_semiring_eqv           := eqv 
; A_semiring_plus          := plus
; A_semiring_times         := times 
; A_semiring_plus_proofs   := A_sg_C_proofs_from_sg_CI_proofs S eq plus w f nt eqvP (A_pre_dioid_with_zero_plus_proofs S dS)
; A_semiring_times_proofs  := A_pre_dioid_with_zero_times_proofs S dS
; A_semiring_id_ann_proofs := A_pre_dioid_with_zero_id_ann_proofs S dS                                                  
; A_semiring_proofs        := semiring_proofs_from_dioid_proofs S eq plus times (A_pre_dioid_with_zero_proofs S dS)
; A_semiring_ast           := Ast_semiring_from_dioid (A_pre_dioid_with_zero_ast S dS)
|}.  


(* 5 *)
Definition A_bs_CI_from_prelattice (S: Type) (lP : A_prelattice S) : A_bs_CI S := 
  let eqv  := A_prelattice_eqv S lP     in               
  let eq   := A_eqv_eq S eqv      in 
  let wS   := A_eqv_witness S eqv in 
  let f    := A_eqv_new S eqv     in
  let ntf  := A_eqv_not_trivial S eqv     in   
  let eqvP := A_eqv_proofs S eqv  in 
  let join := A_prelattice_join S lP    in
  let joinP := A_prelattice_join_proofs S lP in 
  let meet := A_prelattice_meet S lP    in
  let meetP := A_prelattice_meet_proofs S lP in   
  {|
     A_bs_CI_eqv           := eqv 
   ; A_bs_CI_plus          := join 
   ; A_bs_CI_times         := meet 
   ; A_bs_CI_plus_proofs   := joinP 
   ; A_bs_CI_times_proofs  := A_msg_proofs_from_sg_proofs S eq meet (A_sg_proofs_from_sg_CI_proofs S eq meet wS f ntf eqvP meetP)
   ; A_bs_CI_id_ann_proofs := A_prelattice_id_ann_proofs S lP
   ; A_bs_CI_proofs        := bs_proofs_from_lattice_proofs S eq join meet eqvP joinP meetP (A_prelattice_proofs S lP) 
   ; A_bs_CI_ast           := Ast_bs_CI_from_lattice (A_prelattice_ast S lP)
  |}.

(* 6 *) 
Definition A_lattice_from_distributive_lattice (S: Type) (dS : A_distributive_lattice S) : A_lattice S := 
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
    ; A_lattice_proofs        := lattice_proofs_from_distributive_lattice_proofs S eq join meet eqvP  joinP meetP dPS
    ; A_lattice_ast           := Ast_lattice_from_distributive_lattice (A_distributive_lattice_ast S dS)
|}.


(* 7 *) 
Definition A_bs_CI_from_pre_dioid (S: Type) (lP : A_pre_dioid S) : A_bs_CI S := 
  let eqv  := A_pre_dioid_eqv S lP     in               
  let eq   := A_eqv_eq S eqv      in 
  let wS   := A_eqv_witness S eqv in 
  let f    := A_eqv_new S eqv     in
  let ntf  := A_eqv_not_trivial S eqv     in   
  let eqvP := A_eqv_proofs S eqv  in 
  let plus := A_pre_dioid_plus S lP    in
  let plusP := A_pre_dioid_plus_proofs S lP in 
  let times := A_pre_dioid_times S lP    in
  {|
     A_bs_CI_eqv           := eqv 
   ; A_bs_CI_plus          := plus
   ; A_bs_CI_times         := times 
   ; A_bs_CI_plus_proofs   := plusP 
   ; A_bs_CI_times_proofs  := A_pre_dioid_times_proofs S lP 
   ; A_bs_CI_id_ann_proofs := A_pre_dioid_id_ann_proofs S lP
   ; A_bs_CI_proofs        := bs_proofs_from_dioid_proofs S eq plus times eqvP
                                (A_sg_C_proofs_from_sg_CI_proofs S eq plus wS f ntf eqvP plusP) (A_pre_dioid_proofs S lP) 
   ; A_bs_CI_ast           := Ast_bs_CI_from_lattice (A_pre_dioid_ast S lP)
  |}.

(* 8 *) 
Definition A_pre_dioid_from_pre_dioid_with_zero (S: Type) (pd :A_pre_dioid_with_zero S) : A_pre_dioid S := 
{|
  A_pre_dioid_eqv           := A_pre_dioid_with_zero_eqv _ pd 
; A_pre_dioid_plus          := A_pre_dioid_with_zero_plus _ pd 
; A_pre_dioid_times         := A_pre_dioid_with_zero_times _ pd 
; A_pre_dioid_plus_proofs   := A_pre_dioid_with_zero_plus_proofs _ pd 
; A_pre_dioid_times_proofs  := A_pre_dioid_with_zero_times_proofs _ pd 
; A_pre_dioid_id_ann_proofs := id_ann_proofs_from_pid_is_tann_proofs _ _ _ _ (A_pre_dioid_with_zero_id_ann_proofs _ pd)
; A_pre_dioid_proofs        := A_pre_dioid_with_zero_proofs _ pd 
; A_pre_dioid_ast           := A_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 9 *) 
Definition A_pre_dioid_from_pre_dioid_with_one (S: Type) (pd :A_pre_dioid_with_one S) : A_pre_dioid S := 
{|
  A_pre_dioid_eqv           := A_pre_dioid_with_one_eqv _ pd 
; A_pre_dioid_plus          := A_pre_dioid_with_one_plus _ pd 
; A_pre_dioid_times         := A_pre_dioid_with_one_times _ pd 
; A_pre_dioid_plus_proofs   := A_pre_dioid_with_one_plus_proofs _ pd 
; A_pre_dioid_times_proofs  := A_pre_dioid_with_one_times_proofs _ pd 
; A_pre_dioid_id_ann_proofs := id_ann_proofs_from_pann_is_tid_proofs _ _ _ _ (A_pre_dioid_with_one_id_ann_proofs _ pd)
; A_pre_dioid_proofs        := A_pre_dioid_with_one_proofs _ pd 
; A_pre_dioid_ast           := A_pre_dioid_with_one_ast _ pd 
|}.                                                                                                      

(* 10 *) 
Definition A_pre_dioid_with_zero_from_dioid (S: Type) (pd :A_dioid S) : A_pre_dioid_with_zero S := 
{|
  A_pre_dioid_with_zero_eqv           := A_dioid_eqv _ pd 
; A_pre_dioid_with_zero_plus          := A_dioid_plus _ pd 
; A_pre_dioid_with_zero_times         := A_dioid_times _ pd 
; A_pre_dioid_with_zero_plus_proofs   := A_dioid_plus_proofs _ pd 
; A_pre_dioid_with_zero_times_proofs  := A_dioid_times_proofs _ pd 
; A_pre_dioid_with_zero_id_ann_proofs := pid_is_tann_proofs_from_dually_bounded_proofs _ _ _ _ (A_dioid_id_ann_proofs _ pd)
; A_pre_dioid_with_zero_proofs        := A_dioid_proofs _ pd 
; A_pre_dioid_with_zero_ast           := A_dioid_ast _ pd 
|}.                                                                                                      

(* 11 *) 
Definition A_pre_dioid_with_one_from_dioid (S: Type) (pd :A_dioid S) : A_pre_dioid_with_one S := 
{|
  A_pre_dioid_with_one_eqv           := A_dioid_eqv _ pd 
; A_pre_dioid_with_one_plus          := A_dioid_plus _ pd 
; A_pre_dioid_with_one_times         := A_dioid_times _ pd 
; A_pre_dioid_with_one_plus_proofs   := A_dioid_plus_proofs _ pd 
; A_pre_dioid_with_one_times_proofs  := A_dioid_times_proofs _ pd 
; A_pre_dioid_with_one_id_ann_proofs := pann_is_tid_proofs_from_dually_bounded_proofs _ _ _ _ (A_dioid_id_ann_proofs _ pd)
; A_pre_dioid_with_one_proofs        := A_dioid_proofs _ pd 
; A_pre_dioid_with_one_ast           := A_dioid_ast _ pd 
|}.                                                                                                      

(* 12 *) 
Definition A_dioid_from_distributive_lattice (S: Type) (dS : A_distributive_lattice S) : A_dioid S := 
let eqv   := A_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let plus  := A_distributive_lattice_join S dS in
let plusP := A_distributive_lattice_join_proofs S dS in
let times := A_distributive_lattice_meet S dS in
let timesP:= A_distributive_lattice_meet_proofs S dS in
let dPS   := A_distributive_lattice_proofs S dS in
let cong_plus := A_sg_CI_congruence _ _ _ plusP in
let comm_plus := A_sg_CI_commutative _ _ _ plusP in
let comm_times := A_sg_CI_commutative _ _ _ timesP in 
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
; A_dioid_proofs       := dioid_proofs_from_distributive_lattice_proofs S eq plus times eqvP cong_plus comm_plus comm_times dPS
; A_dioid_ast          := Ast_dioid_from_distributive_lattice (A_distributive_lattice_ast S dS)
|}.


(* 13 *) 
Definition A_prelattice_from_distributive_prelattice (S: Type) (dS : A_distributive_prelattice S) : A_prelattice S := 
let eqv   := A_distributive_prelattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let join  := A_distributive_prelattice_join S dS in
let joinP := A_distributive_prelattice_join_proofs S dS in
let meet  := A_distributive_prelattice_meet S dS in
let meetP := A_distributive_prelattice_meet_proofs S dS in
let dPS   := A_distributive_prelattice_proofs S dS in 
{|
      A_prelattice_eqv           := eqv 
    ; A_prelattice_join          := join 
    ; A_prelattice_meet          := meet
    ; A_prelattice_join_proofs   := joinP 
    ; A_prelattice_meet_proofs   := meetP
    ; A_prelattice_id_ann_proofs := A_distributive_prelattice_id_ann_proofs S dS 
    ; A_prelattice_proofs        := lattice_proofs_from_distributive_lattice_proofs S eq join meet eqvP  joinP meetP dPS
    ; A_prelattice_ast           := Ast_lattice_from_distributive_lattice (A_distributive_prelattice_ast S dS)
|}.


(* 14 *) 
Definition A_distributive_prelattice_from_distributive_lattice (S: Type) (dS : A_distributive_lattice S) : A_distributive_prelattice S := 
let eqv   := A_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let join  := A_distributive_lattice_join S dS in
let joinP := A_distributive_lattice_join_proofs S dS in
let meet  := A_distributive_lattice_meet S dS in
let meetP := A_distributive_lattice_meet_proofs S dS in
{|
      A_distributive_prelattice_eqv           := eqv 
    ; A_distributive_prelattice_join          := join 
    ; A_distributive_prelattice_meet          := meet
    ; A_distributive_prelattice_join_proofs   := joinP 
    ; A_distributive_prelattice_meet_proofs   := meetP
    ; A_distributive_prelattice_id_ann_proofs := id_ann_proofs_from_dually_bounded_proofs _ _ _ _ (A_distributive_lattice_id_ann_proofs S dS)
    ; A_distributive_prelattice_proofs        := A_distributive_lattice_proofs S dS 
    ; A_distributive_prelattice_ast           := Ast_lattice_from_distributive_lattice (A_distributive_lattice_ast S dS)
|}.

(* 15 *) 
Definition A_prelattice_from_lattice (S: Type) (dS : A_lattice S) : A_prelattice S := 
let eqv   := A_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let join  := A_lattice_join S dS in
let joinP := A_lattice_join_proofs S dS in
let meet  := A_lattice_meet S dS in
let meetP := A_lattice_meet_proofs S dS in
{|
      A_prelattice_eqv           := eqv 
    ; A_prelattice_join          := join 
    ; A_prelattice_meet          := meet
    ; A_prelattice_join_proofs   := joinP 
    ; A_prelattice_meet_proofs   := meetP
    ; A_prelattice_id_ann_proofs := id_ann_proofs_from_dually_bounded_proofs _ _ _ _ (A_lattice_id_ann_proofs S dS)
    ; A_prelattice_proofs        := A_lattice_proofs S dS
    ; A_prelattice_ast           := Ast_lattice_from_distributive_lattice (A_lattice_ast S dS)
|}.


(* Derived *) 

(* two hops *) 
Definition A_bs_from_semiring (S: Type) (sr : A_semiring S) : A_bs S := 
  A_bs_from_presemiring S (A_presemiring_from_semiring S sr).

Definition A_bs_from_pre_dioid (S: Type) (pd : A_pre_dioid S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_pre_dioid S pd).

Definition A_bs_from_prelattice (S: Type) (l : A_prelattice S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_prelattice S l). 

Definition A_presemiring_from_pre_dioid_with_zero (S: Type) (pd : A_pre_dioid_with_zero S) : A_presemiring S := 
  A_presemiring_from_semiring S (A_semiring_from_pre_dioid_with_zero S pd). 

Definition A_bs_CI_from_lattice (S: Type) (l : A_lattice S) : A_bs_CI S := 
  A_bs_CI_from_prelattice S (A_prelattice_from_lattice S l).

Definition A_bs_CI_from_distributive_prelattice (S: Type) (l : A_distributive_prelattice S) : A_bs_CI S := 
  A_bs_CI_from_prelattice S (A_prelattice_from_distributive_prelattice S l). 

Definition A_bs_CI_from_pre_dioid_with_zero (S: Type) (pd : A_pre_dioid_with_zero S) : A_bs_CI S := 
  A_bs_CI_from_pre_dioid S (A_pre_dioid_from_pre_dioid_with_zero S pd). 

Definition A_bs_CI_from_pre_dioid_with_one (S: Type) (pd : A_pre_dioid_with_one S) : A_bs_CI S := 
  A_bs_CI_from_pre_dioid S (A_pre_dioid_from_pre_dioid_with_one S pd). 

Definition A_pre_dioid_from_dioid (S: Type) (d : A_dioid S) : A_pre_dioid S := 
  A_pre_dioid_from_pre_dioid_with_zero S (A_pre_dioid_with_zero_from_dioid S d). 

Definition A_pre_dioid_with_zero_from_distributive_lattice (S: Type) (dl : A_distributive_lattice S) : A_pre_dioid_with_zero S := 
  A_pre_dioid_with_zero_from_dioid S (A_dioid_from_distributive_lattice S dl). 

Definition A_pre_dioid_with_one_from_distributive_lattice (S: Type) (dl : A_distributive_lattice S) : A_pre_dioid_with_one S := 
  A_pre_dioid_with_one_from_dioid S (A_dioid_from_distributive_lattice S dl). 

Definition A_prelattice_from_distributive_lattice (S: Type) (dl : A_distributive_lattice S) : A_prelattice S := 
  A_prelattice_from_distributive_prelattice S (A_distributive_prelattice_from_distributive_lattice S dl). 


(* three hops *)
Definition A_bs_from_pre_dioid_with_zero (S: Type) (pd : A_pre_dioid_with_zero S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_pre_dioid_with_zero S pd).

Definition A_bs_from_pre_dioid_with_one (S: Type) (pd : A_pre_dioid_with_one S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_pre_dioid_with_one S pd).

Definition A_bs_from_distributive_prelattice (S: Type) (pd : A_distributive_prelattice S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_distributive_prelattice S pd).

Definition A_bs_from_lattice (S: Type) (pd : A_lattice S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_lattice S pd).

Definition A_bs_CI_from_dioid (S: Type) (pd : A_dioid S) : A_bs_CI S := 
  A_bs_CI_from_pre_dioid_with_zero S (A_pre_dioid_with_zero_from_dioid S pd).

Definition A_bs_CI_from_distributive_lattice (S: Type) (pd : A_distributive_lattice S) : A_bs_CI S := 
  A_bs_CI_from_prelattice S (A_prelattice_from_distributive_lattice S pd).

Definition A_pre_dioid_from_distributive_lattice (S: Type) (dl : A_distributive_lattice S) : A_pre_dioid S := 
  A_pre_dioid_from_pre_dioid_with_zero S (A_pre_dioid_with_zero_from_distributive_lattice S dl).

(* four hops *)
Definition A_bs_from_dioid (S: Type) (pd : A_dioid S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_dioid S pd).

Definition A_bs_from_distributive_lattice (S: Type) (pd : A_distributive_lattice S) : A_bs S := 
  A_bs_from_bs_CI S (A_bs_CI_from_distributive_lattice S pd).


(*            

                              bs 
                              | 
                              | 1
                              |
                            bs_CS 
                              |
                              | 2 
                              |
           ----------selective_presemiring
           |                  | 
         3 |                  | 5
           |                  | 
selective_semiring      selective_pre_dioid --------------------------
        |                    /\                                       | 
      4 |                   /  \                                      |
        |                6 /    \ 7                                   | 10
selective_pre_dioid_with_zero  selective_pre_dioid_with_one           | 
                        8 \     / 9                                   |
                           \   /                                      | 
             ---------selective_dioid                                 | 
             |                                                        | 
          11 |                                          A_selective_distributive_prelattice
             |                                        12 /                               \ 13
             |               selective_distributive_prelattice_with_zero      selective_distributive_prelattice_with_one
             |                                        14 \                              / 15 
             -------------------------------------------  selective_distributive_lattice




                                   | 
                                   | 5
                                   |
                          selective_pre_dioid
                        6 /        |        \ 7 
selective_pre_dioid_with_zero    16|       selective_pre_dioid_with_one
    |                              |                           | 
 17 |                 selective_cancellative_pre_dioid         | 18
    |              19 /                               \ 20     |
selective_cancellative_pre_dioid_with_zero     selective_cancellative_pre_dioid_with_one
                    21  \                              / 22
                          selective_cancellative_dioid





selective_pre_dioid_with_zero                     selective_pre_dioid_with_one          
             |                                              | 
             | 23                                           | 24 
             |                                              | 
selective_distributive_prelattice_with_zero    selective_distributive_prelattice_with_one



*)

(* 1 *) 
Definition A_bs_from_bs_CS (S : Type) (bs : A_bs_CS S) : A_bs S :=
{| 
  A_bs_eqv          := A_bs_CS_eqv S bs
; A_bs_plus         := A_bs_CS_plus S bs
; A_bs_times        := A_bs_CS_times S bs
; A_bs_plus_proofs  := A_asg_proofs_from_sg_CS_proofs S
                         (A_eqv_eq S (A_bs_CS_eqv S bs))
                         (A_bs_CS_plus S bs)
                         (A_eqv_witness S (A_bs_CS_eqv S bs))
                         (A_eqv_new S (A_bs_CS_eqv S bs))
                         (A_eqv_not_trivial S (A_bs_CS_eqv S bs))                         
                         (A_eqv_proofs S (A_bs_CS_eqv S bs))
                         (A_bs_CS_plus_proofs S bs)  
; A_bs_times_proofs := A_bs_CS_times_proofs S bs
; A_bs_id_ann_proofs := A_bs_CS_id_ann_proofs S bs                                            
; A_bs_proofs       := A_bs_CS_proofs S bs
; A_bs_ast          := Ast_bs_from_bs_CI (A_bs_CS_ast S bs)
|}.


(* 2 *) 
Definition A_bs_CS_from_selective_presemiring :∀ (S: Type), A_selective_presemiring S -> A_bs_CS S
  := λ S lP,
  let eqv  := A_selective_presemiring_eqv S lP     in               
  let eq   := A_eqv_eq S eqv      in 
  let wS   := A_eqv_witness S eqv in 
  let f    := A_eqv_new S eqv     in
  let ntf  := A_eqv_not_trivial S eqv     in   
  let eqvP := A_eqv_proofs S eqv  in 
  let plus := A_selective_presemiring_plus S lP    in
  let plusP := A_selective_presemiring_plus_proofs S lP in 
  let times := A_selective_presemiring_times S lP    in
  {|
     A_bs_CS_eqv           := eqv 
   ; A_bs_CS_plus          := plus
   ; A_bs_CS_times         := times 
   ; A_bs_CS_plus_proofs   := plusP 
   ; A_bs_CS_times_proofs  := A_selective_presemiring_times_proofs S lP 
   ; A_bs_CS_id_ann_proofs := A_selective_presemiring_id_ann_proofs S lP
   ; A_bs_CS_proofs        := bs_proofs_from_semiring_proofs S eq plus times eqvP
                                (A_sg_C_proofs_from_sg_CS_proofs S eq plus wS f ntf eqvP plusP) (A_selective_presemiring_proofs S lP) 
   ; A_bs_CS_ast           := Ast_bs_CI_from_lattice (A_selective_presemiring_ast S lP)
  |}.





(* 3 *) 
Definition A_selective_presemiring_from_selective_semiring (S: Type) (dS : A_selective_semiring S) : A_selective_presemiring S := 
let eqvS  := A_selective_semiring_eqv S dS in
let eq    := A_eqv_eq S eqvS in
let plus  := A_selective_semiring_plus S dS in
let times := A_selective_semiring_times S dS in 
{|
  A_selective_presemiring_eqv           := eqvS 
; A_selective_presemiring_plus          := plus
; A_selective_presemiring_times         := times 
; A_selective_presemiring_plus_proofs   := A_selective_semiring_plus_proofs S dS 
; A_selective_presemiring_times_proofs  := A_selective_semiring_times_proofs S dS 
; A_selective_presemiring_id_ann_proofs := id_ann_proofs_from_pid_is_tann_proofs S eq plus times (A_selective_semiring_id_ann_proofs S dS)
; A_selective_presemiring_proofs        := A_selective_semiring_proofs S dS 
; A_selective_presemiring_ast           := Ast_presemiring_from_semiring(A_selective_semiring_ast S dS)
|}.

(* 4 *) 
Definition A_selective_semiring_from_selective_pre_dioid_with_zero (S: Type) (dS : A_selective_pre_dioid_with_zero S) : A_selective_semiring S := 
let eqv := A_selective_pre_dioid_with_zero_eqv S dS in
let eqvP := A_eqv_proofs S eqv in
let eq := A_eqv_eq S eqv in
let plus := A_selective_pre_dioid_with_zero_plus S dS in
let times := A_selective_pre_dioid_with_zero_times S dS in 
let w := A_eqv_witness S eqv in
let f := A_eqv_new S eqv in
let nt := A_eqv_not_trivial S eqv in
{|
  A_selective_semiring_eqv           := eqv 
; A_selective_semiring_plus          := plus
; A_selective_semiring_times         := times 
; A_selective_semiring_plus_proofs   := A_selective_pre_dioid_with_zero_plus_proofs S dS
; A_selective_semiring_times_proofs  := A_selective_pre_dioid_with_zero_times_proofs S dS
; A_selective_semiring_id_ann_proofs := A_selective_pre_dioid_with_zero_id_ann_proofs S dS                                                  
; A_selective_semiring_proofs        := semiring_proofs_from_dioid_proofs S eq plus times (A_selective_pre_dioid_with_zero_proofs S dS)
; A_selective_semiring_ast           := Ast_semiring_from_dioid (A_selective_pre_dioid_with_zero_ast S dS)
|}.  

(* 5 *) 
Definition A_selective_presemiring_from_selective_pre_dioid (S: Type) (dS : A_selective_pre_dioid S) : A_selective_presemiring S := 
let eqvS  := A_selective_pre_dioid_eqv S dS in
let eq    := A_eqv_eq S eqvS in
let plus  := A_selective_pre_dioid_plus S dS in
let times := A_selective_pre_dioid_times S dS in 
{|
  A_selective_presemiring_eqv           := eqvS 
; A_selective_presemiring_plus          := plus
; A_selective_presemiring_times         := times 
; A_selective_presemiring_plus_proofs   := A_selective_pre_dioid_plus_proofs S dS 
; A_selective_presemiring_times_proofs  := A_selective_pre_dioid_times_proofs S dS 
; A_selective_presemiring_id_ann_proofs := A_selective_pre_dioid_id_ann_proofs S dS
; A_selective_presemiring_proofs        := semiring_proofs_from_dioid_proofs _ _ _ _ (A_selective_pre_dioid_proofs S dS) 
; A_selective_presemiring_ast           := Ast_presemiring_from_semiring(A_selective_pre_dioid_ast S dS)
|}.

(* 6 *) 
Definition A_selective_pre_dioid_from_selective_pre_dioid_with_zero (S: Type) (pd :A_selective_pre_dioid_with_zero S) : A_selective_pre_dioid S := 
{|
  A_selective_pre_dioid_eqv           := A_selective_pre_dioid_with_zero_eqv _ pd 
; A_selective_pre_dioid_plus          := A_selective_pre_dioid_with_zero_plus _ pd 
; A_selective_pre_dioid_times         := A_selective_pre_dioid_with_zero_times _ pd 
; A_selective_pre_dioid_plus_proofs   := A_selective_pre_dioid_with_zero_plus_proofs _ pd 
; A_selective_pre_dioid_times_proofs  := A_selective_pre_dioid_with_zero_times_proofs _ pd 
; A_selective_pre_dioid_id_ann_proofs := id_ann_proofs_from_pid_is_tann_proofs _ _ _ _ (A_selective_pre_dioid_with_zero_id_ann_proofs _ pd)
; A_selective_pre_dioid_proofs        := A_selective_pre_dioid_with_zero_proofs _ pd 
; A_selective_pre_dioid_ast           := A_selective_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 7 *) 
Definition A_selective_pre_dioid_from_selective_pre_dioid_with_one (S: Type) (pd : A_selective_pre_dioid_with_one S) : A_selective_pre_dioid S := 
{|
  A_selective_pre_dioid_eqv           := A_selective_pre_dioid_with_one_eqv _ pd 
; A_selective_pre_dioid_plus          := A_selective_pre_dioid_with_one_plus _ pd 
; A_selective_pre_dioid_times         := A_selective_pre_dioid_with_one_times _ pd 
; A_selective_pre_dioid_plus_proofs   := A_selective_pre_dioid_with_one_plus_proofs _ pd 
; A_selective_pre_dioid_times_proofs  := A_selective_pre_dioid_with_one_times_proofs _ pd 
; A_selective_pre_dioid_id_ann_proofs := id_ann_proofs_from_pann_is_tid_proofs _ _ _ _ (A_selective_pre_dioid_with_one_id_ann_proofs _ pd)
; A_selective_pre_dioid_proofs        := A_selective_pre_dioid_with_one_proofs _ pd 
; A_selective_pre_dioid_ast           := A_selective_pre_dioid_with_one_ast _ pd 
|}.                                                                                                      


(* 8 *) 
Definition A_selective_pre_dioid_with_zero_from_selective_dioid (S: Type) (pd :A_selective_dioid S) : A_selective_pre_dioid_with_zero S := 
{|
  A_selective_pre_dioid_with_zero_eqv           := A_selective_dioid_eqv _ pd 
; A_selective_pre_dioid_with_zero_plus          := A_selective_dioid_plus _ pd 
; A_selective_pre_dioid_with_zero_times         := A_selective_dioid_times _ pd 
; A_selective_pre_dioid_with_zero_plus_proofs   := A_selective_dioid_plus_proofs _ pd 
; A_selective_pre_dioid_with_zero_times_proofs  := A_selective_dioid_times_proofs _ pd 
; A_selective_pre_dioid_with_zero_id_ann_proofs := pid_is_tann_proofs_from_dually_bounded_proofs _ _ _ _ (A_selective_dioid_id_ann_proofs _ pd)
; A_selective_pre_dioid_with_zero_proofs        := A_selective_dioid_proofs _ pd 
; A_selective_pre_dioid_with_zero_ast           := A_selective_dioid_ast _ pd 
|}.                                                                                                      


(* 9 *) 
Definition A_selective_pre_dioid_with_one_from_selective_dioid (S: Type) (pd :A_selective_dioid S) : A_selective_pre_dioid_with_one S := 
{|
  A_selective_pre_dioid_with_one_eqv           := A_selective_dioid_eqv _ pd 
; A_selective_pre_dioid_with_one_plus          := A_selective_dioid_plus _ pd 
; A_selective_pre_dioid_with_one_times         := A_selective_dioid_times _ pd 
; A_selective_pre_dioid_with_one_plus_proofs   := A_selective_dioid_plus_proofs _ pd 
; A_selective_pre_dioid_with_one_times_proofs  := A_selective_dioid_times_proofs _ pd 
; A_selective_pre_dioid_with_one_id_ann_proofs := pann_is_tid_proofs_from_dually_bounded_proofs _ _ _ _ (A_selective_dioid_id_ann_proofs _ pd)
; A_selective_pre_dioid_with_one_proofs        := A_selective_dioid_proofs _ pd 
; A_selective_pre_dioid_with_one_ast           := A_selective_dioid_ast _ pd 
|}.                                                                                                      


(* 10 *)
Definition A_selective_pre_dioid_from_selective_distributive_prelattice
           (S: Type)
           (dS : A_selective_distributive_prelattice S) : A_selective_pre_dioid S :=
let eqv   := A_selective_distributive_prelattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let plus  := A_selective_distributive_prelattice_join S dS in
let plusP := A_selective_distributive_prelattice_join_proofs S dS in
let times := A_selective_distributive_prelattice_meet S dS in
let timesP:= A_selective_distributive_prelattice_meet_proofs S dS in
let dPS   := A_selective_distributive_prelattice_proofs S dS in
let cong_plus  := A_sg_CS_congruence S eq plus plusP in   
let comm_plus  := A_sg_CS_commutative S eq plus plusP in
let comm_times := A_sg_CS_commutative S eq times timesP in   
let w     := A_eqv_witness S eqv in
let f     := A_eqv_new S eqv in
let nt    := A_eqv_not_trivial S eqv in
{|
  A_selective_pre_dioid_eqv          := eqv 
; A_selective_pre_dioid_plus         := plus
; A_selective_pre_dioid_times        := times 
; A_selective_pre_dioid_plus_proofs  := plusP 
; A_selective_pre_dioid_times_proofs := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CS_proofs S eq times w f nt eqvP timesP)
; A_selective_pre_dioid_id_ann_proofs := A_selective_distributive_prelattice_id_ann_proofs S dS 
; A_selective_pre_dioid_proofs        := dioid_proofs_from_distributive_lattice_proofs S eq plus times eqvP cong_plus comm_plus comm_times dPS
; A_selective_pre_dioid_ast           := Ast_dioid_from_distributive_lattice (A_selective_distributive_prelattice_ast S dS)
|}.

(* 11 *) 
Definition A_selective_dioid_from_selective_distributive_lattice (S: Type) (dS : A_selective_distributive_lattice S) : A_selective_dioid S := 
let eqv   := A_selective_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let plus  := A_selective_distributive_lattice_join S dS in
let plusP := A_selective_distributive_lattice_join_proofs S dS in
let times := A_selective_distributive_lattice_meet S dS in
let timesP:= A_selective_distributive_lattice_meet_proofs S dS in
let dPS   := A_selective_distributive_lattice_proofs S dS in
let cong_plus  := A_sg_CS_congruence S eq plus plusP in   
let comm_plus  := A_sg_CS_commutative S eq plus plusP in
let comm_times := A_sg_CS_commutative S eq times timesP in   
let w     := A_eqv_witness S eqv in
let f     := A_eqv_new S eqv in
let nt    := A_eqv_not_trivial S eqv in
{|
  A_selective_dioid_eqv          := eqv 
; A_selective_dioid_plus         := plus
; A_selective_dioid_times        := times 
; A_selective_dioid_plus_proofs  := plusP 
; A_selective_dioid_times_proofs := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CS_proofs S eq times w f nt eqvP timesP)
; A_selective_dioid_id_ann_proofs := A_selective_distributive_lattice_id_ann_proofs S dS 
; A_selective_dioid_proofs       := dioid_proofs_from_distributive_lattice_proofs S eq plus times eqvP cong_plus comm_plus comm_times dPS
; A_selective_dioid_ast          := Ast_dioid_from_distributive_lattice (A_selective_distributive_lattice_ast S dS)
|}.


(* 12 *) 
Definition A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero
           (S : Type)
           (dS : A_selective_distributive_prelattice_with_zero S) : A_selective_distributive_prelattice S := 
{|
  A_selective_distributive_prelattice_eqv           := A_selective_distributive_prelattice_with_zero_eqv _ dS 
; A_selective_distributive_prelattice_join          := A_selective_distributive_prelattice_with_zero_join _ dS 
; A_selective_distributive_prelattice_meet          := A_selective_distributive_prelattice_with_zero_meet _ dS 
; A_selective_distributive_prelattice_join_proofs   := A_selective_distributive_prelattice_with_zero_join_proofs _ dS 
; A_selective_distributive_prelattice_meet_proofs   := A_selective_distributive_prelattice_with_zero_meet_proofs _ dS 
; A_selective_distributive_prelattice_id_ann_proofs := id_ann_proofs_from_pid_is_tann_proofs _ _ _ _ (A_selective_distributive_prelattice_with_zero_id_ann_proofs _ dS)
; A_selective_distributive_prelattice_proofs        := A_selective_distributive_prelattice_with_zero_proofs _ dS 
; A_selective_distributive_prelattice_ast           := A_selective_distributive_prelattice_with_zero_ast _ dS 
|}.

(* 13 *) 
Definition A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_one 
           (S : Type)
           (dS : A_selective_distributive_prelattice_with_one S) : A_selective_distributive_prelattice S := 
{|
  A_selective_distributive_prelattice_eqv           := A_selective_distributive_prelattice_with_one_eqv _ dS 
; A_selective_distributive_prelattice_join          := A_selective_distributive_prelattice_with_one_join _ dS 
; A_selective_distributive_prelattice_meet          := A_selective_distributive_prelattice_with_one_meet _ dS 
; A_selective_distributive_prelattice_join_proofs   := A_selective_distributive_prelattice_with_one_join_proofs _ dS 
; A_selective_distributive_prelattice_meet_proofs   := A_selective_distributive_prelattice_with_one_meet_proofs _ dS 
; A_selective_distributive_prelattice_id_ann_proofs := id_ann_proofs_from_pann_is_tid_proofs _ _ _ _ (A_selective_distributive_prelattice_with_one_id_ann_proofs _ dS)
; A_selective_distributive_prelattice_proofs        := A_selective_distributive_prelattice_with_one_proofs _ dS 
; A_selective_distributive_prelattice_ast           := A_selective_distributive_prelattice_with_one_ast _ dS 
|}.

(* 14 *) 
Definition A_selective_distributive_prelattice_with_zero_from_selective_distributive_lattice
           (S : Type)
           (dS : A_selective_distributive_lattice S) : A_selective_distributive_prelattice_with_zero S := 
{|
  A_selective_distributive_prelattice_with_zero_eqv           := A_selective_distributive_lattice_eqv _ dS 
; A_selective_distributive_prelattice_with_zero_join          := A_selective_distributive_lattice_join _ dS 
; A_selective_distributive_prelattice_with_zero_meet          := A_selective_distributive_lattice_meet _ dS 
; A_selective_distributive_prelattice_with_zero_join_proofs   := A_selective_distributive_lattice_join_proofs _ dS 
; A_selective_distributive_prelattice_with_zero_meet_proofs   := A_selective_distributive_lattice_meet_proofs _ dS 
; A_selective_distributive_prelattice_with_zero_id_ann_proofs := pid_is_tann_proofs_from_dually_bounded_proofs _ _ _ _ (A_selective_distributive_lattice_id_ann_proofs _ dS)
; A_selective_distributive_prelattice_with_zero_proofs        := A_selective_distributive_lattice_proofs _ dS 
; A_selective_distributive_prelattice_with_zero_ast           := A_selective_distributive_lattice_ast _ dS 
|}.

(* 15 *) 
Definition A_selective_distributive_prelattice_with_one_from_selective_distributive_lattice
           (S : Type)
           (dS : A_selective_distributive_lattice S) : A_selective_distributive_prelattice_with_one S := 
{|
  A_selective_distributive_prelattice_with_one_eqv           := A_selective_distributive_lattice_eqv _ dS 
; A_selective_distributive_prelattice_with_one_join          := A_selective_distributive_lattice_join _ dS 
; A_selective_distributive_prelattice_with_one_meet          := A_selective_distributive_lattice_meet _ dS 
; A_selective_distributive_prelattice_with_one_join_proofs   := A_selective_distributive_lattice_join_proofs _ dS 
; A_selective_distributive_prelattice_with_one_meet_proofs   := A_selective_distributive_lattice_meet_proofs _ dS 
; A_selective_distributive_prelattice_with_one_id_ann_proofs := pann_is_tid_proofs_from_dually_bounded_proofs _ _ _ _ (A_selective_distributive_lattice_id_ann_proofs _ dS)
; A_selective_distributive_prelattice_with_one_proofs        := A_selective_distributive_lattice_proofs _ dS 
; A_selective_distributive_prelattice_with_one_ast           := A_selective_distributive_lattice_ast _ dS 
|}.


(* 16 *)

Definition A_selective_pre_dioid_from_selective_cancellative_pre_dioid (S: Type)
           (pd : A_selective_cancellative_pre_dioid S) : A_selective_pre_dioid S :=
let eqv := A_selective_cancellative_pre_dioid_eqv _ pd in
let eqvP := A_eqv_proofs _ eqv in
let eq := A_eqv_eq _ eqv in 
let wS := A_eqv_witness _ eqv in 
let f := A_eqv_new _ eqv in
let nt := A_eqv_not_trivial _ eqv in
let timesP := A_selective_cancellative_pre_dioid_times_proofs _ pd in
let times := A_selective_cancellative_pre_dioid_times _ pd in
let id_ann_P := A_selective_cancellative_pre_dioid_id_ann_proofs _ pd in
let id_ann_times_plus_P := A_id_ann_times_plus_d _ _ _ _ id_ann_P in 
let id_d := extract_exists_id_decidable_from_exists_id_ann_decidable _ _ _ _ id_ann_times_plus_P in 
{|
  A_selective_pre_dioid_eqv           := eqv 
; A_selective_pre_dioid_plus          := A_selective_cancellative_pre_dioid_plus _ pd 
; A_selective_pre_dioid_times         := times 
; A_selective_pre_dioid_plus_proofs   := A_selective_cancellative_pre_dioid_plus_proofs _ pd 
; A_selective_pre_dioid_times_proofs  := A_msg_proofs_from_sg_CK_proofs S eq times wS f nt eqvP id_d timesP                                               
; A_selective_pre_dioid_id_ann_proofs := id_ann_P 
; A_selective_pre_dioid_proofs        := A_selective_cancellative_pre_dioid_proofs _ pd 
; A_selective_pre_dioid_ast           := A_selective_cancellative_pre_dioid_ast _ pd 
|}.                                                                                                      

(* 17 *)
Definition A_selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero
           (S: Type) (pd :A_selective_cancellative_pre_dioid_with_zero S) : A_selective_pre_dioid_with_zero S := 
let eqv := A_selective_cancellative_pre_dioid_with_zero_eqv _ pd in
let eqvP := A_eqv_proofs _ eqv in
let eq := A_eqv_eq _ eqv in 
let wS := A_eqv_witness _ eqv in 
let f := A_eqv_new _ eqv in
let nt := A_eqv_not_trivial _ eqv in
let timesP := A_selective_cancellative_pre_dioid_with_zero_times_proofs _ pd in
let times := A_selective_cancellative_pre_dioid_with_zero_times _ pd in
let id_ann_P := A_selective_cancellative_pre_dioid_with_zero_id_ann_proofs _ pd in
let id_ann_times_plus_P := A_pid_is_tann_times_plus_d _ _ _ _ id_ann_P in 
let id_d := extract_exists_id_decidable_from_exists_id_ann_decidable _ _ _ _ id_ann_times_plus_P in 
{|
  A_selective_pre_dioid_with_zero_eqv           := eqv 
; A_selective_pre_dioid_with_zero_plus          := A_selective_cancellative_pre_dioid_with_zero_plus _ pd 
; A_selective_pre_dioid_with_zero_times         := times 
; A_selective_pre_dioid_with_zero_plus_proofs   := A_selective_cancellative_pre_dioid_with_zero_plus_proofs _ pd 
; A_selective_pre_dioid_with_zero_times_proofs  := A_msg_proofs_from_sg_CK_proofs S eq times wS f nt eqvP id_d timesP
; A_selective_pre_dioid_with_zero_id_ann_proofs := id_ann_P 
; A_selective_pre_dioid_with_zero_proofs        := A_selective_cancellative_pre_dioid_with_zero_proofs _ pd 
; A_selective_pre_dioid_with_zero_ast           := A_selective_cancellative_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 18 *)

Definition A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one
           (S: Type) (pd :A_selective_cancellative_pre_dioid_with_one S) : A_selective_pre_dioid_with_one S := 
let eqv := A_selective_cancellative_pre_dioid_with_one_eqv _ pd in
let eqvP := A_eqv_proofs _ eqv in
let eq := A_eqv_eq _ eqv in 
let wS := A_eqv_witness _ eqv in 
let f := A_eqv_new _ eqv in
let nt := A_eqv_not_trivial _ eqv in
let timesP := A_selective_cancellative_pre_dioid_with_one_times_proofs _ pd in
let times := A_selective_cancellative_pre_dioid_with_one_times _ pd in
let id_ann_P := A_selective_cancellative_pre_dioid_with_one_id_ann_proofs _ pd in
let id_ann_times_plus_P := A_pann_is_tid_times_plus _ _ _ _ id_ann_P in 
let id_d := inl (extract_exist_id_from_exists_id_ann_equal _ _ _ _ id_ann_times_plus_P) in 
{|
  A_selective_pre_dioid_with_one_eqv           := eqv 
; A_selective_pre_dioid_with_one_plus          := A_selective_cancellative_pre_dioid_with_one_plus _ pd 
; A_selective_pre_dioid_with_one_times         := times 
; A_selective_pre_dioid_with_one_plus_proofs   := A_selective_cancellative_pre_dioid_with_one_plus_proofs _ pd 
; A_selective_pre_dioid_with_one_times_proofs  := A_msg_proofs_from_sg_CK_proofs S eq times wS f nt eqvP id_d timesP
; A_selective_pre_dioid_with_one_id_ann_proofs := id_ann_P 
; A_selective_pre_dioid_with_one_proofs        := A_selective_cancellative_pre_dioid_with_one_proofs _ pd 
; A_selective_pre_dioid_with_one_ast           := A_selective_cancellative_pre_dioid_with_one_ast _ pd 
|}.                                                                                                      

(* 19 *)                                                    
Definition A_selective_cancellative_pre_dioid_from_selective_cancellative_pre_dioid_with_zero
             (S: Type) (pd :A_selective_cancellative_pre_dioid_with_zero S) : A_selective_cancellative_pre_dioid S := 
{|
  A_selective_cancellative_pre_dioid_eqv           := A_selective_cancellative_pre_dioid_with_zero_eqv _ pd 
; A_selective_cancellative_pre_dioid_plus          := A_selective_cancellative_pre_dioid_with_zero_plus _ pd 
; A_selective_cancellative_pre_dioid_times         := A_selective_cancellative_pre_dioid_with_zero_times _ pd 
; A_selective_cancellative_pre_dioid_plus_proofs   := A_selective_cancellative_pre_dioid_with_zero_plus_proofs _ pd 
; A_selective_cancellative_pre_dioid_times_proofs  := A_selective_cancellative_pre_dioid_with_zero_times_proofs _ pd 
; A_selective_cancellative_pre_dioid_id_ann_proofs := id_ann_proofs_from_pid_is_tann_proofs _ _ _ _ (A_selective_cancellative_pre_dioid_with_zero_id_ann_proofs _ pd)
; A_selective_cancellative_pre_dioid_proofs        := A_selective_cancellative_pre_dioid_with_zero_proofs _ pd 
; A_selective_cancellative_pre_dioid_ast           := A_selective_cancellative_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 20 *)                                                    
Definition A_selective_cancellative_pre_dioid_from_selective_cancellative_pre_dioid_with_one
           (S: Type) (pd : A_selective_cancellative_pre_dioid_with_one S) : A_selective_cancellative_pre_dioid S := 
{|
  A_selective_cancellative_pre_dioid_eqv           := A_selective_cancellative_pre_dioid_with_one_eqv _ pd 
; A_selective_cancellative_pre_dioid_plus          := A_selective_cancellative_pre_dioid_with_one_plus _ pd 
; A_selective_cancellative_pre_dioid_times         := A_selective_cancellative_pre_dioid_with_one_times _ pd 
; A_selective_cancellative_pre_dioid_plus_proofs   := A_selective_cancellative_pre_dioid_with_one_plus_proofs _ pd 
; A_selective_cancellative_pre_dioid_times_proofs  := A_selective_cancellative_pre_dioid_with_one_times_proofs _ pd 
; A_selective_cancellative_pre_dioid_id_ann_proofs := id_ann_proofs_from_pann_is_tid_proofs _ _ _ _ (A_selective_cancellative_pre_dioid_with_one_id_ann_proofs _ pd)
; A_selective_cancellative_pre_dioid_proofs        := A_selective_cancellative_pre_dioid_with_one_proofs _ pd 
; A_selective_cancellative_pre_dioid_ast           := A_selective_cancellative_pre_dioid_with_one_ast _ pd 
|}.

(* 21 *)                                                    
Definition A_selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid
           (S: Type) (pd :A_selective_cancellative_dioid S) : A_selective_cancellative_pre_dioid_with_zero S := 
{|
  A_selective_cancellative_pre_dioid_with_zero_eqv           := A_selective_cancellative_dioid_eqv _ pd 
; A_selective_cancellative_pre_dioid_with_zero_plus          := A_selective_cancellative_dioid_plus _ pd 
; A_selective_cancellative_pre_dioid_with_zero_times         := A_selective_cancellative_dioid_times _ pd 
; A_selective_cancellative_pre_dioid_with_zero_plus_proofs   := A_selective_cancellative_dioid_plus_proofs _ pd 
; A_selective_cancellative_pre_dioid_with_zero_times_proofs  := A_selective_cancellative_dioid_times_proofs _ pd 
; A_selective_cancellative_pre_dioid_with_zero_id_ann_proofs := pid_is_tann_proofs_from_dually_bounded_proofs _ _ _ _
                                                                  (A_selective_cancellative_dioid_id_ann_proofs _ pd)
; A_selective_cancellative_pre_dioid_with_zero_proofs        := A_selective_cancellative_dioid_proofs _ pd 
; A_selective_cancellative_pre_dioid_with_zero_ast           := A_selective_cancellative_dioid_ast _ pd 
|}.                                                                                                      


(* 22 *)                                                    
Definition A_selective_cancellative_pre_dioid_with_one_from_selective_cancellative_dioid (S: Type) (pd :A_selective_cancellative_dioid S) : A_selective_cancellative_pre_dioid_with_one S := 
{|
  A_selective_cancellative_pre_dioid_with_one_eqv           := A_selective_cancellative_dioid_eqv _ pd 
; A_selective_cancellative_pre_dioid_with_one_plus          := A_selective_cancellative_dioid_plus _ pd 
; A_selective_cancellative_pre_dioid_with_one_times         := A_selective_cancellative_dioid_times _ pd 
; A_selective_cancellative_pre_dioid_with_one_plus_proofs   := A_selective_cancellative_dioid_plus_proofs _ pd 
; A_selective_cancellative_pre_dioid_with_one_times_proofs  := A_selective_cancellative_dioid_times_proofs _ pd 
; A_selective_cancellative_pre_dioid_with_one_id_ann_proofs := pann_is_tid_proofs_from_dually_bounded_proofs _ _ _ _ (A_selective_cancellative_dioid_id_ann_proofs _ pd)
; A_selective_cancellative_pre_dioid_with_one_proofs        := A_selective_cancellative_dioid_proofs _ pd 
; A_selective_cancellative_pre_dioid_with_one_ast           := A_selective_cancellative_dioid_ast _ pd 
|}.


(* 23 *)
Definition A_selective_pre_dioid_with_zero_from_selective_distributive_prelattice_with_zero
           (S: Type) (dS : A_selective_distributive_prelattice_with_zero S) : A_selective_pre_dioid_with_zero S :=
let eqv   := A_selective_distributive_prelattice_with_zero_eqv _ dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let wS := A_eqv_witness _ eqv in 
let f := A_eqv_new _ eqv in
let nt := A_eqv_not_trivial _ eqv in
let plus  := A_selective_distributive_prelattice_with_zero_join S dS in
let plusP := A_selective_distributive_prelattice_with_zero_join_proofs S dS in
let times := A_selective_distributive_prelattice_with_zero_meet S dS in
let timesP:= A_selective_distributive_prelattice_with_zero_meet_proofs S dS in
let dPS   := A_selective_distributive_prelattice_with_zero_proofs S dS in
let cong_plus  := A_sg_CS_congruence S eq plus plusP in   
let comm_plus  := A_sg_CS_commutative S eq plus plusP in
let comm_times := A_sg_CS_commutative S eq times timesP in   
{|
  A_selective_pre_dioid_with_zero_eqv           := eqv 
; A_selective_pre_dioid_with_zero_plus          := plus 
; A_selective_pre_dioid_with_zero_times         := times 
; A_selective_pre_dioid_with_zero_plus_proofs   := plusP 
; A_selective_pre_dioid_with_zero_times_proofs  := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CS_proofs S eq times wS f nt eqvP timesP)
; A_selective_pre_dioid_with_zero_id_ann_proofs := A_selective_distributive_prelattice_with_zero_id_ann_proofs _ dS
; A_selective_pre_dioid_with_zero_proofs        := dioid_proofs_from_distributive_lattice_proofs S eq plus times eqvP cong_plus comm_plus comm_times dPS 
; A_selective_pre_dioid_with_zero_ast           := A_selective_distributive_prelattice_with_zero_ast _ dS 
|}.                                                                                                      


(* 24 *)
Definition A_selective_pre_dioid_with_one_from_selective_distributive_prelattice_with_one
           (S: Type) (dS : A_selective_distributive_prelattice_with_one S) : A_selective_pre_dioid_with_one S :=
let eqv   := A_selective_distributive_prelattice_with_one_eqv _ dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let wS := A_eqv_witness _ eqv in 
let f := A_eqv_new _ eqv in
let nt := A_eqv_not_trivial _ eqv in
let plus  := A_selective_distributive_prelattice_with_one_join S dS in
let plusP := A_selective_distributive_prelattice_with_one_join_proofs S dS in
let times := A_selective_distributive_prelattice_with_one_meet S dS in
let timesP:= A_selective_distributive_prelattice_with_one_meet_proofs S dS in
let dPS   := A_selective_distributive_prelattice_with_one_proofs S dS in
let cong_plus  := A_sg_CS_congruence S eq plus plusP in   
let comm_plus  := A_sg_CS_commutative S eq plus plusP in
let comm_times := A_sg_CS_commutative S eq times timesP in   
{|
  A_selective_pre_dioid_with_one_eqv           := eqv 
; A_selective_pre_dioid_with_one_plus          := plus 
; A_selective_pre_dioid_with_one_times         := times 
; A_selective_pre_dioid_with_one_plus_proofs   := plusP 
; A_selective_pre_dioid_with_one_times_proofs  := A_msg_proofs_from_sg_proofs S eq times (A_sg_proofs_from_sg_CS_proofs S eq times wS f nt eqvP timesP)
; A_selective_pre_dioid_with_one_id_ann_proofs := A_selective_distributive_prelattice_with_one_id_ann_proofs _ dS
; A_selective_pre_dioid_with_one_proofs        := dioid_proofs_from_distributive_lattice_proofs S eq plus times eqvP cong_plus comm_plus comm_times dPS 
; A_selective_pre_dioid_with_one_ast           := A_selective_distributive_prelattice_with_one_ast _ dS 
|}.                                                                                                      



(* Derived *) 

(* two hops *)

(* 1, 2 *) 
Definition A_bs_from_selective_presemiring (S: Type) (pd : A_selective_presemiring S) : A_bs S := 
  A_bs_from_bs_CS S (A_bs_CS_from_selective_presemiring S pd).

(* 2, 3 *) 
Definition A_bs_CS_from_selective_semiring (S: Type) (sr : A_selective_semiring S) : A_bs_CS S := 
  A_bs_CS_from_selective_presemiring S (A_selective_presemiring_from_selective_semiring S sr).

(* 2, 5 *)
Definition A_bs_CS_from_selective_pre_dioid (S: Type) (sr : A_selective_pre_dioid S) : A_bs_CS S := 
  A_bs_CS_from_selective_presemiring S (A_selective_presemiring_from_selective_pre_dioid S sr).

(* 3, 4 (could also be 5,6) *)
Definition A_selective_presemiring_from_selective_pre_dioid_with_zero
           (S: Type) (pd : A_selective_pre_dioid_with_zero S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_semiring S (A_selective_semiring_from_selective_pre_dioid_with_zero S pd).

(* 4, 8 *)
Definition A_selective_semiring_from_selective_dioid
           (S: Type) (pd : A_selective_dioid S) : A_selective_semiring S := 
  A_selective_semiring_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_dioid S pd).

(* 5, 10 *) 
Definition A_selective_presemiring_from_selective_distributive_prelattice
           (S: Type) (l : A_selective_distributive_prelattice S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_distributive_prelattice S l). 

(* 5, 7 *) 
Definition A_selective_presemiring_from_selective_pre_dioid_with_one
           (S: Type) (pd : A_selective_pre_dioid_with_one S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_pre_dioid_with_one S pd).

(* 5, 16 *)
Definition A_selective_presemiring_from_selective_cancellative_pre_dioid
           (S: Type) (pd : A_selective_cancellative_pre_dioid S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_cancellative_pre_dioid S pd).

(* 6,8 (could be 7,9 as well) *) 
Definition A_selective_pre_dioid_from_selective_dioid (S: Type) (d : A_selective_dioid S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_dioid S d).

(* 6, 17 (or 16,19)*)
Definition A_selective_pre_dioid_from_selective_cancellative_pre_dioid_with_zero
           (S: Type) (d : A_selective_cancellative_pre_dioid_with_zero S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_pre_dioid_with_zero S
           (A_selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero S d).

(* 7, 18*)
Definition A_selective_pre_dioid_from_selective_cancellative_dioid_with_one
           (S: Type) (d : A_selective_cancellative_pre_dioid_with_one S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_pre_dioid_with_one S
           (A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one S d).

(* 8, 11 *) 
Definition A_selective_pre_dioid_with_zero_from_selective_distributive_lattice
           (S: Type) (dl : A_selective_distributive_lattice S) : A_selective_pre_dioid_with_zero S := 
  A_selective_pre_dioid_with_zero_from_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S dl). 

(* 9, 11 *) 
Definition A_selective_pre_dioid_with_one_from_selective_distributive_lattice (S: Type)
           (dl : A_selective_distributive_lattice S) : A_selective_pre_dioid_with_one S := 
  A_selective_pre_dioid_with_one_from_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S dl). 


(* 10, 12 *) 
Definition A_selective_pre_dioid_from_selective_distributive_prelattice_with_zero
           (S: Type) (d : A_selective_distributive_prelattice_with_zero S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_distributive_prelattice S
      (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S d).

(* 10, 13 *) 
Definition A_selective_pre_dioid_from_selective_distributive_prelattice_with_one
           (S: Type) (d : A_selective_distributive_prelattice_with_one S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_distributive_prelattice S
      (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_one S d).

(* 12, 14 (could be 13,15 as well) *) 
Definition A_selective_distributive_prelattice_from_selective_distributive_lattice
           (S: Type) (dl : A_selective_distributive_lattice S) : A_selective_distributive_prelattice S :=
  A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S 
      (A_selective_distributive_prelattice_with_zero_from_selective_distributive_lattice S dl).

(* 17, 21 *)
Definition A_selective_pre_dioid_with_zero_from_selective_cancellative_dioid
           (S: Type) (dl : A_selective_cancellative_dioid S) : A_selective_pre_dioid_with_zero S :=
  A_selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero _ 
     (A_selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid _ dl). 

(* 18, 22 *)
Definition A_selective_pre_dioid_with_one_from_selective_cancellative_dioid
           (S: Type) (dl : A_selective_cancellative_dioid S) : A_selective_pre_dioid_with_one S :=
  A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one _ 
     (A_selective_cancellative_pre_dioid_with_one_from_selective_cancellative_dioid _ dl). 

(* 19, 21 (could be 20,22)*)
Definition A_selective_cancellative_pre_dioid_from_selective_cancellative_dioid
           (S: Type) (dl : A_selective_cancellative_dioid S) : A_selective_cancellative_pre_dioid S :=
  A_selective_cancellative_pre_dioid_from_selective_cancellative_pre_dioid_with_zero _ 
     (A_selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid _ dl). 

(* three hops *)

(* 1,2,3 *)
Definition A_bs_from_selective_semiring
           (S: Type) (pd : A_selective_semiring S) : A_bs S := 
  A_bs_from_selective_presemiring S (A_selective_presemiring_from_selective_semiring S pd).

(* 1,2,5 *)
Definition A_bs_from_selective_pre_dioid
           (S: Type) (pd : A_selective_pre_dioid S) : A_bs S := 
  A_bs_from_selective_presemiring S (A_selective_presemiring_from_selective_pre_dioid S pd).

(* 2,3,4 (or 2,5,6) *)
Definition A_bs_CS_from_selective_pre_dioid_with_zero
           (S: Type) (a : A_selective_pre_dioid_with_zero  S) : A_bs_CS S := 
  A_bs_CS_from_selective_semiring S (A_selective_semiring_from_selective_pre_dioid_with_zero S a).

(* 2,5,7 *)
Definition A_bs_CS_from_selective_pre_dioid_with_one 
           (S: Type) (a : A_selective_pre_dioid_with_one  S) : A_bs_CS S := 
  A_bs_CS_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_pre_dioid_with_one S a).

(* 2,5,10 *)
Definition A_bs_CS_from_selective_distributive_prelattice
           (S: Type) (a : A_selective_distributive_prelattice  S) : A_bs_CS S := 
  A_bs_CS_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_distributive_prelattice S a).

(* 3,4,8 (or 5,6,8 or 5,7,9) *)
Definition A_selective_presemiring_from_selective_dioid
           (S: Type) (a : A_selective_dioid  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_dioid S a).

(* 4,8,11 *)
Definition A_selective_semiring_from_selective_distributive_lattice
           (S: Type) (a : A_selective_distributive_lattice  S) : A_selective_semiring S := 
  A_selective_semiring_from_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S a).

(* 5,6,17 (or 5,16,19) *)
Definition A_selective_presemiring_from_selective_cancellative_pre_dioid_with_zero
           (S: Type) (a : A_selective_cancellative_pre_dioid_with_zero  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid_with_zero S
            (A_selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero S a).

(* 5,7,18 (or 5,16,20) *)
Definition A_selective_presemiring_from_selective_cancellative_pre_dioid_with_one
           (S: Type) (a : A_selective_cancellative_pre_dioid_with_one  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid_with_one S
         (A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one S a).

(* 5,10,12 *)
Definition A_selective_presemiring_from_selective_distributive_prelattice_with_zero
           (S: Type) (a : A_selective_distributive_prelattice_with_zero  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_distributive_prelattice S
        (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S a).

(* 5,10,12 *)
Definition A_selective_presemiring_from_selective_distributive_prelattice_with_one
           (S: Type) (a : A_selective_distributive_prelattice_with_one  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_distributive_prelattice S
        (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_one S a).

(* 6,8,11 (or 7,9,11 or 10,13,15 or 10,12,14) *)
Definition A_selective_pre_dioid_from_selective_distributive_lattice
           (S: Type) (a : A_selective_distributive_lattice  S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S a).

(* 6,17,21 (could be 7,18,22, or 16,20,22, or 16,19,21) *)
Definition A_selective_pre_dioid_from_selective_cancellative_dioid
           (S: Type) (a : A_selective_cancellative_dioid  S) : A_selective_pre_dioid S := 
  A_selective_pre_dioid_from_selective_cancellative_pre_dioid_with_zero S
       (A_selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid S a).


(* four hops *)

(* 1,2,3,4 (or 1,2,5,6) *)
Definition A_bs_from_selective_pre_dioid_with_zero
           (S: Type) (a : A_selective_pre_dioid_with_zero  S) : A_bs S := 
  A_bs_from_selective_semiring S (A_selective_semiring_from_selective_pre_dioid_with_zero S a).

(* 1,2,5,10 *)
Definition A_bs_from_selective_distributive_prelattice
           (S: Type) (a : A_selective_distributive_prelattice  S) : A_bs S := 
  A_bs_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_distributive_prelattice S a).

(* 1,2,5,7 *)
Definition A_bs_from_selective_pre_dioid_with_one
           (S: Type) (a : A_selective_pre_dioid_with_one  S) : A_bs S := 
  A_bs_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_pre_dioid_with_one S a).


(* 1,2,5,16 *)
Definition A_bs_from_selective_cancellative_pre_dioid
           (S: Type) (a : A_selective_cancellative_pre_dioid  S) : A_bs S := 
  A_bs_from_selective_pre_dioid S (A_selective_pre_dioid_from_selective_cancellative_pre_dioid S a).


(* 2,5,6,8 (or 2,3,4,8) *)
Definition A_bs_CS_from_selective_dioid
           (S: Type) (a : A_selective_dioid  S) : A_bs_CS S := 
  A_bs_CS_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_dioid S a).

(* 2,5,6,17 *)
Definition A_bs_CS_from_selective_cancellative_pre_dioid_with_zero
           (S: Type) (a : A_selective_cancellative_pre_dioid_with_zero  S) : A_bs_CS S := 
  A_bs_CS_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero S a).

(* 2,5,7,18 *)
Definition A_bs_CS_from_selective_cancellative_pre_dioid_with_one
           (S: Type) (a : A_selective_cancellative_pre_dioid_with_one  S) : A_bs_CS S := 
  A_bs_CS_from_selective_pre_dioid_with_one S (A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one S a).

(* 2,5,10,12 *)
Definition A_bs_CS_from_selective_distributive_prelattice_with_zero
           (S: Type) (a : A_selective_distributive_prelattice_with_zero  S) : A_bs_CS S := 
  A_bs_CS_from_selective_distributive_prelattice S (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S a).

(* 2,5,10,13 *)
Definition A_bs_CS_from_selective_distributive_prelattice_with_one
           (S: Type) (a : A_selective_distributive_prelattice_with_one  S) : A_bs_CS S := 
  A_bs_CS_from_selective_distributive_prelattice S (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_one S a).


(* 3,4,8,11 (or 5,6,8,11 or 5,7,9,11 or 5,10,12,14) *)
Definition A_selective_presemiring_from_selective_distributive_lattice 
           (S: Type) (a : A_selective_distributive_lattice  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_distributive_lattice S a).

(* 5,6,17,21 (or 5,7,18,22 or 5,16,19,21) *)
Definition A_selective_presemiring_from_selective_cancellative_dioid
           (S: Type) (a : A_selective_cancellative_dioid  S) : A_selective_presemiring S := 
  A_selective_presemiring_from_selective_cancellative_pre_dioid_with_zero S
     (A_selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid S a).

(* five hops *)

(* 1,2,3,4,8 (or 1,2,5,6,8) *)
Definition A_bs_from_selective_dioid
           (S: Type) (a : A_selective_dioid  S) : A_bs S := 
  A_bs_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_dioid S a).

(* 1,2,5,10,12 *)
Definition A_bs_from_selective_distributive_prelattice_with_zero
           (S: Type) (a : A_selective_distributive_prelattice_with_zero  S) : A_bs S := 
  A_bs_from_selective_distributive_prelattice S (A_selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S a).

Definition A_bs_from_selective_distributive_prelattice_with_one 
           (S: Type) (a : A_selective_distributive_prelattice_with_one  S) : A_bs S :=            
  A_bs_from_selective_pre_dioid_with_one S
       (A_selective_pre_dioid_with_one_from_selective_distributive_prelattice_with_one S a).


(* 1,2,5,7,18 *)
Definition A_bs_from_selective_cancellative_pre_dioid_with_one
           (S: Type) (a : A_selective_cancellative_pre_dioid_with_one  S) : A_bs S := 
  A_bs_from_selective_pre_dioid_with_one S (A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one S a).

(* 1,2,5,6,17 *)
Definition A_bs_from_selective_cancellative_pre_dioid_with_zero
           (S: Type) (a : A_selective_cancellative_pre_dioid_with_zero  S) : A_bs S := 
  A_bs_from_selective_pre_dioid_with_zero S (A_selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero S a).

(* 2,5,6,8,11 (or 2,5,10,12,14 or 2,3,4,8,11) *)
Definition A_bs_CS_from_selective_distributive_lattice
           (S: Type) (a : A_selective_distributive_lattice  S) : A_bs_CS S := 
  A_bs_CS_from_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S a).

(* 2,5,6,17,21 (or 2,5,7,18,22) *)
Definition A_bs_CS_from_selective_cancellative_dioid
           (S: Type) (a : A_selective_cancellative_dioid  S) : A_bs_CS S := 
  A_bs_CS_from_selective_cancellative_pre_dioid_with_zero S (A_selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid S a).


(* six hops *)

(* 1,2,3,4,8,11 (or 1,2,5,10,12,14)*)
Definition A_bs_from_selective_distributive_lattice
           (S: Type) (a : A_selective_distributive_lattice  S) : A_bs S := 
  A_bs_from_selective_dioid S (A_selective_dioid_from_selective_distributive_lattice S a).

(* 1,2,5,7,18,22 (or 1,2,5,6,17,21) *)
Definition A_bs_from_selective_cancellative_dioid
           (S: Type) (a : A_selective_cancellative_dioid  S) : A_bs S := 
  A_bs_from_selective_cancellative_pre_dioid_with_one S (A_selective_cancellative_pre_dioid_with_one_from_selective_cancellative_dioid S a).

End Combinators. 
End ACAS.


Section AMCAS.

Definition A_bs_from_mcas (S : Type) (A : A_bs_mcas S) := 
match A with   
| A_BS_Error _ _ => A 
| A_BS_bs _ _    => A
| A_BS_bs_CI _ B => A_BS_bs _ (A_bs_from_bs_CI _ B)
| A_BS_bs_CS _ B => A_BS_bs _ (A_bs_from_bs_CS _ B)
| A_BS_presemiring _ B => A_BS_bs _ (A_bs_from_presemiring _ B)
| A_BS_semiring _ B => A_BS_bs _ (A_bs_from_semiring _ B)
| A_BS_pre_dioid _ B => A_BS_bs _ (A_bs_from_pre_dioid _ B)
| A_BS_pre_dioid_with_one _ B => A_BS_bs _ (A_bs_from_pre_dioid_with_one _ B)
| A_BS_pre_dioid_with_zero _ B => A_BS_bs _ (A_bs_from_pre_dioid_with_zero _ B)
| A_BS_dioid _ B => A_BS_bs _ (A_bs_from_dioid _ B)
| A_BS_prelattice _ B => A_BS_bs _ (A_bs_from_prelattice _ B)
| A_BS_distributive_prelattice _ B => A_BS_bs _ (A_bs_from_distributive_prelattice _ B)
| A_BS_lattice _ B => A_BS_bs _ (A_bs_from_lattice _ B)                       
| A_BS_distributive_lattice _ B => A_BS_bs _ (A_bs_from_distributive_lattice _ B)
| A_BS_selective_presemiring  _ B => A_BS_bs _ (A_bs_from_selective_presemiring  _ B)
| A_BS_selective_semiring _ B => A_BS_bs _ (A_bs_from_selective_semiring _ B)
| A_BS_selective_pre_dioid _ B => A_BS_bs _ (A_bs_from_selective_pre_dioid _ B)
| A_BS_selective_pre_dioid_with_zero _ B => A_BS_bs _ (A_bs_from_selective_pre_dioid_with_zero _ B)                       
| A_BS_selective_pre_dioid_with_one _ B => A_BS_bs _ (A_bs_from_selective_pre_dioid_with_one _ B)
| A_BS_selective_dioid _ B => A_BS_bs _ (A_bs_from_selective_dioid _ B)
| A_BS_selective_cancellative_pre_dioid _ B => A_BS_bs _ (A_bs_from_selective_cancellative_pre_dioid _ B)
| A_BS_selective_cancellative_pre_dioid_with_zero _ B => A_BS_bs _ (A_bs_from_selective_cancellative_pre_dioid_with_zero _ B)
| A_BS_selective_cancellative_pre_dioid_with_one _ B => A_BS_bs _ (A_bs_from_selective_cancellative_pre_dioid_with_one _ B)                       
| A_BS_selective_cancellative_dioid  _ B => A_BS_bs _ (A_bs_from_selective_cancellative_dioid  _ B)
| A_BS_selective_distributive_prelattice _ B => A_BS_bs _ (A_bs_from_selective_distributive_prelattice _ B)
| A_BS_selective_distributive_prelattice_with_zero _ B => A_BS_bs _ (A_bs_from_selective_distributive_prelattice_with_zero _ B)
| A_BS_selective_distributive_prelattice_with_one _ B => A_BS_bs _ (A_bs_from_selective_distributive_prelattice_with_one _ B)
| A_BS_selective_distributive_lattice _ B => A_BS_bs _ (A_bs_from_selective_distributive_lattice _ B)                       
end.

End AMCAS.   

Section CAS.

Section Certificates.

 (* 1 *)
Definition id_ann_certs_from_pid_is_tann_certs {S : Type} (P : @pid_is_tann_certificates S) : @id_ann_certificates S := 
{|
  id_ann_plus_times_d := match pid_is_tann_plus_times P with Assert_Exists_Id_Ann_Equal a => Id_Ann_Cert_Equal a end
; id_ann_times_plus_d := pid_is_tann_times_plus_d P
|}.

(* 2 *)
Definition id_ann_certs_from_pann_is_tid_certs {S : Type} (P : @pann_is_tid_certificates S) : @id_ann_certificates S := 
{|
  id_ann_plus_times_d := pann_is_tid_plus_times_d P
; id_ann_times_plus_d := match pann_is_tid_times_plus P with Assert_Exists_Id_Ann_Equal a => Id_Ann_Cert_Equal a end 
|}.

(* 3 *)
Definition pid_is_tann_certs_from_dually_bounded_certs {S : Type} (P : @dually_bounded_certificates S) : @pid_is_tann_certificates S := 
{|
  pid_is_tann_plus_times   := bounded_plus_id_is_times_ann  P
; pid_is_tann_times_plus_d := match bounded_times_id_is_plus_ann P with Assert_Exists_Id_Ann_Equal a => Id_Ann_Cert_Equal a end
|}.

(* 4 *)
Definition pann_is_tid_certs_from_dually_bounded_certs {S : Type} (P : @dually_bounded_certificates S) : @pann_is_tid_certificates S := 
{|
  pann_is_tid_plus_times_d   := match bounded_plus_id_is_times_ann P with Assert_Exists_Id_Ann_Equal a => Id_Ann_Cert_Equal a end 
; pann_is_tid_times_plus     := bounded_times_id_is_plus_ann  P
|}.

(* Derived *) 
Definition id_ann_certs_from_dually_bounded_certs {S : Type} (P : @dually_bounded_certificates S) : @id_ann_certificates S := 
             id_ann_certs_from_pann_is_tid_certs (pann_is_tid_certs_from_dually_bounded_certs P). 

(* 1 *) 
Definition bs_certs_from_semiring_certs {S: Type} (sr : @semiring_certificates S) : @bs_certificates S := 
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

(* 2 *)
Definition semiring_certs_from_dioid_certs 
       {S : Type} (dlp : @dioid_certificates S) : @semiring_certificates S := 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
; semiring_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
|}.

(* 3 *)
Definition dioid_certs_from_distributive_lattice_certs
       {S : Type} (dlp : @distributive_lattice_certificates S) : @dioid_certificates S := 
{|
  dioid_left_distributive     := Assert_Left_Distributive 
; dioid_right_distributive    := Assert_Right_Distributive 
; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive 
; dioid_left_right_absorptive := Assert_Left_Right_Absorptive 
|}.

(* 4 *)  
Definition lattice_certs_from_distributive_lattice_certs
        {S : Type} (dP : @distributive_lattice_certificates S): @lattice_certificates S := 
   {|
      lattice_absorptive          := Assert_Left_Left_Absorptive 
    ; lattice_absorptive_dual     := Assert_Left_Left_Absorptive_Dual  
    ; lattice_distributive_d      := Certify_Left_Distributive
    ; lattice_distributive_dual_d := Certify_Left_Distributive_Dual 
   |}.


(* 5 *)  
Definition bs_certs_from_lattice_certs
           {S : Type} (lP : @lattice_certificates S) : @bs_certificates S :=
{|
   bs_left_distributive_d      := lattice_distributive_d lP 
 ; bs_right_distributive_d     := match lattice_distributive_d lP with
                                    | Certify_Left_Distributive => Certify_Right_Distributive
                                    | Certify_Not_Left_Distributive trip => Certify_Not_Right_Distributive trip
                                    end 
 ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
 ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
 ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive 
 ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive 
|}.

(* Derived *)

Definition bs_certs_from_dioid_certs 
           {S : Type} (di : @dioid_certificates S) : @bs_certificates S := 
  bs_certs_from_semiring_certs (semiring_certs_from_dioid_certs di).

Definition bs_certs_from_distributive_lattice_certs 
           {S : Type} (dP : @distributive_lattice_certificates S) : @bs_certificates S := 
  bs_certs_from_lattice_certs (lattice_certs_from_distributive_lattice_certs dP). 

Definition semiring_certs_from_distributive_lattice_certs
       {S : Type} (dlp : @distributive_lattice_certificates S) : @semiring_certificates S :=
          semiring_certs_from_dioid_certs (dioid_certs_from_distributive_lattice_certs dlp). 

End Certificates.       

Section Combinators.

(* 1 *) 
Definition bs_from_bs_CI {S : Type} (B : @bs_CI S) : @bs S := 
{| 
  bs_eqv          := bs_CI_eqv B
; bs_plus         := bs_CI_plus B
; bs_times        := bs_CI_times B
; bs_plus_certs   := asg_certs_from_sg_CI_certs S
                         (eqv_eq (bs_CI_eqv B))
                         (bs_CI_plus B)
                         (eqv_witness (bs_CI_eqv B))
                         (eqv_new (bs_CI_eqv B))
                         (bs_CI_plus_certs B)  
; bs_times_certs  := bs_CI_times_certs B
; bs_id_ann_certs := bs_CI_id_ann_certs B
; bs_certs        := bs_CI_certs B
; bs_ast          := Ast_bs_from_bs_CI (bs_CI_ast B)
|}. 

(* 2 *)
Definition bs_from_presemiring {S : Type} (s: @presemiring S) : @bs S := 
{| 
  bs_eqv          := presemiring_eqv s
; bs_plus         := presemiring_plus s 
; bs_times        := presemiring_times s
; bs_plus_certs   := asg_certs_from_sg_C_certs S (presemiring_plus_certs s)
; bs_times_certs  := presemiring_times_certs s
; bs_id_ann_certs := presemiring_id_ann_certs s
; bs_certs        := bs_certs_from_semiring_certs (presemiring_certs s)
; bs_ast          := Ast_bs_from_presemiring (presemiring_ast s)
|}.

(* 3 *) 
Definition presemiring_from_semiring {S : Type} (dS : @semiring S) : @presemiring S := 
{|
  presemiring_eqv           := semiring_eqv dS 
; presemiring_plus          := semiring_plus dS 
; presemiring_times         := semiring_times dS 
; presemiring_plus_certs   := semiring_plus_certs dS 
; presemiring_times_certs  := semiring_times_certs dS 
; presemiring_id_ann_certs := id_ann_certs_from_pid_is_tann_certs (semiring_id_ann_certs dS)
; presemiring_certs        := semiring_certs dS 
; presemiring_ast          := Ast_presemiring_from_semiring(semiring_ast dS)
|}.

(* 4 *) 
Definition semiring_from_pre_dioid_with_zero {S : Type} (dS : @pre_dioid_with_zero S) : @semiring S := 
let eqv := pre_dioid_with_zero_eqv dS  in
let eq := eqv_eq eqv in
let plus := pre_dioid_with_zero_plus dS  in 
{|
  semiring_eqv          := eqv 
; semiring_plus         := plus 
; semiring_times        := pre_dioid_with_zero_times dS 
; semiring_plus_certs   := sg_C_certs_from_sg_CI_certs S eq plus (eqv_witness eqv) (eqv_new eqv) (pre_dioid_with_zero_plus_certs dS)
; semiring_times_certs  := pre_dioid_with_zero_times_certs dS
; semiring_id_ann_certs := pre_dioid_with_zero_id_ann_certs dS                                                  
; semiring_certs        := semiring_certs_from_dioid_certs (pre_dioid_with_zero_certs dS)
; semiring_ast          := Ast_semiring_from_dioid (pre_dioid_with_zero_ast dS)
|}.  


(* 5 *)

Definition bs_CI_from_prelattice {S : Type} (lP : @prelattice S) : @bs_CI S := 
  let eqv  := prelattice_eqv lP  in               
  let eq   := eqv_eq eqv      in 
  let wS   := eqv_witness eqv in 
  let f    := eqv_new eqv     in
  let meet := prelattice_meet lP in
  {|
     bs_CI_eqv          := eqv 
   ; bs_CI_plus         := prelattice_join lP 
   ; bs_CI_times        := meet 
   ; bs_CI_plus_certs   := prelattice_join_certs lP
   ; bs_CI_times_certs  := msg_certs_from_sg_certs S (sg_certs_from_sg_CI_certs S eq meet wS f (prelattice_meet_certs lP))
   ; bs_CI_id_ann_certs := prelattice_id_ann_certs lP
   ; bs_CI_certs        := bs_certs_from_lattice_certs (prelattice_certs lP) 
   ; bs_CI_ast          := Ast_bs_CI_from_lattice (prelattice_ast lP)
  |}.


(* 6 *) 
Definition lattice_from_distributive_lattice {S : Type} (dS : @distributive_lattice S) : @lattice S := 
{|
      lattice_eqv          := distributive_lattice_eqv dS 
    ; lattice_join         := distributive_lattice_join dS 
    ; lattice_meet         := distributive_lattice_meet dS
    ; lattice_join_certs   := distributive_lattice_join_certs dS 
    ; lattice_meet_certs   := distributive_lattice_meet_certs dS
    ; lattice_id_ann_certs := distributive_lattice_id_ann_certs dS 
    ; lattice_certs        := lattice_certs_from_distributive_lattice_certs (distributive_lattice_certs dS)
    ; lattice_ast          := Ast_lattice_from_distributive_lattice (distributive_lattice_ast dS)
|}.

(* 7 *) 
Definition bs_CI_from_pre_dioid {S : Type} (lP : @pre_dioid S) : @bs_CI S := 
  {|
     bs_CI_eqv          := pre_dioid_eqv lP  
   ; bs_CI_plus         := pre_dioid_plus lP
   ; bs_CI_times        := pre_dioid_times lP 
   ; bs_CI_plus_certs   := pre_dioid_plus_certs lP
   ; bs_CI_times_certs  := pre_dioid_times_certs lP 
   ; bs_CI_id_ann_certs := pre_dioid_id_ann_certs lP
   ; bs_CI_certs        := bs_certs_from_dioid_certs (pre_dioid_certs lP) 
   ; bs_CI_ast          := Ast_bs_CI_from_lattice (pre_dioid_ast lP)
  |}.

(* 8 *) 
Definition pre_dioid_from_pre_dioid_with_zero {S : Type} (pd : @pre_dioid_with_zero S) : @pre_dioid S := 
{|
  pre_dioid_eqv           := pre_dioid_with_zero_eqv pd 
; pre_dioid_plus          := pre_dioid_with_zero_plus pd 
; pre_dioid_times         := pre_dioid_with_zero_times pd 
; pre_dioid_plus_certs   := pre_dioid_with_zero_plus_certs pd 
; pre_dioid_times_certs  := pre_dioid_with_zero_times_certs pd 
; pre_dioid_id_ann_certs := id_ann_certs_from_pid_is_tann_certs (pre_dioid_with_zero_id_ann_certs pd)
; pre_dioid_certs        := pre_dioid_with_zero_certs pd 
; pre_dioid_ast           := pre_dioid_with_zero_ast pd 
|}.                                                                                                      

(* 9 *) 
Definition pre_dioid_from_pre_dioid_with_one {S : Type} (pd : @pre_dioid_with_one S) : @pre_dioid S := 
{|
  pre_dioid_eqv           := pre_dioid_with_one_eqv pd 
; pre_dioid_plus          := pre_dioid_with_one_plus pd 
; pre_dioid_times         := pre_dioid_with_one_times pd 
; pre_dioid_plus_certs   := pre_dioid_with_one_plus_certs pd 
; pre_dioid_times_certs  := pre_dioid_with_one_times_certs pd 
; pre_dioid_id_ann_certs := id_ann_certs_from_pann_is_tid_certs (pre_dioid_with_one_id_ann_certs pd)
; pre_dioid_certs        := pre_dioid_with_one_certs pd 
; pre_dioid_ast           := pre_dioid_with_one_ast pd 
|}.                                                                                                      

(* 10 *) 
Definition pre_dioid_with_zero_from_dioid {S : Type} (pd : @dioid S) : @pre_dioid_with_zero S := 
{|
  pre_dioid_with_zero_eqv           := dioid_eqv S pd 
; pre_dioid_with_zero_plus          := dioid_plus S pd 
; pre_dioid_with_zero_times         := dioid_times S pd 
; pre_dioid_with_zero_plus_certs   := dioid_plus_certs S pd 
; pre_dioid_with_zero_times_certs  := dioid_times_certs S pd 
; pre_dioid_with_zero_id_ann_certs := pid_is_tann_certs_from_dually_bounded_certs (dioid_id_ann_certs S pd)
; pre_dioid_with_zero_certs        := dioid_certs S pd 
; pre_dioid_with_zero_ast           := dioid_ast S pd 
|}.                                                                                                      

(* 11 *) 
Definition pre_dioid_with_one_from_dioid {S : Type} (pd :dioid S) : @pre_dioid_with_one S := 
{|
  pre_dioid_with_one_eqv           := dioid_eqv _ pd 
; pre_dioid_with_one_plus          := dioid_plus _ pd 
; pre_dioid_with_one_times         := dioid_times _ pd 
; pre_dioid_with_one_plus_certs   := dioid_plus_certs _ pd 
; pre_dioid_with_one_times_certs  := dioid_times_certs _ pd 
; pre_dioid_with_one_id_ann_certs := pann_is_tid_certs_from_dually_bounded_certs (dioid_id_ann_certs _ pd)
; pre_dioid_with_one_certs        := dioid_certs _ pd 
; pre_dioid_with_one_ast           := dioid_ast _ pd 
|}.                                                                                                      


(* 12 *)
Definition dioid_from_distributive_lattice {S : Type} (dS : @distributive_lattice S) : @dioid S := 
let eqv   := distributive_lattice_eqv dS in
let eq    := eqv_eq eqv in
let times := distributive_lattice_meet dS in
let timesP:= distributive_lattice_meet_certs dS in
let w     := eqv_witness eqv in
let f     := eqv_new eqv in
{|
  dioid_eqv          := eqv 
; dioid_plus         := distributive_lattice_join dS
; dioid_times        := times 
; dioid_plus_certs   := distributive_lattice_join_certs dS
; dioid_times_certs  := msg_certs_from_sg_certs S (sg_certs_from_sg_CI_certs S eq times w f timesP)
; dioid_id_ann_certs := distributive_lattice_id_ann_certs dS 
; dioid_certs        := dioid_certs_from_distributive_lattice_certs (distributive_lattice_certs dS)
; dioid_ast          := Ast_dioid_from_distributive_lattice (distributive_lattice_ast dS)
|}.


(* 13 *) 
Definition prelattice_from_distributive_prelattice {S: Type} (dS : @distributive_prelattice S) : @prelattice S := 
let eqv   := distributive_prelattice_eqv dS in
let eqvP  := eqv_certs eqv in
let eq    := eqv_eq eqv in
let join  := distributive_prelattice_join dS in
let joinP := distributive_prelattice_join_certs dS in
let meet  := distributive_prelattice_meet dS in
let meetP := distributive_prelattice_meet_certs dS in
let dPS   := distributive_prelattice_certs dS in 
{|
      prelattice_eqv           := eqv 
    ; prelattice_join          := join 
    ; prelattice_meet          := meet
    ; prelattice_join_certs   := joinP 
    ; prelattice_meet_certs   := meetP
    ; prelattice_id_ann_certs := distributive_prelattice_id_ann_certs dS 
    ; prelattice_certs        := lattice_certs_from_distributive_lattice_certs dPS
    ; prelattice_ast           := Ast_lattice_from_distributive_lattice (distributive_prelattice_ast dS)
|}.


(* 14 *) 
Definition distributive_prelattice_from_distributive_lattice {S: Type} (dS : @distributive_lattice S) : @distributive_prelattice S := 
let eqv   := distributive_lattice_eqv dS in
let eqvP  := eqv_certs eqv in
let eq    := eqv_eq eqv in
let join  := distributive_lattice_join dS in
let joinP := distributive_lattice_join_certs dS in
let meet  := distributive_lattice_meet dS in
let meetP := distributive_lattice_meet_certs dS in
{|
      distributive_prelattice_eqv           := eqv 
    ; distributive_prelattice_join          := join 
    ; distributive_prelattice_meet          := meet
    ; distributive_prelattice_join_certs   := joinP 
    ; distributive_prelattice_meet_certs   := meetP
    ; distributive_prelattice_id_ann_certs := id_ann_certs_from_dually_bounded_certs (distributive_lattice_id_ann_certs dS)
    ; distributive_prelattice_certs        := distributive_lattice_certs dS 
    ; distributive_prelattice_ast           := Ast_lattice_from_distributive_lattice (distributive_lattice_ast dS)
|}.

(* 15 *) 
Definition prelattice_from_lattice {S: Type} (dS : @lattice S) : @prelattice S := 
let eqv   := lattice_eqv dS in
let eqvP  := eqv_certs eqv in
let eq    := eqv_eq eqv in
let join  := lattice_join dS in
let joinP := lattice_join_certs dS in
let meet  := lattice_meet dS in
let meetP := lattice_meet_certs dS in
{|
      prelattice_eqv           := eqv 
    ; prelattice_join          := join 
    ; prelattice_meet          := meet
    ; prelattice_join_certs   := joinP 
    ; prelattice_meet_certs   := meetP
    ; prelattice_id_ann_certs := id_ann_certs_from_dually_bounded_certs (lattice_id_ann_certs dS)
    ; prelattice_certs        := lattice_certs dS
    ; prelattice_ast           := Ast_lattice_from_distributive_lattice (lattice_ast dS)
|}.


(* Derived *) 

(* two hops *) 
Definition bs_from_semiring {S : Type} (sr : @semiring S) : @bs S := 
  bs_from_presemiring (presemiring_from_semiring sr).

Definition bs_from_pre_dioid {S : Type} (pd : @pre_dioid S) : @bs S := 
  bs_from_bs_CI (bs_CI_from_pre_dioid pd).

Definition bs_from_prelattice {S: Type} (l : @prelattice S) : @bs S := 
  bs_from_bs_CI (bs_CI_from_prelattice l). 

Definition presemiring_from_pre_dioid_with_zero {S : Type} (pd : @pre_dioid_with_zero S) : @presemiring S := 
  presemiring_from_semiring (semiring_from_pre_dioid_with_zero pd).

Definition bs_CI_from_lattice {S: Type} (l : @lattice S) : @bs_CI S := 
  bs_CI_from_prelattice (prelattice_from_lattice l).

Definition bs_CI_from_distributive_prelattice {S : Type} (l : @distributive_prelattice S) : @bs_CI S := 
  bs_CI_from_prelattice (prelattice_from_distributive_prelattice l). 

Definition bs_CI_from_pre_dioid_with_zero {S : Type} (pd : @pre_dioid_with_zero S) : @bs_CI S := 
  bs_CI_from_pre_dioid (pre_dioid_from_pre_dioid_with_zero pd). 

Definition bs_CI_from_pre_dioid_with_one {S : Type} (pd : @pre_dioid_with_one S) : @bs_CI S := 
  bs_CI_from_pre_dioid (pre_dioid_from_pre_dioid_with_one pd). 

Definition pre_dioid_from_dioid {S : Type} (d : @dioid S) : @pre_dioid S := 
  pre_dioid_from_pre_dioid_with_zero  (pre_dioid_with_zero_from_dioid  d). 

Definition pre_dioid_with_zero_from_distributive_lattice {S : Type} (dl : @distributive_lattice S) : @pre_dioid_with_zero S := 
  pre_dioid_with_zero_from_dioid (dioid_from_distributive_lattice dl). 

Definition pre_dioid_with_one_from_distributive_lattice {S : Type} (dl : @distributive_lattice S) : @pre_dioid_with_one S := 
  pre_dioid_with_one_from_dioid (dioid_from_distributive_lattice dl). 

Definition prelattice_from_distributive_lattice {S: Type} (dl : @distributive_lattice S) : @prelattice S := 
  prelattice_from_distributive_prelattice (distributive_prelattice_from_distributive_lattice dl). 


(* three hops *)
Definition bs_from_pre_dioid_with_zero {S : Type} (pd : @pre_dioid_with_zero S) : @bs S := 
  bs_from_bs_CI  (bs_CI_from_pre_dioid_with_zero pd).

Definition bs_from_pre_dioid_with_one {S : Type} (pd : @pre_dioid_with_one S) : @bs S := 
  bs_from_bs_CI  (bs_CI_from_pre_dioid_with_one  pd).

Definition bs_from_distributive_prelattice {S : Type} (pd : @distributive_prelattice S) : @bs S := 
  bs_from_bs_CI  (bs_CI_from_distributive_prelattice  pd).

Definition bs_from_lattice {S: Type} (pd : @lattice S) : @bs S := 
  bs_from_bs_CI (bs_CI_from_lattice pd).

Definition bs_CI_from_dioid {S : Type} (pd : @dioid S) : @bs_CI S := 
  bs_CI_from_pre_dioid_with_zero  (pre_dioid_with_zero_from_dioid  pd).

Definition bs_CI_from_distributive_lattice {S: Type} (pd : @distributive_lattice S) : @bs_CI S := 
  bs_CI_from_prelattice (prelattice_from_distributive_lattice pd).

Definition pre_dioid_from_distributive_lattice {S : Type} (dl : @distributive_lattice S) : @pre_dioid S := 
  pre_dioid_from_pre_dioid_with_zero  (pre_dioid_with_zero_from_distributive_lattice  dl).

(* four hops *)
Definition bs_from_dioid {S : Type} (pd : @dioid S) : @bs S := 
  bs_from_bs_CI (bs_CI_from_dioid  pd).

Definition bs_from_distributive_lattice {S: Type} (pd : @distributive_lattice S) : @bs S := 
  bs_from_bs_CI (bs_CI_from_distributive_lattice pd).


(***************** Selective versions **********************)

(* 1 *) 
Definition bs_from_bs_CS {S : Type} (B : @bs_CS S) : @bs S :=
{| 
  bs_eqv          := bs_CS_eqv B
; bs_plus         := bs_CS_plus B
; bs_times        := bs_CS_times B
; bs_plus_certs  := asg_certs_from_sg_CS_certs S
                         (eqv_eq (bs_CS_eqv B))
                         (bs_CS_plus B)
                         (eqv_witness (bs_CS_eqv B))
                         (eqv_new (bs_CS_eqv B))
                         (bs_CS_plus_certs B)  
; bs_times_certs := bs_CS_times_certs B
; bs_id_ann_certs := bs_CS_id_ann_certs B
; bs_certs       := bs_CS_certs B
; bs_ast          := Ast_bs_from_bs_CI (bs_CS_ast B)
|}.

(* 2 *) 
Definition bs_CS_from_selective_presemiring {S : Type} (lP : @selective_presemiring S) : @ bs_CS S :=
  {|
     bs_CS_eqv          := selective_presemiring_eqv lP   
   ; bs_CS_plus         := selective_presemiring_plus lP    
   ; bs_CS_times        := selective_presemiring_times lP    
   ; bs_CS_plus_certs   := selective_presemiring_plus_certs lP 
   ; bs_CS_times_certs  := selective_presemiring_times_certs lP 
   ; bs_CS_id_ann_certs := selective_presemiring_id_ann_certs lP
   ; bs_CS_certs        := bs_certs_from_semiring_certs (selective_presemiring_certs lP) 
   ; bs_CS_ast          := Ast_bs_CI_from_lattice (selective_presemiring_ast lP)
  |}.

(* 3 *) 
Definition selective_presemiring_from_selective_semiring {S : Type} (dS : @selective_semiring S) : @selective_presemiring S := 
{|
  selective_presemiring_eqv          := selective_semiring_eqv dS 
; selective_presemiring_plus         := selective_semiring_plus dS 
; selective_presemiring_times        := selective_semiring_times dS   
; selective_presemiring_plus_certs   := selective_semiring_plus_certs dS 
; selective_presemiring_times_certs  := selective_semiring_times_certs dS 
; selective_presemiring_id_ann_certs := id_ann_certs_from_pid_is_tann_certs (selective_semiring_id_ann_certs dS)
; selective_presemiring_certs        := selective_semiring_certs dS 
; selective_presemiring_ast          := Ast_presemiring_from_semiring(selective_semiring_ast dS)
|}.

(* 4 *)
Definition selective_semiring_from_selective_pre_dioid_with_zero
           {S : Type} (dS : @selective_pre_dioid_with_zero S) : @selective_semiring S := 
{|
  selective_semiring_eqv          := selective_pre_dioid_with_zero_eqv S dS
; selective_semiring_plus         := selective_pre_dioid_with_zero_plus S dS 
; selective_semiring_times        := selective_pre_dioid_with_zero_times S dS 
; selective_semiring_plus_certs   := selective_pre_dioid_with_zero_plus_certs S dS
; selective_semiring_times_certs  := selective_pre_dioid_with_zero_times_certs S dS
; selective_semiring_id_ann_certs := selective_pre_dioid_with_zero_id_ann_certs S dS                                                  
; selective_semiring_certs        := semiring_certs_from_dioid_certs (selective_pre_dioid_with_zero_certs S dS)
; selective_semiring_ast          := Ast_semiring_from_dioid (selective_pre_dioid_with_zero_ast S dS)
|}.  

(* 5 *) 
Definition selective_presemiring_from_selective_pre_dioid {S : Type} (dS : @selective_pre_dioid S) : @selective_presemiring S := 
{|
  selective_presemiring_eqv          := selective_pre_dioid_eqv S dS 
; selective_presemiring_plus         := selective_pre_dioid_plus S dS
; selective_presemiring_times        := selective_pre_dioid_times S dS 
; selective_presemiring_plus_certs   := selective_pre_dioid_plus_certs S dS 
; selective_presemiring_times_certs  := selective_pre_dioid_times_certs S dS 
; selective_presemiring_id_ann_certs := selective_pre_dioid_id_ann_certs S dS
; selective_presemiring_certs        := semiring_certs_from_dioid_certs (selective_pre_dioid_certs S dS) 
; selective_presemiring_ast          := Ast_presemiring_from_semiring(selective_pre_dioid_ast S dS)
|}.

(* 6 *) 
Definition selective_pre_dioid_from_selective_pre_dioid_with_zero
           {S : Type} (pd : @selective_pre_dioid_with_zero S) : @selective_pre_dioid S := 
{|
  selective_pre_dioid_eqv           := selective_pre_dioid_with_zero_eqv _ pd 
; selective_pre_dioid_plus          := selective_pre_dioid_with_zero_plus _ pd 
; selective_pre_dioid_times         := selective_pre_dioid_with_zero_times _ pd 
; selective_pre_dioid_plus_certs   := selective_pre_dioid_with_zero_plus_certs _ pd 
; selective_pre_dioid_times_certs  := selective_pre_dioid_with_zero_times_certs _ pd 
; selective_pre_dioid_id_ann_certs := id_ann_certs_from_pid_is_tann_certs (selective_pre_dioid_with_zero_id_ann_certs _ pd)
; selective_pre_dioid_certs        := selective_pre_dioid_with_zero_certs _ pd 
; selective_pre_dioid_ast           := selective_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 7 *) 
Definition selective_pre_dioid_from_selective_pre_dioid_with_one
           {S : Type} (pd : @selective_pre_dioid_with_one S) : @selective_pre_dioid S := 
{|
  selective_pre_dioid_eqv           := selective_pre_dioid_with_one_eqv _ pd 
; selective_pre_dioid_plus          := selective_pre_dioid_with_one_plus _ pd 
; selective_pre_dioid_times         := selective_pre_dioid_with_one_times _ pd 
; selective_pre_dioid_plus_certs   := selective_pre_dioid_with_one_plus_certs _ pd 
; selective_pre_dioid_times_certs  := selective_pre_dioid_with_one_times_certs _ pd 
; selective_pre_dioid_id_ann_certs := id_ann_certs_from_pann_is_tid_certs (selective_pre_dioid_with_one_id_ann_certs _ pd)
; selective_pre_dioid_certs        := selective_pre_dioid_with_one_certs _ pd 
; selective_pre_dioid_ast           := selective_pre_dioid_with_one_ast _ pd 
|}.                                                                                                      

(* 8 *) 
Definition selective_pre_dioid_with_zero_from_selective_dioid
           {S : Type} (pd : @selective_dioid S) : @selective_pre_dioid_with_zero S := 
{|
  selective_pre_dioid_with_zero_eqv           := selective_dioid_eqv _ pd 
; selective_pre_dioid_with_zero_plus          := selective_dioid_plus _ pd 
; selective_pre_dioid_with_zero_times         := selective_dioid_times _ pd 
; selective_pre_dioid_with_zero_plus_certs   := selective_dioid_plus_certs _ pd 
; selective_pre_dioid_with_zero_times_certs  := selective_dioid_times_certs _ pd 
; selective_pre_dioid_with_zero_id_ann_certs := pid_is_tann_certs_from_dually_bounded_certs (selective_dioid_id_ann_certs _ pd)
; selective_pre_dioid_with_zero_certs        := selective_dioid_certs _ pd 
; selective_pre_dioid_with_zero_ast           := selective_dioid_ast _ pd 
|}.                                                                                                      


(* 9 *) 
Definition selective_pre_dioid_with_one_from_selective_dioid
           {S : Type} (pd : @selective_dioid S) : @selective_pre_dioid_with_one S := 
{|
  selective_pre_dioid_with_one_eqv           := selective_dioid_eqv _ pd 
; selective_pre_dioid_with_one_plus          := selective_dioid_plus _ pd 
; selective_pre_dioid_with_one_times         := selective_dioid_times _ pd 
; selective_pre_dioid_with_one_plus_certs   := selective_dioid_plus_certs _ pd 
; selective_pre_dioid_with_one_times_certs  := selective_dioid_times_certs _ pd 
; selective_pre_dioid_with_one_id_ann_certs := pann_is_tid_certs_from_dually_bounded_certs (selective_dioid_id_ann_certs _ pd)
; selective_pre_dioid_with_one_certs        := selective_dioid_certs _ pd 
; selective_pre_dioid_with_one_ast           := selective_dioid_ast _ pd 
|}.                                                                                                      


(* 10 *)
Definition selective_pre_dioid_from_selective_distributive_prelattice
           {S : Type}
           (dS : @selective_distributive_prelattice S) : @selective_pre_dioid S :=
let eqv   := selective_distributive_prelattice_eqv dS in
let eq    := eqv_eq eqv in
let w     := eqv_witness eqv in
let f     := eqv_new eqv in
let times := selective_distributive_prelattice_meet dS in
{|
  selective_pre_dioid_eqv          := eqv 
; selective_pre_dioid_plus         := selective_distributive_prelattice_join dS
; selective_pre_dioid_times        := times 
; selective_pre_dioid_plus_certs   := selective_distributive_prelattice_join_certs dS 
; selective_pre_dioid_times_certs  := msg_certs_from_sg_certs S (sg_certs_from_sg_CS_certs S eq times w f
                                               (selective_distributive_prelattice_meet_certs dS))
; selective_pre_dioid_id_ann_certs := selective_distributive_prelattice_id_ann_certs dS 
; selective_pre_dioid_certs        := dioid_certs_from_distributive_lattice_certs (selective_distributive_prelattice_certs dS)
; selective_pre_dioid_ast          := Ast_dioid_from_distributive_lattice (selective_distributive_prelattice_ast dS)
|}.

(* 11 *) 
Definition selective_dioid_from_selective_distributive_lattice {S : Type} (dS : @selective_distributive_lattice S) : @selective_dioid S := 
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
; selective_dioid_times_certs  := msg_certs_from_sg_certs S (sg_certs_from_sg_CS_certs S eq times w f timesP)
; selective_dioid_id_ann_certs := selective_distributive_lattice_id_ann_certs dS 
; selective_dioid_certs        := dioid_certs_from_distributive_lattice_certs dPS
; selective_dioid_ast          := Ast_dioid_from_distributive_lattice (selective_distributive_lattice_ast dS)
|}.


(* 12 *) 
Definition selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero
           (S : Type)
           (dS : @selective_distributive_prelattice_with_zero S) : @selective_distributive_prelattice S := 
{|
  selective_distributive_prelattice_eqv           := selective_distributive_prelattice_with_zero_eqv dS 
; selective_distributive_prelattice_join          := selective_distributive_prelattice_with_zero_join dS 
; selective_distributive_prelattice_meet          := selective_distributive_prelattice_with_zero_meet dS 
; selective_distributive_prelattice_join_certs   := selective_distributive_prelattice_with_zero_join_certs dS 
; selective_distributive_prelattice_meet_certs   := selective_distributive_prelattice_with_zero_meet_certs dS 
; selective_distributive_prelattice_id_ann_certs := id_ann_certs_from_pid_is_tann_certs (selective_distributive_prelattice_with_zero_id_ann_certs dS)
; selective_distributive_prelattice_certs        := selective_distributive_prelattice_with_zero_certs dS 
; selective_distributive_prelattice_ast           := selective_distributive_prelattice_with_zero_ast dS 
|}.

(* 13 *) 
Definition selective_distributive_prelattice_from_selective_distributive_prelattice_with_one 
           (S : Type)
           (dS : @selective_distributive_prelattice_with_one S) : @selective_distributive_prelattice S := 
{|
  selective_distributive_prelattice_eqv           := selective_distributive_prelattice_with_one_eqv dS 
; selective_distributive_prelattice_join          := selective_distributive_prelattice_with_one_join dS 
; selective_distributive_prelattice_meet          := selective_distributive_prelattice_with_one_meet dS 
; selective_distributive_prelattice_join_certs   := selective_distributive_prelattice_with_one_join_certs dS 
; selective_distributive_prelattice_meet_certs   := selective_distributive_prelattice_with_one_meet_certs dS 
; selective_distributive_prelattice_id_ann_certs := id_ann_certs_from_pann_is_tid_certs (selective_distributive_prelattice_with_one_id_ann_certs dS)
; selective_distributive_prelattice_certs        := selective_distributive_prelattice_with_one_certs dS 
; selective_distributive_prelattice_ast           := selective_distributive_prelattice_with_one_ast dS 
|}.

(* 14 *) 
Definition selective_distributive_prelattice_with_zero_from_selective_distributive_lattice
           (S : Type)
           (dS : @selective_distributive_lattice S) : @selective_distributive_prelattice_with_zero S := 
{|
  selective_distributive_prelattice_with_zero_eqv           := selective_distributive_lattice_eqv dS 
; selective_distributive_prelattice_with_zero_join          := selective_distributive_lattice_join dS 
; selective_distributive_prelattice_with_zero_meet          := selective_distributive_lattice_meet dS 
; selective_distributive_prelattice_with_zero_join_certs   := selective_distributive_lattice_join_certs dS 
; selective_distributive_prelattice_with_zero_meet_certs   := selective_distributive_lattice_meet_certs dS 
; selective_distributive_prelattice_with_zero_id_ann_certs := pid_is_tann_certs_from_dually_bounded_certs (selective_distributive_lattice_id_ann_certs dS)
; selective_distributive_prelattice_with_zero_certs        := selective_distributive_lattice_certs dS 
; selective_distributive_prelattice_with_zero_ast           := selective_distributive_lattice_ast dS 
|}.

(* 15 *) 
Definition selective_distributive_prelattice_with_one_from_selective_distributive_lattice
           (S : Type)
           (dS : @selective_distributive_lattice S) : @selective_distributive_prelattice_with_one S := 
{|
  selective_distributive_prelattice_with_one_eqv           := selective_distributive_lattice_eqv dS 
; selective_distributive_prelattice_with_one_join          := selective_distributive_lattice_join dS 
; selective_distributive_prelattice_with_one_meet          := selective_distributive_lattice_meet dS 
; selective_distributive_prelattice_with_one_join_certs   := selective_distributive_lattice_join_certs dS 
; selective_distributive_prelattice_with_one_meet_certs   := selective_distributive_lattice_meet_certs dS 
; selective_distributive_prelattice_with_one_id_ann_certs := pann_is_tid_certs_from_dually_bounded_certs (selective_distributive_lattice_id_ann_certs dS)
; selective_distributive_prelattice_with_one_certs        := selective_distributive_lattice_certs dS 
; selective_distributive_prelattice_with_one_ast           := selective_distributive_lattice_ast dS 
|}.


(* 16 *)
Definition selective_pre_dioid_from_selective_cancellative_pre_dioid {S : Type}
           (pd : @selective_cancellative_pre_dioid S) : @selective_pre_dioid S :=
let eqv := selective_cancellative_pre_dioid_eqv _ pd in
let eq := eqv_eq eqv in 
let wS := eqv_witness eqv in 
let f := eqv_new eqv in
let timesP := selective_cancellative_pre_dioid_times_certs _ pd in
let times := selective_cancellative_pre_dioid_times _ pd in
let id_ann_P := selective_cancellative_pre_dioid_id_ann_certs _ pd in
let id_ann_times_plus_P := id_ann_times_plus_d id_ann_P in 
let id_d := extract_exists_id_certifiable_from_exists_id_ann_certifiable id_ann_times_plus_P in 
{|
  selective_pre_dioid_eqv           := eqv 
; selective_pre_dioid_plus          := selective_cancellative_pre_dioid_plus _ pd 
; selective_pre_dioid_times         := times 
; selective_pre_dioid_plus_certs   := selective_cancellative_pre_dioid_plus_certs _ pd 
; selective_pre_dioid_times_certs  := msg_certs_from_sg_CK_certs S eq times wS f id_d timesP                                               
; selective_pre_dioid_id_ann_certs := id_ann_P 
; selective_pre_dioid_certs        := selective_cancellative_pre_dioid_certs _ pd 
; selective_pre_dioid_ast           := selective_cancellative_pre_dioid_ast _ pd 
|}.                                                                                                      



(* 17 *)
Definition selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero
           {S : Type} (pd : @selective_cancellative_pre_dioid_with_zero S) : @selective_pre_dioid_with_zero S := 
let eqv := selective_cancellative_pre_dioid_with_zero_eqv _ pd in
let eq := eqv_eq eqv in 
let wS := eqv_witness eqv in 
let f := eqv_new eqv in
let timesP := selective_cancellative_pre_dioid_with_zero_times_certs _ pd in
let times := selective_cancellative_pre_dioid_with_zero_times _ pd in
let id_ann_P := selective_cancellative_pre_dioid_with_zero_id_ann_certs _ pd in
let id_ann_times_plus_P := pid_is_tann_times_plus_d id_ann_P in 
let id_d := extract_exists_id_certifiable_from_exists_id_ann_certifiable id_ann_times_plus_P in 
{|
  selective_pre_dioid_with_zero_eqv           := eqv 
; selective_pre_dioid_with_zero_plus          := selective_cancellative_pre_dioid_with_zero_plus _ pd 
; selective_pre_dioid_with_zero_times         := times 
; selective_pre_dioid_with_zero_plus_certs   := selective_cancellative_pre_dioid_with_zero_plus_certs _ pd 
; selective_pre_dioid_with_zero_times_certs  := msg_certs_from_sg_CK_certs S eq times wS f id_d timesP
; selective_pre_dioid_with_zero_id_ann_certs := id_ann_P 
; selective_pre_dioid_with_zero_certs        := selective_cancellative_pre_dioid_with_zero_certs _ pd 
; selective_pre_dioid_with_zero_ast           := selective_cancellative_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 18 *)

Definition selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one
           {S : Type} (pd : @selective_cancellative_pre_dioid_with_one S) : @selective_pre_dioid_with_one S := 
let eqv := selective_cancellative_pre_dioid_with_one_eqv _ pd in
let eq := eqv_eq eqv in 
let wS := eqv_witness eqv in 
let f := eqv_new eqv in
let timesP := selective_cancellative_pre_dioid_with_one_times_certs _ pd in
let times := selective_cancellative_pre_dioid_with_one_times _ pd in
let id_ann_P := selective_cancellative_pre_dioid_with_one_id_ann_certs _ pd in
let id_ann_times_plus_P := pann_is_tid_times_plus id_ann_P in 
let id_d := match id_ann_times_plus_P with
                | Assert_Exists_Id_Ann_Equal id => Certify_Exists_Id id 
            end in  
{|
  selective_pre_dioid_with_one_eqv           := eqv 
; selective_pre_dioid_with_one_plus          := selective_cancellative_pre_dioid_with_one_plus _ pd 
; selective_pre_dioid_with_one_times         := times 
; selective_pre_dioid_with_one_plus_certs   := selective_cancellative_pre_dioid_with_one_plus_certs _ pd 
; selective_pre_dioid_with_one_times_certs  := msg_certs_from_sg_CK_certs S eq times wS f id_d timesP
; selective_pre_dioid_with_one_id_ann_certs := id_ann_P 
; selective_pre_dioid_with_one_certs        := selective_cancellative_pre_dioid_with_one_certs _ pd 
; selective_pre_dioid_with_one_ast           := selective_cancellative_pre_dioid_with_one_ast _ pd 
|}.                                                                                                      


(* 19 *)                                                    
Definition selective_cancellative_pre_dioid_from_selective_cancellative_pre_dioid_with_zero
             {S : Type} (pd : @selective_cancellative_pre_dioid_with_zero S) : @selective_cancellative_pre_dioid S := 
{|
  selective_cancellative_pre_dioid_eqv           := selective_cancellative_pre_dioid_with_zero_eqv _ pd 
; selective_cancellative_pre_dioid_plus          := selective_cancellative_pre_dioid_with_zero_plus _ pd 
; selective_cancellative_pre_dioid_times         := selective_cancellative_pre_dioid_with_zero_times _ pd 
; selective_cancellative_pre_dioid_plus_certs   := selective_cancellative_pre_dioid_with_zero_plus_certs _ pd 
; selective_cancellative_pre_dioid_times_certs  := selective_cancellative_pre_dioid_with_zero_times_certs _ pd 
; selective_cancellative_pre_dioid_id_ann_certs := id_ann_certs_from_pid_is_tann_certs (selective_cancellative_pre_dioid_with_zero_id_ann_certs _ pd)
; selective_cancellative_pre_dioid_certs        := selective_cancellative_pre_dioid_with_zero_certs _ pd 
; selective_cancellative_pre_dioid_ast           := selective_cancellative_pre_dioid_with_zero_ast _ pd 
|}.                                                                                                      

(* 20 *)                                                    
Definition selective_cancellative_pre_dioid_from_selective_cancellative_pre_dioid_with_one
           {S : Type} (pd : @selective_cancellative_pre_dioid_with_one S) : @selective_cancellative_pre_dioid S := 
{|
  selective_cancellative_pre_dioid_eqv           := selective_cancellative_pre_dioid_with_one_eqv _ pd 
; selective_cancellative_pre_dioid_plus          := selective_cancellative_pre_dioid_with_one_plus _ pd 
; selective_cancellative_pre_dioid_times         := selective_cancellative_pre_dioid_with_one_times _ pd 
; selective_cancellative_pre_dioid_plus_certs   := selective_cancellative_pre_dioid_with_one_plus_certs _ pd 
; selective_cancellative_pre_dioid_times_certs  := selective_cancellative_pre_dioid_with_one_times_certs _ pd 
; selective_cancellative_pre_dioid_id_ann_certs := id_ann_certs_from_pann_is_tid_certs (selective_cancellative_pre_dioid_with_one_id_ann_certs _ pd)
; selective_cancellative_pre_dioid_certs        := selective_cancellative_pre_dioid_with_one_certs _ pd 
; selective_cancellative_pre_dioid_ast           := selective_cancellative_pre_dioid_with_one_ast _ pd 
|}.

(* 21 *)                                                    
Definition selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid
           {S : Type} (pd : @selective_cancellative_dioid S) : @selective_cancellative_pre_dioid_with_zero S := 
{|
  selective_cancellative_pre_dioid_with_zero_eqv           := selective_cancellative_dioid_eqv _ pd 
; selective_cancellative_pre_dioid_with_zero_plus          := selective_cancellative_dioid_plus _ pd 
; selective_cancellative_pre_dioid_with_zero_times         := selective_cancellative_dioid_times _ pd 
; selective_cancellative_pre_dioid_with_zero_plus_certs   := selective_cancellative_dioid_plus_certs _ pd 
; selective_cancellative_pre_dioid_with_zero_times_certs  := selective_cancellative_dioid_times_certs _ pd 
; selective_cancellative_pre_dioid_with_zero_id_ann_certs := pid_is_tann_certs_from_dually_bounded_certs
                                                                  (selective_cancellative_dioid_id_ann_certs _ pd)
; selective_cancellative_pre_dioid_with_zero_certs        := selective_cancellative_dioid_certs _ pd 
; selective_cancellative_pre_dioid_with_zero_ast           := selective_cancellative_dioid_ast _ pd 
|}.                                                                                                      


(* 22 *)                                                    
Definition selective_cancellative_pre_dioid_with_one_from_selective_cancellative_dioid
           {S : Type} (pd : @selective_cancellative_dioid S) : @selective_cancellative_pre_dioid_with_one S := 
{|
  selective_cancellative_pre_dioid_with_one_eqv           := selective_cancellative_dioid_eqv _ pd 
; selective_cancellative_pre_dioid_with_one_plus          := selective_cancellative_dioid_plus _ pd 
; selective_cancellative_pre_dioid_with_one_times         := selective_cancellative_dioid_times _ pd 
; selective_cancellative_pre_dioid_with_one_plus_certs   := selective_cancellative_dioid_plus_certs _ pd 
; selective_cancellative_pre_dioid_with_one_times_certs  := selective_cancellative_dioid_times_certs _ pd 
; selective_cancellative_pre_dioid_with_one_id_ann_certs := pann_is_tid_certs_from_dually_bounded_certs (selective_cancellative_dioid_id_ann_certs _ pd)
; selective_cancellative_pre_dioid_with_one_certs        := selective_cancellative_dioid_certs _ pd 
; selective_cancellative_pre_dioid_with_one_ast           := selective_cancellative_dioid_ast _ pd 
|}.                                                                                                      


(* 23 *)
Definition selective_pre_dioid_with_zero_from_selective_distributive_prelattice_with_zero
           {S: Type} (dS : @selective_distributive_prelattice_with_zero S) : @selective_pre_dioid_with_zero S :=
let eqv   := selective_distributive_prelattice_with_zero_eqv dS in
let eqvP  := eqv_certs eqv in
let eq    := eqv_eq eqv in
let wS := eqv_witness eqv in 
let f := eqv_new eqv in
let plus  := selective_distributive_prelattice_with_zero_join dS in
let plusP := selective_distributive_prelattice_with_zero_join_certs dS in
let times := selective_distributive_prelattice_with_zero_meet dS in
let timesP:= selective_distributive_prelattice_with_zero_meet_certs dS in
let dPS   := selective_distributive_prelattice_with_zero_certs dS in
{|
  selective_pre_dioid_with_zero_eqv           := eqv 
; selective_pre_dioid_with_zero_plus          := plus 
; selective_pre_dioid_with_zero_times         := times 
; selective_pre_dioid_with_zero_plus_certs   := plusP 
; selective_pre_dioid_with_zero_times_certs  := msg_certs_from_sg_certs _ (sg_certs_from_sg_CS_certs S eq times wS f timesP)
; selective_pre_dioid_with_zero_id_ann_certs := selective_distributive_prelattice_with_zero_id_ann_certs dS
; selective_pre_dioid_with_zero_certs        := dioid_certs_from_distributive_lattice_certs dPS 
; selective_pre_dioid_with_zero_ast           := selective_distributive_prelattice_with_zero_ast dS 
|}.                                                                                                      


(* 24 *)
Definition selective_pre_dioid_with_one_from_selective_distributive_prelattice_with_one
           {S: Type} (dS : @selective_distributive_prelattice_with_one S) : @selective_pre_dioid_with_one S :=
let eqv   := selective_distributive_prelattice_with_one_eqv dS in
let eqvP  := eqv_certs eqv in
let eq    := eqv_eq eqv in
let wS := eqv_witness eqv in 
let f := eqv_new eqv in
let plus  := selective_distributive_prelattice_with_one_join dS in
let plusP := selective_distributive_prelattice_with_one_join_certs dS in
let times := selective_distributive_prelattice_with_one_meet dS in
let timesP:= selective_distributive_prelattice_with_one_meet_certs dS in
let dPS   := selective_distributive_prelattice_with_one_certs dS in
{|
  selective_pre_dioid_with_one_eqv           := eqv 
; selective_pre_dioid_with_one_plus          := plus 
; selective_pre_dioid_with_one_times         := times 
; selective_pre_dioid_with_one_plus_certs   := plusP 
; selective_pre_dioid_with_one_times_certs  := msg_certs_from_sg_certs _ (sg_certs_from_sg_CS_certs _ eq times wS f timesP)
; selective_pre_dioid_with_one_id_ann_certs := selective_distributive_prelattice_with_one_id_ann_certs dS
; selective_pre_dioid_with_one_certs        := dioid_certs_from_distributive_lattice_certs dPS 
; selective_pre_dioid_with_one_ast           := selective_distributive_prelattice_with_one_ast dS 
|}.                                                                                                      



(* Derived *) 

(* two hops *)

(* 1, 2 *) 
Definition bs_from_selective_presemiring {S : Type} (pd : @selective_presemiring S) : @bs S := 
  bs_from_bs_CS (bs_CS_from_selective_presemiring pd).

(* 2, 3 *) 
Definition bs_CS_from_selective_semiring {S : Type} (sr : @selective_semiring S) : @bs_CS S := 
  bs_CS_from_selective_presemiring (selective_presemiring_from_selective_semiring sr).

(* 2, 5 *)
Definition bs_CS_from_selective_pre_dioid {S : Type} (sr : @selective_pre_dioid S) : @bs_CS S := 
  bs_CS_from_selective_presemiring (selective_presemiring_from_selective_pre_dioid sr).

(* 3, 4 (could also be 5,6) *)
Definition selective_presemiring_from_selective_pre_dioid_with_zero
           {S : Type} (pd : @selective_pre_dioid_with_zero S) : @selective_presemiring S := 
  selective_presemiring_from_selective_semiring (selective_semiring_from_selective_pre_dioid_with_zero pd).

(* 4, 8 *)
Definition selective_semiring_from_selective_dioid
           {S : Type} (pd : @selective_dioid S) : @selective_semiring S := 
  selective_semiring_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_dioid pd).

(* 5, 10 *) 
Definition selective_presemiring_from_selective_distributive_prelattice
           {S : Type} (l : @selective_distributive_prelattice S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid (selective_pre_dioid_from_selective_distributive_prelattice l). 

(* 5, 7 *) 
Definition selective_presemiring_from_selective_pre_dioid_with_one
           {S : Type} (pd : @selective_pre_dioid_with_one S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid (selective_pre_dioid_from_selective_pre_dioid_with_one pd).

(* 5, 16 *)
Definition selective_presemiring_from_selective_cancellative_pre_dioid
           {S : Type} (pd : @selective_cancellative_pre_dioid S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid (selective_pre_dioid_from_selective_cancellative_pre_dioid pd).

(* 6,8 (could be 7,9 as well) *) 
Definition selective_pre_dioid_from_selective_dioid {S : Type} (d : @selective_dioid S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_dioid d).

(* 6, 17 (or 16,19) *)
Definition selective_pre_dioid_from_selective_cancellative_pre_dioid_with_zero
           {S : Type} (d : @selective_cancellative_pre_dioid_with_zero S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_pre_dioid_with_zero 
           (selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero d).

(* 7, 18 *)
Definition selective_pre_dioid_from_selective_cancellative_dioid_with_one
           {S : Type} (d : @selective_cancellative_pre_dioid_with_one S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_pre_dioid_with_one 
           (selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one  d).

(* 8, 11 *) 
Definition selective_pre_dioid_with_zero_from_selective_distributive_lattice
           {S : Type} (dl : @selective_distributive_lattice S) : @selective_pre_dioid_with_zero S := 
  selective_pre_dioid_with_zero_from_selective_dioid  (selective_dioid_from_selective_distributive_lattice  dl). 

(* 9, 11 *) 
Definition selective_pre_dioid_with_one_from_selective_distributive_lattice {S : Type}
           (dl : @selective_distributive_lattice S) : @selective_pre_dioid_with_one S := 
  selective_pre_dioid_with_one_from_selective_dioid (selective_dioid_from_selective_distributive_lattice dl). 


(* 10, 12 *) 
Definition selective_pre_dioid_from_selective_distributive_prelattice_with_zero
           {S : Type} (d : @selective_distributive_prelattice_with_zero S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_distributive_prelattice 
      (selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S d).

(* 10, 13 *) 
Definition selective_pre_dioid_from_selective_distributive_prelattice_with_one
           {S : Type} (d : @selective_distributive_prelattice_with_one S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_distributive_prelattice 
      (selective_distributive_prelattice_from_selective_distributive_prelattice_with_one S d).

(* 12, 14 (could be 13,15 as well) *) 
Definition selective_distributive_prelattice_from_selective_distributive_lattice
           {S : Type} (dl : @selective_distributive_lattice S) : @selective_distributive_prelattice S :=
  selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S
      (selective_distributive_prelattice_with_zero_from_selective_distributive_lattice S dl).

(* 17, 21  *)
Definition selective_pre_dioid_with_zero_from_selective_cancellative_dioid
           {S : Type} (dl : @selective_cancellative_dioid S) : @selective_pre_dioid_with_zero S :=
  selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero 
     (selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid dl). 



(* 18, 22 *)
Definition selective_pre_dioid_with_one_from_selective_cancellative_dioid
           {S : Type} (dl : @selective_cancellative_dioid S) : @selective_pre_dioid_with_one S :=
  selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one 
     (selective_cancellative_pre_dioid_with_one_from_selective_cancellative_dioid dl). 

(* 19, 21 (could be 20,22)*)
Definition selective_cancellative_pre_dioid_from_selective_cancellative_dioid
           {S : Type} (dl : @selective_cancellative_dioid S) : @selective_cancellative_pre_dioid S :=
  selective_cancellative_pre_dioid_from_selective_cancellative_pre_dioid_with_zero 
     (selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid dl). 

(* three hops *)

(* 1,2,3 *)
Definition bs_from_selective_semiring
           {S : Type} (pd : @selective_semiring S) : @bs S := 
  bs_from_selective_presemiring (selective_presemiring_from_selective_semiring pd).

(* 1,2,5 *)
Definition bs_from_selective_pre_dioid
           {S : Type} (pd : @selective_pre_dioid S) : @bs S := 
  bs_from_selective_presemiring (selective_presemiring_from_selective_pre_dioid pd).

(* 2,3,4 (or 2,5,6) *)
Definition bs_CS_from_selective_pre_dioid_with_zero
           {S : Type} (a : @selective_pre_dioid_with_zero  S) : @bs_CS S := 
  bs_CS_from_selective_semiring (selective_semiring_from_selective_pre_dioid_with_zero a).

(* 2,5,7 *)
Definition bs_CS_from_selective_pre_dioid_with_one 
           {S : Type} (a : @selective_pre_dioid_with_one  S) : @bs_CS S := 
  bs_CS_from_selective_pre_dioid (selective_pre_dioid_from_selective_pre_dioid_with_one a).

(* 2,5,10 *)
Definition bs_CS_from_selective_distributive_prelattice
           {S : Type} (a : @selective_distributive_prelattice  S) : @bs_CS S := 
  bs_CS_from_selective_pre_dioid (selective_pre_dioid_from_selective_distributive_prelattice a).

(* 3,4,8 (or 5,6,8 or 5,7,9) *)
Definition selective_presemiring_from_selective_dioid
           {S : Type} (a : @selective_dioid  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_dioid a).

(* 4,8,11 *)
Definition selective_semiring_from_selective_distributive_lattice
           {S : Type} (a : @selective_distributive_lattice  S) : @selective_semiring S := 
  selective_semiring_from_selective_dioid (selective_dioid_from_selective_distributive_lattice a).

(* 5,6,17 (or 5,16,19)  *)
Definition selective_presemiring_from_selective_cancellative_pre_dioid_with_zero
           {S : Type} (a : @selective_cancellative_pre_dioid_with_zero  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid_with_zero 
            (selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero a).

(* 5,7,18 (or 5,16,20) *)
Definition selective_presemiring_from_selective_cancellative_pre_dioid_with_one
           {S : Type} (a : @selective_cancellative_pre_dioid_with_one  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid_with_one 
         (selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one a).

(* 5,10,12 *)
Definition selective_presemiring_from_selective_distributive_prelattice_with_zero
           {S : Type} (a : @selective_distributive_prelattice_with_zero  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_distributive_prelattice 
        (selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S a).

(* 5,10,12 *)
Definition selective_presemiring_from_selective_distributive_prelattice_with_one
           {S : Type} (a : @selective_distributive_prelattice_with_one  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_distributive_prelattice 
        (selective_distributive_prelattice_from_selective_distributive_prelattice_with_one S a).

(* 6,8,11 (or 7,9,11 or 10,13,15 or 10,12,14) *)
Definition selective_pre_dioid_from_selective_distributive_lattice
           {S : Type} (a : @selective_distributive_lattice  S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_dioid (selective_dioid_from_selective_distributive_lattice a).

(* 6,17,21 (could be 7,18,22, or 16,20,22, or 16,19,21) *)
Definition selective_pre_dioid_from_selective_cancellative_dioid
           {S : Type} (a : @selective_cancellative_dioid  S) : @selective_pre_dioid S := 
  selective_pre_dioid_from_selective_cancellative_pre_dioid_with_zero 
       (selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid a).

(* four hops *)

(* 1,2,3,4 (or 1,2,5,6) *)
Definition bs_from_selective_pre_dioid_with_zero
           {S : Type} (a : @selective_pre_dioid_with_zero  S) : @bs S := 
  bs_from_selective_semiring (selective_semiring_from_selective_pre_dioid_with_zero a).

(* 1,2,5,10 *)
Definition bs_from_selective_distributive_prelattice
           {S : Type} (a : @selective_distributive_prelattice  S) : @bs S := 
  bs_from_selective_pre_dioid (selective_pre_dioid_from_selective_distributive_prelattice a).

(* 1,2,5,7 *)
Definition bs_from_selective_pre_dioid_with_one
           {S : Type} (a : @selective_pre_dioid_with_one  S) : @bs S := 
  bs_from_selective_pre_dioid (selective_pre_dioid_from_selective_pre_dioid_with_one a).


(* 1,2,5,16 *)
Definition bs_from_selective_cancellative_pre_dioid
           {S : Type} (a : @selective_cancellative_pre_dioid  S) : @bs S := 
  bs_from_selective_pre_dioid (selective_pre_dioid_from_selective_cancellative_pre_dioid a).


(* 2,5,6,8 (or 2,3,4,8) *)
Definition bs_CS_from_selective_dioid
           {S : Type} (a : @selective_dioid  S) : @bs_CS S := 
  bs_CS_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_dioid a).

(* 2,5,6,17 *)
Definition bs_CS_from_selective_cancellative_pre_dioid_with_zero
           {S : Type} (a : @selective_cancellative_pre_dioid_with_zero  S) : @bs_CS S := 
  bs_CS_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero a).

(* 2,5,7,18 *)
Definition bs_CS_from_selective_cancellative_pre_dioid_with_one
           {S : Type} (a : @selective_cancellative_pre_dioid_with_one  S) : @bs_CS S := 
  bs_CS_from_selective_pre_dioid_with_one (selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one a).

(* 2,5,10,12 *)
Definition bs_CS_from_selective_distributive_prelattice_with_zero
           {S : Type} (a : @selective_distributive_prelattice_with_zero  S) : @bs_CS S := 
  bs_CS_from_selective_distributive_prelattice (selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S a).

(* 2,5,10,13 *)
Definition bs_CS_from_selective_distributive_prelattice_with_one
           {S : Type} (a : @selective_distributive_prelattice_with_one  S) : @bs_CS S := 
  bs_CS_from_selective_distributive_prelattice (selective_distributive_prelattice_from_selective_distributive_prelattice_with_one S a).


(* 3,4,8,11 (or 5,6,8,11 or 5,7,9,11 or 5,10,12,14) *)
Definition selective_presemiring_from_selective_distributive_lattice 
           {S : Type} (a : @selective_distributive_lattice  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_distributive_lattice a).

(* 5,6,17,21 (or 5,7,18,22 or 5,16,19,21) *)
Definition selective_presemiring_from_selective_cancellative_dioid
           {S : Type} (a : @selective_cancellative_dioid  S) : @selective_presemiring S := 
  selective_presemiring_from_selective_cancellative_pre_dioid_with_zero 
     (selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid a).

(* five hops *)

(* 1,2,3,4,8 (or 1,2,5,6,8) *)
Definition bs_from_selective_dioid
           {S : Type} (a : @selective_dioid  S) : @bs S := 
  bs_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_dioid a).

(* 1,2,5,10,12 *)
Definition bs_from_selective_distributive_prelattice_with_zero
           {S : Type} (a : @selective_distributive_prelattice_with_zero  S) : @bs S := 
  bs_from_selective_distributive_prelattice (selective_distributive_prelattice_from_selective_distributive_prelattice_with_zero S a).

Definition bs_from_selective_distributive_prelattice_with_one 
           {S: Type} (a : @selective_distributive_prelattice_with_one  S) : @bs S :=            
  bs_from_selective_pre_dioid_with_one 
       (selective_pre_dioid_with_one_from_selective_distributive_prelattice_with_one a).



(* 1,2,5,7,18 *)
Definition bs_from_selective_cancellative_pre_dioid_with_one
           {S : Type} (a : @selective_cancellative_pre_dioid_with_one  S) : @bs S := 
  bs_from_selective_pre_dioid_with_one (selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one a).

(* 1,2,5,6,17 *)
Definition bs_from_selective_cancellative_pre_dioid_with_zero
           {S: Type} (a : @selective_cancellative_pre_dioid_with_zero  S) : @bs S := 
  bs_from_selective_pre_dioid_with_zero (selective_pre_dioid_with_zero_from_selective_cancellative_pre_dioid_with_zero a).



(* 2,5,6,8,11 (or 2,5,10,12,14 or 2,3,4,8,11) *)
Definition bs_CS_from_selective_distributive_lattice
           {S : Type} (a : @selective_distributive_lattice  S) : @bs_CS S := 
  bs_CS_from_selective_dioid (selective_dioid_from_selective_distributive_lattice a).

(* 2,5,6,17,21 (or 2,5,7,18,22) *)
Definition bs_CS_from_selective_cancellative_dioid
           {S : Type} (a : @selective_cancellative_dioid  S) : @bs_CS S := 
  bs_CS_from_selective_cancellative_pre_dioid_with_zero (selective_cancellative_pre_dioid_with_zero_from_selective_cancellative_dioid a).

(* six hops *)

(* 1,2,3,4,8,11 (or 1,2,5,10,12,14)*)
Definition bs_from_selective_distributive_lattice
           {S : Type} (a : @selective_distributive_lattice  S) : @bs S := 
  bs_from_selective_dioid (selective_dioid_from_selective_distributive_lattice a).

(* 1,2,5,7,18,22 (or 1,2,5,6,17,21) *)
Definition bs_from_selective_cancellative_dioid
           {S : Type} (a : @selective_cancellative_dioid  S) : @bs S := 
  bs_from_selective_cancellative_pre_dioid_with_one (selective_cancellative_pre_dioid_with_one_from_selective_cancellative_dioid a).

End Combinators.

End CAS.

Section Verify. 

Section Certificates.

Variable S : Type.
Variable eq : brel S.   
Variable eqvP : eqv_proofs S eq.
Variable plus times : binary_op S.

Lemma correct_id_ann_certs_from_pid_is_tann_certs (P : pid_is_tann_proofs S eq plus times): 
   id_ann_certs_from_pid_is_tann_certs (P2C_pid_is_tann S eq plus times P)
   =
   P2C_id_ann S eq plus times (id_ann_proofs_from_pid_is_tann_proofs S eq plus times P).
Proof. destruct P.
       unfold id_ann_certs_from_pid_is_tann_certs, id_ann_proofs_from_pid_is_tann_proofs. 
       unfold P2C_pid_is_tann, P2C_id_ann; simpl. 
       reflexivity. 
Qed.

Lemma correct_id_ann_certs_from_pann_is_tid_certs (P : pann_is_tid_proofs S eq plus times): 
   id_ann_certs_from_pann_is_tid_certs (P2C_pann_is_tid S eq plus times P)
   =
   P2C_id_ann S eq plus times (id_ann_proofs_from_pann_is_tid_proofs S eq plus times P).
Proof. destruct P.
       unfold id_ann_certs_from_pann_is_tid_certs, id_ann_proofs_from_pann_is_tid_proofs. 
       unfold P2C_pann_is_tid, P2C_id_ann; simpl. 
       reflexivity. 
Qed.

Lemma correct_pid_is_tann_certs_from_dually_bounded_certs (P : dually_bounded_proofs S eq plus times): 
   pid_is_tann_certs_from_dually_bounded_certs (P2C_dually_bounded S eq plus times P)
   =
   P2C_pid_is_tann S eq plus times (pid_is_tann_proofs_from_dually_bounded_proofs S eq plus times P).
Proof. destruct P.
       unfold pid_is_tann_certs_from_dually_bounded_certs, pid_is_tann_proofs_from_dually_bounded_proofs. 
       unfold P2C_pid_is_tann, P2C_dually_bounded; simpl. 
       reflexivity. 
Qed.

Lemma correct_pann_is_tid_certs_from_dually_bounded_certs (P : dually_bounded_proofs S eq plus times): 
   pann_is_tid_certs_from_dually_bounded_certs (P2C_dually_bounded S eq plus times P)
   =
   P2C_pann_is_tid S eq plus times (pann_is_tid_proofs_from_dually_bounded_proofs S eq plus times P).
Proof. destruct P.
       unfold pann_is_tid_certs_from_dually_bounded_certs, pann_is_tid_proofs_from_dually_bounded_proofs. 
       unfold P2C_pann_is_tid, P2C_dually_bounded; simpl. 
       reflexivity. 
Qed.


(* 1 *)
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


(* 2 *)
Definition correct_semiring_certs_from_dioid_certs (dp : dioid_proofs S eq plus times) : 
  P2C_semiring _ _ _ _  (semiring_proofs_from_dioid_proofs S eq plus times dp) 
  =                                     
  semiring_certs_from_dioid_certs (P2C_dioid _ _ _ _ dp). 
Proof. destruct dp.
       unfold P2C_semiring, P2C_dioid, semiring_proofs_from_dioid_proofs, semiring_certs_from_dioid_certs; simpl.
       reflexivity.        
Qed.

(* 3 *)
Lemma correct_dioid_certs_from_distributive_lattice_certs
      (cong_plus : bop_congruence S eq plus) 
      (comm_plus : bop_commutative S eq plus) 
      (comm_times : bop_commutative S eq times) 
      (dl : distributive_lattice_proofs S eq plus times) : 
    P2C_dioid _ _ _ _ (dioid_proofs_from_distributive_lattice_proofs S eq plus times eqvP cong_plus comm_plus comm_times dl)
    = 
    dioid_certs_from_distributive_lattice_certs (P2C_distributive_lattice _ _ _ _ dl). 
Proof. destruct dl.
       unfold P2C_dioid, P2C_distributive_lattice.
       unfold dioid_certs_from_distributive_lattice_certs, dioid_proofs_from_distributive_lattice_proofs; simpl. 
       reflexivity.        
Qed.
  
(* 4 *)
Lemma correct_lattice_certs_from_distributive_lattice_certs
      (eqv : A_eqv S)
      (plusP : sg_CI_proofs S (A_eqv_eq S eqv) plus)
      (timesP : sg_CI_proofs S (A_eqv_eq S eqv) times)
      (bp : distributive_lattice_proofs S (A_eqv_eq S eqv) plus times): 
   lattice_certs_from_distributive_lattice_certs (P2C_distributive_lattice S (A_eqv_eq S eqv) plus times bp)
   =
   P2C_lattice S (A_eqv_eq S eqv) plus times (lattice_proofs_from_distributive_lattice_proofs S (A_eqv_eq S eqv) plus times (A_eqv_proofs S eqv) plusP timesP bp).
Proof. destruct bp.
       unfold P2C_distributive_lattice, lattice_proofs_from_distributive_lattice_proofs, P2C_lattice.  
       unfold lattice_certs_from_distributive_lattice_certs; simpl. 
       reflexivity. 
Qed.

(* 5 *)  
Lemma correct_bs_certs_from_lattice_certs (plusP : sg_CI_proofs S eq plus) (timesP : sg_CI_proofs S eq times) (lP : lattice_proofs S eq plus times) : 
  P2C_bs S eq plus times (bs_proofs_from_lattice_proofs S eq plus times eqvP plusP timesP lP)
  =                                      
  bs_certs_from_lattice_certs (P2C_lattice S eq plus times lP). 
Proof. destruct lP. unfold bs_proofs_from_lattice_proofs, P2C_lattice, bs_certs_from_lattice_certs, P2C_bs; simpl.
       destruct A_lattice_distributive_d as [LD | [[a [b c]] NLD] ]; simpl; auto. 
Qed.                    
  
End Certificates. 


Section Combinators.

(* 1 *)   
Theorem correct_bs_from_bs_CI (S : Type) (P : A_bs_CI S) : 
    bs_from_bs_CI (A2C_bs_CI S P) = A2C_bs S (A_bs_from_bs_CI S P).
Proof. destruct P.
       unfold bs_from_bs_CI, A_bs_from_bs_CI, A2C_bs_CI, A2C_bs; simpl.
       (* asg_certs_from_sg_CI_certs is derived *) 
       unfold asg_certs_from_sg_CI_certs, A_asg_proofs_from_sg_CI_proofs.
       rewrite <- correct_asg_certs_from_sg_C_certs. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs. 
       reflexivity. 
Qed.
  
(* 2 *) 
Theorem correct_bs_from_presemiring (S : Type) (P : A_presemiring S) : 
    bs_from_presemiring (A2C_presemiring S P) = A2C_bs S (A_bs_from_presemiring S P).
Proof. destruct P.
       unfold bs_from_presemiring, A_bs_from_presemiring, A2C_presemiring, A2C_bs; simpl.
       rewrite correct_bs_certs_from_semiring_certs.
       reflexivity. 
Qed.

(* 3 *) 
Theorem correct_presemiring_from_semiring (S: Type) (sr : A_semiring S) :
    presemiring_from_semiring (A2C_semiring S sr) = A2C_presemiring S (A_presemiring_from_semiring S sr).
Proof. destruct sr.
       unfold presemiring_from_semiring, A_presemiring_from_semiring, A2C_semiring, A2C_presemiring; simpl.
       rewrite correct_id_ann_certs_from_pid_is_tann_certs. 
       reflexivity. 
Qed.

(* 4 *) 
Theorem correct_semiring_from_pre_dioid_with_zero (S: Type) (dS : A_pre_dioid_with_zero S) : 
    semiring_from_pre_dioid_with_zero (A2C_pre_dioid_with_zero S dS) = A2C_semiring S (A_semiring_from_pre_dioid_with_zero S dS).  
Proof. destruct dS. 
       unfold semiring_from_pre_dioid_with_zero, A_semiring_from_pre_dioid_with_zero, A2C_semiring, A2C_pre_dioid_with_zero; simpl.
       rewrite correct_semiring_certs_from_dioid_certs.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       reflexivity. 
Qed.
  
(* 5 *)
Theorem correct_bs_CI_from_lattice (S: Type) (lP : A_lattice S) : 
  bs_CI_from_lattice (A2C_lattice S lP) = A2C_bs_CI S (A_bs_CI_from_lattice S lP). 
Admitted. 
    
(* 6 *) 
Theorem correct_lattice_from_distributive_lattice (S: Type) (dS : A_distributive_lattice S) : 
  lattice_from_distributive_lattice (A2C_distributive_lattice S dS)
  =
  A2C_lattice S (A_lattice_from_distributive_lattice S dS). 
Admitted. 

(* 7 *) 
Theorem correct_bs_CI_from_pre_dioid (S: Type) (pd : A_pre_dioid S) : 
   bs_CI_from_pre_dioid (A2C_pre_dioid S pd) = A2C_bs_CI S (A_bs_CI_from_pre_dioid S pd).
Admitted. 

(* 8 *) 
Theorem correct_pre_dioid_from_pre_dioid_with_zero (S: Type) (pd :A_pre_dioid_with_zero S) : 
  pre_dioid_from_pre_dioid_with_zero (A2C_pre_dioid_with_zero S pd)
  =
  A2C_pre_dioid S (A_pre_dioid_from_pre_dioid_with_zero S pd). 
Admitted. 

(* 9 *) 
Theorem correct_pre_dioid_from_pre_dioid_with_one (S: Type) (pd :A_pre_dioid_with_one S) : 
  pre_dioid_from_pre_dioid_with_one (A2C_pre_dioid_with_one S pd)
  =
  A2C_pre_dioid S (A_pre_dioid_from_pre_dioid_with_one S pd).  
Admitted.

(* 10 *) 
Theorem correct_pre_dioid_with_zero_from_dioid (S: Type) (d :A_dioid S) : 
  pre_dioid_with_zero_from_dioid (A2C_dioid S d)
  =
  A2C_pre_dioid_with_zero S (A_pre_dioid_with_zero_from_dioid S d). 
Admitted.

(* 11 *) 
Theorem correct_pre_dioid_with_one_from_dioid (S: Type) (d :A_dioid S) : 
  pre_dioid_with_one_from_dioid (A2C_dioid S d) = A2C_pre_dioid_with_one S (A_pre_dioid_with_one_from_dioid S d). 
Admitted.

(* 12 *) 
Theorem correct_dioid_from_distributive_lattice (S: Type) (d : A_distributive_lattice S) : 
  dioid_from_distributive_lattice (A2C_distributive_lattice S d) = A2C_dioid S (A_dioid_from_distributive_lattice S d). 
Admitted.

(*************** selective versions **********************)

(*** TODO .... *****) 

End Combinators. 
End Verify.   


Section MCAS. 
                       
Definition bs_from_mcas {S : Type} (A : @bs_mcas S) := 
match A with   
| BS_Error _ => A 
| BS_bs _    => A
| BS_bs_CI B => BS_bs (bs_from_bs_CI B)
| BS_bs_CS B => BS_bs (bs_from_bs_CS B)
| BS_presemiring B => BS_bs (bs_from_presemiring B)
| BS_semiring B => BS_bs (bs_from_semiring B)
| BS_pre_dioid B => BS_bs (bs_from_pre_dioid B)
| BS_pre_dioid_with_one B => BS_bs (bs_from_pre_dioid_with_one B)
| BS_pre_dioid_with_zero B => BS_bs (bs_from_pre_dioid_with_zero B)
| BS_dioid B => BS_bs (bs_from_dioid B)
| BS_prelattice B => BS_bs (bs_from_prelattice B)
| BS_distributive_prelattice B => BS_bs (bs_from_distributive_prelattice B)
| BS_lattice B => BS_bs (bs_from_lattice B)                       
| BS_distributive_lattice B => BS_bs (bs_from_distributive_lattice B)
| BS_selective_presemiring  B => BS_bs (bs_from_selective_presemiring  B)
| BS_selective_semiring B => BS_bs (bs_from_selective_semiring B)
| BS_selective_pre_dioid B => BS_bs (bs_from_selective_pre_dioid B)
| BS_selective_pre_dioid_with_zero B => BS_bs (bs_from_selective_pre_dioid_with_zero B)                       
| BS_selective_pre_dioid_with_one B => BS_bs (bs_from_selective_pre_dioid_with_one B)
| BS_selective_dioid B => BS_bs (bs_from_selective_dioid B)
| BS_selective_cancellative_pre_dioid B => BS_bs (bs_from_selective_cancellative_pre_dioid B)
| BS_selective_cancellative_pre_dioid_with_zero B => BS_bs (bs_from_selective_cancellative_pre_dioid_with_zero B)
| BS_selective_cancellative_pre_dioid_with_one B => BS_bs (bs_from_selective_cancellative_pre_dioid_with_one B)                       
| BS_selective_cancellative_dioid  B => BS_bs (bs_from_selective_cancellative_dioid  B)
| BS_selective_distributive_prelattice B => BS_bs (bs_from_selective_distributive_prelattice B)
| BS_selective_distributive_prelattice_with_zero B => BS_bs (bs_from_selective_distributive_prelattice_with_zero B)
| BS_selective_distributive_prelattice_with_one B => BS_bs (bs_from_selective_distributive_prelattice_with_one B)
| BS_selective_distributive_lattice B => BS_bs (bs_from_selective_distributive_lattice B)                       
end.

End MCAS.   

