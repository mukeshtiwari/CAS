
Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.bs.add_ann_add_id. 
Require Import CAS.coq.bs.add_id_add_ann. 
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.theory.facts.

Require Import CAS.coq.bs.union_intersect.

Section Theory.

  (* theory is in CAS.coq.bs.union_intersect *) 

End Theory.

Section ACAS.


Definition bs_proofs_union_intersect : 
  ∀ (S : Type) (eq : brel S) (c : cas_constant),
     eqv_proofs S eq -> 
     distributive_lattice_proofs
       (with_constant (finite_set S)) 
       (@brel_add_constant (finite_set S) (brel_set eq) c)
       (@bop_add_ann (finite_set S) (bop_union eq) c)
       (@bop_add_id (finite_set S) (bop_intersect eq) c)
:= λ S eq c eqvS,
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in
let tranS := A_eqv_transitive _ _ eqvS in      
{|
  A_distributive_lattice_absorptive        := bops_union_intersect_left_left_absorptive S eq refS symS tranS c
; A_distributive_lattice_absorptive_dual   := bops_intersect_union_left_left_absorptive S eq refS symS tranS c
; A_distributive_lattice_distributive      := bops_union_intersect_left_distributive S eq refS symS tranS c
|}. 


Definition A_dl_union_intersect : ∀ (S : Type),  A_eqv S -> cas_constant -> A_distributive_lattice (with_constant (finite_set S)) 
  := λ S eqv c,
  let eq  := A_eqv_eq S eqv in
  let s   := A_eqv_witness S eqv in
  let f   := A_eqv_new S eqv in
  let ntS := A_eqv_not_trivial S eqv in
  let eqP := A_eqv_proofs S eqv in 
{|
  A_distributive_lattice_eqv         := A_eqv_add_constant (finite_set S) (A_eqv_set S eqv) c 
; A_distributive_lattice_join        := @bop_add_ann (finite_set S) (bop_union eq) c
; A_distributive_lattice_meet        := @bop_add_id (finite_set S) (bop_intersect eq) c
; A_distributive_lattice_join_proofs := sg_CI_proofs_union S eq c s f ntS eqP 
; A_distributive_lattice_meet_proofs := sg_CI_proofs_intersect S eq c s f ntS eqP 
; A_distributive_lattice_proofs      := bs_proofs_union_intersect S eq c eqP 
; A_distributive_lattice_ast         := Ast_distributive_lattice_union_intersect(c, A_eqv_ast S eqv) 
|}.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  