Require Import CAS.code.basic_types.
Require Import CAS.a_code.a_cas_records. 
Require Import CAS.a_code.a_cas.bs.union_intersect.
Require Import CAS.a_code.a_cas.bs.dual. 


Definition A_dl_intersect_union : ∀ (S : Type),  A_eqv S -> cas_constant -> A_distributive_lattice (with_constant (finite_set S)) 
  := λ S eqv c, A_distributive_lattice_dual _ (A_dl_union_intersect S eqv c). 
    
