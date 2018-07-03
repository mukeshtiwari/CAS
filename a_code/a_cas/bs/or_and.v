Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.bs.dual.
Require Import CAS.a_code.a_cas.bs.and_or.


Definition A_distributive_lattice_or_and : A_distributive_lattice bool := A_distributive_lattice_dual bool A_distributive_lattice_and_or. 
