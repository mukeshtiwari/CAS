Require Import CAS.a_code.a_cas_records.

Require Import CAS.a_code.a_cas.bs.dual.
Require Import CAS.a_code.a_cas.bs.min_max.


Definition A_distributive_lattice_max_min : A_distributive_lattice nat := A_distributive_lattice_dual nat A_distributive_lattice_min_max. 
