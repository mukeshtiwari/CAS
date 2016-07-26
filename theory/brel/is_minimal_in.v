Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.strictify.

(*
Require Import CAS.theory.brel_subset.
Require Import CAS.theory.brel_set.
Require Import CAS.theory.brel2_in_set.
Require Import CAS.theory.bprop_forall. 
*) 

(* 
Definition is_minimal_in : ∀ S : Type, brel S → brel S → brel2 S (finite_set S)
:= λ S eq lte, brel2_conjunction S (finite_set S) 
                  (brel2_reverse (finite_set S) S (in_set S eq))
                  (brel2_lift_set_right S (brel_dual S (brel_strictify S lte))).                  


Definition brel2_congruence (S T : Type) (rS : brel S) (rT : brel T) (r : brel2 S T) := 
    ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> r s1 t1 = r s2 t2. 

*) 





