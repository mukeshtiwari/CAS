
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set. 

Require Import CAS.coq.po.properties.

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Open Scope list_scope.

(* brel_subset defined in coq/eqv/set.v *) 

Close Scope nat.

Section Theory.

Variable S: Type.
Variable eq : brel S.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.
  

(********

brel_subset_reflexive : brel_reflexive (finite_set S) (brel_subset r). 

and 

Lemma brel_subset_transitive : brel_transitive (finite_set S) (brel_subset r). 

both proved in in coq/eqv/set.v 

*********)

Lemma brel_subset_antisymmetric : brel_antisymmetric (finite_set S) (brel_set eq) (brel_subset eq). 
Proof. intros x y H1 H2.
       unfold brel_set. unfold brel_and_sym.
       rewrite H1, H2. auto.
Defined.

(*
Print brel_subset_antisymmetric. 

brel_subset_antisymmetric = 
λ (x y : finite_set S) 
  (H1 : brel_subset eq x y = true) 
  (H2 : brel_subset eq y x = true),
  eq_ind_r (λ b : bool, (b && brel_subset eq y x)%bool = true)
           (eq_ind_r (λ b : bool, (true && b)%bool = true) eq_refl H2) H1
 : brel_antisymmetric (finite_set S) (brel_set eq) (brel_subset eq)
*) 
End Theory. 
