Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.tr.properties. 

Close Scope nat. 

Definition slt_distributive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition slt_not_distributive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition slt_distributive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_distributive L S r add ltr) + (slt_not_distributive L S r add ltr). 
 
Definition slt_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition slt_not_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition slt_absorptive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_absorptive L S r add ltr) + (slt_not_absorptive L S r add ltr). 

Definition slt_strictly_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), ((r s (add s (ltr l s)) = true) * (r (ltr l s) (add s (ltr l s)) = false)).

Definition slt_not_strictly_absorptive (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  ((r s (add s (ltr l s)) = false)  +  (r (ltr l s) (add s (ltr l s)) = true)) end }. 

Definition slt_strictly_absorptive_decidable (L S : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_strictly_absorptive L S r add ltr) + (slt_not_strictly_absorptive L S r add ltr). 

Definition stl_exists_id_ann_equal (L S : Type) (r : brel S) (b : binary_op S) (ltr : L -> (S -> S)) 
  := { i : S & (bop_is_id S r b i) * (ltr_is_ann L S r ltr i)}.

Definition stl_exists_id_ann_not_equal (L S : Type) (r : brel S) (b : binary_op S) (ltr : L -> (S -> S)) 
  := { z : S * S & match z with (i, a) => (bop_is_id S r b i) * (ltr_is_ann L S r ltr a) * (r i a = false) end}.

Inductive stl_exists_id_ann_decidable (L S : Type) (eq : brel S) (b : binary_op S) (ltr : L -> (S -> S))  : Type :=
| STL_Id_Ann_Proof_None      : (bop_not_exists_id S eq b) * (ltr_not_exists_ann L S eq ltr) -> stl_exists_id_ann_decidable L S eq b ltr 
| STL_Id_Ann_Proof_Id_None   : (bop_exists_id S eq b) * (ltr_not_exists_ann L S eq ltr)     -> stl_exists_id_ann_decidable L S eq b ltr 
| STL_Id_Ann_Proof_None_Ann  : (bop_not_exists_id S eq b) * (ltr_exists_ann L S eq ltr)     -> stl_exists_id_ann_decidable L S eq b ltr 
| STL_Id_Ann_Proof_Equal     : stl_exists_id_ann_equal L S eq b ltr                         -> stl_exists_id_ann_decidable L S eq b ltr 
| STL_Id_Ann_Proof_Not_Equal : stl_exists_id_ann_not_equal L S eq b ltr                     -> stl_exists_id_ann_decidable L S eq b ltr 
. 
