Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.tr.properties. 

Close Scope nat.

Section ACAS.

Section Left_Properties.  

Definition slt_distributive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition slt_not_distributive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition slt_distributive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_distributive r add ltr) + (slt_not_distributive r add ltr). 
 
Definition slt_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition slt_not_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition slt_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_absorptive r add ltr) + (slt_not_absorptive r add ltr). 

Definition slt_strictly_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), ((r s (add s (ltr l s)) = true) * (r (ltr l s) (add s (ltr l s)) = false)).

Definition slt_not_strictly_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  ((r s (add s (ltr l s)) = false)  +  (r (ltr l s) (add s (ltr l s)) = true)) end }. 

Definition slt_strictly_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (slt_strictly_absorptive r add ltr) + (slt_not_strictly_absorptive r add ltr). 

Definition slt_exists_id_ann_equal {L S : Type} (r : brel S) (b : binary_op S) (ltr : L -> (S -> S)) 
  := { i : S & (bop_is_id S r b i) * (ltr_is_ann L S r ltr i)}.

Definition slt_exists_id_ann_not_equal {L S : Type} (r : brel S) (b : binary_op S) (ltr : L -> (S -> S)) 
  := { z : S * S & match z with (i, a) => (bop_is_id S r b i) * (ltr_is_ann L S r ltr a) * (r i a = false) end}.

Inductive slt_exists_id_ann_decidable {L S : Type} (eq : brel S) (b : binary_op S) (ltr : L -> (S -> S))  : Type :=
| SLT_Id_Ann_Proof_None      : (bop_not_exists_id S eq b) * (ltr_not_exists_ann L S eq ltr) -> slt_exists_id_ann_decidable eq b ltr 
| SLT_Id_Ann_Proof_Id_None   : (bop_exists_id S eq b) * (ltr_not_exists_ann L S eq ltr)     -> slt_exists_id_ann_decidable eq b ltr 
| SLT_Id_Ann_Proof_None_Ann  : (bop_not_exists_id S eq b) * (ltr_exists_ann L S eq ltr)     -> slt_exists_id_ann_decidable eq b ltr 
| SLT_Id_Ann_Proof_Equal     : slt_exists_id_ann_equal eq b ltr                         -> slt_exists_id_ann_decidable eq b ltr 
| SLT_Id_Ann_Proof_Not_Equal : slt_exists_id_ann_not_equal eq b ltr                     -> slt_exists_id_ann_decidable eq b ltr 
. 

End Left_Properties.


Section Right_Properties.

Definition srt_distributive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S)
   := ∀ (l : L) (t u : S), r (rtr (add t u) l) (add (rtr t l) (rtr u l)) = true. 

Definition rtr_is_ann (L S : Type) (rS : brel S) (rtr : rtr_type L S) (s : S) 
  := ∀ l : L, (rS (rtr s l ) s = true).
  
End Right_Properties.


End ACAS. 

Section CAS.

   Inductive assert_slt_distributive  {L S : Type} :=
   | Assert_Slt_Distributive : assert_slt_distributive.

   Inductive assert_slt_not_distributive {L S : Type} :=
   | Assert_Slt_Not_Distributive :  L * (S * S) -> assert_slt_not_distributive.
   
   Inductive check_slt_distributive {L S : Type} :=
   | Certify_Slt_Distributive : check_slt_distributive
   | Certify_Slt_Not_Distributive : L * (S * S) -> check_slt_distributive.

   Inductive assert_slt_absorptive {L S : Type} :=
   | Assert_Slt_Absorptive : assert_slt_absorptive.

   Inductive assert_slt_not_absorptive {L S : Type} :=
   | Assert_Slt_Not_Absorptive : L * S  -> assert_slt_not_absorptive.

   Inductive check_slt_absorptive {L S : Type} := 
   | Certify_Slt_Absorptive : check_slt_absorptive
   | Certify_Slt_Not_Absorptive : L * S -> check_slt_absorptive.


   Inductive assert_slt_strictly_absorptive {L S : Type} :=
   | Assert_Slt_Strictly_Absorptive : assert_slt_strictly_absorptive.

   Inductive assert_slt_not_strictly_absorptive {L S : Type} :=
   | Assert_Slt_Not_Strictly_Absorptive : L * S  -> assert_slt_not_strictly_absorptive.

   Inductive check_slt_strictly_absorptive {L S : Type} := 
   | Certify_Slt_Strictly_Absorptive : check_slt_strictly_absorptive
   | Certify_Slt_Not_Strictly_Absorptive : L * S -> check_slt_strictly_absorptive.

   Inductive assert_slt_exists_id_ann_equal {L S : Type} :=
   | Assert_Slt_Exists_Id_Ann_Equal : S -> assert_slt_exists_id_ann_equal.

   Inductive assert_slt_exists_id_ann_not_equal {L S : Type} :=
   | Assert_Slt_Exists_Id_Ann_Not_Equal : S * S -> assert_slt_exists_id_ann_not_equal.


   Inductive check_slt_exists_id_ann {L S : Type} : Type :=
   | Certify_SLT_Id_Ann_Proof_None : check_slt_exists_id_ann
   | Certify_SLT_Id_Ann_Proof_Id_None : S  -> check_slt_exists_id_ann
   | Certify_SLT_Id_Ann_Proof_None_Ann : S -> check_slt_exists_id_ann
   | Certify_SLT_Id_Ann_Proof_Equal     : S -> check_slt_exists_id_ann
   | Certify_SLT_Id_Ann_Proof_Not_Equal : S * S -> check_slt_exists_id_ann.




End CAS.


Section Translation.

   Definition p2c_slt_distributive_assert 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_distributive r add ltr -> @assert_slt_distributive L S := 
    λ _,  Assert_Slt_Distributive.

   Definition p2c_slt_not_distributive_assert 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_not_distributive r add ltr -> @assert_slt_not_distributive L S := 
    λ slt,  Assert_Slt_Not_Distributive (projT1 slt).
      
   Definition p2c_slt_distributive_check 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_distributive_decidable r add ltr -> @check_slt_distributive L S :=
    λ slt, match slt with 
      | inl _ => Certify_Slt_Distributive
      | inr p => Certify_Slt_Not_Distributive (projT1 p)
    end.
    
  Definition p2c_slt_absorptive_assert  
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_absorptive r add ltr -> @assert_slt_absorptive L S :=
    λ _, Assert_Slt_Absorptive.

  Definition p2c_slt_not_absorptive_assert  
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_not_absorptive r add ltr -> @assert_slt_not_absorptive L S :=
    λ slt, Assert_Slt_Not_Absorptive (projT1 slt).

  Definition p2c_slt_absorptive_check 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_absorptive_decidable r add ltr -> @check_slt_absorptive L S :=
    λ slt, match slt with 
      | inl _ => Certify_Slt_Absorptive
      | inr p => Certify_Slt_Not_Absorptive (projT1 p)
    end.


  Definition p2c_slt_strictly_absorptive_assert  
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_strictly_absorptive r add ltr -> @assert_slt_strictly_absorptive L S :=
    λ _, Assert_Slt_Strictly_Absorptive.

  Definition p2c_slt_not_strictly_absorptive_assert  
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_not_strictly_absorptive r add ltr -> @assert_slt_not_strictly_absorptive L S :=
    λ slt, Assert_Slt_Not_Strictly_Absorptive (projT1 slt).

  Definition p2c_slt_strictly_absorptive_check 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_strictly_absorptive_decidable r add ltr -> @check_slt_strictly_absorptive L S :=
    λ slt, match slt with 
      | inl _ => Certify_Slt_Strictly_Absorptive
      | inr p => Certify_Slt_Not_Strictly_Absorptive (projT1 p)
    end.

  Definition p2c_slt_exists_id_ann_equal_assert 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_exists_id_ann_equal r add ltr -> @assert_slt_exists_id_ann_equal L S :=
    λ slt, Assert_Slt_Exists_Id_Ann_Equal (projT1 slt).


  Definition p2c_slt_exists_id_ann_not_equal_assert 
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) :
    slt_exists_id_ann_not_equal r add ltr -> @assert_slt_exists_id_ann_not_equal L S :=
    λ slt, Assert_Slt_Exists_Id_Ann_Not_Equal (projT1 slt).
  
  Definition p2c_slt_exists_id_ann_check
    {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) : 
    slt_exists_id_ann_decidable r add ltr -> @check_slt_exists_id_ann L S :=
  λ slt, match slt with
    | SLT_Id_Ann_Proof_None _ _ _ (_, _) => Certify_SLT_Id_Ann_Proof_None 
    | SLT_Id_Ann_Proof_Id_None  _ _ _ (p, _) => Certify_SLT_Id_Ann_Proof_Id_None (projT1 p)
    | SLT_Id_Ann_Proof_None_Ann _ _ _ (_, p) => Certify_SLT_Id_Ann_Proof_None_Ann (projT1 p)
    | SLT_Id_Ann_Proof_Equal _ _ _ p => Certify_SLT_Id_Ann_Proof_Equal (projT1 p)
    | SLT_Id_Ann_Proof_Not_Equal _ _ _ p => Certify_SLT_Id_Ann_Proof_Not_Equal (projT1 p)
  end.
  
  
End Translation.


    
  
  

  

   

