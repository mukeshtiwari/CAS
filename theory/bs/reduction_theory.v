Require Export Coq.Unicode.Utf8.
(* Require Import Coq.Bool.Bool.   *) 
Require Import CAS.code.basic_types.
Require Import CAS.code.brel.
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.uop_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.bs_properties. 
Require Import CAS.theory.facts.
Require Import CAS.theory.brel.reduce.
Require Import CAS.theory.bop.reduction_theory. 


Section ReductionTheory.

  
  Variable S : Type.
  Variable r : unary_op S.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.  
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.   
  Variable r_cong : uop_congruence S eq r.  
  Variable r_idem : uop_idempotent S eq r.  
  Definition T : Type := red_Type S r eq.
  Definition eqT : brel T := red_eq S r eq.
  Variable add mul : binary_op S.
  Variable add_cong : bop_congruence S eq add.
  Variable mul_cong : bop_congruence S eq mul.   
  Definition addT : binary_op T := red_bop S add r eq r_idem. 
  Definition mulT : binary_op T := red_bop S mul r eq r_idem.

  Lemma addT_mulT_left_distributive :
    bop_left_uop_invariant S eq (bop_reduce r add) r ->
    bop_right_uop_invariant S eq (bop_reduce r add) r ->
    bop_right_uop_invariant S eq (bop_reduce r mul) r ->    
    bop_left_distributive S eq add mul -> 
    bop_left_distributive T eqT addT mulT.
  Proof. intros ali ari mri ldist [a Pa] [b Pb] [c Pc]. unfold Pr in Pa, Pb, Pc.
         compute. 
         assert (H1 := mri a (add b c)). compute in H1. 
         assert (H2 := r_left_and_right S add r eq symS tranS ali ari (mul a b) (mul a c)).
         assert (H3 := ldist a b c). apply r_cong in H3. 
         assert (H4 := tranS _ _ _ H1 H3).  
         assert (H5 := tranS _ _ _ H4 H2).
         exact H5.
  Qed.


  Lemma addT_mulT_right_distributive :
    bop_left_uop_invariant S eq (bop_reduce r add) r ->
    bop_right_uop_invariant S eq (bop_reduce r add) r ->
    bop_left_uop_invariant S eq (bop_reduce r mul) r ->    
    bop_right_distributive S eq add mul -> 
    bop_right_distributive T eqT addT mulT.
  Proof. intros ali ari mri rdist [a Pa] [b Pb] [c Pc]. unfold Pr in Pa, Pb, Pc.
         compute. 
         assert (H1 := mri (add b c) a). compute in H1. 
         assert (H2 := r_left_and_right S add r eq symS tranS ali ari (mul b a) (mul c a)).
         assert (H3 := rdist a b c). apply r_cong in H3. 
         assert (H4 := tranS _ _ _ H1 H3).  
         assert (H5 := tranS _ _ _ H4 H2).
         exact H5.
  Qed.

Definition bop_pseudo_left_distributive (S : Type) (eq : brel S) (r : unary_op S) (add mul : binary_op S) 
  := ∀ a b c : S, 
  eq (r (mul (r a) (r (add (r b) (r c))))) (r (add (r (mul (r a) (r b))) (r (mul (r a) (r c))))) = true. 
         
Definition bop_pseudo_right_distributive (S : Type) (eq : brel S) (r : unary_op S) (add mul : binary_op S) 
  := ∀ a b c : S, 
  eq (r (mul (r (add (r b) (r c))) (r a))) (r (add (r (mul (r b) (r a))) (r (mul (r c) (r a))))) = true.

Lemma red_bop_left_dist_iso : bop_left_distributive T eqT addT mulT <-> bop_pseudo_left_distributive S eq r add mul. 
Proof. split; intro H.
         intros s1 s2 s3.  
         assert (H1 := H (inj S r eq r_idem s1) (inj S r eq r_idem s2) (inj S r eq r_idem s3)). compute in H1.
         exact H1. 
         intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := H s1 s2 s3). compute in H1. unfold Pr in p1, p2, p3.
         assert (H2 := add_cong _ _ _ _ p2 p3). apply r_cong in H2. 
         assert (H3 := mul_cong _ _ _ _ p1 H2). apply r_cong in H3. 
         assert (H4 := mul_cong _ _ _ _ p1 p2). apply r_cong in H4.
         assert (H5 := mul_cong _ _ _ _ p1 p3). apply r_cong in H5.                   
         assert (H6 := add_cong _ _ _ _ H4 H5). apply r_cong in H6. 
         apply symS in H3.
         assert (H7 := tranS _ _ _ H3 H1).         
         assert (H8 := tranS _ _ _ H7 H6).         
         exact H8.          
Qed.

Lemma red_bop_right_dist_iso : bop_right_distributive T eqT addT mulT <-> bop_pseudo_right_distributive S eq r add mul. 
Proof. split; intro H.
         intros s1 s2 s3.  
         assert (H1 := H (inj S r eq r_idem s1) (inj S r eq r_idem s2) (inj S r eq r_idem s3)). compute in H1.
         exact H1. 
         intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := H s1 s2 s3). compute in H1. unfold Pr in p1, p2, p3.
         assert (H2 := add_cong _ _ _ _ p2 p3). apply r_cong in H2. 
         assert (H3 := mul_cong _ _ _ _ H2 p1). apply r_cong in H3. 
         assert (H4 := mul_cong _ _ _ _ p2 p1). apply r_cong in H4.
         assert (H5 := mul_cong _ _ _ _ p3 p1). apply r_cong in H5.                   
         assert (H6 := add_cong _ _ _ _ H4 H5). apply r_cong in H6. 
         apply symS in H3.
         assert (H7 := tranS _ _ _ H3 H1).         
         assert (H8 := tranS _ _ _ H7 H6).         
         exact H8.          
Qed.  


End ReductionTheory. 


(*
Section Reduced_Semigroup_Direct.

(*  Note on types: 
  red_Type : ∀ S : Type, unary_op S → brel S → Type 
  red_eq   : ∀ (S : Type) (r : unary_op S) (eqS : brel S), brel (red_Type S r eqS)
  red_bop  : ∀ S : Type, binary_op S → ∀ (r : unary_op S) (eqS : brel S), uop_idempotent S eqS r → binary_op (red_Type S r eqS) 
*)

Definition reduced_eqv_proofs : ∀ (S : Type) (eq : brel S) (r : unary_op S) (b : binary_op S),  
    eqv_proofs S eq -> reduction_eqv_proofs S eq r -> eqv_proofs (red_Type S r eq) (red_eq S r eq)
:= λ S eq r b eqv red,
{|
  eqv_reflexive      := red_ref S r eq (eqv_reflexive S eq eqv) 
; eqv_transitive     := red_trans S r eq (eqv_transitive S eq eqv) 
; eqv_symmetric      := red_sym S r eq (eqv_symmetric S eq eqv)
; eqv_congruence     := red_cong S r eq (eqv_congruence S eq eqv)                                
; eqv_witness        := inj S r eq (rep_idem S eq r red) (eqv_witness S eq eqv)                         
|}.

Definition reduced_semigroup_proofs :
  ∀ (S : Type)
    (eq : brel S)
    (r : unary_op S)
    (b : binary_op S)
    (eqv : eqv_proofs S eq)
    (csg : semigroup_proofs S eq b)
    (req : reduction_eqv_proofs S eq r)     
    (rb  : reduction_bop_proofs S eq r (bop_reduce r b)) 
    (dec : bop_commutative_decidable (red_Type S r eq) (red_eq S r eq) (red_bop S b r eq (rep_idem _ _ _ req))), 
         semigroup_proofs (red_Type S r eq) (red_eq S r eq) (red_bop S b r eq (rep_idem _ _ _ req))
:= λ S eq r b eqv csg req rb dec,
{|
  sg_associative := red_bop_ass S b r eq
                           (eqv_symmetric S eq eqv)
                           (eqv_transitive S eq eqv)
                           (sg_associative S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)
                           (rb_left S eq r _ rb)
                           (rb_right S eq r _ rb)                            
  ; sg_congruence  := red_bop_cong S b r eq
                           (sg_congruence S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)

  ; sg_commutative_d  := dec 
|}.

Definition reduced_commutative_semigroup_proofs :
  ∀ (S : Type)
    (eq : brel S)
    (r : unary_op S)
    (b : binary_op S)
    (eqv : eqv_proofs S eq)
    (csg : commutative_semigroup_proofs S eq b)
    (req : reduction_eqv_proofs S eq r)     
    (rb  : reduction_bop_proofs S eq r (bop_reduce r b)), 
         commutative_semigroup_proofs (red_Type S r eq) (red_eq S r eq) (red_bop S b r eq (rep_idem _ _ _ req))
:= λ S eq r b eqv csg req rb,
{|
  csg_associative := red_bop_ass S b r eq
                           (eqv_symmetric S eq eqv)
                           (eqv_transitive S eq eqv)
                           (csg_associative S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)
                           (rb_left S eq r _ rb)
                           (rb_right S eq r _ rb)                            
  ; csg_congruence  := red_bop_cong S b r eq
                           (csg_congruence S eq b csg)
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)

  ; csg_commutative  := red_bop_comm S b r eq
                           (rep_cong S eq r req)
                           (rep_idem S eq r req)
                           (csg_commutative S eq b csg)                           
|}.


(* semigroup combinators for reductions --- not extaction friendly! *) 
Definition semigroup_reduced:
  ∀ (S : Type)
     (csg : semigroup S)
     (r : unary_op S)
     (req : reduction_eqv_proofs S (eq S csg) r)
     (rb  : reduction_bop_proofs S (eq S csg) r (bop_reduce r (bop S csg)))
     (dec : bop_commutative_decidable (red_Type S r (eq S csg)) (red_eq S r (eq S csg)) (red_bop S (bop S csg) r (eq S csg) (rep_idem _ _ _ req))),      
           semigroup (red_Type S r (eq S csg))
:= λ S csg r req rb dec,
{|
   eq   := red_eq S r (eq S csg)
;  bop  := red_bop S (bop S csg) r (eq S csg) (rep_idem _ _ _ req)
;  eqv  := reduced_eqv_proofs S (eq S csg) r (bop S csg) (eqv S csg) req
;  sgp  := reduced_semigroup_proofs S (eq S csg) r (bop S csg) (eqv S csg) (sgp S csg) req rb dec
|}.


Definition commutative_semigroup_direct_reduction :
  ∀ (S : Type)
     (csg : commutative_semigroup S)
     (r : unary_op S)
     (req : reduction_eqv_proofs S (ceq S csg) r)     
     (rb  : reduction_bop_proofs S (ceq S csg) r (bop_reduce r (cbop S csg))),
         commutative_semigroup (red_Type S r (ceq S csg))
:= λ S csg r req rb,
{|
   ceq   := red_eq S r (ceq S csg)
;  cbop  := red_bop S (cbop S csg) r (ceq S csg) (rep_idem _ _ _ req)
;  ceqv  := reduced_eqv_proofs S (ceq S csg) r (cbop S csg) (ceqv S csg) req
;  csgp  := reduced_commutative_semigroup_proofs S (ceq S csg) r (cbop S csg) (ceqv S csg) (csgp S csg) req rb
|}.
End Reduced_Semigroup_Direct.

*) 
