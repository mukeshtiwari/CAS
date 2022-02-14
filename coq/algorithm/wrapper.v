
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.algorithm.Matrix.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 
(*
Check matrix_exp_unary.
Check matrix_fixpoint.
*)
Open Scope string_scope.

Definition A_instantiate_matrix_exp_unary (U : Type) 
           (A : A_bs_mcas U)
           (Node : Type)
           (F : finite_set Node) (eqN : brel Node)
  : (Matrix Node U -> nat -> Matrix Node U) + string :=
  match A_bs_mcas_cast_up U A with
  | A_BS_bs _ A' =>
    let bsP := A_bs_proofs _ A' in
    let eqv := A_bs_eqv _ A' in
    let id_annP := A_bs_id_ann_proofs _ A' in
    match A_id_ann_plus_times_d _ _ _ _ id_annP with
    | Id_Ann_Proof_Equal _ _ _ _ zeroP =>
      match A_id_ann_times_plus_d _ _ _ _ id_annP with
      | Id_Ann_Proof_Equal _ _ _ _ oneP =>
        match A_bs_left_distributive_d _ _ _ _ bsP with
        | inl _ =>
          match A_bs_right_distributive_d _ _ _ _ bsP with
          | inl _ =>
            match A_sg_commutative_d _ _ _ (A_bs_plus_proofs _ A') with
            | inl _ => inl (matrix_exp_unary Node F eqN U (projT1 zeroP) (projT1 oneP) (A_bs_plus _ A') (A_bs_times _ A')) 
            | inr _ => inr "Error : the algebra must have a commutative addition"
            end 
          | inr _ => inr "Error : the algebra is not right distributive"
          end 
        | inr _ => inr "Error : the algebra is not left distributive"
        end 
      | _ => inr "Error : the multiplicative id must be additive annihilator"
      end
    | _ => inr "Error : the additive id must be multiplicative annihilator"
    end
  | _    => inr "Internal Error : instantiate_matrix_exp_unary"
  end.
  
  

(* matrix_fixpoint properties *)
Lemma a_instantiated : forall (R : Type) (A : A_bs_mcas R) (Node : Type) 
  (F : finite_set Node) (eqN : brel Node) zeroR oneR plusR mulR,
  A_instantiate_matrix_exp_unary R A Node F eqN = 
  inl (matrix_exp_unary Node F eqN R zeroR oneR plusR mulR) ->
  exists eqR,
  properties.brel_reflexive R eqR /\ 
  properties.brel_symmetric R eqR /\
  properties.brel_transitive R eqR /\ 
  (forall r : R, eqR (plusR zeroR r) r = true) (* zero_left_identity_plus *) /\ 
  (forall r : R, eqR (plusR r zeroR) r = true) (* zero_right_identity_plus *) /\ 
  (forall a b c : R, eqR (plusR a (plusR b c)) 
    (plusR (plusR a b) c) = true) (* plus_associative *) /\ 
  (forall a b : R, eqR (plusR a b) (plusR b a) = true)  (* plus_commutative *) /\ 
  (forall a, eqR (plusR a a) a = true) (* plus_idempotence *) /\ 
  (forall a b c : R, eqR (mulR a (plusR b c)) 
    (plusR (mulR a b) (mulR a c)) = true) (* left_distributive_mul_over_plus *) /\ 
  (forall a b c : R, eqR (mulR (plusR a b) c) 
    (plusR (mulR a c) (mulR b c)) = true) (* right_distributive_mul_over_plus *) /\ 
  (forall a b c : R, eqR (mulR a (mulR b c)) 
    (mulR (mulR a b) c) = true)  (* mul_associative *) /\ 
  (forall r : R, eqR (mulR oneR r) r = true) (* one_left_identity_mul *) /\ 
  (forall r : R, eqR (mulR r oneR) r = true) (* one_right_identity_mul *) /\ 
  (forall a : R, eqR (plusR oneR a) oneR = true) (* multiplicative identity is additive annihilator *)/\ 
  (forall a : R, eqR (mulR zeroR a) zeroR = true) (* zero_left_anhilator_mul *) /\
  (forall a : R, eqR (mulR a zeroR) zeroR = true) (* zero_right_anhilator_mul *).
Proof.
  intros * Ha.
  destruct (A_bs_cas_up_is_error_or_bs R A) as [[l Hl] | [a Hr]].
  rewrite Hl in Ha.
  unfold A_instantiate_matrix_exp_unary in Ha.
  simpl in Ha.
  congruence.
  destruct a.
  destruct A_bs_eqv.
  exists A_eqv_eq.
  destruct A_eqv_proofs.
  split. assumption.
  split. assumption.
  split. assumption.
  split. 
  intros ?.
  simpl in *.
  destruct A_bs_id_ann_proofs.
  destruct A_id_ann_times_plus_d.
  simpl in *.
Admitted.




  