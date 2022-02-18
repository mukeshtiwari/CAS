
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.algorithm.Matrix.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 
Require Import List.
Import ListNotations.
(*
Check matrix_exp_unary.
Check matrix_fixpoint.
*)
Open Scope string_scope.
Open Scope list_scope. 


(* Get rid of this function *)
Definition A_instantiate_matrix_exp_unary (U : Type) 
           (A : A_bs_mcas U)
           (Node : Type)
           (F : finite_set Node) (eqN : brel Node)
  : (Matrix Node U -> nat -> Matrix Node U) + (list string) :=
  let B := A_bs_mcas_cast_up U A in 
  match B with
  | A_BS_Error _ l => inr l 
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
            | inr _ => inr ("Error : the algebra must have a commutative addition" :: nil) 
            end 
          | inr _ => inr ("Error : the algebra is not right distributive" :: nil)
          end 
        | inr _ => inr ("Error : the algebra is not left distributive" :: nil) 
        end 
      | _ => inr ("Error : the multiplicative id must be additive annihilator" :: nil) 
      end
    | _ => inr ("Error : the additive id must be multiplicative annihilator" :: nil)
    end
  | _    => inr ("Internal Error : instantiate_matrix_exp_unary" :: nil) 
  end.
  

Definition A_instantiate_matrix_exp_unary_curry (U : Type) 
  (A : A_bs_mcas U)
  (Node : Type)
  : (finite_set Node -> brel Node -> Matrix Node U -> nat -> Matrix Node U) + (list string) :=
  let B := A_bs_mcas_cast_up U A in 
  match B with
  | A_BS_Error _ l => inr l 
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
    | inl _ => inl (fun (F : finite_set Node) (eqN : brel Node) => 
      matrix_exp_unary Node F eqN U (projT1 zeroP) (projT1 oneP) (A_bs_plus _ A') (A_bs_times _ A')) 
    | inr _ => inr ("Error : the algebra must have a commutative addition" :: nil) 
    end 
  | inr _ => inr ("Error : the algebra is not right distributive" :: nil)
  end 
  | inr _ => inr ("Error : the algebra is not left distributive" :: nil) 
  end 
  | _ => inr ("Error : the multiplicative id must be additive annihilator" :: nil) 
  end
  | _ => inr ("Error : the additive id must be multiplicative annihilator" :: nil)
  end
  | _    => inr ("Internal Error : instantiate_matrix_exp_unary" :: nil) 
  end.

  

(* Change this lemma to reflect new funciton matrix_fixpoint properties *)
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


(* Get rid of this function*)
Definition instantiate_matrix_exp_unary {U : Type} 
           (A : @bs_mcas U)
           (Node : Type)
           (F : finite_set Node) (eqN : brel Node)
  : (Matrix Node U -> nat -> Matrix Node U) + (list string) :=
  let B := bs_mcas_cast_up A in 
  match B with
  | BS_Error l => inr l 
  | BS_bs A' =>
    let bsP := bs_certs A' in
    let eqv := bs_eqv A' in
    let id_annP := bs_id_ann_certs A' in
    match id_ann_plus_times_d id_annP with
    | Id_Ann_Cert_Equal zero =>
      match id_ann_times_plus_d id_annP with
      | Id_Ann_Cert_Equal one =>
        match bs_left_distributive_d bsP with
        | Certify_Left_Distributive =>
          match bs_right_distributive_d bsP with
          | Certify_Right_Distributive =>
            match sg_commutative_d (bs_plus_certs A') with
            | Certify_Commutative =>
              inl (matrix_exp_unary Node F eqN U zero one (bs_plus A') (bs_times A')) 
            | _ => inr ("Error : the algebra must have a commutative addition" :: nil) 
            end 
          | _ => inr ("Error : the algebra is not right distributive" :: nil)
          end 
        | _ => inr ("Error : the algebra is not left distributive" :: nil) 
        end 
      | _ => inr ("Error : the multiplicative id must be additive annihilator" :: nil) 
      end
    | _ => inr ("Error : the additive id must be multiplicative annihilator" :: nil)
    end
  | _    => inr ("Internal Error : instantiate_matrix_exp_unary" :: nil) 
  end.



Definition instantiate_matrix_exp_unary_curry {U : Type} 
           (A : @bs_mcas U) (Node : Type)
  : (finite_set Node -> brel Node -> Matrix Node U -> nat -> Matrix Node U) 
  + (list string) :=
  let B := bs_mcas_cast_up A in 
  match B with
  | BS_Error l => inr l 
  | BS_bs A' =>
    let bsP := bs_certs A' in
    let eqv := bs_eqv A' in
    let id_annP := bs_id_ann_certs A' in
    match id_ann_plus_times_d id_annP with
    | Id_Ann_Cert_Equal zero =>
      match id_ann_times_plus_d id_annP with
      | Id_Ann_Cert_Equal one =>
        match bs_left_distributive_d bsP with
        | Certify_Left_Distributive =>
          match bs_right_distributive_d bsP with
          | Certify_Right_Distributive =>
            match sg_commutative_d (bs_plus_certs A') with
            | Certify_Commutative =>
              inl (fun (F : finite_set Node) (eqN : brel Node) => 
              matrix_exp_unary Node F eqN U zero one (bs_plus A') (bs_times A')) 
            | _ => inr ("Error : the algebra must have a commutative addition" :: nil) 
            end 
          | _ => inr ("Error : the algebra is not right distributive" :: nil)
          end 
        | _ => inr ("Error : the algebra is not left distributive" :: nil) 
        end 
      | _ => inr ("Error : the multiplicative id must be additive annihilator" :: nil) 
      end
    | _ => inr ("Error : the additive id must be multiplicative annihilator" :: nil)
    end
  | _    => inr ("Internal Error : instantiate_matrix_exp_unary" :: nil) 
  end.

  
(* Write a new theorem for the changed functions *)  
Theorem correct_instantiate_matrix_exp_unary {U : Type} 
           (A : A_bs_mcas U)
           (Node : Type)
           (F : finite_set Node) (eqN : brel Node) :
  instantiate_matrix_exp_unary (A2C_mcas_bs _ A) Node F eqN
  =
  A_instantiate_matrix_exp_unary U A Node F eqN. 
Proof. unfold instantiate_matrix_exp_unary, A_instantiate_matrix_exp_unary.
       case_eq(A_bs_cas_up_is_error_or_bs _ A).
       + intros [l J] K. rewrite J. compute. reflexivity. 
       + intros [B J] K. rewrite correct_bs_mcas_cast_up. rewrite J. 
         unfold A2C_mcas_bs; simpl.
         destruct A_bs_id_ann_proofs.
         destruct A_id_ann_plus_times_d; simpl.
         ++ destruct p as [P1 P2]. reflexivity. 
         ++ destruct p as [P1 P2]. reflexivity. 
         ++ destruct p as [P1 P2]. reflexivity. 
         ++ destruct b as [id_ann [P1 P2]].
            destruct A_id_ann_times_plus_d; simpl.
            +++ destruct p as [Q1 Q2]. reflexivity. 
            +++ destruct p as [Q1 Q2]. reflexivity. 
            +++ destruct p as [Q1 Q2]. reflexivity. 
            +++ destruct A_bs_proofs.
                destruct A_bs_left_distributive_d as [LD | [trip1 NLD]];
                  destruct A_bs_right_distributive_d as [RD | [trip2 NRD]]; simpl;
                    try reflexivity.
                destruct A_bs_plus_proofs; simpl. 
                destruct A_sg_commutative_d as [Comm | [[x y] Q]]; simpl. 
                ++++ reflexivity.
                ++++ reflexivity.                                   
            +++ reflexivity.              
         ++ reflexivity. 
Qed.



Record square_matrix (A : Type) := mk_square_matrix {
  size : nat;
  mat : nat -> nat -> A;
  algebra : @bs_mcas A
}.


Fixpoint list_enum (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: list_enum n' 
  end.
  

Definition call_instantiate_matrix_exp_unary_curry (A : Type) (alg : @bs_mcas A) 
  : (square_matrix A -> square_matrix A) + (list string).
  refine(
  let insmat := @instantiate_matrix_exp_unary_curry A alg nat in
  match insmat with
  | inr x => inr x
  | inl mp => inl (fun ms => _)
  end).
  exact (mk_square_matrix _ (size _ ms) 
    (mp (List.rev (list_enum (size _ ms))) Nat.eqb (mat _ ms) (Nat.sub (size _ ms) 1))
    (algebra _ ms)).
Defined.






  


    



