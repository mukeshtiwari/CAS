
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.algorithm.Matrix.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 
Check matrix_exp_unary.
Check matrix_fixpoint.

Open Scope string_scope.

Definition A_instantiate_matrix_exp_unary (S : Type) 
           (A : A_bs_mcas S)
           (Node : Type)
           (F : finite_set Node) (eqN : brel Node)
  : (Matrix Node S -> nat -> Matrix Node S) + string :=
  match A_bs_mcas_cast_up _ A with
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
            | inl _ => inl (matrix_exp_unary Node F eqN S (projT1 zeroP) (projT1 oneP) (A_bs_plus _ A') (A_bs_times _ A')) 
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

(* 
Check matrix_fixpoint.
Theorem test (S : Type) 
           (A : A_bs_mcas S)
           (Node : Type)
           (F : finite_set Node) (eqN : brel Node)
           (MM : Matrix Node S -> nat -> Matrix Node S): 
  A_instantiate_matrix_exp_unary S A Node F eqN = inl MM ->
  I can instantiate matrix_fixpoint.
*)   
               
                                                                 

