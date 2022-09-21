Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import
        CAS.coq.algorithms.matrix_definition 
        CAS.coq.algorithms.matrix_algorithms. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 
Require Import List. 
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope. 


Definition A_bs_instantiate_matrix_exp_curry (U : Type) 
           (A : A_bs_mcas U) : (nat -> functional_matrix U -> nat -> functional_matrix U) + (list string) :=
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
            | inl _ => inl (fun (n : nat) =>
                            fun (m : functional_matrix U) =>
                            fun (k : nat) => 
                              matrix_exp (projT1 zeroP) (projT1 oneP) (A_bs_plus _ A') (A_bs_times _ A') n m k)
                             
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



Definition bs_instantiate_matrix_exp_curry {U : Type} 
           (A : @bs_mcas U) : (nat -> functional_matrix U -> nat -> functional_matrix U) + (list string) :=           
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
              inl (fun (n : nat) => 
                   fun (m : functional_matrix U) => 
                   fun (k : nat) => matrix_exp zero one (bs_plus A') (bs_times A') n m k) 
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


Theorem correct_instantiate_matrix_exp_unary_curry {U : Type} 
    (A : A_bs_mcas U) :
  bs_instantiate_matrix_exp_curry (A2C_mcas_bs _ A)
  =
  A_bs_instantiate_matrix_exp_curry U A. 
Proof. unfold bs_instantiate_matrix_exp_curry, A_bs_instantiate_matrix_exp_curry.
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
  
Fixpoint list_enum (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: list_enum n' 
  end.
  
Definition bs_instantiate_matrix_exp_square_matrix {U : Type} (A : @bs_mcas U) 
  : (nat -> nat -> @square_matrix U -> @square_matrix U) + (list string) := 
  match bs_instantiate_matrix_exp_curry A with
  | inr x => inr x
  | inl mp => inl (fun n k sqm => 
                     {|
                         sqm_size              := sqm_size sqm
                       ; sqm_functional_matrix := mp n (sqm_functional_matrix sqm) k 
                     |})
                  
  end.







  


    



