Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 
Require Import CAS.coq.eqv.add_constant.

Require Import CAS.coq.tr.left.from_sg.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.tr.left.add_ann.


Section Theory.

End Theory.



Section ACAS.

Section Decide.

      


End Decide.

Section Proofs. 

  Lemma slt_add_ann_proof 
      {L S : Type} (c : cas_constant) 
      (r : brel S) (bop : binary_op S)
      (ltr : ltr_type L S) :
      slt_proofs r bop ltr ->
      slt_proofs (sum.brel_sum brel_constant r) 
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [[Hd | Hnd] [Ha | Hna] [Hsa | Hnsa]].
    econstructor.
    left.
    intros ? [Ht | Ht] [Hu | Hu];
    simpl; try reflexivity.
    admit.
    admit.
    apply Hd.
  Admitted.


End Proofs.

Section Combinators.

  Definition A_slt_add_zero {L S : Type} (A : @A_slt L S) (c : cas_constant) :
    @A_slt L (with_constant S).
  Proof.
    refine 
    {|
        A_slt_carrier := A_eqv_add_constant S (A_slt_carrier A) c
      ; A_slt_label  := A_slt_label A
      ; A_slt_plus  := bop_add_id (A_slt_plus A) c                                        
      ; A_slt_trans  := ltr_add_ann_op (A_slt_trans A) c
      ; A_slt_plus_proofs := sg_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_carrier A))
        (structures.A_eqv_new _ (A_slt_carrier A))
        (structures.A_eqv_not_trivial _ (A_slt_carrier A)) 
        (structures.A_eqv_proofs _ (A_slt_carrier A)) 
        (A_slt_plus_proofs A)           
      ; A_slt_trans_proofs := A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_carrier A))
          (structures.A_eqv_witness _ (A_slt_label A))
          _ _ _ (A_slt_trans_proofs A) 
      ; A_slt_exists_plus_ann_d :=  bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_carrier A))) 
         (A_slt_exists_plus_ann_d A)                                  
      ; A_slt_id_ann_proofs_d  := _                                               
      ; A_slt_proofs := _                                 
      ; A_slt_ast := _  
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_carrier A))).
    intros ?; reflexivity.

    destruct A; simpl in * |- *.
    destruct A_slt_carrier; simpl in * |- *.
    Print slt_proofs.



  Definition A_slt_C_add_zero {L S : Type} (A : @A_slt_C L S) (c : cas_constant) :
    @A_slt_C L (with_constant S).
  Proof.
  Admitted.



End Combinators.   
End ACAS.

Section AMCAS.

Open Scope string_scope.   

Definition A_mcas_slt_add_zero {L S : Type}
  (A : @A_slt_mcas L S) (c : cas_constant) : @A_slt_mcas L (with_constant S).
Proof.
  refine 
    match A with 

  

Definition A_mcas_bs_add_zero (S : Type) (A : A_bs_mcas S) (c : cas_constant) := 
  match (A_bs_mcas_cast_up _ A) with
  | A_BS_bs _ B => A_bs_classify _ (A_BS_bs _ (A_bs_add_zero _ B c))
  | A_BS_Error _ str => A_BS_Error _ str                                                                                      
  | _ => A_BS_Error _ ("internal error : A_bs_mcas_add_zero" :: nil) 
  end.

End AMCAS. 


Section CAS.

Section Certify.
    


End Certify.

Section Certificates.



End Certificates.   

Section Combinators.


End Combinators.   
End CAS.


Section MCAS. 

Open Scope string_scope.
  
Definition mcas_bs_add_zero {S : Type} (A : @bs_mcas S) (c : cas_constant) := 
  match (bs_mcas_cast_up A) with
  | BS_bs B => bs_classify (BS_bs (bs_add_zero B c))
  | BS_Error str => BS_Error str                                                                                      
  | _ => BS_Error ("internal error : A_bs_mcas_add_zero" :: nil) 
  end.

End MCAS. 




Section Verify.



Section Certify.

End Certify.

Section Combinators. 

End Combinators. 

End Verify.   


