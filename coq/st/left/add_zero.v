Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.tr.left.from_sg.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.tr.left.add_ann.

Require Import List. 
Import ListNotations.

Section Theory.

End Theory.



Section ACAS.

Section Decide.

      


End Decide.

Section Proofs. 

  Context 
    {L S : Type}
    (c : cas_constant)
    (wL : L)
    (wS : S)
    (l : brel L)
    (r : brel S)
    (ltr : ltr_type L S)
    (bop : binary_op S)
    (eqv_l : @eqv_proofs L l)
    (eqv_s : @eqv_proofs S r).



  Lemma slt_add_ann_distributive_decidable :
    slt_distributive_decidable r bop ltr ->
    slt_distributive_decidable 
      (sum.brel_sum brel_constant r) 
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Hb].
    + left.
      unfold slt_distributive in * |- *.
      intros ? [t | t] [u | u];
      simpl.
      ++ reflexivity.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ apply Ha;
         try assumption.
    + right.
      unfold slt_not_distributive in * |- *.
      destruct Hb as ((au, (bu, cu)) & H).
      exists (au, (inr bu, inr cu)).
      exact H.
  Qed.
 


  Lemma slt_add_ann_absorptive_decidable :
    slt_absorptive_decidable r bop ltr ->
    slt_absorptive_decidable 
      (sum.brel_sum brel_constant r) 
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Ha].
    + left.
      unfold slt_absorptive in * |- *.
      intros ? [sa | sa].
      ++ reflexivity.
      ++ apply Ha; try assumption.
    + right.
      unfold slt_not_absorptive in * |- *.
      destruct Ha as ((au, bu) & H).
      exists (au, inr bu).
      exact H.
  Qed.
    
  Lemma slt_add_ann_strictly_absorptive_decidable :
    slt_strictly_absorptive_decidable r bop ltr ->
    slt_strictly_absorptive_decidable 
      (sum.brel_sum brel_constant r)
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Ha].
    + right.
      unfold slt_strictly_absorptive in * |-.
      unfold slt_not_strictly_absorptive.
      exists (wL, inl c);
      simpl.
      right.
      reflexivity.
    + right.
      unfold slt_not_strictly_absorptive in * |- *.
      destruct Ha as ((au, bu) & [Hu | Hu]).
      exists (au, inr bu); simpl.
      left. exact Hu.
      exists (au, inr bu); simpl.
      right. exact Hu.
  Qed.
      



  Lemma slt_add_ann_proof  :
    slt_proofs r bop ltr ->
    slt_proofs (sum.brel_sum brel_constant r) 
    (bop_add_id bop c) 
    (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + apply slt_add_ann_distributive_decidable;
      try assumption.
    + apply slt_add_ann_absorptive_decidable;
      try assumption.
    + apply slt_add_ann_strictly_absorptive_decidable; 
      try assumption.
  Qed.

  Lemma left_dioid_add_ann_proof : 
    left_dioid_proofs r bop ltr ->
    left_dioid_proofs (sum.brel_sum brel_constant r)
      (bop_add_id bop c) (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + unfold slt_distributive in * |- *.
      intros ? [t | t] [u | u];
      simpl.
      ++ reflexivity.
      ++ destruct eqv_s; simpl in *.
        apply A_eqv_reflexive.
      ++ destruct eqv_s; simpl in *.
        apply A_eqv_reflexive.
      ++ apply Ha;
        try assumption.
    + unfold slt_absorptive in * |- *.
      intros ? [sa | sa].
      ++ reflexivity.
      ++ apply Hb; try assumption.
    + apply slt_add_ann_strictly_absorptive_decidable; 
      try assumption.
  Qed.
  

  Lemma left_semiring_add_ann_proofs :
    left_semiring_proofs r bop ltr ->
    left_semiring_proofs (sum.brel_sum brel_constant r)
      (bop_add_id bop c) (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha Hb].
    econstructor.
    + unfold slt_distributive in * |- *.
      intros ? [t | t] [u | u];
      simpl.
      ++ reflexivity.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ apply Ha;
         try assumption.
    + unfold slt_not_absorptive in * |- *.
      destruct Hb as ((au, bu) & H).
      exists (au, inr bu);
      simpl.
      exact H.
  Qed.


End Proofs.

Section Combinators.

  Definition A_slt_add_zero {L S : Type} 
    (A : @A_slt L S) (c : cas_constant) :
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
      ; A_slt_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_label A))
         (A_eqv_eq S (A_slt_carrier A)) (A_slt_trans A) 
         (A_slt_plus A) (A_eqv_proofs S (A_slt_carrier A)) 
         (A_slt_proofs A)                                 
      ; A_slt_ast :=  Cas_ast ("A_slt_add_zero", [A_slt_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_carrier A))).
    intros ?; reflexivity.
  Defined.    



  Definition A_slt_C_add_zero {L S : Type} 
    (A : @A_slt_C L S) (c : cas_constant) :
    @A_slt_C L (with_constant S).
  Proof.
    refine
    {|
        A_slt_C_carrier := A_eqv_add_constant S (A_slt_C_carrier A) c
      ; A_slt_C_label  := A_slt_C_label A
      ; A_slt_C_plus  := bop_add_id (A_slt_C_plus A) c                                             
      ; A_slt_C_trans  := ltr_add_ann_op (A_slt_C_trans A) c
      ; A_slt_C_plus_proofs  := sg_C_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_C_carrier A))
        (structures.A_eqv_new _ (A_slt_C_carrier A))
        (structures.A_eqv_not_trivial _ (A_slt_C_carrier A)) 
        (structures.A_eqv_proofs _ (A_slt_C_carrier A)) 
        (A_slt_C_plus_proofs A)           
      ; A_slt_C_trans_proofs :=  A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_C_carrier A))
          (structures.A_eqv_witness _ (A_slt_C_label A))
          _ _ _ (A_slt_C_trans_proofs A) 
      ; A_slt_C_exists_plus_ann_d := bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_C_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_C_carrier A))) 
         (A_slt_C_exists_plus_ann_d A)                                         
      ; A_slt_C_id_ann_proofs_d := _                                            
      ; A_slt_C_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_C_label A))
         (A_eqv_eq S (A_slt_C_carrier A)) (A_slt_C_trans A) 
         (A_slt_C_plus A) (A_eqv_proofs S (A_slt_C_carrier A)) 
         (A_slt_C_proofs A)                               
      ; A_slt_C_ast := Cas_ast ("A_slt_C_add_zero", [A_slt_C_ast A])
    
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_C_carrier A))).
    intros ?; reflexivity.
  Defined.

  Definition A_slt_CS_add_zero {L S : Type} 
    (A : @A_slt_CS L S) (c : cas_constant) :
    @A_slt_CS L (with_constant S).
  Proof.
    refine
    {|
        A_slt_CS_carrier  := A_eqv_add_constant S (A_slt_CS_carrier A) c
      ; A_slt_CS_label := A_slt_CS_label A
      ; A_slt_CS_plus  := bop_add_id (A_slt_CS_plus A) c                                          
      ; A_slt_CS_trans := ltr_add_ann_op (A_slt_CS_trans A) c 
      ; A_slt_CS_plus_proofs  := sg_CS_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_CS_carrier A))
        (structures.A_eqv_proofs _ (A_slt_CS_carrier A)) 
        (A_slt_CS_plus_proofs A)        
      ; A_slt_CS_trans_proofs  := A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_CS_carrier A))
          (structures.A_eqv_witness _ (A_slt_CS_label A))
          _ _ _ (A_slt_CS_trans_proofs A) 
      ; A_slt_CS_exists_plus_ann_d := bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_CS_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_CS_carrier A))) 
         (A_slt_CS_exists_plus_ann_d A)                                   
      ; A_slt_CS_id_ann_proofs_d  := _                                    
      ; A_slt_CS_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_CS_label A))
         (A_eqv_eq S (A_slt_CS_carrier A)) (A_slt_CS_trans A) 
         (A_slt_CS_plus A) (A_eqv_proofs S (A_slt_CS_carrier A)) 
         (A_slt_CS_proofs A)                               
      ; A_slt_CS_ast := Cas_ast ("A_slt_CS_add_zero", [A_slt_CS_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_CS_carrier A))).
    intros ?; reflexivity.
  Defined.
    

  Definition A_slt_CI_add_zero {L S : Type} 
    (A : @A_slt_CI L S) (c : cas_constant) :
    @A_slt_CI L (with_constant S).
  Proof.
    refine
    {|
        A_slt_CI_carrier  := A_eqv_add_constant S (A_slt_CI_carrier A) c
      ; A_slt_CI_label := A_slt_CI_label A
      ; A_slt_CI_plus  := bop_add_id (A_slt_CI_plus A) c                                          
      ; A_slt_CI_trans := ltr_add_ann_op (A_slt_CI_trans A) c 
      ; A_slt_CI_plus_proofs  := sg_CI_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_CI_carrier A))
        (structures.A_eqv_proofs _ (A_slt_CI_carrier A)) 
        (A_slt_CI_plus_proofs A)        
      ; A_slt_CI_trans_proofs  := A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_CI_carrier A))
          (structures.A_eqv_witness _ (A_slt_CI_label A))
          _ _ _ (A_slt_CI_trans_proofs A) 
      ; A_slt_CI_exists_plus_ann_d := bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_CI_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_CI_carrier A))) 
         (A_slt_CI_exists_plus_ann_d A)                                   
      ; A_slt_CI_id_ann_proofs_d  := _                                    
      ; A_slt_CI_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_CI_label A))
         (A_eqv_eq S (A_slt_CI_carrier A)) (A_slt_CI_trans A) 
         (A_slt_CI_plus A) (A_eqv_proofs S (A_slt_CI_carrier A)) 
         (A_slt_CI_proofs A)                               
      ; A_slt_CI_ast := Cas_ast ("A_slt_CI_add_zero", [A_slt_CI_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_CI_carrier A))).
    intros ?; reflexivity.
  Defined.


  Definition A_slt_C_zero_is_ltr_ann_add_zero {L S : Type} 
    (A : @A_slt_C_zero_is_ltr_ann L S) (c : cas_constant) :
    @A_slt_C_zero_is_ltr_ann L (with_constant S).
  Proof.
    refine
    {|
        A_slt_C_zero_is_ltr_ann_carrier  := 
          A_eqv_add_constant S (A_slt_C_zero_is_ltr_ann_carrier A) c
      ; A_slt_C_zero_is_ltr_ann_label  := 
          A_slt_C_zero_is_ltr_ann_label A
      ; A_slt_C_zero_is_ltr_ann_plus  :=  
          bop_add_id (A_slt_C_zero_is_ltr_ann_plus A) c                               
      ; A_slt_C_zero_is_ltr_ann_trans   := 
          ltr_add_ann_op (A_slt_C_zero_is_ltr_ann_trans A) c 
      ; A_slt_C_zero_is_ltr_ann_plus_proofs  := 
          sg_C_proofs_add_id S _ c _ 
            (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier A))
            (structures.A_eqv_new _ (A_slt_C_zero_is_ltr_ann_carrier A))
            (structures.A_eqv_not_trivial _ (A_slt_C_zero_is_ltr_ann_carrier A)) 
            (structures.A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier A)) 
            (A_slt_C_zero_is_ltr_ann_plus_proofs A)        
      ; A_slt_C_zero_is_ltr_ann_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier A))
          (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_label A))
          _ _ _ (A_slt_C_zero_is_ltr_ann_trans_proofs A) 
      ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d :=  
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier A))) 
         (A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A)                                    
      ; A_slt_C_zero_is_ltr_ann_id_ann_proofs  :=   _                                          
      ; A_slt_C_zero_is_ltr_ann_proofs :=  
          slt_add_ann_proof c (A_eqv_witness L (A_slt_C_zero_is_ltr_ann_label A))
         (A_eqv_eq S (A_slt_C_zero_is_ltr_ann_carrier A)) 
         (A_slt_C_zero_is_ltr_ann_trans A) 
         (A_slt_C_zero_is_ltr_ann_plus A) 
         (A_eqv_proofs S (A_slt_C_zero_is_ltr_ann_carrier A)) 
         (A_slt_C_zero_is_ltr_ann_proofs A)                                 
      ; A_slt_C_zero_is_ltr_ann_ast := 
          Cas_ast ("A_slt_C_zero_is_ltr_ann_add_zero", 
            [A_slt_C_zero_is_ltr_ann_ast A])
    |}.
    
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier A))).
    intros ?; reflexivity.
  Defined.


  Definition A_selective_left_pre_dioid_add_zero {L S : Type} 
    (A : @A_selective_left_pre_dioid L S) (c : cas_constant) :
    @A_selective_left_pre_dioid L (with_constant S).
  Proof.
    refine
    {|
        A_selective_left_pre_dioid_carrier  := 
          A_eqv_add_constant S (A_selective_left_pre_dioid_carrier A) c
      ; A_selective_left_pre_dioid_label := 
         A_selective_left_pre_dioid_label A
      ; A_selective_left_pre_dioid_plus :=  
          bop_add_id (A_selective_left_pre_dioid_plus A) c                                           
      ; A_selective_left_pre_dioid_trans  := 
          ltr_add_ann_op (A_selective_left_pre_dioid_trans A) c 
      ; A_selective_left_pre_dioid_plus_proofs  := 
          sg_CS_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_selective_left_pre_dioid_carrier A))
          (structures.A_eqv_proofs _ (A_selective_left_pre_dioid_carrier A)) 
          (A_selective_left_pre_dioid_plus_proofs A)      
      ; A_selective_left_pre_dioid_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_selective_left_pre_dioid_carrier A))
          (structures.A_eqv_witness _ (A_selective_left_pre_dioid_label A))
          _ _ _ (A_selective_left_pre_dioid_trans_proofs A) 
      ; A_selective_left_pre_dioid_exists_plus_ann := 
          bop_add_id_exists_ann S
         (A_eqv_eq S (A_selective_left_pre_dioid_carrier A)) c
         (A_selective_left_pre_dioid_plus A)
         (A_eqv_reflexive S
            (A_eqv_eq S (A_selective_left_pre_dioid_carrier A))
            (A_eqv_proofs S (A_selective_left_pre_dioid_carrier A)))
         (A_selective_left_pre_dioid_exists_plus_ann A)
      ; A_selective_left_pre_dioid_id_ann_proofs_d := _                        
      ; A_selective_left_pre_dioid_proofs :=  
          left_dioid_add_ann_proof c
         (A_eqv_witness L (A_selective_left_pre_dioid_label A))
         (A_eqv_eq S (A_selective_left_pre_dioid_carrier A))
         (A_selective_left_pre_dioid_trans A)
         (A_selective_left_pre_dioid_plus A)
         (A_eqv_proofs S (A_selective_left_pre_dioid_carrier A))
         (A_selective_left_pre_dioid_proofs A)                                
      ; A_selective_left_pre_dioid_ast := 
          Cas_ast ("A_selective_left_pre_dioid_add_zero", 
            [A_selective_left_pre_dioid_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_selective_left_pre_dioid_carrier A))).
    intros ?; reflexivity.
  Defined.


   Definition A_selective_left_dioid_add_zero {L S : Type} 
    (A : @A_selective_left_dioid L S) (c : cas_constant) :
    @A_selective_left_dioid L (with_constant S).
  Proof.
    refine
    {|
        A_selective_left_dioid_carrier  := 
          A_eqv_add_constant S (A_selective_left_dioid_carrier A) c
      ; A_selective_left_dioid_label := 
         A_selective_left_dioid_label A
      ; A_selective_left_dioid_plus :=  
          bop_add_id (A_selective_left_dioid_plus A) c                                           
      ; A_selective_left_dioid_trans  := 
          ltr_add_ann_op (A_selective_left_dioid_trans A) c 
      ; A_selective_left_dioid_plus_proofs  := 
          sg_CS_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_selective_left_dioid_carrier A))
          (structures.A_eqv_proofs _ (A_selective_left_dioid_carrier A)) 
          (A_selective_left_dioid_plus_proofs A)      
      ; A_selective_left_dioid_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_selective_left_dioid_carrier A))
          (structures.A_eqv_witness _ (A_selective_left_dioid_label A))
          _ _ _ (A_selective_left_dioid_trans_proofs A) 
      ; A_selective_left_dioid_exists_plus_ann := 
          bop_add_id_exists_ann S
         (A_eqv_eq S (A_selective_left_dioid_carrier A)) c
         (A_selective_left_dioid_plus A)
         (A_eqv_reflexive S
            (A_eqv_eq S (A_selective_left_dioid_carrier A))
            (A_eqv_proofs S (A_selective_left_dioid_carrier A)))
         (A_selective_left_dioid_exists_plus_ann A)
      ; A_selective_left_dioid_id_ann_proofs := _                        
      ; A_selective_left_dioid_proofs :=  
          left_dioid_add_ann_proof c
         (A_eqv_witness L (A_selective_left_dioid_label A))
         (A_eqv_eq S (A_selective_left_dioid_carrier A))
         (A_selective_left_dioid_trans A)
         (A_selective_left_dioid_plus A)
         (A_eqv_proofs S (A_selective_left_dioid_carrier A))
         (A_selective_left_dioid_proofs A)                                
      ; A_selective_left_dioid_ast := 
          Cas_ast ("A_selective_left_dioid_add_zero", 
            [A_selective_left_dioid_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_selective_left_dioid_carrier A))).
    intros ?; reflexivity.
  Defined.

  Definition A_left_dioid_add_zero {L S : Type} 
    (A : @A_left_dioid L S) (c : cas_constant) :
    @A_left_dioid L (with_constant S).
  Proof.
    refine
    {|
        A_left_dioid_carrier  := 
          A_eqv_add_constant S (A_left_dioid_carrier A) c
      ; A_left_dioid_label := 
         A_left_dioid_label A
      ; A_left_dioid_plus :=  
          bop_add_id (A_left_dioid_plus A) c                                           
      ; A_left_dioid_trans  := 
          ltr_add_ann_op (A_left_dioid_trans A) c 
      ; A_left_dioid_plus_proofs  := 
          sg_CI_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_dioid_carrier A))
          (structures.A_eqv_proofs _ (A_left_dioid_carrier A)) 
          (A_left_dioid_plus_proofs A)      
      ; A_left_dioid_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_dioid_carrier A))
          (structures.A_eqv_witness _ (A_left_dioid_label A))
          _ _ _ (A_left_dioid_trans_proofs A) 
      ; A_left_dioid_exists_plus_ann := 
          bop_add_id_exists_ann S
         (A_eqv_eq S (A_left_dioid_carrier A)) c
         (A_left_dioid_plus A)
         (A_eqv_reflexive S
            (A_eqv_eq S (A_left_dioid_carrier A))
            (A_eqv_proofs S (A_left_dioid_carrier A)))
         (A_left_dioid_exists_plus_ann A)
      ; A_left_dioid_id_ann_proofs := _                        
      ; A_left_dioid_proofs :=  
          left_dioid_add_ann_proof c
         (A_eqv_witness L (A_left_dioid_label A))
         (A_eqv_eq S (A_left_dioid_carrier A))
         (A_left_dioid_trans A)
         (A_left_dioid_plus A)
         (A_eqv_proofs S (A_left_dioid_carrier A))
         (A_left_dioid_proofs A)                                
      ; A_left_dioid_ast := 
          Cas_ast ("A_left_dioid_add_zero", 
            [A_left_dioid_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_dioid_carrier A))).
    intros ?; reflexivity.
  Defined.

  Definition A_left_pre_semring_add_zero {L S : Type} 
    (A : @A_left_pre_semiring L S) (c : cas_constant) :
    @A_left_pre_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_pre_semiring_carrier   := 
          A_eqv_add_constant S (A_left_pre_semiring_carrier A) c
      ; A_left_pre_semiring_label   :=  
          A_left_pre_semiring_label A
      ; A_left_pre_semiring_plus   := 
          bop_add_id (A_left_pre_semiring_plus A) c                                                
      ; A_left_pre_semiring_trans  := 
          ltr_add_ann_op (A_left_pre_semiring_trans A) c 
      ; A_left_pre_semiring_plus_proofs := 
          sg_C_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_pre_semiring_carrier A))
          (structures.A_eqv_new _ (A_left_pre_semiring_carrier A))
          (structures.A_eqv_not_trivial _ (A_left_pre_semiring_carrier A)) 
          (structures.A_eqv_proofs _ (A_left_pre_semiring_carrier A)) 
          (A_left_pre_semiring_plus_proofs A)                                 
      ; A_left_pre_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_pre_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_pre_semiring_label A))
          _ _ _ (A_left_pre_semiring_trans_proofs A)
      ; A_left_pre_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_pre_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_pre_semiring_carrier A))) 
         (A_left_pre_semiring_exists_plus_ann_d A)                          
      ; A_left_pre_semiring_id_ann_proofs_d := _ 
      ; A_left_pre_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_pre_semiring_carrier A))
         (A_left_pre_semiring_trans A) (A_left_pre_semiring_plus A)
         (A_eqv_proofs S (A_left_pre_semiring_carrier A))
         (A_left_pre_semiring_proofs A)
      ; A_left_pre_semiring_ast := 
          Cas_ast ("A_left_pre_semiring_add_zero", 
            [A_left_pre_semiring_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_pre_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.


  Definition A_left_semring_add_zero {L S : Type} 
    (A : @A_left_semiring L S) (c : cas_constant) :
    @A_left_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_semiring_carrier   := 
          A_eqv_add_constant S (A_left_semiring_carrier A) c
      ; A_left_semiring_label   :=  
          A_left_semiring_label A
      ; A_left_semiring_plus   := 
          bop_add_id (A_left_semiring_plus A) c                                                
      ; A_left_semiring_trans  := 
          ltr_add_ann_op (A_left_semiring_trans A) c 
      ; A_left_semiring_plus_proofs := 
          sg_C_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_semiring_carrier A))
          (structures.A_eqv_new _ (A_left_semiring_carrier A))
          (structures.A_eqv_not_trivial _ (A_left_semiring_carrier A)) 
          (structures.A_eqv_proofs _ (A_left_semiring_carrier A)) 
          (A_left_semiring_plus_proofs A)                                 
      ; A_left_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_semiring_label A))
          _ _ _ (A_left_semiring_trans_proofs A)
      ; A_left_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_semiring_carrier A))) 
         (A_left_semiring_exists_plus_ann_d A)                          
      ; A_left_semiring_id_ann_proofs:= _ 
      ; A_left_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_semiring_carrier A))
         (A_left_semiring_trans A) (A_left_semiring_plus A)
         (A_eqv_proofs S (A_left_semiring_carrier A))
         (A_left_semiring_proofs A)
      ; A_left_semiring_ast := 
          Cas_ast ("A_left_semiring_add_zero", 
            [A_left_semiring_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.

  

  











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


