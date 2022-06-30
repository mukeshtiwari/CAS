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



  Definition A_left_pre_semiring_add_zero {L S : Type} 
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


  Definition A_left_semiring_add_zero {L S : Type} 
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




  Definition A_left_idempotent_semiring_add_zero {L S : Type} 
    (A : @A_left_idempotent_semiring L S) (c : cas_constant) :
    @A_left_idempotent_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_idempotent_semiring_carrier   := 
          A_eqv_add_constant S (A_left_idempotent_semiring_carrier A) c
      ; A_left_idempotent_semiring_label   :=  
          A_left_idempotent_semiring_label A
      ; A_left_idempotent_semiring_plus   := 
          bop_add_id (A_left_idempotent_semiring_plus A) c                                                
      ; A_left_idempotent_semiring_trans  := 
          ltr_add_ann_op (A_left_idempotent_semiring_trans A) c 
      ; A_left_idempotent_semiring_plus_proofs := 
          sg_CI_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_idempotent_semiring_carrier A))
          (structures.A_eqv_proofs _ (A_left_idempotent_semiring_carrier A)) 
          (A_left_idempotent_semiring_plus_proofs A)        
      ; A_left_idempotent_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_idempotent_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_idempotent_semiring_label A))
          _ _ _ (A_left_idempotent_semiring_trans_proofs A)
      ; A_left_idempotent_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_idempotent_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_idempotent_semiring_carrier A))) 
         (A_left_idempotent_semiring_exists_plus_ann_d A)                          
      ; A_left_idempotent_semiring_id_ann_proofs:= _ 
      ; A_left_idempotent_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
         (A_left_idempotent_semiring_trans A) (A_left_idempotent_semiring_plus A)
         (A_eqv_proofs S (A_left_idempotent_semiring_carrier A))
         (A_left_idempotent_semiring_proofs A)
      ; A_left_idempotent_semiring_ast := 
          Cas_ast ("A_left_idempotent_semiring_add_zero", 
            [A_left_idempotent_semiring_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_idempotent_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.

  
  

  Definition A_left_selective_semiring_add_zero {L S : Type} 
    (A : @A_left_selective_semiring L S) (c : cas_constant) :
    @A_left_selective_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_selective_semiring_carrier   := 
          A_eqv_add_constant S (A_left_selective_semiring_carrier A) c
      ; A_left_selective_semiring_label   :=  
          A_left_selective_semiring_label A
      ; A_left_selective_semiring_plus   := 
          bop_add_id (A_left_selective_semiring_plus A) c                                                
      ; A_left_selective_semiring_trans  := 
          ltr_add_ann_op (A_left_selective_semiring_trans A) c 
      ; A_left_selective_semiring_plus_proofs := 
          sg_CS_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_selective_semiring_carrier A))
          (structures.A_eqv_proofs _ (A_left_selective_semiring_carrier A)) 
          (A_left_selective_semiring_plus_proofs A)                                  
      ; A_left_selective_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_selective_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_selective_semiring_label A))
          _ _ _ (A_left_selective_semiring_trans_proofs A)
      ; A_left_selective_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_selective_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_selective_semiring_carrier A))) 
         (A_left_selective_semiring_exists_plus_ann_d A)                          
      ; A_left_selective_semiring_id_ann_proofs:= _ 
      ; A_left_selective_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_selective_semiring_carrier A))
         (A_left_selective_semiring_trans A) (A_left_selective_semiring_plus A)
         (A_eqv_proofs S (A_left_selective_semiring_carrier A))
         (A_left_selective_semiring_proofs A)
      ; A_left_selective_semiring_ast := 
          Cas_ast ("A_left_selective_semiring_add_zero", 
            [A_left_selective_semiring_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_selective_semiring_carrier A))).
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
    | A_SLT_Error ls => A_SLT_Error ls
    | A_SLT slt => A_slt_classify_slt  (A_slt_add_zero slt c)
    | A_SLT_C slt => A_slt_C_classify_slt (A_slt_C_add_zero slt c) 
    | A_SLT_CS slt => A_slt_CS_classify_slt (A_slt_CS_add_zero slt c)
    | A_SLT_CI slt => A_slt_CI_classify_slt (A_slt_CI_add_zero  slt c)
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_slt_C_zero_is_ltr_ann_classify_slt (A_slt_C_zero_is_ltr_ann_add_zero slt c)
    | A_SLT_Left_Pre_Semiring slt => 
        A_slt_classify_left_pre_semiring_slt (A_left_pre_semiring_add_zero slt c)
    | A_SLT_Dioid slt => 
        A_slt_classify_left_dioid_slt (A_left_dioid_add_zero slt c)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_slt_classify_selective_left_pre_dioid_slt (A_selective_left_pre_dioid_add_zero  slt c)
    | A_SLT_Semiring slt => 
        A_slt_classify_left_semiring_slt  (A_left_semiring_add_zero slt c) 
    | A_SLT_Selective_Dioid slt => 
        A_slt_classify_selective_left_dioid_slt (A_selective_left_dioid_add_zero slt c) 
    | A_SLT_Selective_Semiring slt => 
        A_slt_classify_left_selective_semiring_slt (A_left_selective_semiring_add_zero  slt c)
    | A_SLT_Idempotent_Semiring slt => 
        A_slt_classify_left_idempotent_semiring_slt (A_left_idempotent_semiring_add_zero slt c) 
    end.
Defined.


End AMCAS. 


Section CAS.

Section Certify.
    
  Context 
    {L S : Type}
    (c : cas_constant)
    (wL : L)
    (wS : S)
    (l : brel L)
    (r : brel S)
    (ltr : ltr_type L S)
    (bop : binary_op S).

 
  Lemma slt_add_ann_distributive_check :
    @check_slt_distributive L S ->
    @check_slt_distributive L (with_constant S).
  Proof.
    intros Ha.
    destruct Ha eqn:H.
    + apply Certify_Slt_Distributive.
    + apply Certify_Slt_Not_Distributive.
      destruct p as (au, (bu, cu)).  
      exact (au, (inr bu, inr cu)).
  Defined.
  
 


  Lemma slt_add_ann_absorptive_check :
    @check_slt_absorptive L S ->
    @check_slt_absorptive L (with_constant S). 
  Proof.
    intros Ha.
    case Ha eqn:H.
    + apply Certify_Slt_Absorptive.
    + apply Certify_Slt_Not_Absorptive.
      destruct p as (au, bu).
      exact (au, inr bu).
  Defined.  

    
  Lemma slt_add_ann_strictly_absorptive_check :
    @check_slt_strictly_absorptive L S ->
    @check_slt_strictly_absorptive L (with_constant S).
  Proof.
    intros Ha.
    case Ha eqn:H.
    + apply Certify_Slt_Strictly_Absorptive.
    + apply Certify_Slt_Not_Strictly_Absorptive.
      destruct p as (au, bu).
      exact (au, inr bu).
  Defined.
  


 
  Lemma slt_add_ann_certificate  :
    @slt_certificates L S ->
    @slt_certificates L (with_constant S).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + exact (slt_add_ann_distributive_check Ha).
    + exact (slt_add_ann_absorptive_check Hb).
    + exact (slt_add_ann_strictly_absorptive_check Hc).
  Defined.   

  

  Lemma left_dioid_add_ann_certificate : 
    @left_dioid_certificates L S -> 
    @left_dioid_certificates L (with_constant S).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + exact Assert_Slt_Distributive.
    + exact Assert_Slt_Absorptive.
    + exact (slt_add_ann_strictly_absorptive_check Hc).
  Defined.   
   

  Lemma left_semiring_add_ann_certificate :
    @left_semiring_certificates L S ->
    @left_semiring_certificates L (with_constant S). 
  Proof.
    intros [Ha Hb].
    econstructor.
    + exact Assert_Slt_Distributive.
    + case Hb eqn:H.
      destruct p as (au, av).
      exact (Assert_Slt_Not_Absorptive (au, inr av)).
  Defined.
  
End Certify.

Section Certificates.



End Certificates.   

Section Combinators.

  Definition slt_add_zero {L S : Type} 
    (A : @slt L S) (c : cas_constant) :
    @slt L (with_constant S).
  Proof.
    refine 
    {|
        slt_carrier := eqv_add_constant (slt_carrier A) c
      ; slt_label  := slt_label A
      ; slt_plus  := bop_add_id (slt_plus A) c                                        
      ; slt_trans  := ltr_add_ann_op (slt_trans A) c
      ; slt_plus_certs := sg_certs_add_id c
          (structures.eqv_witness (slt_carrier A))
          (structures.eqv_new (slt_carrier A))
          (slt_plus_certs A)    
      ; slt_trans_certs := ltr_add_ann_certs c 
          (structures.eqv_witness (slt_carrier A))
          (structures.eqv_witness (slt_label A))
          (slt_trans_certs A)
      ; slt_exists_plus_ann_d := @bop_add_id_exists_ann_check S 
          (slt_exists_plus_ann_d A)                          
      ; slt_id_ann_certs_d  := Certify_SLT_Id_Ann_Proof_Equal (inl c)                                              
      ; slt_certs := slt_add_ann_certificate (slt_certs A)                          
      ; slt_ast :=  Cas_ast ("A_slt_add_zero", [slt_ast A])
    |}.
  Defined.

  Definition slt_C_add_zero {L S : Type} 
    (A : @slt_C L S) (c : cas_constant) :
    @slt_C L (with_constant S).
  Proof.
    refine
    {|
        slt_C_carrier := eqv_add_constant (slt_C_carrier A) c
      ; slt_C_label  := slt_C_label A
      ; slt_C_plus  := bop_add_id (slt_C_plus A) c                                             
      ; slt_C_trans  := ltr_add_ann_op (slt_C_trans A) c
      ; slt_C_plus_certs  := sg_C_certs_add_id c
          (structures.eqv_witness (slt_C_carrier A))
          (structures.eqv_new (slt_C_carrier A))
          (slt_C_plus_certs A)
      ; slt_C_trans_certs :=  ltr_add_ann_certs c
          (structures.eqv_witness (slt_C_carrier A))
          (structures.eqv_witness (slt_C_label A))
          (slt_C_trans_certs A) 
      ; slt_C_exists_plus_ann_d :=  @bop_add_id_exists_ann_check S 
         (slt_C_exists_plus_ann_d A)                                         
      ; slt_C_id_ann_certs_d :=  Certify_SLT_Id_Ann_Proof_Equal (inl c)                                             
      ; slt_C_certs := slt_add_ann_certificate (slt_C_certs A)                             
      ; slt_C_ast := Cas_ast ("A_slt_C_add_zero", [slt_C_ast A])
    
    |}.
  Defined.

  Definition slt_CS_add_zero {L S : Type} 
    (A : @slt_CS L S) (c : cas_constant) :
    @slt_CS L (with_constant S).
  Proof.
    refine
    {|
        slt_CS_carrier  := eqv_add_constant (slt_CS_carrier A) c
      ; slt_CS_label := slt_CS_label A
      ; slt_CS_plus  := bop_add_id (slt_CS_plus A) c                                          
      ; slt_CS_trans := ltr_add_ann_op (slt_CS_trans A) c 
      ; slt_CS_plus_certs  := sg_CS_certs_add_id c 
        (slt_CS_plus_certs A)        
      ; slt_CS_trans_certs  := ltr_add_ann_certs c
          (structures.eqv_witness (slt_CS_carrier A))
          (structures.eqv_witness (slt_CS_label A))
          (slt_CS_trans_certs A) 
      ; slt_CS_exists_plus_ann_d :=  @bop_add_id_exists_ann_check S 
         (slt_CS_exists_plus_ann_d A)                                   
      ; slt_CS_id_ann_certs_d  :=  Certify_SLT_Id_Ann_Proof_Equal (inl c)                                     
      ; slt_CS_certs := slt_add_ann_certificate (slt_CS_certs A)                             
      ; slt_CS_ast := Cas_ast ("A_slt_CS_add_zero", [slt_CS_ast A])
    |}.
  Defined.




  Definition slt_CI_add_zero {L S : Type} 
    (A : @slt_CI L S) (c : cas_constant) :
    @slt_CI L (with_constant S).
  Proof.
    refine
    {|
        slt_CI_carrier  := eqv_add_constant (slt_CI_carrier A) c
      ; slt_CI_label := slt_CI_label A
      ; slt_CI_plus  := bop_add_id (slt_CI_plus A) c                                          
      ; slt_CI_trans := ltr_add_ann_op (slt_CI_trans A) c 
      ; slt_CI_plus_certs  := sg_CI_certs_add_id c 
        (slt_CI_plus_certs A)        
      ; slt_CI_trans_certs  := ltr_add_ann_certs c
          (structures.eqv_witness (slt_CI_carrier A))
          (structures.eqv_witness (slt_CI_label A))
          (slt_CI_trans_certs A) 
      ; slt_CI_exists_plus_ann_d :=  @bop_add_id_exists_ann_check S 
         (slt_CI_exists_plus_ann_d A)                                   
      ; slt_CI_id_ann_certs_d  :=  Certify_SLT_Id_Ann_Proof_Equal (inl c)                                     
      ; slt_CI_certs := slt_add_ann_certificate (slt_CI_certs A)                             
      ; slt_CI_ast := Cas_ast ("A_slt_CS_add_zero", [slt_CI_ast A])
    |}.
  Defined.

  


  Definition slt_C_zero_is_ltr_ann_add_zero {L S : Type} 
    (A : @slt_C_zero_is_ltr_ann L S) (c : cas_constant) :
    @slt_C_zero_is_ltr_ann L (with_constant S).
  Proof.
    refine
    {|
        slt_C_zero_is_ltr_ann_carrier  := 
          eqv_add_constant (slt_C_zero_is_ltr_ann_carrier A) c
      ; slt_C_zero_is_ltr_ann_label  := 
          slt_C_zero_is_ltr_ann_label A
      ; slt_C_zero_is_ltr_ann_plus  :=  
          bop_add_id (slt_C_zero_is_ltr_ann_plus A) c                               
      ; slt_C_zero_is_ltr_ann_trans   := 
          ltr_add_ann_op (slt_C_zero_is_ltr_ann_trans A) c 
      ; slt_C_zero_is_ltr_ann_plus_certs  := 
          sg_C_certs_add_id c 
            (structures.eqv_witness (slt_C_zero_is_ltr_ann_carrier A))
            (structures.eqv_new (slt_C_zero_is_ltr_ann_carrier A))
            (slt_C_zero_is_ltr_ann_plus_certs A)        
      ; slt_C_zero_is_ltr_ann_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (slt_C_zero_is_ltr_ann_carrier A))
          (structures.eqv_witness (slt_C_zero_is_ltr_ann_label A))
          (slt_C_zero_is_ltr_ann_trans_certs A) 
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d :=  
          @bop_add_id_exists_ann_check S
         (slt_C_zero_is_ltr_ann_exists_plus_ann_d A)                                    
      ; slt_C_zero_is_ltr_ann_id_ann_certs  := Assert_Slt_Exists_Id_Ann_Equal (inl c)                                           
      ; slt_C_zero_is_ltr_ann_certs :=  
          slt_add_ann_certificate
         (slt_C_zero_is_ltr_ann_certs A)                                 
      ; slt_C_zero_is_ltr_ann_ast := 
          Cas_ast ("A_slt_C_zero_is_ltr_ann_add_zero", 
            [slt_C_zero_is_ltr_ann_ast A])
    |}.
  Defined.


  Definition selective_left_pre_dioid_add_zero {L S : Type} 
    (A : @selective_left_pre_dioid L S) (c : cas_constant) :
    @selective_left_pre_dioid L (with_constant S).
  Proof.
    refine
    {|
        selective_left_pre_dioid_carrier  := 
          eqv_add_constant (selective_left_pre_dioid_carrier A) c
      ; selective_left_pre_dioid_label := 
         selective_left_pre_dioid_label A
      ; selective_left_pre_dioid_plus :=  
          bop_add_id (selective_left_pre_dioid_plus A) c                                           
      ; selective_left_pre_dioid_trans  := 
          ltr_add_ann_op (selective_left_pre_dioid_trans A) c 
      ; selective_left_pre_dioid_plus_certs  := 
          sg_CS_certs_add_id c   
          (selective_left_pre_dioid_plus_certs A)      
      ; selective_left_pre_dioid_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (selective_left_pre_dioid_carrier A))
          (structures.eqv_witness (selective_left_pre_dioid_label A))
          (selective_left_pre_dioid_trans_certs A) 
      ; selective_left_pre_dioid_exists_plus_ann := 
          properties.Assert_Exists_Ann (inl c)
      ; selective_left_pre_dioid_id_ann_certs_d :=  
          Certify_SLT_Id_Ann_Proof_Equal (inl c)                         
      ; selective_left_pre_dioid_certs :=  
          left_dioid_add_ann_certificate
         (selective_left_pre_dioid_certs A)                                
      ; selective_left_pre_dioid_ast := 
          Cas_ast ("A_selective_left_pre_dioid_add_zero", 
            [selective_left_pre_dioid_ast A])
    |}.
  Defined.

   


  Definition selective_left_dioid_add_zero {L S : Type} 
    (A : @selective_left_dioid L S) (c : cas_constant) :
    @selective_left_dioid L (with_constant S).
  Proof.
    Check  left_dioid_add_ann_certificate.
    refine
    {|
        selective_left_dioid_carrier  := 
          eqv_add_constant (selective_left_dioid_carrier A) c
      ; selective_left_dioid_label := 
         selective_left_dioid_label A
      ; selective_left_dioid_plus :=  
          bop_add_id (selective_left_dioid_plus A) c                                           
      ; selective_left_dioid_trans  := 
          ltr_add_ann_op (selective_left_dioid_trans A) c 
      ; selective_left_dioid_plus_certs  := 
          sg_CS_certs_add_id c 
          (selective_left_dioid_plus_certs A)      
      ; selective_left_dioid_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (selective_left_dioid_carrier A))
          (structures.eqv_witness (selective_left_dioid_label A))
          (selective_left_dioid_trans_certs A) 
      ; selective_left_dioid_exists_plus_ann := 
           properties.Assert_Exists_Ann (inl c)
      ; selective_left_dioid_id_ann_certs :=
          Assert_Slt_Exists_Id_Ann_Equal (inl c)                        
      ; selective_left_dioid_certs :=  
          left_dioid_add_ann_certificate
         (selective_left_dioid_certs A)                                
      ; selective_left_dioid_ast := 
          Cas_ast ("selective_left_dioid_add_zero", 
            [selective_left_dioid_ast A])
    |}.
  Defined.

  
  Definition left_dioid_add_zero {L S : Type} 
    (A : @left_dioid L S) (c : cas_constant) :
    @left_dioid L (with_constant S).
  Proof.
    refine
    {|
        left_dioid_carrier  := 
          eqv_add_constant (left_dioid_carrier A) c
      ; left_dioid_label := 
         left_dioid_label A
      ; left_dioid_plus :=  
          bop_add_id (left_dioid_plus A) c                                           
      ; left_dioid_trans  := 
          ltr_add_ann_op (left_dioid_trans A) c 
      ; left_dioid_plus_certs  := 
          sg_CI_certs_add_id c
          (left_dioid_plus_certs A)      
      ; left_dioid_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (left_dioid_carrier A))
          (structures.eqv_witness (left_dioid_label A))
          (left_dioid_trans_certs A) 
      ; left_dioid_exists_plus_ann := 
          properties.Assert_Exists_Ann (inl c)
      ; left_dioid_id_ann_certs := 
          Assert_Slt_Exists_Id_Ann_Equal (inl c)                         
      ; left_dioid_certs :=  
          left_dioid_add_ann_certificate
         (left_dioid_certs A)                                
      ; left_dioid_ast := 
          Cas_ast ("left_dioid_add_zero", 
            [left_dioid_ast A])
    |}.
  Defined.


  

    






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


