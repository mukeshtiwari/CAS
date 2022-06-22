Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.set. 
Require Import CAS.coq.sg.union. 
Require Import CAS.coq.tr.left.insert.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.union_union. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.

Section Theory.

Variables (S : Type)
          (wS : S)   
          (eq : brel S)
          (f : S -> S)
          (nt : brel_not_trivial S eq f)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (trn : brel_transitive S eq). 

Lemma slt_union_insert_distributive : @slt_distributive S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. intros s X Y. unfold slt_distributive, ltr_insert.
       apply bops_union_union_left_distributive; auto. 
Qed. 

Lemma slt_union_insert_not_absorptive : 
       @slt_not_absorptive S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. exists (wS, nil). compute. reflexivity. Defined. 

Lemma slt_union_insert_not_strictly_absorptive : 
       @slt_not_strictly_absorptive S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. exists (wS, nil). left. compute. reflexivity. Defined. 

Lemma slt_union_insert_exists_id_ann_decide (fin_d : carrier_is_finite_decidable S eq) : 
     @slt_exists_id_ann_decidable S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq).
Proof. destruct fin_d as [finP | nfinP].
       + assert (A : @slt_exists_id_ann_not_equal S (finite_set S) (brel_set eq) (bop_union eq) (ltr_insert eq)).
            exists (nil, (projT1 finP) tt). split. split. 
            apply bop_union_nil_is_id; auto. 
            apply ltr_insert_enum_is_ann; auto.
            case_eq(brel_set eq nil (projT1 finP tt)); intro B; auto.
            destruct finP as [enum P]. unfold projT1 in B.
            assert (C := P wS).
            apply brel_set_elim_prop in B;auto. destruct B as [B1 B2].
            assert (D := B2 _ C).
            compute in D. discriminate D.
         exact (@SLT_Id_Ann_Proof_Not_Equal _ _ _ _ _ A). 
       + exact (@SLT_Id_Ann_Proof_Id_None _ _ _ _ _ 
                   (bop_union_exists_id S eq ref sym trn,
                    ltr_insert_not_exists_ann S eq wS f nt ref sym trn nfinP)).
Defined.          


End Theory.

Section ACAS.


Definition union_insert_left_semiring_proofs (S : Type) (eq : brel S) (wS : S) (eqvP : eqv_proofs S eq) :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in      
{|
  A_left_semiring_distributive   := @slt_union_insert_distributive S eq ref sym trn 
; A_left_semiring_not_absorptive := @slt_union_insert_not_absorptive S wS eq 
|}.
 
End ACAS.   
