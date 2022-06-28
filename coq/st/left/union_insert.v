(*
Approach 1
----------
union_insert eqv SELF

(inr X) + (inr Y) = inr (X union Y)
(inl SELF) + _    = (inl SELF)

x |> inr X    = inr ({x} union X) 
x |> inl SELF = inr {x} 

+id  = inr {}
+ann = inl SELF

problem: not distributive 

lhs = x |> (inl SELF) + (inr X) 
    = x |> (inl SELF) 
    = inr {x} 

rhs = (x |> (inl SELF)) + (x |> (inr X)) 
    = inr {x} union' inr ({x} union X)
    = inr ({x} union X)

Approach 2
----------
start with distributive 

x |> X = {x} union X
(+) = union

(+)-id = {} 

note : x |> {} = {x} 

So, {} could be read as "self". However, 
such a best value should be the (+) annahilator, not the id. 

Add a double ann now. 

(inl SELF) + _    = (inl SELF)

but 

x |> inl SELF = inl SELF

which is not correct. 

Approach 3
----------

*) 
Require Import Coq.Strings.String.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.tr.left.insert.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.union_union. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.

Section Theory.

Variables (S : Type)
          (c : cas_constant) 
          (wS : S)   
          (eq : brel S)
          (f : S -> S)
          (nt : brel_not_trivial S eq f)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (trn : brel_transitive S eq). 


Lemma slt_union_insert_not_distributive :
  @slt_not_distributive S
                    (with_constant (finite_set S))
                    (brel_sum brel_constant (brel_set eq))
                    (bop_add_ann (bop_union eq) c) 
                    (ltr_insert eq).
Proof. exists (wS, (inl c, inr ((f wS) :: nil))); simpl. 
       case_eq(brel_set eq (wS :: nil)
                        (bop_union eq (wS :: nil)
                                   (bop_union eq (wS :: nil) (f wS :: nil)))); intro A; auto.
       apply brel_set_elim_prop in A; auto.
       destruct A as [A B]. 
       assert (C : set.in_set eq (bop_union eq (wS :: nil) (bop_union eq (wS :: nil) (f wS :: nil))) (f wS) = true).
          apply in_set_bop_union_intro; auto.
          right. apply in_set_bop_union_intro; auto.
          right. compute. rewrite ref. reflexivity.
       assert (D := B _ C). compute in D.
       destruct (nt wS) as [L R].
       rewrite R in D. discriminate D. 
Defined. 

Lemma slt_union_insert_not_absorptive : 
  @slt_not_absorptive S
                    (with_constant (finite_set S))
                    (brel_sum brel_constant (brel_set eq))
                    (bop_add_ann (bop_union eq) c) 
                    (ltr_insert eq).
Proof. exists (wS, inr nil). compute. reflexivity. Defined. 

Lemma slt_union_insert_not_strictly_absorptive : 
  @slt_not_strictly_absorptive S
                    (with_constant (finite_set S))
                    (brel_sum brel_constant (brel_set eq))
                    (bop_add_ann (bop_union eq) c) 
                    (ltr_insert eq).
Proof. exists (wS, inr nil). left. compute. reflexivity. Defined. 

Lemma slt_union_insert_exists_id_ann_decide (fin_d : carrier_is_finite_decidable S eq) : 
  @slt_exists_id_ann_decidable S
                               (with_constant (finite_set S))
                               (brel_sum brel_constant (brel_set eq))
                               (bop_add_ann (bop_union eq) c) 
                               (ltr_insert eq).
Proof. destruct fin_d as [finP | nfinP].
       + assert (A : @slt_exists_id_ann_not_equal S
                                                  (with_constant (finite_set S))
                                                  (brel_sum brel_constant (brel_set eq))
                                                  (bop_add_ann (bop_union eq) c) 
                                                  (ltr_insert eq)).
         exists (inr nil, inr ((projT1 finP) tt)); simpl. split. split.
         apply bop_add_ann_is_id. 
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
                   (bop_add_ann_exists_id _ _ c (bop_union eq) (bop_union_exists_id S eq ref sym trn), 
                    ltr_insert_not_exists_ann S eq wS ref sym trn nfinP)).
Defined.          


End Theory.

Section ACAS.

(*
Definition union_insert_left_semiring_proofs (S : Type) (eq : brel S) (wS : S) (eqvP : eqv_proofs S eq) :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in      
{|
  A_left_semiring_distributive   := @slt_union_insert_distributive S eq ref sym trn 
; A_left_semiring_not_absorptive := @slt_union_insert_not_absorptive S wS eq 
|}.

Open Scope string_scope.


Definition A_slt_union_insert (S :Type) (eqv : A_eqv S) :=
let eq         := A_eqv_eq S eqv in
let wS          := A_eqv_witness S eqv in
let f          := A_eqv_new S eqv in
let ntS        := A_eqv_not_trivial S eqv in
let fin_d      := A_eqv_finite_d S eqv in
let eqvP       := A_eqv_proofs S eqv in
let refS       := A_eqv_reflexive _ _ eqvP in
let symS       := A_eqv_symmetric _ _ eqvP in
let trnS       := A_eqv_transitive _ _ eqvP in
  {|
    A_left_pre_semiring_carrier           := A_eqv_set S eqv 
  ; A_left_pre_semiring_label             := eqv 
  ; A_left_pre_semiring_plus              := bop_union eq 
  ; A_left_pre_semiring_trans             := ltr_insert eq 
  ; A_left_pre_semiring_plus_proofs       := (* ugh!  need some abstraction here....*)
                                             A_sg_C_proofs_from_sg_CI_proofs
                                               (finite_set S) 
                                               (brel_set eq)
                                               (bop_union eq) 
                                               (wS :: nil)
                                               (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil)
                                               (brel_set_not_trivial S eq wS)
                                               (eqv_proofs_set S eq eqvP)
                                               (sg_CI_proofs_union eqv)
  ; A_left_pre_semiring_trans_proofs      := ltr_insert_proofs S eq wS f ntS eqvP 
  ; A_left_pre_semiring_exists_plus_ann_d := bop_union_exists_ann_decide S eq refS symS trnS fin_d 
  ; A_left_pre_semiring_id_ann_proofs_d   := slt_union_insert_exists_id_ann_decide S wS eq refS symS trnS fin_d 
  ; A_left_pre_semiring_proofs            := union_insert_left_semiring_proofs S eq wS eqvP  
  ; A_left_pre_semiring_ast               := Cas_ast ("slt_union_insert", (Cas_eqv_ast (A_eqv_ast _ eqv)) :: nil)
|}.

 
End ACAS.   

Section AMCAS.


Definition A_mcas_slt_union_insert (S : Type) (eqv : @A_mcas_eqv S) :=
match eqv with
| A_EQV_eqv A    => A_slt_classify (A_SLT_Left_Pre_Semiring (A_slt_union_insert _ A))
| A_EQV_Error sl => A_SLT_Error sl     
end.
  
End AMCAS.   

Section CAS.

Definition union_insert_left_semiring_certs {S : Type} (wS : S) :=
{|
  left_semiring_distributive   := Assert_Slt_Distributive 
; left_semiring_not_absorptive := @Assert_Slt_Not_Absorptive S (finite_set S) (wS, nil) 
|}.

Open Scope string_scope.


Definition slt_union_insert_exists_id_ann_certify {S : Type} (fin_d : @check_is_finite S) : @check_slt_exists_id_ann S (finite_set S) :=
  match fin_d with
  | Certify_Is_Finite enum => Certify_SLT_Id_Ann_Proof_Not_Equal (nil, enum tt)
  | Certify_Is_Not_Finite  => Certify_SLT_Id_Ann_Proof_Id_None nil 
  end. 
  
Definition slt_union_insert {S :Type} (eqv : @eqv S) :=
let eq         := eqv_eq eqv in
let wS         := eqv_witness eqv in
let f          := eqv_new eqv in
let fin_d      := eqv_finite_d eqv in
  {|
    left_pre_semiring_carrier           := eqv_set eqv 
  ; left_pre_semiring_label             := eqv 
  ; left_pre_semiring_plus              := bop_union eq 
  ; left_pre_semiring_trans             := ltr_insert eq 
  ; left_pre_semiring_plus_certs        := (* ugh!  need some abstraction here....*)
                                             sg_C_certs_from_sg_CI_certs
                                               (finite_set S) 
                                               (brel_set eq)
                                               (bop_union eq) 
                                               (wS :: nil)
                                               (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil)
                                               (sg_CI_certs_union eqv)
  ; left_pre_semiring_trans_certs       := ltr_insert_certs wS f 
  ; left_pre_semiring_exists_plus_ann_d := bop_union_exists_ann_certify fin_d 
  ; left_pre_semiring_id_ann_certs_d    := slt_union_insert_exists_id_ann_certify fin_d 
  ; left_pre_semiring_certs             := union_insert_left_semiring_certs wS
  ; left_pre_semiring_ast               := Cas_ast ("slt_union_insert", (Cas_eqv_ast (eqv_ast eqv)) :: nil)
|}.

  
  
End CAS.

Section MCAS.

Definition mcas_slt_union_insert {S : Type} (eqv : @mcas_eqv S) :=
match eqv with
| EQV_eqv A    => slt_classify (SLT_Left_Pre_Semiring (slt_union_insert A))
| EQV_Error sl => SLT_Error sl     
end.
  

End MCAS.

Section Verify.

Lemma correct_id_ann_certs_union_insert
      (S : Type)
      (eq : brel S)
      (wS : S)
      (fin_d : carrier_is_finite_decidable S eq)
      (ref : brel_reflexive S eq)
      (sym : brel_symmetric S eq) 
      (trn : brel_transitive S eq) : 
     slt_union_insert_exists_id_ann_certify (p2c_is_finite_check S eq fin_d)
     =
     p2c_slt_exists_id_ann_check (brel_set eq) (bop_union eq) (ltr_insert eq)
        (slt_union_insert_exists_id_ann_decide S wS eq ref sym trn fin_d). 
Proof. unfold p2c_slt_exists_id_ann_check, slt_union_insert_exists_id_ann_decide,
              slt_union_insert_exists_id_ann_certify, p2c_is_finite_check; 
              destruct fin_d as [[enum A] | C]; simpl; reflexivity. 
Qed.

Lemma correct_certs_union_insert (S : Type) (eq : brel S) (wS : S) (eqvP : eqv_proofs S eq) :    
      union_insert_left_semiring_certs wS 
      = 
      P2C_left_semiring (brel_set eq) (bop_union eq) (ltr_insert eq)
        (union_insert_left_semiring_proofs S eq wS eqvP). 
Proof. unfold union_insert_left_semiring_certs,
       union_insert_left_semiring_proofs,
       P2C_left_semiring; compute.
       reflexivity. 
Qed. 
  
Theorem correct_union_insert (S : Type) (eqv: A_eqv S) : 
    slt_union_insert (A2C_eqv S eqv)
    =
    A2C_left_pre_semiring (A_slt_union_insert S eqv).
Proof. unfold slt_union_insert, A_slt_union_insert, A2C_left_pre_semiring; simpl.
       rewrite correct_eqv_set.
       rewrite correct_bop_union_certs.
       rewrite correct_ltr_certs_insert. 
       rewrite <- correct_bop_union_exists_ann_certify.
       rewrite <- correct_id_ann_certs_union_insert.       
       rewrite <- correct_certs_union_insert.        
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.

       reflexivity.
Qed. 

 
Theorem correct_bop_mcas_union_insert (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_slt_union_insert (A2C_mcas_eqv S eqvS)  
         = 
         A2C_mcas_slt (A_mcas_slt_union_insert S eqvS). 
Proof. destruct eqvS; simpl.
       + reflexivity. 
       + rewrite correct_union_insert.
         apply correctness_slt_classify_left_pre_semiring_slt. 
Qed.  

End Verify.   
*) 
