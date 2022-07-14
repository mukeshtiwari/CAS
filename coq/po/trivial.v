Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.


Section Compute.

Definition brel_trivial {S : Type} :  brel S  := λ  x y, true. 

End Compute.   

Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable wS : S.
Variable f  : S -> S.
Variable nt : brel_not_trivial S eq f. 
  

Lemma brel_trivial_congruence : brel_congruence S eq brel_trivial. 
Proof. compute; intros; auto. Qed. 

Lemma brel_trivial_reflexive : brel_reflexive S brel_trivial. 
Proof. compute; intros; auto. Qed. 

Lemma brel_trivial_transitive : brel_transitive S brel_trivial. 
Proof. compute; intros; auto. Qed. 

Lemma brel_trivial_not_antisymmetric :
     brel_not_antisymmetric S eq brel_trivial. 
Proof. exists (wS, f wS). compute; intros; auto.
       destruct (nt wS) as [A B]. rewrite A. auto. 
Defined. 


Lemma brel_trivial_total : brel_total S brel_trivial. 
Proof. compute; intros; auto. Qed. 


Lemma brel_trivial_not_exists_qo_top : 
    brel_not_exists_qo_top S eq brel_trivial. 
Proof. intro s. unfold brel_not_is_qo_top. right.
       unfold lte_equiv_not_unique.
       destruct (nt s) as [A B].
       exists (f s); compute; auto. 
Defined.

Lemma brel_trivial_not_exists_qo_bottom : 
    brel_not_exists_qo_bottom S eq brel_trivial. 
Proof. intro s. unfold brel_not_is_qo_bottom. right.
       unfold lte_equiv_not_unique.
       destruct (nt s) as [A B].
       exists (f s); compute; auto. 
Defined.

Lemma brel_trivial_trivial : order_trivial S brel_trivial. 
Proof. intros s t. compute; reflexivity. Qed. 

End Theory.

Section ACAS.

Definition or_proofs_trivial (S : Type) (eq : brel S) (wS : S) (f : S → S) (nt : brel_not_trivial S eq f) : 
    wo_proofs S eq brel_trivial := 
{|
  A_wo_congruence    := brel_trivial_congruence S eq
; A_wo_reflexive     := brel_trivial_reflexive S 
; A_wo_transitive    := brel_trivial_transitive S 
; A_wo_not_antisymmetric := brel_trivial_not_antisymmetric S eq wS f nt
; A_wo_total         := brel_trivial_total S
; A_wo_trivial_d     := inl (brel_trivial_trivial S)                                           
|}. 


Definition A_or_trivial {S : Type} (eqv : A_eqv S) : A_wo S := 
  let wS := A_eqv_witness S eqv in
  let f  := A_eqv_new S eqv in
  let nt := A_eqv_not_trivial S eqv in      
  let eq := A_eqv_eq S eqv in
  {| 
     A_wo_eqv               := eqv 
   ; A_wo_lte               := brel_trivial
   ; A_wo_not_exists_top    := brel_trivial_not_exists_qo_top S eq f nt
   ; A_wo_not_exists_bottom := brel_trivial_not_exists_qo_bottom S eq f nt
   ; A_wo_proofs            := or_proofs_trivial S eq wS f nt
   ; A_wo_ast               := Ast_or_trivial (A_eqv_ast S eqv)
   |}. 

End ACAS.

Section AMCAS.

  Definition A_mcas_or_trivial {S : Type} (meqv : @A_mcas_eqv S) :=
    match meqv with
    | A_EQV_Error sl => A_OR_Error sl
    | A_EQV_eqv eqv => A_OR_wo (A_or_trivial eqv)
    end.
  
End AMCAS.   
 

Section CAS.

Definition or_certs_trivial {S : Type} (wS : S) (f : S -> S) : @wo_certificates S := 
{|
  wo_congruence        := Assert_Brel_Congruence
; wo_reflexive         := Assert_Reflexive 
; wo_transitive        := Assert_Transitive 
; wo_not_antisymmetric := Assert_Not_Antisymmetric (wS, f wS) 
; wo_total             := Assert_Total
; wo_trivial_d         := Certify_Order_Trivial 
|}. 

Definition or_trivial {S : Type} :  @eqv S -> @wo S 
:= λ eqv,
  let wS := eqv_witness eqv in
  let f := eqv_new eqv in           
  {| 
     wo_eqv               := eqv
   ; wo_lte               := brel_trivial
   ; wo_not_exists_top    := Assert_Not_Exists_Qo_Top 
   ; wo_not_exists_bottom := Assert_Not_Exists_Qo_Bottom 
   ; wo_certs             := or_certs_trivial wS f 
   ; wo_ast               := Ast_or_trivial (eqv_ast eqv)
   |}. 
 
End CAS.

Section MCAS.

    Definition mcas_or_trivial {S : Type} (meqv : @mcas_eqv S) :=
    match meqv with
    | EQV_Error sl => OR_Error sl
    | EQV_eqv eqv => OR_wo (or_trivial eqv)
    end.

End MCAS.   


Section Verify.
  
Lemma correct_or_certs_trivial (S : Type) (eq : brel S) (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f): 
       or_certs_trivial wS f 
       = 
       P2C_wo eq brel_trivial (or_proofs_trivial S eq wS f nt).
Proof. compute. reflexivity. Qed. 


Theorem correct_or_trivial (S : Type) (E : A_eqv S):  
         or_trivial (A2C_eqv S E)  = A2C_wo (A_or_trivial E). 
Proof. unfold or_trivial, A_or_trivial, A2C_wo; simpl. 
       rewrite <- correct_or_certs_trivial. reflexivity.        
Qed.


Theorem correct_mcas_or_trivial (S : Type) (E : @A_mcas_eqv S):  
         mcas_or_trivial (A2C_mcas_eqv S E)  = A2C_mcas_or (A_mcas_or_trivial E). 
Proof. destruct E; simpl. 
       + reflexivity.
       + rewrite <- correct_or_trivial. reflexivity.        
Qed.



End Verify.   
  
