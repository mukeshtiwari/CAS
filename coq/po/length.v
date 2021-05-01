Require Import Coq.Lists.List.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.


Require Import CAS.coq.eqv.list.
Require Import CAS.coq.po.lte_nat.

Open Scope list_scope.

Section Compute.

Definition brel_length {S : Type} :  brel (list S)  :=
   λ l1 l2 , brel_lte_nat (length l1) (length l2).  

End Compute.   

Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable wS : S.
  

Lemma brel_length_congruence : brel_congruence (list S) (brel_list eq) brel_length. 
Admitted. 

Lemma brel_length_reflexive : brel_reflexive (list S) brel_length. 
Proof. intros a. unfold brel_length. apply brel_lte_nat_reflexive; auto. Qed. 

Lemma brel_length_transitive : brel_transitive (list S) brel_length. 
Proof. intros a b c. unfold brel_length. apply brel_lte_nat_transitive; auto. Qed. 

Lemma brel_length_not_antisymmetric (f  : S -> S) (nt : brel_not_trivial S eq f):
     brel_not_antisymmetric (list S) (brel_list eq) brel_length. 
Proof. exists (wS :: nil, (f wS) :: nil). compute; intros; auto.
       destruct (nt wS) as [A B]. rewrite A. auto. 
Defined. 


Lemma brel_length_total : brel_total (list S) brel_length. 
Proof. intros a b. unfold brel_length. apply brel_lte_nat_total. Qed. 

Lemma brel_length_empty_is_bottom : brel_is_bottom (list S) brel_length nil.
Proof. intro l. compute; auto. Qed. 

Lemma brel_length_empty_is_qo_bottom : brel_is_qo_bottom (list S) (brel_list eq) brel_length nil. 
Proof. split. apply brel_length_empty_is_bottom.
       intros l A B. destruct l. compute; auto. compute in B. discriminate B. 
Qed. 

Lemma brel_length_exists_qo_bottom : brel_exists_qo_bottom (list S) (brel_list eq) brel_length. 
Proof. exists nil. apply brel_length_empty_is_qo_bottom.  Defined. 

Lemma brel_length_not_exists_qo_top : brel_not_exists_qo_top (list S) (brel_list eq) brel_length. 
Proof. intros l. left. exists (wS :: l). induction l. 
          compute; auto. 
Admitted. 


End Theory.

Section ACAS.
  
Definition wp_proofs_length (S : Type) (eq : brel S) (wS : S) (f : S → S) (nt : brel_not_trivial S eq f) : 
    wp_proofs (list S) (brel_list eq) brel_length := 
{|
  A_wp_congruence    := brel_length_congruence S eq wS 
; A_wp_reflexive     := brel_length_reflexive S 
; A_wp_transitive    := brel_length_transitive S 
; A_wp_not_antisymmetric := brel_length_not_antisymmetric S eq wS f nt
; A_wp_total         := brel_length_total S
|}. 



Definition A_wp_length (S : Type): A_eqv S -> A_wp (list S)
:= λ eqv,
  let wS := A_eqv_witness S eqv in
  let f  := A_eqv_new S eqv in
  let nt := A_eqv_not_trivial S eqv in      
  let eq := A_eqv_eq S eqv in
  {| 
     A_wp_eqv             := A_eqv_list S eqv 
   ; A_wp_lte             := brel_length
   ; A_wp_exists_top_d    := inr (brel_length_not_exists_qo_top S eq wS)
   ; A_wp_exists_bottom   := brel_length_exists_qo_bottom S eq                                  
   ; A_wp_proofs          := wp_proofs_length S eq wS f nt
   ; A_wp_ast             := Ast_qo_length (A_eqv_ast S eqv)
   |}. 

End ACAS.
 

Section CAS.

Definition wp_certs_length {S : Type} (wS : S) (f : S -> S) : @wp_certificates (list S) := 
{|
  wp_congruence    := Assert_Brel_Congruence
; wp_reflexive     := Assert_Reflexive 
; wp_transitive    := Assert_Transitive 
; wp_not_antisymmetric := Assert_Not_Antisymmetric (wS :: nil, (f wS) :: nil) 
; wp_total          := Assert_Total
|}. 


Definition wp_length {S : Type} :  @eqv S -> @wp (list S) 
:= λ eqv,
  let wS := eqv_witness eqv in
  let f := eqv_new eqv in           
  {| 
     wp_eqv            := eqv_list eqv
   ; wp_lte            := brel_length
   ; wp_exists_top_d    := Certify_Not_Exists_Qo_Top
   ; wp_exists_bottom   := Assert_Exists_Qo_Bottom nil 
   ; wp_certs          := wp_certs_length wS f 
   ; wp_ast            := Ast_qo_length (eqv_ast eqv)
   |}. 



 
End CAS.

Section Verify.


  
Lemma correct_wp_certs_length (S : Type) (eq : brel S) (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f): 
       wp_certs_length wS f 
       = 
       P2C_wp (list S) (brel_list eq) brel_length (wp_proofs_length S eq wS f nt).
Proof. compute. reflexivity. Qed. 


Theorem correct_sg_length (S : Type) (E : A_eqv S):  
         wp_length (A2C_eqv S E)  = A2C_wp (list S) (A_wp_length S E). 
Proof. unfold wp_length, A_wp_length, A2C_wp; simpl. 
       rewrite <- correct_wp_certs_length. reflexivity.        
Qed. 


End Verify.   
  