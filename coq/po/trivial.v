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


End Theory.

Section ACAS.
  
Definition wp_proofs_trivial (S : Type) (eq : brel S) (wS : S) (f : S → S) (nt : brel_not_trivial S eq f) : 
    wp_proofs S eq brel_trivial := 
{|
  A_wp_congruence    := brel_trivial_congruence S eq
; A_wp_reflexive     := brel_trivial_reflexive S 
; A_wp_transitive    := brel_trivial_transitive S 
; A_wp_not_antisymmetric := brel_trivial_not_antisymmetric S eq wS f nt
; A_wp_total         := brel_trivial_total S
|}. 



Definition A_wp_trivial (S : Type): A_eqv S -> A_wp S
:= λ eqv,
  let wS := A_eqv_witness S eqv in
  let f  := A_eqv_new S eqv in
  let nt := A_eqv_not_trivial S eqv in      
  let eq := A_eqv_eq S eqv in
  {| 
     A_wp_eqv            := eqv 
   ; A_wp_lte            := brel_trivial
   ; A_wp_exists_top_d    := inr (brel_trivial_not_exists_qo_top S eq f nt)                                                                
   ; A_wp_exists_bottom_d := inr (brel_trivial_not_exists_qo_bottom S eq f nt)                                  
   ; A_wp_proofs         := wp_proofs_trivial S eq wS f nt
   ; A_wp_ast            := Ast_qo_trivial (A_eqv_ast S eqv)
   |}. 

End ACAS.
 

Section CAS.

Definition wp_certs_trivial {S : Type} (wS : S) (f : S -> S) : @wp_certificates S := 
{|
  wp_congruence    := Assert_Brel_Congruence
; wp_reflexive     := Assert_Reflexive 
; wp_transitive    := Assert_Transitive 
; wp_not_antisymmetric := Assert_Not_Antisymmetric (wS, f wS) 
; wp_total       := Assert_Total
|}. 


Definition wp_trivial {S : Type} :  @eqv S -> @wp S 
:= λ eqv,
  let wS := eqv_witness eqv in
  let f := eqv_new eqv in           
  {| 
     wp_eqv            := eqv
   ; wp_lte            := brel_trivial
   ; wp_exists_top_d    := Certify_Not_Exists_Qo_Top 
   ; wp_exists_bottom_d := Certify_Not_Exists_Qo_Bottom 
   ; wp_certs          := wp_certs_trivial wS f 
   ; wp_ast            := Ast_qo_trivial (eqv_ast eqv)
   |}. 



 
End CAS.

Section Verify.


  
Lemma correct_po_certs_trivial (S : Type) (eq : brel S) (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f): 
       wp_certs_trivial wS f 
       = 
       P2C_wp S eq brel_trivial (wp_proofs_trivial S eq wS f nt).
Proof. compute. reflexivity. Qed. 


Theorem correct_sg_trivial (S : Type) (E : A_eqv S):  
         wp_trivial (A2C_eqv S E)  = A2C_wp S (A_wp_trivial S E). 
Proof. unfold wp_trivial, A_wp_trivial, A2C_wp; simpl. 
       rewrite <- correct_po_certs_trivial. reflexivity.        
Qed. 


End Verify.   
  