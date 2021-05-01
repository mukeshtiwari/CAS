Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.

Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum. 

Require Import CAS.coq.theory.facts.


Section Compute.

Definition brel_add_bottom : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} lte c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => true  (* new bottom ! *) 
   | (inr _), (inl _) => false 
   | (inr a), (inr b) => lte a b 
   end.
  

End Compute.   

Section Theory.
Variable bottom : cas_constant.
Variable S  : Type.  

Variable eq : brel S.
Variable refl : brel_reflexive S eq.

Variable lte : brel S.
Variable lteTran : brel_transitive S lte.
Variable lteCong : brel_congruence S eq lte.

Notation "a [+] b"  := (brel_add_bottom b a)       (at level 15).

Lemma brel_add_bottom_congruence : brel_congruence (with_constant S ) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. unfold brel_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; compute; intros A B; auto; discriminate. Qed. 

Lemma brel_add_bottom_reflexive (lteRefl : brel_reflexive S lte) : brel_reflexive (with_constant S ) (bottom [+] lte). 
Proof. intros [c | s]; compute; auto. Qed. 

Lemma brel_add_bottom_not_reflexive (NlteRefl : brel_not_reflexive S lte) :
     brel_not_reflexive (with_constant S ) (bottom [+] lte). 
Proof. destruct NlteRefl as [s P]. exists (inr _ s); compute; auto. Defined.

Definition brel_add_bottom_reflexive_decide : 
     brel_reflexive_decidable S lte  → brel_reflexive_decidable (with_constant S) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl refl  => inl _ (brel_add_bottom_reflexive refl)
   | inr nrefl => inr _ (brel_add_bottom_not_reflexive nrefl)
   end.  


Lemma brel_add_bottom_transitive : brel_transitive (with_constant S ) (bottom [+] lte). 
Proof. intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; intros A B; auto. 
       discriminate. exact (lteTran _ _ _ A B). 
Qed.

Lemma brel_add_bottom_antisymmetric (anti : brel_antisymmetric S eq lte):
     brel_antisymmetric (with_constant S ) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. intros [c1 | s1] [c2 | s2]; compute; intros A B; auto. Qed.

Lemma brel_add_bottom_not_antisymmetric (nanti : brel_not_antisymmetric S eq lte):
     brel_not_antisymmetric (with_constant S ) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. destruct nanti as [[s1 s2] [A B] _]. exists (inr s1, inr s2); compute; auto. Defined.

Definition brel_add_bottom_antisymmetic_decide : 
  brel_antisymmetric_decidable S eq lte  →
     brel_antisymmetric_decidable (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl anti  => inl _ (brel_add_bottom_antisymmetric anti)
   | inr nanti => inr _ (brel_add_bottom_not_antisymmetric nanti)
   end.  

Lemma brel_add_bottom_is_bottom : brel_is_bottom (with_constant S) (bottom [+] lte) (inl bottom). 
Proof. intros [c | s]; compute; auto. Qed.

Lemma brel_add_bottom_is_qo_bottom :
     brel_is_qo_bottom (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte) (inl bottom). 
Proof. split. apply brel_add_bottom_is_bottom. 
       intros [c | s]; compute; auto.
Qed.      

Lemma brel_add_bottom_exists_bottom : brel_exists_bottom (with_constant S) (bottom [+] lte). 
Proof. exists (inl bottom). apply brel_add_bottom_is_bottom. Defined.

Lemma brel_add_bottom_exists_qo_bottom : brel_exists_qo_bottom (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. exists (inl bottom). apply brel_add_bottom_is_qo_bottom. Defined. 


Lemma brel_add_bottom_is_top (t : S) (top : brel_is_top S lte t) : brel_is_top (with_constant S) (bottom [+] lte) (inr t). 
Proof. intros [c | s]; compute; auto. Qed. 


Lemma brel_add_bottom_exists_top (top : brel_exists_top S lte) :
     brel_exists_top (with_constant S) (bottom [+] lte). 
Proof. destruct top as [t A]. exists (inr t). apply brel_add_bottom_is_top; auto. Defined. 

Lemma brel_add_bottom_not_exists_top (wS : S) (ntop : brel_not_exists_top S lte) :
    brel_not_exists_top (with_constant S) (bottom [+] lte). 
Proof. intros [c | s]. exists (inr wS); compute; auto. 
       destruct (ntop s) as [b A]. exists (inr b); compute; auto.
Defined.

Definition brel_add_bottom_exists_top_decide (wS : S) : 
     brel_exists_top_decidable S lte  → brel_exists_top_decidable (with_constant S) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl top  => inl _ (brel_add_bottom_exists_top top)
   | inr ntop => inr _ (brel_add_bottom_not_exists_top wS ntop)
   end.  


Lemma brel_add_bottom_exists_qo_top (top : brel_exists_qo_top S eq lte) :
     brel_exists_qo_top (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. destruct top as [t A]. destruct A as [A B]; auto.
       exists (inr t). split.
       apply brel_add_bottom_is_top; auto. 
       intros [c | s]; compute; auto.
Defined. 

Lemma brel_add_bottom_not_exists_qo_top (wS : S) (ntop : brel_not_exists_qo_top S eq lte) :
    brel_not_exists_qo_top (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. unfold brel_not_exists_qo_top in ntop. unfold brel_not_exists_qo_top. 
       unfold brel_not_is_qo_top in ntop. unfold brel_not_is_qo_top. 
       intros [c | s].  
          left. unfold brel_not_is_top. exists (inr wS); compute; auto. 
          destruct (ntop s) as [[u A] | [u [[A B] C]]].
             left. exists (inr u); compute; auto.
             right. exists (inr u); compute; auto.
Defined.

Definition brel_add_bottom_exists_qo_top_decide (wS : S) : 
  brel_exists_qo_top_decidable S eq lte
  → brel_exists_qo_top_decidable (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl top  => inl _ (brel_add_bottom_exists_qo_top top)
   | inr ntop => inr _ (brel_add_bottom_not_exists_qo_top wS ntop)
   end.  



Lemma brel_add_bottom_total (tot : brel_total S lte) : brel_total (with_constant S ) (bottom [+] lte). 
Proof. intros [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma brel_add_bottom_not_total (ntot : brel_not_total S lte) : brel_not_total (with_constant S ) (bottom [+] lte). 
Proof. destruct ntot as [[s1 s2] [A B]]. exists (inr s1, inr s2). compute; auto. Defined. 


Definition brel_add_bottom_total_decide : 
     brel_total_decidable S lte  → brel_total_decidable (with_constant S) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl tot  => inl _ (brel_add_bottom_total tot)
   | inr ntot => inr _ (brel_add_bottom_not_total ntot)
   end.  

End Theory.

Section ACAS.
  
Definition qo_proofs_add_bottom : 
   ∀ (S : Type) (eq lte : brel S) (c : cas_constant) (s : S),
     qo_proofs S eq lte -> qo_proofs (with_constant S) (brel_sum brel_constant eq) (brel_add_bottom lte c)
:= λ S eq lte c s qoP,
{|
  A_qo_congruence    := brel_add_bottom_congruence c S eq lte (A_qo_congruence _ _ _ qoP)  
; A_qo_reflexive     := brel_add_bottom_reflexive c S lte (A_qo_reflexive _ _ _ qoP)
; A_qo_transitive    := brel_add_bottom_transitive c S lte (A_qo_transitive _ _ _ qoP)                                                    
; A_qo_not_antisymmetric := brel_add_bottom_not_antisymmetric c S eq lte (A_qo_not_antisymmetric _ _ _ qoP)   
; A_qo_not_total     := brel_add_bottom_not_total c S lte (A_qo_not_total _ _ _ qoP)
|}. 



Definition A_po_add_bottom : ∀ (S : Type) (c : cas_constant),  A_qo S -> A_qo_with_bottom (with_constant S) 
:= λ S c qoS,
  let lte := A_qo_lte S qoS in
  let s  := A_eqv_witness S (A_qo_eqv S qoS) in
  let eq := A_eqv_eq S (A_qo_eqv S qoS) in
  {| 
     A_qowb_eqv             := A_eqv_add_constant S (A_qo_eqv S qoS) c  
   ; A_qowb_lte            := brel_add_bottom lte c
   ; A_qowb_exists_top_d   := brel_add_bottom_exists_qo_top_decide c S eq lte s (A_qo_exists_top_d S qoS)
   ; A_qowb_exists_bottom  := brel_add_bottom_exists_qo_bottom c S eq lte 
   ; A_qowb_proofs         := qo_proofs_add_bottom S eq lte c s (A_qo_proofs S qoS)
   ; A_qowb_ast            := Ast_po_add_bottom (c, A_qo_ast S qoS)
   |}. 


End ACAS.


Section CAS.



Definition brel_add_bottom_reflexive_check : 
   ∀ {S : Type},  @check_reflexive S → @check_reflexive (with_constant S) 
:= λ {S} dS,  
   match dS with 
   | Certify_Reflexive       => Certify_Reflexive
   | Certify_Not_Reflexive s => Certify_Not_Reflexive (inr _ s)
   end. 

Definition brel_add_bottom_total_check : 
   ∀ {S : Type},  @check_total S → @check_total (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Total            => Certify_Total
   | Certify_Not_Total (s, t) => Certify_Not_Total (inr s, inr t)
   end. 


Definition brel_add_bottom_exists_bottom_check : 
   ∀ {S : Type},  @check_exists_bottom S → @check_exists_bottom (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Bottom b   => Certify_Exists_Bottom (inr b)
   | Certify_Not_Exists_Bottom => Certify_Not_Exists_Bottom
   end. 


Definition brel_add_bottom_exists_qo_bottom_check : 
   ∀ {S : Type},  @check_exists_qo_bottom S → @check_exists_qo_bottom (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Qo_Bottom b   => Certify_Exists_Qo_Bottom (inr b)
   | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
   end. 


Definition brel_add_bottom_exists_qo_top_check : 
   ∀ {S : Type},  @check_exists_qo_top S → @check_exists_qo_top (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Qo_Top b   => Certify_Exists_Qo_Top (inr b)
   | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
   end. 



Definition qo_certs_add_bottom {S : Type} : 
      @qo_certificates S -> @qo_certificates (with_constant S)
:= λ qoP,
{|
  qo_congruence    := Assert_Brel_Congruence
; qo_reflexive     := Assert_Reflexive 
; qo_transitive    := Assert_Transitive 
; qo_not_antisymmetric := match qo_not_antisymmetric qoP with
                          | Assert_Not_Antisymmetric (s, t) => Assert_Not_Antisymmetric (inr s, inr t) 
                          end 
; qo_not_total  := match qo_not_total qoP with
                 | Assert_Not_Total (s, t) => Assert_Not_Total (inr s, inr t)
                 end 
|}. 


Definition po_add_bottom {S : Type} (c : cas_constant):  @qo S -> @qo_with_bottom (with_constant S) 
:= λ qoS,
  {| 
     qowb_eqv            := eqv_add_constant (qo_eqv qoS) c  
   ; qowb_lte            := brel_add_bottom (qo_lte qoS) c
   ; qowb_exists_top_d   := brel_add_bottom_exists_qo_top_check (qo_exists_top_d qoS)
   ; qowb_exists_bottom  := Assert_Exists_Qo_Bottom (inl c)
   ; qowb_certs          := qo_certs_add_bottom (qo_certs qoS) 
   ; qowb_ast            := Ast_po_add_bottom (c, qo_ast qoS)
   |}. 



 
End CAS.

Section Verify.


  
Lemma correct_po_certs_add_bottom (S : Type) (eq lte : brel S) (wS : S) (b : cas_constant) (P : qo_proofs S eq lte) : 
       qo_certs_add_bottom (P2C_qo S eq lte P) 
       = 
       P2C_qo (with_constant S) 
          (brel_sum brel_constant eq) 
          (brel_add_bottom lte b) 
          (qo_proofs_add_bottom S eq lte b wS P).
Proof. destruct P.  unfold qo_proofs_add_bottom, qo_certs_add_bottom, P2C_qo; simpl.
       destruct A_qo_not_antisymmetric as [[s t] [A B]]. simpl.
       unfold p2c_not_antisymmetric_assert.
       destruct A_qo_not_total as [[st] [C D]]; simpl; reflexivity. 
Defined. 


Theorem correct_sg_add_bottom (S : Type) (b : cas_constant) (qoS : A_qo S):  
         po_add_bottom b (A2C_qo S qoS) 
         = 
         A2C_qo_with_bottom (with_constant S) (A_po_add_bottom S b qoS). 
Proof. destruct qoS. unfold po_add_bottom, A_po_add_bottom, A2C_qo, A2C_qo_with_bottom; simpl.
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_po_certs_add_bottom.
       unfold brel_add_bottom_exists_qo_bottom.
       unfold p2c_exists_qo_bottom_assert. simpl.
       destruct A_qo_exists_top_d as [[t [A B]] | Q];
       unfold p2c_exists_qo_top_check; simpl; reflexivity.        
Qed. 


End Verify.   
  