Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 

Require Import CAS.coq.tr.left.from_sg.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.



Section Theory.

Variables (S : Type)
          (wS : S)   
          (eq : brel S)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (plus : binary_op S) 
          (times : binary_op S). 

Lemma slt_from_bs_distributive 
      (LD : bop_left_distributive S eq plus times) : 
      slt_distributive S S eq plus (ltr_from_sg times). 
Proof. intros s t u. unfold ltr_from_sg. apply LD. Qed.


Lemma slt_from_bs_absorptive 
       (lrabs : bops_left_right_absorptive S eq plus times) :
       slt_absorptive S S eq plus (ltr_from_sg times).
Proof. intros s t. unfold ltr_from_sg. exact (lrabs t s). Qed. 

Lemma slt_from_bs_not_absorptive 
       (nlrabs : bops_not_left_right_absorptive S eq plus times) :
       slt_not_absorptive S S eq plus (ltr_from_sg times).
Proof. destruct nlrabs as [[s t] P]. exists(t, s). compute. exact P. Defined. 


Lemma slt_from_bs_strictly_absorptive 
       (lrabs : bops_strictly_left_right_absorptive S eq plus times) :  
       slt_strictly_absorptive S S eq plus (ltr_from_sg times).
Proof. intros s t.  unfold ltr_from_sg. apply lrabs. Qed. 


Lemma slt_union_insert_not_strictly_absorptive 
       (nlrabs : bops_not_strictly_left_right_absorptive S eq plus times) :  
       slt_not_strictly_absorptive S S eq plus (ltr_from_sg times).
Proof. destruct nlrabs as [[s t] [P | P]]; exists(t, s); compute. left; exact P. right. exact P. Defined. 
      
End Theory.   
