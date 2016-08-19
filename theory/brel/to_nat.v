Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties. 

Open Scope nat_scope. 

Lemma brel_to_nat_reflexive : brel_reflexive nat brel_to_nat. 
Proof. induction s; simpl; auto. Qed. 

Lemma brel_to_nat_antisymmetric : brel_antisymmetric nat brel_eq_nat brel_to_nat. 
Proof. induction s; induction t; simpl; intros; auto. Qed. 

Lemma brel_to_nat_transitive : brel_transitive nat brel_to_nat. 
Proof. induction s; induction t; simpl; intros u H1 H2; destruct u; auto. 
       discriminate. apply (IHs _ _ H1 H2). 
Qed. 

Lemma bre_to_nat_lemma1 : ∀ s u : nat, brel_eq_nat (S s) (S u) = true -> brel_eq_nat s u = true. 
Proof. induction s; induction u; simpl; intro H; auto. Qed. 

Lemma bre_to_nat_lemma2 : ∀ u : nat, brel_eq_nat 0 (S u) = false. 
Proof. induction u; compute; reflexivity. Qed. 

Lemma bre_to_nat_lemma3 : ∀ u : nat, brel_eq_nat (S u) 0 = false.  
Proof. induction u; compute; reflexivity. Qed. 


Lemma brel_to_nat_congruence : brel_congruence nat brel_eq_nat brel_to_nat. 
Proof. unfold brel_congruence. induction s; induction t; induction u; induction v; intros H Q; auto. 
       rewrite bre_to_nat_lemma2 in H. discriminate. 
       rewrite bre_to_nat_lemma2 in H. discriminate. 
       rewrite bre_to_nat_lemma2 in Q. discriminate.
       rewrite bre_to_nat_lemma3 in H. discriminate. 
       rewrite bre_to_nat_lemma3 in H. discriminate. 
       rewrite bre_to_nat_lemma3 in Q. discriminate.
       unfold brel_to_nat. simpl.  fold brel_to_nat. 
       apply IHs. apply bre_to_nat_lemma1; auto.  apply bre_to_nat_lemma1; auto.  
Qed. 


Lemma brel_to_nat_total : brel_total nat brel_to_nat. 
Proof. induction s; induction t; simpl; auto. Qed. 
