Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts.



Open Scope list_scope.


(* note similarity in this and next lemma .... 

   ∀ (s : list S) (t1 t2 : S),
   r t1 t2 = true → in_list S r s t1 = true → in_set S r s t2 = true
*) 

Lemma in_set_right_congruence : 
       ∀ (S : Type) (r : brel S), 
       brel_symmetric S r -> brel_transitive S r -> 
          brel2_right_congruence (finite_set S) S r (in_list S r). 
Proof. intros S r symS transS. unfold brel2_right_congruence. 
       induction s; intros t1 t2 H1 H2. 
       unfold in_list in H2. discriminate.        
       unfold in_list. fold in_set. 
       unfold in_list in H2. fold in_list in H2. 
       apply orb_is_true_left in H2. destruct H2 as [H2|H2]. 
       apply symS in H1. rewrite (transS t2 t1 a H1 H2). simpl. reflexivity. 
       fold in_list. 
       rewrite (IHs _ _ H1 H2). rewrite orb_comm. simpl. reflexivity. 
Defined. 

(* 
   ∀ (X : list S) (s t : S),
   r s t = true → in_set S r X s = in_set S r X t
*) 
Lemma in_set_bProp_congruence : 
       ∀ (S : Type) (r : brel S),  
       brel_symmetric S r -> brel_transitive S r -> 
          ∀ (X : finite_set S), bProp_congruence S r (in_list S r X). 
Proof. intros S r symS transS. unfold bProp_congruence. 
       induction X. auto. 
       intros s t H. 
       unfold in_list. fold in_list. 
       rewrite (IHX s t H). 
       case_eq(r s a); intro J. 
          simpl. apply symS in H. rewrite (transS _ _ _ H J). auto. 
          simpl. assert (fact : r t a = false). 
             case_eq(r t a); intro F. rewrite (transS _ _ _ H F) in J. assumption. 
             reflexivity.            
          rewrite fact. simpl. reflexivity. 
Defined. 




