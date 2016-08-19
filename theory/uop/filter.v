
Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.uop_properties. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 





Lemma uop_filter_nil_elim : 
    ∀ (S : Type) (eq : brel S) (f : bProp S), 
        bProp_congruence S eq f -> 
        ∀ (s : finite_set S),
            uop_filter S f s = nil -> 
               ∀ a : S,  (in_set S eq s a = true) -> (f a = false).
Proof. unfold uop_filter. intros S eq f cong. induction s; intros H b J. 
         compute in J. discriminate. 
         unfold in_set in J. fold in_set in J. simpl in H. 
         case_eq(eq b a); case_eq(f a); intros M N; 
           rewrite N in J; rewrite M in H; simpl in J; simpl in H.
              discriminate. 
              assert (A := cong b a N). rewrite M in A. assumption. 
              discriminate. 
              apply IHs; auto. 
Defined. 

