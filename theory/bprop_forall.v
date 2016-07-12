Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts.
Require Import CAS.theory.brel2_in_set. 
Require Import CAS.theory.brel_set. 


Lemma bProp_forall_true_elim : 
  ∀ (S : Type) (eq : brel S) (f : bProp S), 
    bProp_congruence S eq f  → 
       ∀ (X : finite_set S), 
         bProp_forall S f X = true  → 
             ∀ a : S, in_set S eq X a = true → f a = true. 
Proof. intros S eq f cong. induction X; intro H. 
       intros a J. compute in J. discriminate. 
       intros b J. apply in_set_cons_elim in J. destruct J as [L | R]. 
          unfold bProp_forall in H. unfold List.forallb in H.
          apply andb_is_true_left in H. destruct H as [K _]. 
          assert (A := cong _ _ L). rewrite A. assumption. 
          unfold bProp_forall in H. simpl in H.  
          apply andb_is_true_left in H. destruct H as [K J]. 
          unfold bProp_forall in IHX. assert (A := IHX J). 
          apply A; auto. 
Defined. 

Lemma bProp_forall_false_elim : 
  ∀ (S : Type) (eq : brel S) (f : bProp S), 
    brel_reflexive S eq →
       ∀ (X : finite_set S), 
         bProp_forall S f X = false  → 
             ((X <> nil) * {a : S & (in_set S eq X a = true) * (f a = false) }). 
Proof. intros S eq f refS. induction X; intros H. 
          compute in H. discriminate. 
          unfold bProp_forall in H. simpl in H.                  
          apply andb_is_false_left in H. destruct H as [L | R]. 
             split. 
                apply cons_not_nil. 
                exists a. split. apply in_set_cons_intro. left. apply refS. assumption.  
             assert (A := IHX R). destruct A as [AL  AR]. split. 
                apply cons_not_nil. 
                destruct AR as [b [B C]]. exists b. split. 
                   unfold in_set. fold in_set. rewrite B. apply orb_comm. 
                   assumption. 
Defined. 


Lemma bProp_forall_bProp_congruence :
  ∀ (S : Type) (eq : brel S) (f : bProp S), 
    brel_reflexive S eq →
    brel_symmetric S eq   →
    brel_transitive S eq   →
    bProp_congruence S eq f  → 
      bProp_congruence (finite_set S) (brel_set S eq) (bProp_forall S f). 
Proof. intros S eq f refS symS transS cong. unfold bProp_congruence. intros X Y E. 
       apply brel_set_elim_prop in E; auto. destruct E as [L R].
       case_eq(bProp_forall S f X); case_eq(bProp_forall S f Y); intros H1 H2. 
          reflexivity. 
          assert (A1 := bProp_forall_false_elim _ eq _ refS _ H1). 
          assert (A2 := bProp_forall_true_elim _ eq _ cong _ H2). 
          destruct A1 as [_ [a [B C]]].
          assert (D := R a B). 
          assert (F := A2 a D). rewrite F in C. discriminate. 

          assert (A1 := bProp_forall_true_elim _ eq _ cong _ H1). 
          assert (A2 := bProp_forall_false_elim _ eq _ refS _ H2). 
          destruct A2 as [ _ [a [B C]]].
          assert (D := L a B). 
          assert (F := A1 a D). rewrite F in C. discriminate. 

          reflexivity. 
Defined. 



