Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 

Lemma brel_and_sym_congruence: ∀ (S : Type) (r1 r2 : brel S), 
         brel_symmetric S r1 -> 
         brel_congruence S r1 r2 -> brel_congruence S r1 (brel_and_sym S r2). 
Proof. intros S r1 r2. unfold brel_congruence, brel_and_sym. 
       intros symS congS s t u v H Q. 
       rewrite (congS _ _ _ _ H Q).
       rewrite (congS _ _ _ _ Q H). 
       reflexivity. 
Defined. 


Lemma brel_and_sym_relexive : ∀ (S : Type) (r : brel S), 
              (brel_reflexive _ r) → brel_reflexive S (brel_and_sym S r). 
Proof. intros S r. unfold brel_reflexive, brel_and_sym. intros refS s. 
       rewrite (refS s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_transitive : ∀ (S : Type) (r : brel S), 
              (brel_transitive _ r) → brel_transitive S (brel_and_sym S r). 
Proof. intros S r. unfold brel_transitive, brel_and_sym. intros transS s t u H1 H2. 
       apply andb_is_true_left in H1. destruct H1 as [H1_l H1_r].        
       apply andb_is_true_left in H2. destruct H2 as [H2_l H2_r].        
       rewrite (transS _ _ _ H1_l H2_l).
       rewrite (transS _ _ _ H2_r H1_r ). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_symmetric : ∀ (S : Type) (r : brel S), 
              brel_symmetric S (brel_and_sym S r). 
Proof. intros S r. unfold brel_symmetric, brel_and_sym. intros s t H. 
       apply andb_is_true_left in H. destruct H as [H_l H_r].        
       rewrite H_l. rewrite H_r. simpl. reflexivity. 
Defined. 


Lemma brel_and_sym_uop_congruence : 
   ∀ (S : Type) (eq : brel S) (u : unary_op S), 
     uop_congruence S eq u →
        uop_congruence S (brel_and_sym S eq) u. 
Proof. intros S eq u cong. unfold uop_congruence. unfold brel_and_sym. 
       intros s t H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       apply andb_is_true_right. split. 
          apply cong. assumption. 
          apply cong. assumption. 
Defined. 

Lemma brel_and_sym_witness : ∀ (S : Type) (r : brel S), 
        brel_reflexive S r → 
        brel_witness S r → 
           brel_witness S (brel_and_sym S r). 
Proof. unfold brel_witness, brel_and_sym. intros S r  refS [s P].
       exists s. rewrite (refS s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_negate : ∀ (S : Type) (r : brel S), 
          brel_negate S r → brel_negate S (brel_and_sym S r). 
Proof. unfold brel_negate, brel_and_sym. 
       intros S r [f Pf]. exists f. intro s. 
       destruct (Pf s) as [L R]. rewrite L, R. auto. 
Defined. 


Definition brel_and_sym_nonrivial : ∀ (S : Type) (r : brel S), 
        brel_reflexive S r → 
        brel_nontrivial S r → 
           brel_nontrivial S (brel_and_sym S r)
:= λ S r refS ntS, 
   {| 
      brel_nontrivial_witness := brel_and_sym_witness S r refS (brel_nontrivial_witness S r ntS)
    ; brel_nontrivial_negate  := brel_and_sym_negate S r (brel_nontrivial_negate S r ntS)
   |}. 

