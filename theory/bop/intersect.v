Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.facts.
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.
Require Import CAS.theory.brel.add_constant.
Require Import CAS.theory.bop.add_id.


Section Intersect.
  Variable S: Type.
  Variable eq : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S eq f. 
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.

Lemma in_set_bop_intersect_intro : ∀ (X Y : finite_set S) (a : S),
       (in_set eq X a = true) * (in_set eq Y a = true) → in_set eq (bop_intersect eq X Y) a = true. 
Proof. intros X Y a H. unfold bop_intersect. 
       apply in_set_filter_intro; auto.
       apply in_set_bProp_congruence; auto.
Qed. 


Lemma in_set_bop_intersect_elim : ∀ (X Y : finite_set S) (a : S),
       in_set eq (bop_intersect eq X Y) a = true  → (in_set eq X a = true) * (in_set eq Y a = true). 
Proof. intros X Y a H. 
       unfold bop_intersect in H. 
       apply in_set_filter_elim in H. assumption.
       apply in_set_bProp_congruence; auto. 
Qed. 

(* 

Issue with intersect : If the carrier set S is infinite, 
then the id for intersect is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the id. 


The "bop_intersect_..._raw" results below capture the properties 
of union before the id is added. 

*) 





Lemma bop_intersect_congruence_raw : bop_congruence (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. unfold bop_intersect. unfold bop_congruence. 
       assert (fact := brel_set_congruence S eq refS symS tranS). 
       intros s1 s2 t1 t2 H1 H2. 
       unfold brel_congruence in fact. 
       apply brel_set_intro_prop; auto. 
       split. 
          intros a J. 
          apply in_set_filter_intro; auto.
          apply in_set_bProp_congruence; auto.
          apply in_set_filter_elim in J. destruct J as [JL JR].
          assert(fact1 := in_set_left_congruence S eq symS tranS a _ _ H1).
          assert(fact2 := in_set_left_congruence S eq symS tranS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 
          apply in_set_bProp_congruence; auto. 
          intros a J. 
          apply in_set_filter_intro; auto.
          apply in_set_bProp_congruence; auto. 
          apply in_set_filter_elim in J. destruct J as [JL JR]. 
          assert(fact1 := in_set_left_congruence S eq symS tranS a _ _ H1).
          assert(fact2 := in_set_left_congruence S eq symS tranS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 
       apply in_set_bProp_congruence; auto. 
Qed. 

(* simplify?  theorems about composition? *) 
Lemma bop_intersect_associative_raw : bop_associative (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intros s t u. apply brel_set_intro_prop; auto. 
       split. 
          intros a H.
          assert (J : bProp_congruence S eq (in_set eq s)). apply in_set_bProp_congruence; auto.
          assert (K : bProp_congruence S eq (in_set eq t)). apply in_set_bProp_congruence; auto.          
         apply in_set_filter_intro; auto. 
         apply in_set_filter_elim in H; auto.  
         destruct H as [HL HR]. apply in_set_filter_elim in HL; auto. 
         destruct HL as [HLL HLR]. 
         split;auto.            
            apply in_set_filter_intro; auto. 
            apply in_set_bProp_congruence; auto.

         intros a H. 
         apply in_set_filter_intro; auto. 
         apply in_set_bProp_congruence; auto.
         assert (J : bProp_congruence S eq (in_set eq s)). apply in_set_bProp_congruence; auto.
         assert (K : bProp_congruence S eq (in_set eq t)). apply in_set_bProp_congruence; auto.          
         apply in_set_filter_elim in H; auto. 
         destruct H as [HL HR]. apply in_set_filter_elim in HR; auto. 
         destruct HR as [HRL HRR]. 
         split; auto. 
            apply in_set_filter_intro; auto. 
Qed. 

Lemma bop_intersect_idempotent_raw : bop_idempotent (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intro s. destruct s. 
          compute. reflexivity.
          unfold brel_set. unfold brel_and_sym. apply andb_is_true_right. 
          split.
             apply brel_subset_intro; auto. 
             intros x H. 
             apply in_set_filter_elim in H.
             destruct H as [HL HR]. assumption. 
             apply in_set_bProp_congruence; auto.
             apply brel_subset_intro; auto. 
             intros x H. 
             apply in_set_filter_intro; auto. 
             apply in_set_bProp_congruence; auto.
Qed. 

Lemma uop_filter_false_is_nil : ∀ (X : finite_set S), filter (λ _ : S, false) X = nil.
Proof. unfold uop_filter. induction X; compute; auto. Qed. 

Lemma bop_intersect_commutative_raw : bop_commutative(finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intros s t. destruct s; destruct t. 
          compute; auto.
          unfold bop_intersect.  unfold in_set at 1. 
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          unfold bop_intersect.  unfold in_set at 2.           
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          apply brel_set_intro_prop; auto. 
          split; intros x H. 
             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro; auto.
             apply in_set_bProp_congruence; auto.
             apply in_set_bProp_congruence; auto.             

             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro; auto.
             apply in_set_bProp_congruence; auto.
             apply in_set_bProp_congruence; auto.             
Qed. 

Lemma bop_intersect_not_selective_raw : bop_not_selective (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists ((wS ::nil), ((f wS) :: nil)).
       destruct (ntS wS) as [L R].
       split; unfold bop_intersect; unfold uop_filter; unfold filter; unfold in_set; rewrite R; compute; auto. 
Defined. 

Lemma bop_intersect_nil :  ∀ (X : finite_set S), brel_set eq (bop_intersect eq nil X) nil = true. 
Proof. intro X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_intersect_elim in H; auto. 
       destruct H as [HL  HR]. 
       assumption. 
       apply brel_subset_intro; auto. 
       intros a H. compute in H. discriminate. 
Defined. 


Lemma bop_intersect_nil_is_ann : bop_is_ann (finite_set S) (brel_set eq) (bop_intersect eq) nil. 
Proof. unfold bop_is_ann. 
       intro s. 
       assert (fact1 : brel_set eq (bop_intersect eq nil s) nil = true). 
          apply bop_intersect_nil; auto. 
       assert (fact2 : brel_set eq (bop_intersect eq s nil) (bop_intersect eq nil s) = true). 
          apply bop_intersect_commutative_raw; auto. 
       assert (fact3 : brel_set eq (bop_intersect eq s nil) nil = true). 
          apply (brel_set_transitive S eq refS symS tranS _ _ _ fact2 fact1). 
       rewrite fact1, fact3. auto. 
Defined. 


Lemma bop_intersect_exists_ann_raw : bop_exists_ann (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists nil. apply bop_intersect_nil_is_ann. Defined. 


(* ************************************* cooked ************************************* *) 

Variable c : cas_constant. 

Lemma bop_intersect_associative : 
        bop_associative
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_associative; auto. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_associative_raw; auto. 
Qed. 


Lemma bop_intersect_congruence : 
        bop_congruence
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_congruence; auto.
       apply brel_set_symmetric; auto.        
       apply bop_intersect_congruence_raw; auto.        
Qed. 


Lemma bop_intersect_commutative : 
        bop_commutative
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_commutative; auto. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_commutative_raw; auto. 
Qed. 

Lemma bop_intersect_idempotent : 
        bop_idempotent
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_idempotent. apply bop_intersect_idempotent_raw; auto. Qed. 

Lemma bop_intersect_not_selective : 
        bop_not_selective
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_not_selective. apply bop_intersect_not_selective_raw; auto. Defined. 

Lemma bop_intersect_exists_id : 
        bop_exists_id
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_exists_id.  apply brel_set_reflexive; auto. Defined. 


Lemma bop_intersect_exists_ann : 
        bop_exists_ann
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_exists_ann; auto. 
       apply brel_set_reflexive; auto.        
       apply bop_intersect_exists_ann_raw; auto. 
Defined. 

(* not needed as intersect is sg_CI ?
Lemma bop_intersect_not_is_left : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_is_left
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply bop_commutative_implies_not_is_left. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply brel_add_constant_symmetric; auto.      
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_transitive; auto.      
       apply brel_set_transitive; auto. 
       apply bop_intersect_commutative; auto. 
Defined. 



Lemma bop_intersect_not_is_right : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_is_right
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply bop_commutative_implies_not_is_right. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply brel_add_constant_symmetric; auto.      
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_transitive; auto.      
       apply brel_set_transitive; auto. 
       apply bop_intersect_commutative; auto. 
Defined. 



Lemma bop_intersect_not_left_cancellative : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_left_cancellative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_ann_implies_not_left_cancellative. 
       apply brel_add_constant_reflexive. 
       apply brel_set_reflexive; auto. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_ann; auto. 
Defined. 



Lemma bop_intersect_not_right_cancellative : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_right_cancellative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_ann_implies_not_right_cancellative. 
       apply brel_add_constant_reflexive. 
       apply brel_set_reflexive; auto. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_ann; auto. 
Defined. 


Lemma bop_intersect_not_left_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_left_constant
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_id_implies_not_left_constant. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_right_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_right_constant
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_id_implies_not_right_constant. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_anti_left : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_anti_left
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c refS symS transS. 
       apply exists_id_implies_not_anti_left. 
       apply brel_add_constant_symmetric; auto.
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_witness. 
       apply brel_set_witness. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_anti_right : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_anti_right
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c refS symS transS. 
       apply exists_id_implies_not_anti_right. 
       apply brel_add_constant_symmetric; auto.
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_witness. 
       apply brel_set_witness. 
       apply bop_intersect_exists_id; auto. 
Defined. 

*) 
End Intersect. 