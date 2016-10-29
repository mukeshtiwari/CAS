Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.add_constant.
Require Import CAS.theory.brel.set.
Require Import CAS.theory.uop.duplicate_elim. 
Require Import CAS.theory.bop.add_id. 

Lemma in_set_bop_intersect_intro : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S) (a : S),
      brel_symmetric S eq →
      brel_transitive S eq →
       (in_set S eq X a = true) * (in_set S eq Y a = true) →
         in_set S eq (bop_intersect S eq X Y) a = true. 
Proof. intros S eq lt X Y a symS transS H. 
       unfold bop_intersect. 
       apply in_set_filter_intro; auto.
       apply in_set_bProp_congruence; auto. 
Defined. 


Lemma in_set_bop_intersect_elim : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S) (a : S),
      brel_symmetric S eq →
      brel_transitive S eq →
       in_set S eq (bop_intersect S eq X Y) a = true  →
       (in_set S eq X a = true) * (in_set S eq Y a = true). 
Proof. intros S eq lt X Y a symS transS H. 
       unfold bop_intersect in H. 
       apply in_set_filter_elim in H. assumption. 
       apply in_set_bProp_congruence; auto. 
Defined. 

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


(* 
   ∀ (t : S) (s1 s2 : finite_set S),
   brel_set S X s1 s2 = true → in_set S X s1 t = in_set S X s2 t
*) 
Lemma in_set_left_congruence : 
       ∀ (S : Type) (r : brel S),
       brel_symmetric S r -> brel_transitive S r -> 
         brel2_left_congruence (finite_set S) S (brel_set S r) (in_set S r). 
Proof. intros S r symS transS. unfold brel2_left_congruence.
       intros t s1 s2 H. 
       apply brel_set_elim_prop in H; auto. destruct H as [L R]. 
       case_eq(in_set S r s1 t); intro J; 
       case_eq(in_set S r s2 t); intro K; auto.  
          rewrite (L t J) in K. assumption. 
          rewrite (R t K) in J. discriminate. 
Defined. 



Lemma bop_intersect_congruence_raw : 
   ∀ (S : Type) (r : brel S), 
     brel_reflexive S r -> brel_symmetric S r -> brel_transitive S r -> 
           bop_congruence (finite_set S) (brel_set S r) (bop_intersect S r).
Proof. intros S r refS symS transS. unfold bop_intersect. 
       unfold bop_congruence. 
       assert (fact := brel_set_congruence S r refS symS transS). 
       intros s1 s2 t1 t2 H1 H2. 
       unfold brel_congruence in fact. 
       apply brel_set_intro_prop; auto. 
       split. 
          intros a J. 
          apply in_set_filter_intro; auto.  
          apply in_set_bProp_congruence; auto. 
          apply in_set_filter_elim in J. destruct J as [JL JR]. 
          assert(fact1 := in_set_left_congruence _ _ symS transS a _ _ H1).
          assert(fact2 := in_set_left_congruence _ _ symS transS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 

          apply in_set_bProp_congruence; auto. 

          intros a J. 
          apply in_set_filter_intro; auto.  
          apply in_set_bProp_congruence; auto. 
          apply in_set_filter_elim in J. destruct J as [JL JR]. 
          assert(fact1 := in_set_left_congruence _ _ symS transS a _ _ H1).
          assert(fact2 := in_set_left_congruence _ _ symS transS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 

          apply in_set_bProp_congruence; auto. 
Defined. 

(* simplify?  theorems about composition? *) 
Lemma bop_intersect_associative_raw : 
   ∀ (S : Type) (r : brel S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
         bop_associative (finite_set S) (brel_set S r) (bop_intersect S r).
Proof. intros S r refS symS transS. unfold bop_intersect. 
       unfold bop_associative. 
       intros s t u. 
       apply brel_set_intro_prop; auto. 
       split. 
         intros a H. 
         apply in_set_filter_intro. apply in_set_bProp_congruence; auto. 
         apply in_set_filter_elim in H. 
         destruct H as [HL HR]. apply in_set_filter_elim in HL. 
         destruct HL as [HLL HLR]. 
         split.           
            assumption. 
            apply in_set_filter_intro.          apply in_set_bProp_congruence; auto.
            split; assumption. 
         apply in_set_bProp_congruence; auto.
         apply in_set_bProp_congruence; auto. 


         intros a H. 
         apply in_set_filter_intro. apply in_set_bProp_congruence; auto. 
         apply in_set_filter_elim in H. 
         destruct H as [HL HR]. apply in_set_filter_elim in HR. 
         destruct HR as [HRL HRR]. 
         split.           
            apply in_set_filter_intro.          apply in_set_bProp_congruence; auto.
            split; assumption. 
            assumption. 

         apply in_set_bProp_congruence; auto.
         apply in_set_bProp_congruence; auto. 
Defined.

Lemma bop_intersect_idempotent_raw : 
     ∀ (S : Type) 
       (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
           bop_idempotent (finite_set S) (brel_set S r) (bop_intersect S r).
Proof. intros S r refS symS transS. unfold bop_intersect. unfold bop_idempotent.
       intro s. destruct s. 
          compute. reflexivity. 
          apply brel_set_intro_prop; auto. split.          
             intros x H. 
             apply in_set_filter_elim in H. destruct H as [HL HR]. assumption. 
             apply in_set_bProp_congruence; auto.
             intros x H. 
             apply in_set_filter_intro. apply in_set_bProp_congruence; auto.
               split; assumption. 
Defined. 

Lemma uop_filter_false_is_nil : ∀ (S : Type) (X : finite_set S), filter (λ _ : S, false) X = nil.
Proof. unfold uop_filter. intro S. induction X.  
       compute. reflexivity. 
       unfold filter.  unfold filter in IHX. 
       assumption. 
Defined. 

Lemma bop_intersect_commutative_raw : 
   ∀ (S : Type) (r : brel S), 
   brel_reflexive S r -> 
   brel_symmetric S r -> 
   brel_transitive S r -> 
           bop_commutative(finite_set S) (brel_set S r) (bop_intersect S r).
Proof. intros S r refS symS transS. unfold bop_intersect. 
       unfold bop_commutative. 
       intros s t. destruct s; destruct t.  
          compute. reflexivity. 
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity. 
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          apply brel_set_intro_prop; auto. 
          split. 
             intros x H. 
             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro. apply in_set_bProp_congruence; auto.
             rewrite HL, HR. auto. 
             apply in_set_bProp_congruence; auto.             

             intros x H. 
             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro. apply in_set_bProp_congruence; auto.
             rewrite HL, HR. auto. 
             apply in_set_bProp_congruence; auto.             
Defined.

Lemma bop_intersect_not_selective_raw : 
   ∀ (S : Type) (r : brel S), 
   brel_reflexive S r -> 
   brel_symmetric S r -> 
   brel_nontrivial S r -> 
      bop_not_selective (finite_set S) (brel_set S r) (bop_intersect S r).
Proof. intros S r refS symS ntS. unfold bop_intersect, bop_not_selective. 
       destruct (brel_nontrivial_witness _ _ ntS) as [s Ps].
       destruct (brel_nontrivial_negate _ _ ntS) as [f Pf].
       exists ((s ::nil), ((f s) ::nil)). 
       destruct (Pf s) as [L R]. 
       split. 
          unfold uop_filter. unfold filter. unfold in_set. rewrite R. simpl. 
             compute. reflexivity. 
          unfold uop_filter. unfold filter. unfold in_set. rewrite R. simpl. 
             compute. reflexivity. 
Defined.


Lemma bop_intersect_nil : ∀ (S : Type) (r : brel S),
     brel_reflexive S r ->
     brel_symmetric S r -> 
     brel_transitive S r -> 
            ∀ (X : finite_set S), brel_set S r (bop_intersect S r nil X) nil = true. 
Proof. intros S r refS symS transS X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_intersect_elim in H; auto. 
       destruct H as [HL  HR]. 
       assumption. 
       apply brel_subset_intro; auto. 
       intros a H. compute in H. discriminate. 
Defined. 


Lemma bop_intersect_exists_ann_raw : ∀ (S : Type) (r : brel S), 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
         bop_exists_ann (finite_set S) (brel_set S r) (bop_intersect S r).
Proof. intros S r refS symS transS. exists nil. 
       unfold bop_is_ann. 
       intro s. 
       assert (fact1 : brel_set S r (bop_intersect S r nil s) nil = true). 
          apply bop_intersect_nil; auto. 
       assert (fact2 : brel_set S r (bop_intersect S r s nil) (bop_intersect S r nil s) = true). 
          apply bop_intersect_commutative_raw; auto. 
       assert (fact3 : brel_set S r (bop_intersect S r s nil) nil = true). 
          apply (brel_set_transitive S r refS symS transS _ _ _ fact2 fact1). 
       rewrite fact1, fact3. auto. 
Defined. 


(* ************************************* cooked ************************************* *) 


Lemma bop_intersect_associative : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_associative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bop_add_id_associative. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_associative_raw; auto. 
Defined. 


Lemma bop_intersect_congruence : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_congruence
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bop_add_id_congruence. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_congruence_raw; auto. 
Defined. 


Lemma bop_intersect_commutative : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_commutative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bop_add_id_commutative. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_commutative_raw; auto. 
Defined. 


Lemma bop_intersect_idempotent : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_idempotent
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bop_add_id_idempotent. 
       apply bop_intersect_idempotent_raw; auto. 
Defined. 


Lemma bop_intersect_not_selective : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
        bop_not_selective
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS. 
       apply bop_add_id_not_selective.
       apply bop_intersect_not_selective_raw; auto. 
Defined. 


Lemma bop_intersect_exists_id : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_exists_id
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply bop_add_id_exists_id.  
       apply brel_set_reflexive; auto. 

Defined. 


Lemma bop_intersect_exists_ann : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_exists_ann
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS . 
       apply bop_add_id_exists_ann. 
       apply brel_set_reflexive; auto.        
       apply bop_intersect_exists_ann_raw; auto. 
Defined. 


Lemma bop_intersect_not_is_left : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_is_left
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS transS. 
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
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_is_right
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS transS. 
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
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_left_cancellative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS transS. 
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
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_right_cancellative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS transS. 
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
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_left_constant
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS transS. 
       apply exists_id_implies_not_left_constant. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_right_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_right_constant
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c ntS refS symS transS. 
       apply exists_id_implies_not_right_constant. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_anti_left : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_anti_left
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply exists_id_implies_not_anti_left. 
       apply brel_add_constant_symmetric; auto.
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_witness. 
       apply brel_set_witness. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_anti_right : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
        bop_not_anti_right
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S r) c)
            (bop_add_id (finite_set S) (bop_intersect S r) c). 
Proof. intros S r c refS symS transS. 
       apply exists_id_implies_not_anti_right. 
       apply brel_add_constant_symmetric; auto.
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_witness. 
       apply brel_set_witness. 
       apply bop_intersect_exists_id; auto. 
Defined. 







