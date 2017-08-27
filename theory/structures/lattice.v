
Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop.

Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.bs_properties.

Section Lattice.

Variable S : Type.
Variable eqv : brel S.
Variable nt  : brel_nontrivial S eqv.                  

Variable ref : brel_reflexive S eqv. 
Variable sym : brel_symmetric S eqv.
Variable trn : brel_transitive S eqv.

Variable join : binary_op S.  
Variable meet : binary_op S.
 
Variable j_cng : bop_congruence S eqv join.
Variable j_ass : bop_associative S eqv join.
Variable j_com : bop_commutative S eqv join.
Variable j_idm : bop_idempotent S eqv join.

Variable m_cng : bop_congruence S eqv meet.
Variable m_ass : bop_associative S eqv meet.
Variable m_com : bop_commutative S eqv meet.
Variable m_idm : bop_idempotent S eqv meet.

Variable abs      : bops_left_left_absorptive S eqv join meet.
Variable abs_dual : bops_left_left_absorptive S eqv meet join. 

Notation "a == b"    := (eqv a b = true) (at level 30).
Notation "a != b"    := (eqv a b = false) (at level 15).
Notation "a (j) b"   := (join a b) (at level 15).
Notation "a (m) b"   := (meet a b) (at level 15).

Lemma meet_to_join : ∀ (a b : S),  a == a (m) b → b == a (j) b.
Proof. intros a b H.
       assert (F1 := abs b a).
       assert (F2 := m_com a b). apply sym in F2.       
       assert (F4 := j_cng _ _ _ _ (ref b) F2).
       assert (F5 := trn _ _ _ F1 F4). apply sym in H. 
       assert (F6 := j_cng _ _ _ _ (ref b) H).
       assert (F7 := trn _ _ _ F5 F6).
       assert (F8 := j_com b a).
       assert (F9 := trn _ _ _ F7 F8).
       exact F9.
Defined. 

Lemma join_to_meet : ∀ (a b : S),  a == a (j) b → b == a (m) b.
Proof. intros a b H.
       assert (F1 := abs_dual b a).
       assert (F2 := j_com a b). apply sym in F2.       
       assert (F4 := m_cng _ _ _ _ (ref b) F2).
       assert (F5 := trn _ _ _ F1 F4). apply sym in H. 
       assert (F6 := m_cng _ _ _ _ (ref b) H).
       assert (F7 := trn _ _ _ F5 F6).
       assert (F8 := m_com b a).
       assert (F9 := trn _ _ _ F7 F8).
       exact F9.
Qed.

Lemma one_is_join_annihilator: ∀ (i : S),  bop_is_id S eqv meet i → bop_is_ann S eqv join i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply meet_to_join in R.
       split.
       assert (F1 := j_com a i).
       assert (F2 := trn _ _ _ R F1).
       apply sym. exact F2.       
       apply sym. exact R.
Defined. 

Lemma zero_is_meet_annihilator: ∀ (i : S),  bop_is_id S eqv join i → bop_is_ann S eqv meet i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply join_to_meet in R.
       split.
       assert (F1 := m_com a i).
       assert (F2 := trn _ _ _ R F1).
       apply sym. exact F2.       
       apply sym. exact R.
Qed.

Lemma join_annihilator_is_one : ∀ (i : S),  bop_is_ann S eqv join i  → bop_is_id S eqv meet i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply join_to_meet in L.
       split.
       apply sym. exact L.       
       assert (F1 := m_com i a).
       assert (F2 := trn _ _ _ L F1).
       apply sym. exact F2.       
Qed.        

Lemma meet_annihilator_is_zero : ∀ (i : S),  bop_is_ann S eqv meet i  → bop_is_id S eqv join i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply meet_to_join in L.
       split.
       apply sym. exact L.       
       assert (F1 := j_com i a).
       assert (F2 := trn _ _ _ L F1).
       apply sym. exact F2.       
Qed.


Lemma exists_meet_id_implies_exists_join_ann : bop_exists_id S eqv meet -> bop_exists_ann S eqv join.  
Proof. intros [i P]. exists i. apply one_is_join_annihilator; auto. Defined. 

Lemma exists_join_ann_implies_exists_meet_id :  bop_exists_ann S eqv join -> bop_exists_id S eqv meet.  
Proof. intros [a P]. exists a. apply join_annihilator_is_one; auto. Defined. 

Lemma exists_join_id_implies_exists_meet_ann : bop_exists_id S eqv join -> bop_exists_ann S eqv meet.  
Proof. intros [i P]. exists i. apply zero_is_meet_annihilator; auto. Defined. 

Lemma exists_meet_ann_implies_exists_join_id :  bop_exists_ann S eqv meet -> bop_exists_id S eqv join.  
Proof. intros [a P]. exists a. apply meet_annihilator_is_zero; auto. Defined.

Lemma test : bop_exists_id S eqv meet -> bops_id_equals_ann_II S eqv meet join.
Proof. intros [i P]. exists i. split. exact P. apply one_is_join_annihilator. exact P. Qed. 

Lemma test2 : bop_exists_ann S eqv join -> bops_id_equals_ann_II S eqv meet join.
Proof. intros [a P]. exists a. split. apply join_annihilator_is_one. exact P. exact P. Qed. 


Lemma distributive_implies_distributive_dual : bop_left_distributive S eqv join meet -> bop_left_distributive S eqv meet join. 
Proof. intros D a b c. apply sym.
       assert (F0 := D (a (j) b) a c).
       assert (F1 := abs_dual a b).
       assert (F2 := m_com a (a (j) b)). 
       assert (F3 := trn _ _ _ F1 F2).  apply sym in F3. 
       assert (F4 := m_com (a (j) b) c).
       assert (F5 := D c a b).       
       assert (F6 := trn _ _ _ F4 F5).
       assert (F7 := j_cng _ _ _ _ F3 F6).
       assert (F8 := trn _ _ _ F0 F7).
       assert (F9 := m_com c a).
       assert (F10 := m_com c b).
       assert (F11 := j_cng _ _ _ _ F9 F10).
       assert (F12 := j_cng _ _ _ _ (ref a) F11).
       assert (F13 := trn _ _ _ F8 F12).
       assert (F14 := j_ass a (a (m) c) (b (m) c)). apply sym in F14.
       assert (F15 := trn _ _ _ F13 F14).
       assert (F16 := abs a c). apply sym in F16.
       assert (F17 := j_cng _ _ _ _ F16 (ref (b (m) c))).
       assert (R := trn _ _ _ F15 F17).
       exact R. 
Qed.

Lemma distributive_dual_implies_distributive : bop_left_distributive S eqv meet join -> bop_left_distributive S eqv join meet. 
Proof. intros D a b c. apply sym.
       assert (F0 := D (a (m) b) a c).
       assert (F1 := abs a b).
       assert (F2 := j_com a (a (m) b)).
       assert (F3 := trn _ _ _ F1 F2).  apply sym in F3. 
       assert (F4 := j_com (a (m) b) c).
       assert (F5 := D c a b).       
       assert (F6 := trn _ _ _ F4 F5).
       assert (F7 := m_cng _ _ _ _ F3 F6).
       assert (F8 := trn _ _ _ F0 F7).
       assert (F9 := j_com c a).
       assert (F10 := j_com c b).
       assert (F11 := m_cng _ _ _ _ F9 F10).
       assert (F12 := m_cng _ _ _ _ (ref a) F11).
       assert (F13 := trn _ _ _ F8 F12).
       assert (F14 := m_ass a (a (j) c) (b (j) c)). apply sym in F14.
       assert (F15 := trn _ _ _ F13 F14).
       assert (F16 := abs_dual a c). apply sym in F16.
       assert (F17 := m_cng _ _ _ _ F16 (ref (b (j) c))).
       assert (R := trn _ _ _ F15 F17).
       exact R. 
Qed.


(*
a == a (m) 1 
  == a (m) (1 (j) b) 
  == (a (m) 1) (j)  (a (m) b)
  == a (j) (a (m) b)
 *)
Lemma t : bop_exists_id S eqv meet -> bop_left_distributive S eqv join meet -> bops_left_left_absorptive S eqv join meet.
Proof. intros [i P] D a b.
       assert (Q := one_is_join_annihilator i P). 
       destruct (P a) as [L R]. apply sym in R.
       destruct (Q b) as [U V]. apply sym in U.
       assert (F1 := m_cng _ _ _ _ (ref a) U).
       assert (F2 := D a i b).  apply sym in R.
       assert (F3 := j_cng _ _ _ _ R (ref (a (m) b))). apply sym in R.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ R F1) F2) F3). 
       exact C.
Qed.        

Lemma t_dual : bop_exists_id S eqv join -> bop_left_distributive S eqv meet join -> bops_left_left_absorptive S eqv meet join.
Proof. intros [i P] D a b.
       assert (Q := zero_is_meet_annihilator i P). 
       destruct (P a) as [L R]. apply sym in R.
       destruct (Q b) as [U V]. apply sym in U.
       assert (F1 := j_cng _ _ _ _ (ref a) U).
       assert (F2 := D a i b).  apply sym in R.
       assert (F3 := m_cng _ _ _ _ R (ref (a (j) b))). apply sym in R.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ R F1) F2) F3). 
       exact C.
Qed.        

Section DistributiveLattice.

  Variable dis : bop_left_distributive S eqv join meet. 
  
End DistributiveLattice.   

End Lattice.

