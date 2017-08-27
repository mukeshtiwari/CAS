
Require Import CAS.code.basic_types. 
Require Import CAS.code.ast.
Require Import CAS.code.brel. 
Require Import CAS.code.bop.

Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 


Definition bops_id_equals_ann_II (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { i : S & (bop_is_id S r b1 i) * (bop_is_ann S r b2 i)}. 

Definition bop_is_glb (S : Type) (lte : brel S) (bop : binary_op S) 
  := ∀ a b : S, (lte (bop a b) a = true) *
                 (lte (bop a b) b = true) *
                 (∀ c : S, ((lte c a = true) * (lte c b = true)) → (lte c (bop a b) = true)). 

Definition bop_is_lub (S : Type) (lte : brel S) (bop : binary_op S) 
  := ∀ a b : S, (lte a (bop a b) = true) *
                 (lte b (bop a b) = true) *
                 (∀ c : S, ((lte a c = true) * (lte b c = true)) → (lte (bop a b) c = true)). 

Section SemiLattice.

Variable S : Type.
Variable eqv : brel S.
Variable nt  : brel_nontrivial S eqv.                  

Variable ref : brel_reflexive S eqv. 
Variable sym : brel_symmetric S eqv.
Variable trn : brel_transitive S eqv.

Variable bop : binary_op S.
 
Variable cng : bop_congruence S eqv bop.
Variable ass : bop_associative S eqv bop.
Variable com : bop_commutative S eqv bop.
Variable idm : bop_idempotent S eqv bop.

Notation "a == b"    := (eqv a b = true) (at level 30).
Notation "a != b"    := (eqv a b = false) (at level 30).
Notation "a (+) b"   := (bop a b) (at level 15).


Lemma bop_is_glb_wrt_llte : bop_is_glb S (brel_llte eqv bop) bop.
Proof. intros a b. split; compute. split.
       assert (F0 := idm a). apply sym in F0.
       assert (F1 := com a b). 
       assert (F2 := cng _ _ _ _ F0 (ref b)).
       assert (F3 := ass a a b).        
       assert (F4 := cng _ _ _ _ (ref a) F1).
       assert (F5 := ass a b a).  apply sym in F5.
       assert (R := trn _ _ _ (trn _ _ _ (trn _ _ _ F2 F3) F4) F5).
       exact R.

       assert (F0 := idm b). apply sym in F0. 
       assert (F1 := cng _ _ _ _ (ref a) F0).              
       assert (F2 := ass a b b).  apply sym in F2.
       assert (R := trn _ _ _ F1 F2).
       exact R.

       intros c [L R].
       assert (F0 := idm c). apply sym in F0.
       assert (F1 := cng _ _ _ _ L R).
       assert (F2 := ass c a (c (+) b)).
       assert (F3 := com a (c (+) b)).
       assert (F4 := cng _ _ _ _ (ref c) F3).
       assert (F5 := ass c (c (+) b) a).  apply sym in F5.
       assert (F6 := ass c c b).  apply sym in F6.
       assert (F7 := cng _ _ _ _ F6 (ref a)).
       assert (F8 := ass (c (+) c) b a).  
       assert (F9 := com b a).       apply sym in F0.
       assert (F10 := cng _ _ _ _ F0 F9). apply sym in F0.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ F0 F1) F2) F4) F5) F7) F8) F10).       
       exact C.
Qed. 

Lemma bop_is_lub_wrt_rlte : bop_is_lub S (brel_rlte eqv bop) bop.
Proof. intros a b. split; compute. split.

       assert (F0 := idm a). apply sym in F0. 
       assert (F1 := cng _ _ _ _ F0 (ref b)).              
       assert (F2 := ass a a b).  
       assert (R := trn _ _ _ F1 F2).
       exact R.
       
       assert (F0 := idm b). apply sym in F0.
       assert (F1 := com a b). 
       assert (F2 := cng _ _ _ _ (ref a) F0).
       assert (F3 := ass a b b).  apply sym in F3.      
       assert (F4 := cng _ _ _ _ F1 (ref b)).
       assert (F5 := ass b a b).  
       assert (R := trn _ _ _ (trn _ _ _ (trn _ _ _ F2 F3) F4) F5).        
       exact R. 

       intros c [L R].
       assert (F0 := idm c). apply sym in F0.
       assert (F1 := cng _ _ _ _ L R).
       assert (F2 := ass a c (b (+) c)).
       assert (F3 := com c (b (+) c)).
       assert (F4 := cng _ _ _ _ (ref a) F3).
       assert (F6 := ass b c c).  
       assert (F7 := cng _ _ _ _ (ref a) F6).
       assert (F8 := ass a b (c (+) c)).  apply sym in F8. apply sym in F0. 
       assert (F10 := cng _ _ _ _ (ref (a (+) b)) F0). apply sym in F0.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ F0 F1) F2) F4) F7) F8) F10).       
       exact C.
Qed. 


End SemiLattice.
