Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.dual.
Require Import CAS.coq.po.from_sg.

Require Import CAS.coq.sg.properties.

Require Import CAS.coq.os.properties.



(*********************** OS properties ************************************)

Section GLB_LUB.
  
Variables (S : Type) (eq lte : brel S) (bS : binary_op S). 

Lemma lower_bound_implies_dual_upper_bound (s t u : S) : 
       is_lower_bound lte s t u -> is_upper_bound (brel_dual lte) s t u. 
Proof. compute. auto. Qed. 

Lemma dual_upper_bound_implies_lower_bound (s t u : S) : 
       is_upper_bound (brel_dual lte) s t u -> is_lower_bound lte s t u. 
Proof. compute. auto. Qed. 

Lemma upper_bound_implies_dual_lower_bound (s t u : S) : 
       is_upper_bound lte s t u -> is_lower_bound (brel_dual lte) s t u. 
Proof. compute. auto. Qed. 

Lemma dual_lower_bound_implies_upper_bound  (s t u : S) : 
       is_lower_bound (brel_dual lte) s t u -> is_upper_bound lte s t u. 
Proof. compute. auto. Qed. 

       
Lemma glb_implies_dual_lub (b : binary_op S) (P : bop_is_glb lte b) : bop_is_lub (brel_dual lte) b.
Proof. intros s t.
       assert (A := P s t). unfold is_glb in A. destruct A as [A B]. 
       unfold is_lub. split. 
       - apply lower_bound_implies_dual_upper_bound; auto. 
       - intros u C.
         unfold brel_dual. apply B.
         apply dual_upper_bound_implies_lower_bound; auto. 
Qed. 

Lemma lub_implies_dual_glb (b : binary_op S) (P : bop_is_lub lte b) : bop_is_glb (brel_dual lte) b.
Proof. intros s t.
       assert (A := P s t). unfold is_lub in A. destruct A as [A B]. 
       unfold is_glb. split. 
       - apply upper_bound_implies_dual_lower_bound; auto. 
       - intros u C.
         unfold brel_dual. apply B.
         apply dual_lower_bound_implies_upper_bound; auto. 
Qed. 

End GLB_LUB.

Section GLB_LUB_Right_Left. 

Variables (S : Type) (eq lte : brel S) (bS : binary_op S) 
         (refS : brel_reflexive S eq)
         (symS : brel_symmetric S eq)
         (trnS : brel_transitive S eq)          
         (assoS : bop_associative S eq bS)
         (congS : bop_congruence S eq bS)
         (idemS : bop_idempotent S eq bS)
         (commS : bop_commutative S eq bS).

Notation "a == b"    := (eq a b = true) (at level 30).
Notation "a != b"    := (eq a b = false) (at level 30).
Notation "a (+) b"   := (bS a b) (at level 15).


Lemma bop_is_glb_wrt_lte_left : bop_is_glb (brel_lte_left eq bS) bS.
Proof. intros a b. split; compute. split.
       assert (F0 := idemS a). apply symS in F0.
       assert (F1 := commS a b). 
       assert (F2 := congS _ _ _ _ F0 (refS b)).
       assert (F3 := assoS a a b).        
       assert (F4 := congS _ _ _ _ (refS a) F1).
       assert (F5 := assoS a b a).  apply symS in F5.
       assert (R := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F2 F3) F4) F5).
       exact R.

       assert (F0 := idemS b). apply symS in F0. 
       assert (F1 := congS _ _ _ _ (refS a) F0).              
       assert (F2 := assoS a b b).  apply symS in F2.
       assert (R := trnS _ _ _ F1 F2).
       exact R.

       intros c [L R].
       assert (F0 := idemS c). apply symS in F0.
       assert (F1 := congS _ _ _ _ L R).
       assert (F2 := assoS c a (c (+) b)).
       assert (F3 := commS a (c (+) b)).
       assert (F4 := congS _ _ _ _ (refS c) F3).
       assert (F5 := assoS c (c (+) b) a).  apply symS in F5.
       assert (F6 := assoS c c b).  apply symS in F6.
       assert (F7 := congS _ _ _ _ F6 (refS a)).
       assert (F8 := assoS (c (+) c) b a).  
       assert (F9 := commS b a).       apply symS in F0.
       assert (F10 := congS _ _ _ _ F0 F9). apply symS in F0.
       assert (C := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F0 F1) F2) F4) F5) F7) F8) F10).       
       exact C.
Qed. 

Lemma bop_is_lub_wrt_lte_right : bop_is_lub (brel_lte_right eq bS) bS.
Proof. intros a b. split; compute. split.
       assert (F0 := idemS a). apply symS in F0. 
       assert (F1 := congS _ _ _ _ F0 (refS b)).              
       assert (F2 := assoS a a b).  
       assert (R := trnS _ _ _ F1 F2).
       exact R.
       
       assert (F0 := idemS b). apply symS in F0.
       assert (F1 := commS a b). 
       assert (F2 := congS _ _ _ _ (refS a) F0).
       assert (F3 := assoS a b b).  apply symS in F3.      
       assert (F4 := congS _ _ _ _ F1 (refS b)).
       assert (F5 := assoS b a b).  
       assert (R := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F2 F3) F4) F5).        
       exact R. 

       intros c [L R].
       assert (F0 := idemS c). apply symS in F0.
       assert (F1 := congS _ _ _ _ L R).
       assert (F2 := assoS a c (b (+) c)).
       assert (F3 := commS c (b (+) c)).
       assert (F4 := congS _ _ _ _ (refS a) F3).
       assert (F6 := assoS b c c).  
       assert (F7 := congS _ _ _ _ (refS a) F6).
       assert (F8 := assoS a b (c (+) c)).  apply symS in F8. apply symS in F0. 
       assert (F10 := congS _ _ _ _ (refS (a (+) b)) F0). apply symS in F0.
       assert (C := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F0 F1) F2) F4) F7) F8) F10).       
       exact C.
Qed.

End GLB_LUB_Right_Left. 



