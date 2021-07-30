Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.theory.in_set. 


Open Scope list_scope.

(* because the definitions have changed too often .... *) 
Lemma yet_another_sanity_check (S : Type) (rS : brel S) (bS : binary_op S)
      (sym : brel_symmetric S rS)
      (comm : bop_commutative S rS bS) 
      (bf : something_is_finite S rS bS)
      (bnf : something_not_is_finite S rS bS) : true = false.
Proof. destruct bf as [[BOTTOMS w] [A B]].
       destruct bnf as [F C].
       destruct (C BOTTOMS A) as [D E].
       destruct (B (F BOTTOMS)) as [G | G].
          rewrite G in D. discriminate D.
          destruct G as [G1 [G2 G3]].
          assert (H := E _ G1). 
          destruct H as [H | H].
             rewrite H in G2. discriminate G2.
             rewrite H in G3. discriminate G3.
Defined.  

Lemma exists_ann_implies_something_is_finite (T : Type) (eq : brel T) (b : binary_op T)
      (cong : bop_congruence T eq b)
      (ref : brel_reflexive T eq)
      (sym : brel_symmetric T eq)
      (trn : brel_transitive T eq)
      (comm : bop_commutative T eq b) 
      (idm : bop_idempotent T eq b)
      (g : T -> T)                 
      (Pg : brel_not_trivial T eq g)
      (ann : bop_exists_ann T eq b) : 
  something_is_finite T eq b.
Proof. destruct ann as [a P]. unfold something_is_finite. 
       exists (a::nil, λ t, a).  split. 
          intros s A t B. left. 
          apply (in_set_singleton_elim T eq sym) in A. 
          apply (in_set_singleton_elim T eq sym) in B. 
          assert (C := P a). destruct C as [_ C].
          assert (D := cong _ _ _ _ A B).                     
          assert (E := cong _ _ _ _ B A).                     
          apply sym in A. apply sym in B. apply sym in C. 
          assert (F := trn _ _ _ B (trn _ _ _ C E)). 
          assert (G := trn _ _ _ A (trn _ _ _ C D)). split. 
             exact F.
             exact G. 
          intro s.
          case_eq(eq a s); intro A. 
             left. apply (in_set_singleton_intro T eq sym). exact A. 
             right.
                assert (B := P s). destruct B as [B1 B2]. split. 
                apply (in_set_singleton_intro T eq sym). apply ref.
                split. apply sym. exact B1. 
                case_eq(eq s (b s a)); intro C; auto. 
                   destruct (P s) as [D E].
                   assert (F := trn _ _ _ C E). apply sym in F. 
                   rewrite F in A. discriminate A. 
Qed.


Lemma not_exists_ann_implies_something_is_not_finite (T : Type) (F : list T → T)  (eq : brel T) (b : binary_op T)
      (cong : bop_congruence T eq b)
      (ref : brel_reflexive T eq)
      (sym : brel_symmetric T eq)
      (trn : brel_transitive T eq)
      (comm : bop_commutative T eq b) 
      (idm : bop_idempotent T eq b)
      (g : T -> T)                 
      (Pg : brel_not_trivial T eq g)
      (ann : bop_not_exists_ann T eq b) : 
  something_not_is_finite T eq b.
Proof. unfold something_not_is_finite. exists F.
       unfold bop_not_exists_ann in ann. unfold bop_not_is_ann in ann. 
       intros B I. split.
          admit. 
          intros s C.          
Admitted.