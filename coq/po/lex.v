Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Section Computation.

Definition brel_lex_left : ∀ {S T : Type}, brel S → brel T → brel (S * T) 
:= λ {S T} lteS lteT x y,  
   match x, y with
   | (a, b), (c, d) => bop_or (below lteS c a)
                              (bop_and (equiv lteS a c) (lteT b d)) 
   end.

End Computation.   

Section Theory.

Variable S  : Type. 
Variable T  : Type. 

Variable eqS  : brel S.
Variable conS : brel_congruence S eqS eqS. 
Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.
Variable trnS : brel_transitive S eqS.

Variable eqT : brel T. 
Variable conT : brel_congruence T eqT eqT. 
Variable refT : brel_reflexive T eqT.
Variable trnT : brel_transitive T eqT.

Variable lteS    : brel S. 
Variable lteConS : brel_congruence S eqS lteS. 
Variable lteTrnS : brel_transitive S lteS.

Variable lteT    : brel T. 
Variable lteConT : brel_congruence T eqT lteT. 
Variable lteTrnT : brel_transitive T lteT.

Notation "p <*> q" := (brel_product p q) (at level 15).
Notation "p [*] q" := (brel_lex_left p q) (at level 15).


Notation "a =S b"   := (eqS a b = true) (at level 15).
Notation "a !=S b"  := (eqS a b = false) (at level 15).
Notation "a =T b"   := (eqT a b = true) (at level 15).
Notation "a !=T b"  := (eqT a b = false) (at level 15).
Notation "a <=S b"  := (lteS a b = true) (at level 15).
Notation "a !<=S b" := (lteS a b = false) (at level 15).
Notation "a <=T b"  := (lteT a b = true) (at level 15).
Notation "a !<=T b" := (lteT a b = false) (at level 15).
Notation "a <S b"   := (below lteS b a = true) (at level 15).
Notation "a !<S b"  := (below lteS b a = false) (at level 15).
Notation "a <T b"   := (below lteT b a = true) (at level 15).
Notation "a !<T b"  := (below lteT b a = false) (at level 15).


Lemma brel_lex_left_congruence : brel_congruence (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]; intros H1 H2.
       unfold brel_product in H1, H2. 
       destruct (bop_and_elim _ _ H1) as [C1 C2].
       destruct (bop_and_elim _ _ H2) as [C3 C4].
       unfold brel_lex_left. 
       rewrite (equiv_congruence S eqS lteS lteConS _ _ _ _ C1 C3). 
       rewrite (lteConT _ _ _ _ C2 C4). 
       rewrite (below_congruence S eqS lteS lteConS _ _ _ _ C3 C1). 
       reflexivity.
Qed.        

Lemma brel_lex_left_reflexive :
      brel_reflexive S lteS -> brel_reflexive T lteT -> 
        brel_reflexive (S * T) (lteS [*] lteT). 
Proof. intros lteRefS lteRefT [s t]. unfold brel_lex_left.
       apply bop_or_intro. right.
       apply bop_and_intro.
          apply equiv_reflexive; auto. 
          apply lteRefT.
Qed.           

Lemma brel_lex_left_transitive : brel_transitive (S * T) (lteS [*] lteT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. unfold brel_lex_left.
       intros A B.
       apply bop_or_intro.        
       apply bop_or_elim in A. apply bop_or_elim in B. 
       destruct A as [A | A]; destruct B as [B | B]. 
       - left. apply (below_transitive S lteS lteTrnS _ _ _ A B). 
       - apply bop_and_elim in B. destruct B as [B1 B2]. 
         left. apply equiv_elim in B1. destruct B1 as [_ B1].
         apply (below_pseudo_transitive_right S lteS lteTrnS _ _ _ A B1). 
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply equiv_elim in A1. destruct A1 as [_ A1].
         left. apply (below_pseudo_transitive_left S lteS lteTrnS _ _ _ A1 B).
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply bop_and_elim in B. destruct B as [B1 B2].
         right.
         rewrite (lteTrnT _ _ _ A2 B2).
         rewrite (equiv_transitive S lteS lteTrnS _ _ _ B1 A1).
         compute. reflexivity. 
Qed.

Lemma brel_lex_left_antisymmetric :
  brel_antisymmetric S eqS lteS -> brel_antisymmetric T eqT lteT -> 
     brel_antisymmetric (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. intros asymS asymT [s1 t1] [s2 t2]. unfold brel_lex_left.
       intros A B. 
       apply bop_or_elim in A. apply bop_or_elim in B.
       unfold brel_product. 
       destruct A as [A | A]; destruct B as [B | B]. 
       - assert (C := below_transitive S lteS lteTrnS _ _ _ A B).
         rewrite (below_not_reflexive S lteS s1) in C. discriminate C.
       - apply bop_and_elim in B. destruct B as [B1 B2]. 
         apply equiv_elim in B1. destruct B1 as [_ B1].
         assert (C := below_pseudo_transitive_right S lteS lteTrnS _ _ _ A B1). 
         rewrite (below_not_reflexive S lteS s1) in C. discriminate C.
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply equiv_elim in A1. destruct A1 as [_ A1].
         assert (C := below_pseudo_transitive_left S lteS lteTrnS _ _ _ A1 B).
         rewrite (below_not_reflexive S lteS s1) in C. discriminate C.
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply bop_and_elim in B. destruct B as [B1 B2].
         rewrite (asymT _ _ A2 B2).
         apply equiv_elim in A1. destruct A1 as [A1 A3].
         rewrite (asymS _ _ A3 A1).         
         compute. reflexivity. 
Qed. 


End Theory. 
