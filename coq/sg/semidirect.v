Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.product.

Require Import CAS.coq.tr.properties. 
Require Import CAS.coq.st.properties. 


(*  
    f : S -> T -> T         

    s |> t === f s t
 
    (s.s') |> t = s |> (s' |> t)    [f (s.s') t = f s' (f s t)]

*) 
Definition ltr_is_action (T S: Type) (rS : brel S) (bT : binary_op T) (f : ltr_type T S)
  := ∀ (t1 t2 : T) (s : S), rS (f (bT t1 t2) s) (f t1 (f t2 s)) = true.


Section Computation. 

(*
    (s1, t1) X| (s2, t2) = (s1 . (t1 |> s2), t1 * t2) 
*) 
Definition bop_left_semidirect (L S : Type) (bS : binary_op S) (bT : binary_op L) (f : ltr_type L S) : binary_op (S * L) 
:= λ x y,  
   match x, y with
    | (s1, t1), (s2, t2) => (bS s1 (f t1 s2), bT t1 t2) 
   end.


(* or should we treat this as a left tranform? 


    (l, t1) X| (s, t2) = (l |1> (t1 |2> s), t1 * t2) 
*) 
Definition ltr_left_semidirect (L1 T S : Type) (ltr1 : ltr_type L1 S) (bT : binary_op T) (ltr2 : ltr_type T S) : ltr_type (L1 * T) (S * T) 
:= λ x y,  
   match x, y with
    | (l, t1), (s, t2) => (ltr1 l (ltr2 t1 s), bT t1 t2) 
   end.

End Computation. 

Section SG_Theory.

Variable S T : Type. 
Variable eqS : brel S. 
Variable eqT : brel T.

Variable refS : brel_reflexive S eqS. 
Variable symS : brel_symmetric S eqS.
Variable trnS : brel_transitive S eqS.


Variable timesS : binary_op S. 
Variable timesT: binary_op T.
Variable f  : ltr_type T S.

Variable congS : bop_congruence S eqS timesS.
Variable congT : bop_congruence T eqT timesT.
Variable congLtr : ltr_congruence T S eqT eqS f.



Local Notation "a =S b"  := (eqS a b = true) (at level 15).
Local Notation "a !=S b"  := (eqS a b = false) (at level 15).
Local Notation "a =T b"  := (eqT a b = true) (at level 15).
Local Notation "a == b"  := (brel_product S T eqS eqT a b = true) (at level 15).
Local Notation "a *S b"  := (timesS a b) (at level 15).
Local Notation "a *T b"  := (timesT a b) (at level 15).
Local Notation "a |> b"  := (f a b) (at level 15).
Local Notation "bs [X|] bT"  := (bop_left_semidirect T S timesS timesT f) (at level 15).
Local Notation "a X| b"  := (bop_left_semidirect T S timesS timesT f a b) (at level 15).

Local Notation "a <*> b"  := (brel_product a b) (at level 15).
Local Notation "a [*] b"  := (bop_product a b) (at level 15).


Definition sg_semidirect := bop_left_semidirect T S timesS timesT f.
  


Lemma bop_left_semidirect_congruence : bop_congruence (S * T) (eqS <*> eqT) sg_semidirect.
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (bop_and_elim _ _ H1) as [C1 C2].
       destruct (bop_and_elim _ _ H2) as [C3 C4].
       apply bop_and_intro. 
       apply congS; auto. apply congT; auto.
Qed. 


Lemma bop_left_semidirect_associative
      (assoS : bop_associative S eqS timesS)
      (assoT : bop_associative T eqT timesT) 
      (disf : slt_distributive T S eqS timesS f)
      (act  : ltr_is_action T S eqS timesT f) : 
   bop_associative (S * T) (eqS <*> eqT) sg_semidirect. 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply bop_and_intro. 
          (* show ((s1 *S (t1 |> s2)) *S ((t1 *T t2) |> s3)) =S (s1 *S (t1 |> (s2 *S (t2 |> s3))))

               (s1 *S (t1 |> s2)) *S ((t1 *T t2) |> s3)
            = {act} 
               (s1 *S (t1 |> s2)) *S (t1 |> (t2 |> s3))
            = {assoS} 
               s1 *S ((t1 |> s2) *S (t1 |> (t2 |> s3)))
            = {diss} 
               s1 *S (t1 |> (s2 *S (t2 |> s3)))
          *) 
          assert (fact1 := act t1 t2 s3). 
          assert (fact2 := disf t1 s2 (f t2 s3)).
          assert (fact3 := congS _ _ _ _ (refS (s1 *S f t1 s2)) fact1). 
          assert (fact4 := assoS s1 (f t1 s2) (f t1 (f t2 s3))). 
          assert (fact5 := trnS _ _ _ fact3 fact4). 
          assert (fact6 := congS _ _ _ _ (refS s1) fact2). apply symS in fact6.
          assert (fact7 := trnS _ _ _ fact5 fact6). 
          assumption. 
          apply assoT.
Qed. 

(* 
The problem with the semigroup version is that it is very 
hard to prove basic properties without introducing a lot of 
crazy new properties.   A few examples are given below. 
*) 
Lemma bop_left_semidirect_commutative 
      (crazy : ∀ (s1 s2 : S) (t1 t2 : T), (s1 *S (t1 |> s2)) =S (s2 *S (t2 |> s1)))
      (commT : bop_commutative T eqT timesT) : 
         bop_commutative (S * T) (eqS <*> eqT) sg_semidirect. 
Proof. intros (s1, t1) (s2, t2). simpl. 
       apply bop_and_intro. apply crazy. apply commT. 
Defined. 


Lemma bop_left_semidirect_selective 
      (crazy : ∀ (s1 s2 : S) (t1 t2 : T),
          ((t1 *T t2) =T t1 -> (s1 *S (t1 |> s2)) =S s1)
          *
          ((t1 *T t2) =T t2 -> (s1 *S (t1 |> s2)) =S s2))
      (selT : bop_selective T eqT timesT) : 
         bop_selective (S * T) (eqS <*> eqT) sg_semidirect. 
Proof. intros (s1, t1) (s2, t2). simpl.
       destruct (crazy s1 s2 t1 t2) as [C1 C2]. 
       destruct (selT t1 t2) as [A | A].
       + left. apply bop_and_intro. 
         ++ apply C1; auto. 
         ++ exact A. 
       + right. apply bop_and_intro. 
         ++ apply C2; auto. 
         ++ exact A. 
Qed. 


Lemma bop_left_semidirect_idempotent 
      (crazy : ∀ (s : S) (t : T),  (s *S (t |> s)) =S s) 
      (idemT : bop_idempotent T eqT timesT) : 
         bop_idempotent (S * T) (eqS <*> eqT) sg_semidirect. 
Proof. intros (s, t). simpl. apply bop_and_intro. 
       + apply crazy. 
       + apply idemT. 
Qed. 


End SG_Theory.   


Section LTR_Theory.

  
End LTR_Theory.   

Section ACAS.

(*  
Record left_transform_proofs (L S : Type) (eqS : brel S) (eqL : brel L) (ltr : ltr_type L S) := 
{
  A_left_transform_congruence          : ltr_congruence L S eqL eqS ltr    
; A_left_transform_is_right_d          : ltr_is_right_decidable L S eqS ltr
; A_left_transform_left_constant_d     : ltr_left_constant_decidable L S eqS ltr                                                       
; A_left_transform_left_cancellative_d : ltr_left_cancellative_decidable L S eqS ltr
}.


Record A_left_transform (L S : Type) :=
{
  A_left_transform_carrier      : A_eqv S
; A_left_transform_label        : A_eqv L                                                       
; A_left_transform_ltr          : ltr_type L S (* T -> (S -> S) *)
; A_left_transform_exists_id_d  : ltr_exists_id_decidable L S  (A_eqv_eq S A_left_transform_carrier) A_left_transform_ltr 
; A_left_transform_exists_ann_d : ltr_exists_ann_decidable L S (A_eqv_eq S A_left_transform_carrier) A_left_transform_ltr 
; A_left_transform_proofs       : left_transform_proofs L S (A_eqv_eq S A_left_transform_carrier) (A_eqv_eq L A_left_transform_label)  A_left_transform_ltr
; A_left_transform_ast          : cas_ltr_ast
}.
 *)
  
End ACAS. 
