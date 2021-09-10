Require Import Coq.Bool.Bool.
Require Export CAS.coq.common.compute.
Require Import CAS.coq.theory.facts.


Definition ltr_congruence (S T : Type) (rS : brel S) (rT : brel T) (f : left_transform S T) := 
   ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> rT (f s1 t1) (f s2 t2) = true.

(*  
    f : S -> T -> T         

    s |> === f s t
 
    (s.s') |> t = s |> (s' |> t)    [f (s.s') t = f s' (f s t)]

*) 
Definition ltr_associative (S T: Type) (rT : brel T) (bS : binary_op S) (f : left_transform S T)
  := ∀ (s1 s2 : S) (t : T), rT (f (bS s1 s2) t) (f s1 (f s2 t)) = true.

(*

  s |> t*t' = (s |> t) * (s |> t') 

*)

Definition ltr_distributive (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := ∀ (s : S) (t1 t2 : T), rT (f s (bT t1 t2)) (bT (f s t1) (f s t2)) = true. 

Definition ltr_idempotent (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := ∀ (s : S) (t : T), rT (bT t (f s t)) t = true. 

Definition ltr_not_idempotent (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := { z : (S * T) & 
        match z with (s, t) => 
               rT (bT t (f s t)) t = false 
        end 
      }.

Definition bop_is_left_id (S : Type) (r : brel S) (b : binary_op S) (i : S) 
    := ∀ s : S, r (b i s) s = true.

Definition bop_not_is_left_id (S : Type) (r : brel S) (b : binary_op S) (i : S)
    := {s : S & r (b i s) s = false }.

Definition bop_exists_left_id (S : Type) (r : brel S) (b : binary_op S) 
    := {i : S & bop_is_left_id S r b i}.

Definition bop_not_exists_left_id (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ i : S, bop_not_is_left_id S r b i.

Definition bop_is_right_id (S : Type) (r : brel S) (b : binary_op S) (i : S) 
    := ∀ s : S, r (b s i) s = true.

Definition bop_not_is_right_id (S : Type) (r : brel S) (b : binary_op S) (i : S)
    := {s : S & r (b s i) s = false}.

Definition bop_exists_right_id (S : Type) (r : brel S) (b : binary_op S) 
    := {i : S & bop_is_right_id S r b i}.

Definition bop_not_exists_right_id (S : Type) (r : brel S) (b : binary_op S) 
  := ∀ i : S, bop_not_is_right_id S r b i.

Lemma exists_id_implies_exists_left_id_and_exists_right_id (S : Type) (eqS : brel S) (bS : binary_op S) :
  bop_exists_id S eqS bS -> {s : S & (bop_is_left_id S eqS bS s) * (bop_is_right_id S eqS bS s) }.
Proof. intros [s P]. exists s; split; intro s'.
       destruct (P s') as [L R]. assumption.
       destruct (P s') as [L R]. assumption.
Qed.        



Definition ltr_preserves_right_id (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
  := ∀ (t  : T),  bop_is_right_id T rT bT t -> ∀ (s  : S),  rT t (f s t) = true.

Definition uop_is_id (S : Type) (eqS : brel S) (u : unary_op S) 
  := ∀ s : S, eqS s (u s) = true.

Definition ltr_preserves_right_id2 (S T: Type) (eqS : brel S) (bS : binary_op S) (rT : brel T) (f : left_transform S T)
  := ∀ (s  : S),  bop_is_right_id S eqS bS s -> uop_is_id T rT (f s). 

(*

(s1, t1) X| (s2, t2) = (s1 . (t1 |> s2), t1 * t2) 

*) 
Definition bop_left_semidirect (S T : Type) (bS : binary_op S) (bT : binary_op T) (f : left_transform T S) : binary_op (S * T) 
:= λ x y,  
   match x, y with
    | (s1, t1), (s2, t2) => (bS s1 (f t1 s2), bT t1 t2) 
   end.


(* Examples 

Sortest Paths with Gains and Losses:

   f n c = n * c 

  (min, plus) llex-|> (min, times) 

  (a, b) X| (c, d) = (a + (b *c), b * d) 

  (plus, 0, _)   (times, 1, 0) 

Shortest Paths with Discounting:  

  f n c = c * d^n,    (fixed d, 0 < d < 1)

  (min, plus) llex-|> (min, plus) 

  (a, b) X| (c, d) = (a + (c * d^b), b + d) 

  (plus, 0, _)  (plus, 0, _) 

*) 


Section Test. 
Variable S T : Type. 
Variable eqS : brel S. 
Variable eqT : brel T. 

Variable plusS : binary_op S. 
Variable plusT: binary_op T.
Variable timesS : binary_op S. 
Variable timesT: binary_op T.
Variable f  : left_transform T S.

Definition left_semidirect := bop_left_semidirect S T timesS timesT f.

(* all needed for associativity *)
Variable refS : brel_reflexive S eqS. 
Variable symS : brel_symmetric S eqS.
Variable tranS : brel_transitive S eqS.

(* used in selectivity *)
Variable symT : brel_symmetric T eqT.
(* used in not_left_cancel *)
Variable refT : brel_reflexive T eqT.

Variable plus_assS : bop_associative S eqS plusS. 
Variable plus_assT : bop_associative T eqT plusT.
Variable times_assS : bop_associative S eqS timesS. 
Variable times_assT : bop_associative T eqT timesT.
Variable f_ass  : ltr_associative T S eqS timesT f.            (*  f (t1 # t2) s =S f t1 (f t2 s)            f (t1 # t2) = (f t1) o (f t2) *)

Variable congf : ltr_congruence T S eqT eqS f.

Variable cong_plusS : bop_congruence S eqS plusS.
Variable cong_plusT : bop_congruence T eqT plusT.
Variable congS : bop_congruence S eqS timesS.
Variable congT : bop_congruence T eqT timesT.


(* Require IDs *)

Variable has_idS : bop_exists_id S eqS timesS. 
Variable has_idT : bop_exists_id T eqT timesT. 


(* For now, requre a very nicely behaved f *)
Variable disf  : ltr_distributive T S eqS timesS f.           (*  f t (s1 *S s2) =S (f t s1) *S (f t s2)                                    *)
Variable dis_plus_f  : ltr_distributive T S eqS plusS f.           (*  f t (s1 +S s2) =S (f t s1) +S (f t s2)                                    *) 
Variable ridSf : ltr_preserves_right_id T S eqS timesS f.     (*  ridS =S (f s ridS). *) 
Variable ridTf : ltr_preserves_right_id2 T S eqT timesT eqS f. (*     s =S (f ridT s).                     f ridT = identity function over S*)
Variable annSf : ∀ (s  : S),  bop_is_ann S eqS timesS s -> ∀ (t : T),  eqS s (f t s) = true. 
Variable annTf : ∀ (t  : T),  bop_is_ann T eqT timesT t -> ∀ (s : S),  bop_is_ann S eqS timesS (f t s). 


(* Requre ANNs ? *)

(* Require preservation of ids.  
   Note that with f_ass and disf alone we have 

   f t s =S f (idT # t) s =S f idT (f t s) 
   f t s =S f (t # idT) s =S f t (f idT s)          

   f t s =S f t (s *S idS) =S (f t s) *S (f t idS)
   f t s =S f t (idS *S s) =S (f t idS) *S (f t s)
*) 

(* Require preservation of anns.  
   Note that with f_ass and disf alone we have 

   f annT s =S f (annT # t) s =S f annT (f t s) 
   f annT s =S f (t # annT) s =S f t (f annT s)          

   f t annS =S f t (s *S annS) =S (f t s) *S (f t annS)
   f t annS =S f t (annS *S s) =S (f t annS) *S (f t s)
*) 

Notation "a =S b"  := (eqS a b = true) (at level 15).
Notation "a !=S b"  := (eqS a b = false) (at level 15).
Notation "a =T b"  := (eqT a b = true) (at level 15).
Notation "a == b"  := (brel_product S T eqS eqT a b = true) (at level 15).
Notation "a +S b"  := (plusS a b) (at level 15).
Notation "a +T b"  := (plusT a b) (at level 15).
Notation "a *S b"  := (timesS a b) (at level 15).
Notation "a *T b"  := (timesT a b) (at level 15).
Notation "a |> b"  := (f a b) (at level 15).
Notation "bs [X|] bT"  := (bop_left_semidirect S T timesS timesT f) (at level 15).
Notation "a X| b"  := (bop_left_semidirect S T timesS timesT f a b) (at level 15).

Notation "a <*> b"  := (brel_product a b) (at level 15).
Notation "a [*] b"  := (bop_product a b) (at level 15).
Notation "a [!+] b" := (bop_llex eqS a b) (at level 15).




Lemma bop_left_semidirect_associative : bop_associative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split. 
          (* show ((s1 *S f t1 s2) *S f (t1 # t2) s3) =S (s1 *S f t1 (s2 *S f t2 s3))

               ((s1 *S f t1 s2) *S f (t1 # t2) s3) 
            = {f_ass} 
               ((s1 *S f t1 s2) *S f t1 (f t2 s3))
            = {times_assS} 
               s1 *S ((f t1 s2) *S f t1 (f t2 s3)))
            = {diss} 
               s1 *S (f t1 (s2 *S f t2 s3))
          *) 
          assert (fact1 := f_ass t1 t2 s3). 
          assert (fact2 := disf t1 s2 (f t2 s3)).
          assert (fact3 := congS _ _ _ _ (refS (s1 *S f t1 s2)) fact1). 
          assert (fact4 := times_assS s1 (f t1 s2) (f t1 (f t2 s3))). 
          assert (fact5 := tranS _ _ _ fact3 fact4). 
          assert (fact6 := congS _ _ _ _ (refS s1) fact2). apply symS in fact6.
          assert (fact7 := tranS _ _ _ fact5 fact6). 
          assumption. 
          apply times_assT.
Defined.  


Lemma bop_left_semidirect_congruence : bop_congruence (S * T) (brel_product eqS eqT) left_semidirect.
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       apply andb_is_true_right. split.  
          apply congS. assumption. apply congf. assumption. assumption. 
          apply congT. assumption. assumption. 
Defined.


Lemma bop_left_semidirect_exists_id : bop_exists_id (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. destruct (exists_id_implies_exists_left_id_and_exists_right_id _ _ _ has_idS) as [idS [is_left_idS is_right_idS]].
       destruct (exists_id_implies_exists_left_id_and_exists_right_id _ _ _ has_idT) as [idT [is_left_idT is_right_idT]].
       exists (idS, idT). intros [s2 t2].
       split; compute. 
       case_eq(eqS (idS *S f idT s2) s2); intro J.
          apply is_left_idT.           
          assert (fact1 := ridTf idT is_right_idT s2). 
          assert (fact2 := congS _ _ _ _ (refS idS) fact1).
          assert (fact3 := is_left_idS s2). apply symS in fact3. 
          assert (fact4 := tranS _ _ _ fact3 fact2). apply symS in fact4.
          rewrite fact4 in J. discriminate. 
       case_eq(eqS (s2 *S f t2 idS) s2 ); intro J.
          apply is_right_idT.           
          assert (fact1 := ridSf idS is_right_idS t2). apply symS in fact1.
          assert (fact2 := congS _ _ _ _ (refS s2) fact1).          
          assert (fact3 := is_right_idS s2). apply symS in fact3. apply symS in fact2.
          assert (fact4 := tranS _ _ _ fact3 fact2). apply symS in fact4.
          rewrite fact4 in J. discriminate.
Qed.           

Lemma bop_left_semidirect_exists_ann :
  bop_exists_ann S eqS timesS ->
  bop_exists_ann T eqT timesT ->
         bop_exists_ann (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [annS P] [annT Q]. exists (annS, annT). intros [s2 t2]. 
       destruct (Q t2) as [LT RT].
       split; compute.
       destruct (P (f annT s2)) as [LS _].        
       case_eq (eqS (annS *S f annT s2) annS); intro J. 
          exact LT. 
          rewrite LS in J. discriminate.
       destruct (P s2) as [_ RS].                  
       case_eq (eqS (s2 *S f t2 annS) annS); intro J.           
          exact RT.                                                  
          assert (fact1 := annSf annS P t2).
          assert (fact2 := congS _ _ _ _ (refS s2) fact1). apply symS in RS.
          assert (fact3 := tranS _ _ _ RS fact2). apply symS in fact3.
          rewrite fact3 in J. discriminate.
Qed.


Lemma bop_left_semidirect_not_exists_ann_v1 :
  bop_not_exists_ann T eqT timesT ->
         bop_not_exists_ann (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros H (s, t). unfold bop_not_is_ann.
       destruct(H t) as [t' [Q | Q]]; exists (s, t'); compute.
          left. case_eq (eqS (s *S f t s) s); intro J; auto. 
          right. case_eq (eqS (s *S f t' s) s); intro J; auto.
Qed.

Lemma bop_left_semidirect_not_exists_ann_v2 :
  bop_not_exists_ann S eqS timesS ->
  bop_exists_ann T eqT timesT ->
         bop_not_exists_ann (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros F [annT P] (s, t). compute in F. 
       destruct (F (f annT s)) as [wS Q]. exists (wS, annT). compute.
       case_eq(eqS (s *S f t wS) s); intro J; case_eq(eqS (wS *S f annT s) s); intro K; auto.
       destruct (annTf annT P s wS) as [L R]. 
       destruct Q as [Q | Q].
          rewrite L in Q. discriminate.           
          rewrite R in Q. discriminate.           
Qed.


Lemma bop_left_semidirect_idempotent : 
      ltr_idempotent T S eqS timesS f → 
      bop_idempotent T eqT timesT → 
         bop_idempotent (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   unfold bop_idempotent. intros L R (s, t). simpl. 
   apply andb_is_true_right. split. 
      rewrite L. reflexivity. 
      rewrite R. reflexivity. 
Defined. 


Lemma bop_left_semidirect_not_idempotent_v1 : 
      ltr_not_idempotent T S eqS timesS f → 
         bop_not_idempotent (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [ [t s] P]. 
       exists (s, t). simpl. 
       apply andb_is_false_right. left. assumption. 
Defined. 

Lemma bop_left_semidirect_not_idempotent_v2 (s : S) : 
      bop_not_idempotent T eqT timesT → 
         bop_not_idempotent (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [ t P ]. 
       exists (s, t). simpl. 
       apply andb_is_false_right. right . assumption. 
Defined. 

(* *) 
Lemma bop_left_semidirect_left_cancellative :
      (∀ (s1 s2 : S) (t : T), f t s1 =S f t s2  → s1 =S s2) → 
      bop_left_cancellative S eqS timesS  → 
      bop_left_cancellative T eqT timesT → 
      bop_left_cancellative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros I L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply L in HL. apply R in HR. rewrite HR. rewrite (I s2 s3 t1 HL). auto. 
Defined. 


Lemma bop_left_semidirect_left_cancellative_II :
      (∀ (s s' s'': S) (t : T), (s *S (f t s')) =S (s *S (f t s''))  → s' =S s'') → 
      bop_left_cancellative T eqT timesT → 
      bop_left_cancellative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros I R [s1 t1] [s2 t2] [s3 t3]; simpl; intro H. 
   apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply R in HR. rewrite HR. rewrite (I s1 s2 s3 t1 HL). auto. 
Defined. 

Lemma bop_left_semidirect_not_left_cancellative_v1 (s : S):
      bop_not_left_cancellative T eqT timesT → 
      bop_not_left_cancellative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [[t1 [t2 t3]] [L R]].  exists ( (s, t1), ( (s, t2), (s, t3) ) ). compute. split. 
       rewrite (refS (s *S f t1 s)). assumption.        
       rewrite (refS s). assumption.        
Defined. 


Lemma bop_left_semidirect_not_left_cancellative_v2 :
      { s : S & {s' : S & {s'': S & {t : T &  (s *S (f t s')) =S (s *S (f t s'')) * (s' !=S s'')}}}} -> 
      bop_not_left_cancellative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [s [s' [s'' [t [L R]]]]].  exists ( (s, t), ( (s', t), (s'', t) ) ). compute.
       rewrite R. rewrite L. rewrite (refT (t *T t)). split; reflexivity. 
Defined. 


Lemma bop_left_semidirect_right_cancellative : 
      (∀ (s1 s2 s3 : S) (t1 t2 : T), (s2 *S (f t1 s1)) =S (s3 *S (f t2 s1)) -> s2 =S s3) -> 
      bop_right_cancellative T eqT timesT → 
      bop_right_cancellative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3] ; simpl. intro H. 
   apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply andb_is_true_right. split. 
      apply (L s1 s2 s3 t2 t3 HL). 
      apply R in HR. assumption. 
Qed.

(* 
Print bop_left_semidirect_right_cancellative. 

bop_left_semidirect_right_cancellative = 
λ (L : ∀ (s1 s2 s3 : S) (t1 t2 : T), (s2 *S f t1 s1) =S (s3 *S f t2 s1) → s2 =S s3) 
  (R : bop_right_cancellative T eqT timesT) 
  (s : S * T),
let (s1, t1) as p return (∀ t u : S * T, left_semidirect t p == left_semidirect u p → t == u) := s 
in λ t : S * T,
     let (s2, t2) as p return (∀ u : S * T, left_semidirect p (s1, t1) == left_semidirect u (s1, t1) → p == u) := t 
     in λ u : S * T,
         let (s3, t3) as p return (left_semidirect (s2, t2) (s1, t1) == left_semidirect p (s1, t1) → (s2, t2) == p) := u 
         in λ (H : eqS (s2 *S f t2 s1) (s3 *S f t3 s1) && eqT (t2 *T t1) (t3 *T t1) = true)
              (H0:(s2 *S f t2 s1) =S (s3 *S f t3 s1) * (t2 *T t1) =T (t3 *T t1)
                  :=andb_is_true_left (eqS (s2 *S f t2 s1) (s3 *S f t3 s1)) (eqT (t2 *T t1) (t3 *T t1)) H),
              let (HL, HR) := H0 
              in andb_is_true_right (eqS s2 s3) (eqT t2 t3) (L s1 s2 s3 t2 t3 HL, let HR0 := R t1 t2 t3 HR : t2 =T t3 in HR0)
     : (∀ (s1 s2 s3 : S) (t1 t2 : T), (s2 *S f t1 s1) =S (s3 *S f t2 s1) → s2 =S s3)
       → bop_right_cancellative T eqT timesT → bop_right_cancellative (S * T) (brel_product S T eqS eqT) left_semidirect


HERE

*) 
Lemma bop_left_semidirect_not_right_cancellative_v1 (s : S) : 
  bop_not_right_cancellative T eqT timesT →
  (∀ (s : S) (t1 t2 : T), (s *S f t1 s) =S (s *S f t2 s))  →
      bop_not_right_cancellative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros [[t1 [t2 t3]] [L R]] K; exists ( (s, t1), ( (s, t2), (s, t3) ) ). split. 
      compute. case_eq (eqS (s *S f t2 s) (s *S f t3 s)); intro J.
         exact L. 
         assert (F := K s t2 t3). rewrite F in J. discriminate. 
      compute. rewrite (refS s). exact R. 
Defined. 



Lemma bop_left_semidirect_is_left : 
      bop_is_left S eqS timesS → 
      bop_is_left T eqT timesT → 
      bop_is_left (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_left_semidirect_not_is_left_v1 (t : T) : 
      bop_not_is_left S eqS timesS → 
      bop_not_is_left (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [[s s'] P]. exists ( (s, t), (s', t) ). compute.
       case_eq(eqS (s *S f t s') s); intro H.
          admit. 
          reflexivity. 
Admitted.        


Lemma bop_left_semidirect_not_is_left_v2 (s : S) : 
      bop_not_is_left T eqT timesT → 
      bop_not_is_left (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [[t t'] P]. exists ( (s, t), (s, t') ). compute. rewrite P. 
       case_eq (eqS (s *S f t s) s); intro J; auto. 
Qed. 


Lemma bop_left_semidirect_left_constant : 
      bop_left_constant S eqS timesS → 
      bop_left_constant T eqT timesT → 
      bop_left_constant (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
Defined. 


Lemma bop_left_semidirect_not_left_constant_v1 (s : S) :
      bop_not_left_constant T eqT timesT → 
      bop_not_left_constant (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [[t1 [t2 t3]] F]. exists ( (s, t1), ( (s, t2), (s, t3) ) ). compute.
       rewrite (refS (s *S f t1 s)). exact F. 
Qed. 

Lemma bop_left_semidirect_not_left_constant_v2 (t : T) :
      bop_not_left_constant S eqS timesS → 
      bop_not_left_constant (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [[s1 [s2 s3]] F]. exists ( (s1, t), ( (s2, t), (s3, t) ) ). compute.
       rewrite (refT (t *T t)).
       case_eq(eqS (s1 *S f t s2) (s1 *S f t s3)); intro J; auto. 
       admit. (* need (s1 *S f t s2) !=S (s1 *S f t s3)  *) 
Admitted. 


Lemma bop_left_semidirect_is_right_I : 
      (((bop_is_right S eqS timesS) * (∀ (s : S) (t: T), eqS (f t s) s = true)) 
       + (∀ (s1 s2 : S) (t: T), eqS (timesS s1 (f t s2)) s2 = true))   → 
      bop_is_right T eqT timesT → 
      bop_is_right (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite R. simpl.
       destruct L as [ [rcS L ] | L].
         admit. 
         rewrite L. simpl. reflexivity. 
Admitted. 


Lemma bop_left_semidirect_is_right_II :
       (∀ (s1 s2 : S) (t: T), s1 *S (f t s2) =S s2)   → 
      bop_is_right T eqT timesT → 
      bop_is_right (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros H R (s1, t1) (s2, t2). compute.
       rewrite (H s1 s2 t1). apply R. 
Qed.        





Lemma bop_left_semidirect_right_constant : 
      (((bop_right_constant S eqS timesS) * (∀ (s : S) (t1 t2: T), eqS (f t1 s) (f t2 s) = true)) 
         + (∀ (s1 s2 s3 : S) (t1 t2: T), eqS (timesS s2 (f t1 s1)) (timesS s3 (f t2 s1)) = true)) → 
      bop_right_constant T eqT timesT → 
      bop_right_constant (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. 
      destruct L as [ [rcS L ] | L].
         admit. 
         rewrite L. simpl. reflexivity. 
      apply R. 

Admitted. 

(* needs negation *) 
Lemma bop_left_semidirect_product_anti_left : 
      (bop_anti_left S eqS timesS) + (bop_anti_left T eqT timesT) → 
      bop_anti_left (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. apply P. 
      right. apply P. 
Defined. 

(* needs negation *) 
Lemma bop_left_semidirect_anti_right : 
      ((bop_anti_right S eqS timesS) * (∀ (s : S) (t : T), eqS s (f t s) = true)) 
      + (∀ (s1 s2 : S) (t : T), eqS s1 (timesS s2 (f t s1)) = false)
      + (bop_anti_right T eqT timesT) → 
      bop_anti_right (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. 
   intros [R | L] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. destruct R as [ [rcS P ] | P].
         admit. 
         rewrite P. simpl. reflexivity. 
      right. apply L. 
Admitted. 



(*        

  Strange: 
  Q = 
   ∀ (s1 s2 : S) (t1 t2 : T), 
    ( (s1 =S (s1 *S f t1 s2)) *  (t1 =T (t1 *T t2)) ) 
       +
    ( (s2 =S (s1 *S f t1 s2)) *  (t2 =T (t1 *T t2)) )

  (Q idS s t idT) simplifies to 
    (idS =S f t s)  + ( (s =S (f idT s)) *  (idT =T t) )

  (Q s idS idT t) simplifies to 
    ( (s =S (s *S f idT idS)) *  (idT =T (idT *T t)) ) 
       +
    ( (idS =S (s *S f idT idS)) *  (t =T (idT *T t)) )
    

Use    f (t1 *T t2) s =S f t1 (f t2 s)         
       f t (s1 *S s2) =S (f t s1) *S (f t s2)       
to explore? 

    


*)

(* needs negation *) 
Lemma bop_left_semidirect_selective :
  (∀ (s1 s2 : S) (t1 t2 : T), 
    ( (s1 =S (s1 *S f t1 s2)) *  (t1 =T (t1 *T t2)) ) 
       +
    ( (s2 =S (s1 *S f t1 s2)) *  (t2 =T (t1 *T t2)) )
   ) → 
   bop_selective (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros P [s1 t1] [s2 t2]; compute.
       assert (Q := P s1 s2 t1 t2).
       destruct Q as [[H1 H2]| [H1 H2]].
       apply symS in H1. apply symT in H2. rewrite H1, H2. left. reflexivity. 
       apply symS in H1. apply symT in H2. rewrite H1, H2. right. reflexivity.
Qed.        


(* STRANGE : s1 + (f t1 s2) = s2 + (f t2 s1) *)
Definition ltr_commutative (S T: Type) (eqT : brel T) (timesT : binary_op T) (f : left_transform S T)
   := ∀ (s1 s2 : S) (t1 t2 : T), eqT (timesT t1 (f s1 t2)) (timesT t2 (f s2 t1)) = true. 

Definition ltr_not_commutative (S T: Type) (eqT : brel T) (timesT : binary_op T) (f : left_transform S T)
   := { z : (S * S) * (T * T) & 
        match z with ((s1, s2), (t1, t2)) => 
              eqT (timesT t1 (f s1 t2)) (timesT t2 (f s2 t1)) = false 
        end 
      }. 

(*
bop_commutative T eqT timesT → f t2 (f t1 s) s =S f t1 (f t2 s)

ltr_commutative T S eqS timesS f → 
    f t (s1 *S s2) =S (f t s1) *S (f t s2)
                  =S s2 *S (f t' (f t s1))
                  =S s2 *S (f (t' *T t) s1)
                  =S s1 *S (f t'' s2)
Hmm, what to do with this? Contradict pres of ann? 

what if "f t idS = idS"?   
Then ltr_commutative IFF (f t s = s and *S is commutative).  

    f t s =S idS *S (f t s) 
          =S s *S (f t' idS)   (ltr_commutative) 
          =S s *S idS 
          =S s 

Require "f t idS = idS"?   

*) 
Lemma bop_left_semidirect_commutative :
      ltr_commutative T S eqS timesS f →    (* s1 *S (f t1 s2) =S s2 *S (f t2 s1) *) 
      bop_commutative T eqT timesT → 
         bop_commutative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. 
       apply andb_is_true_right. split. 
          rewrite L. reflexivity.           
          rewrite R. reflexivity. 
Defined. 

Lemma bop_semidirec_not_commutative_v1 : 
      ltr_not_commutative T S eqS timesS f → 
         bop_not_commutative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [[ [t1 t2] [s1 s2 ] ] P]. 
       exists ((s1, t1), (s2, t2)). simpl. 
       apply andb_is_false_right. left. assumption. 
Defined. 


Lemma bop_semidirec_not_commutative_v2 (s : S) : 
      bop_not_commutative T eqT timesT → 
         bop_not_commutative (S * T) (brel_product eqS eqT) left_semidirect. 
Proof. intros [ [t1 t2] P]. 
       exists ((s, t1), (s, t2)). simpl. 
       apply andb_is_false_right. right. assumption. 
Defined.


Lemma bop_product_left_semidirect_left_distributive : 
      bop_left_distributive S eqS plusS timesS → bop_left_distributive T eqT plusT timesT → 
             bop_left_distributive (S * T) (eqS <*> eqT) (plusS [*] plusT) (timesS [X|] timesT). 
Proof. intros ldS ldT. unfold bop_left_distributive. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split. 
          assert (J1 := dis_plus_f t1 s2 s3).
          assert (J2 := congS _ _ _ _ (refS s1) J1).                 
          assert (J3 := ldS s1 (t1 |> s2) (t1 |> s3)).
          assert (J4 := tranS _ _ _ J2 J3). 
          exact J4. 
          apply ldT. 
Qed. 

Lemma bop_product_left_semidirect_right_distributive : 
      bop_right_distributive S eqS plusS timesS → bop_right_distributive T eqT plusT timesT → 
             bop_right_distributive (S * T) (eqS <*> eqT) (plusS [*] plusT) (timesS [X|] timesT). 
Proof. intros rdS rdT. unfold bop_left_distributive. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split. 
          (*
             ((s2 +S s3) *S ((t2 +T t3) |> s1)) 
              =S (s2 *S ((t2 +T t3) |> s1)) +S (s3 *S ((t2 +T t3) |> s1)) 
              =S (s2 *S ((t2 |> s1) +S (t3|> s1))) +S (s3 *S ((t2 |> s1) +S (t3|> s1)))
              =S ((s2 *S (t2 |> s1)) +S (s3 *S (t3 |> s1)))   +S   ((s2 *S (t3 |> s1)) +S (s3 *S (t2 |> s1)))
              =S ???
              =S (s2 *S (t2 |> s1)) +S (s3 *S (t3 |> s1))

              need (s2 *S (t2 |> s1)) <= (s2 *S (t3 |> s1))     
                   (s3 *S (t3 |> s1)) <= (s3 *S (t2 |> s1))

              or   (s2 *S (t2 |> s1)) <= (s3 *S (t2 |> s1))  No! 
                   (s3 *S (t3 |> s1)) <= (s2 *S (t3 |> s1))  No! 


                   (s2 *S (t2 |> s1)) = (s2 *S (t2 |> s1)) +S (s2 *S (t3 |> s1))     
                                      = s2 *S ((t2 |> s1) +S (t3 |> s1)) 
                                      = s2 *S ((t2 +T t3) |> s1)

                   need  t2 |> s1 = (t2 +T t3) |> s1   Not likely! 

           *)
          admit. 
          apply rdT. 
Admitted.


Lemma bop_llex_left_semidirect_left_distributive :
      bop_selective S eqS plusS -> 
      bop_left_distributive S eqS plusS timesS → bop_left_distributive T eqT plusT timesT → 
             bop_left_distributive (S * T) (eqS <*> eqT) (plusS [!+] plusT) (timesS [X|] timesT). 
Proof. intros selS ldS ldT. unfold bop_left_distributive. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split.
          assert (J1 := dis_plus_f t1 s2 s3).
          assert (J2 := congS _ _ _ _ (refS s1) J1).                 
          assert (J3 := ldS s1 (t1 |> s2) (t1 |> s3)).
          assert (J4 := tranS _ _ _ J2 J3). 
          exact J4.

          case_eq(eqS s2 s3); intro J1;
          case_eq(brel_llt eqS plusS s2 s3); intro J2;             
          case_eq(eqS (s1 *S (t1 |> s2)) (s1 *S (t1 |> s3))); intro J3;
          case_eq(brel_llt eqS plusS (s1 *S (t1 |> s2)) (s1 *S (t1 |> s3))); intro J4; compute in *; auto.
          rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5; rewrite J5 in J2; discriminate J2.
          rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5; rewrite J5 in J2; discriminate J2.            
          admit. (* J1, J3 -> false *)
          admit. (* J1, J3 -> false *)           
          rewrite J3 in J4. case_eq(eqS (s1 *S (t1 |> s2)) ((s1 *S (t1 |> s2)) +S (s1 *S (t1 |> s3)))); intro J5; rewrite J5 in J4; discriminate J4.
          rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             rewrite J3 in J4. rewrite J5 in J2.
             (* need contradiction from 
                  J1 : s2 !=S s3
                  J5 : s2 =S (s2 +S s3)          s2 < s3 
                  J3 : (s1 *S (t1 |> s2)) =S (s1 *S (t1 |> s3))
                  need < preservation 
             *) 
             admit. 
             rewrite J5 in J2; discriminate J2.
          rewrite J3 in J4. rewrite J1 in J2.
             case_eq(eqS s2 (s2 +S s3)); intro J5; case_eq(eqS (s1 *S (t1 |> s2)) ((s1 *S (t1 |> s2)) +S (s1 *S (t1 |> s3)))); intro J6.
                rewrite J6 in J4. discriminate J4. 
                rewrite J6 in J4. rewrite J5 in J2.
                   (* need contradiction from 
                      J1 : s2 !=S s3
                      J5 : s2 =S (s2 +S s3)       s2 < s3 
                      J3 : (s1 *S (t1 |> s2)) !=S (s1 *S (t1 |> s3))
                      J6 : (s1 *S (t1 |> s2)) !=S ((s1 *S (t1 |> s2)) +S (s1 *S (t1 |> s3)))  

                      Again, need some sort of < preservation 
                      s2 < s3 -> (s1 *S (t1 |> s2)) < (s1 *S (t1 |> s3))
                      
                      break into ? 
                            s2 < s3 -> (s *S s2) < (s *S s3)                     
                            s2 < s3 -> (t |> s2) < (t |> s3)                     

                            s2 = s2 +S s3 <> s3 -> (s *S s2) = (s *S s2) +S (s *S s3) <> (s *S s3)
                        ld: s2 = s2 +S s3 <> s3 -> (s *S s2) = s *S (s2 +S s3) = s *S s2 <> (s *S s3)
                        so, just need cancellativity. 

                        s2 = s2 +S s3 <> s3  -> (t |> s2) = (t |> s2) +S (t |> s3) <> (t |> s3)
                        s2 = s2 +S s3 <> s3  -> (t |> s2) = (t |> (s2 +S s3)  = t |> s2 <> (t |> s3)
                        so, just need cancellativity. 

                   *) 
                   admit. 
                rewrite J5 in J2. discriminate J2.
                rewrite J5 in J2. discriminate J2.
           rewrite J3 in J4. case_eq(eqS (s1 *S (t1 |> s2)) ((s1 *S (t1 |> s2)) +S (s1 *S (t1 |> s3)))); intro J5; rewrite J5 in J4; discriminate J4.
           rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
              rewrite J5 in J2; discriminate J2.
              destruct (selS s2 s3) as [L | R].
                 apply symS in L. rewrite L in J5. discriminate J5.
                 (* s3 < s2 
                    but 
                    (s1 *S (t1 |> s2)) = (s1 *S (t1 |> s3))
                 *)
                 admit. 
           rewrite J3 in J4. rewrite J1 in J2.
               case_eq(eqS s2 (s2 +S s3)); intro J5; case_eq(eqS (s1 *S (t1 |> s2)) ((s1 *S (t1 |> s2)) +S (s1 *S (t1 |> s3)))); intro J6.
                rewrite J5 in J2. discriminate J2.
                rewrite J5 in J2. discriminate J2.
                rewrite J5 in J2. rewrite J6 in J4.
                   destruct (selS s2 s3) as [L | R].
                      apply symS in L. rewrite L in J5. discriminate J5.
                      (* s3 < s2
                         but 
                         (s1 *S (t1 |> s2)) < (s1 *S (t1 |> s3))
                       *)
                      admit. 
                rewrite J6 in J4. discriminate J4.
Admitted. 


Lemma bop_llex_left_semidirect_right_distributive :
      bop_selective S eqS plusS -> 
      bop_right_distributive S eqS plusS timesS → bop_right_distributive T eqT plusT timesT → 
             bop_right_distributive (S * T) (eqS <*> eqT) (plusS [!+] plusT) (timesS [X|] timesT). 
Proof. intros selS ldS ldT. unfold bop_right_distributive. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split.
          case_eq(eqS s2 s3); intro J1;
          case_eq(brel_llt eqS plusS s2 s3); intro J2; compute in *; auto.
             rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J3; rewrite J3 in J2; discriminate J2. 
             admit. (* case seems true *) 
             rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J3.
                admit. (* < preservation *) 
                rewrite J3 in J2; discriminate J2.              
             rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J3.
                rewrite J3 in J2; discriminate J2.              
                admit. (* < preservation *) 

          case_eq(eqS s2 s3); intro J1;
          case_eq(brel_llt eqS plusS s2 s3); intro J2;
          case_eq(eqS (s2 *S (t2 |> s1)) (s3 *S (t3 |> s1))); intro J3;
          case_eq(brel_llt eqS plusS (s2 *S (t2 |> s1)) (s3 *S (t3 |> s1))); intro J4; compute in *; auto.
          rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5; rewrite J5 in J2; discriminate J2.
          rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5; rewrite J5 in J2; discriminate J2.
          rewrite J3 in J4. case_eq(eqS (s2 *S (t2 |> s1)) ((s2 *S (t2 |> s1)) +S (s3 *S (t3 |> s1)))); intro J5.
             rewrite J1 in J2. rewrite J5 in J4. admit. 
             rewrite J5 in J4. discriminate J4.
         rewrite J3 in J4. case_eq(eqS (s2 *S (t2 |> s1)) ((s2 *S (t2 |> s1)) +S (s3 *S (t3 |> s1)))); intro J5.
             rewrite J5 in J4. discriminate J4.
             admit.              
         rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             admit.
             rewrite J5 in J2; discriminate J2.          
         rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             admit.
             rewrite J5 in J2; discriminate J2.          
         rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             admit.
             rewrite J5 in J2; discriminate J2.
         rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             rewrite J5 in J2; discriminate J2.                          
             admit.
         rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             rewrite J5 in J2; discriminate J2.                          
             admit.             
         rewrite J1 in J2. case_eq(eqS s2 (s2 +S s3)); intro J5.
             rewrite J5 in J2; discriminate J2.                          
             admit.             
Admitted.        


Lemma bop_llex_left_semidirect_left_left_absorptive :
      bop_selective S eqS plusS -> 
      bops_left_left_absorptive S eqS plusS timesS → bops_left_left_absorptive T eqT plusT timesT → 
      bops_left_left_absorptive (S * T) (eqS <*> eqT) (plusS [!+] plusT) (timesS [X|] timesT).
Proof. intros selS laS laT [s1 t1] [s2 t2]. compute.
       case_eq(eqS s1 (s1 +S (s1 *S (t1 |> s2)))); intro J1;
       case_eq(eqS s1 (s1 *S (t1 |> s2))); intro J2;
       case_eq(eqS s1 (s1 *S (t1 |> s2))); intro J3; compute in *; auto.
          admit. 
          rewrite J2 in J3. discriminate J3.
          rewrite J2 in J3. discriminate J3.           
          admit.
Admitted. 
          
End Test.

