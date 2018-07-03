Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop.
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.facts. 


Definition ltr_congruence (S T : Type) (rS : brel S) (rT : brel T) (f : left_transform S T) := 
   ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> rT (f s1 t1) (f s2 t2) = true.

Definition ltr_associative (S T: Type) (rT : brel T) (bS : binary_op S) (f : left_transform S T)
    := ∀ (s1 s2 : S) (t : T), rT (f (bS s1 s2) t) (f s1 (f s2 t)) = true. 

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

Lemma exists_id_implies_exists_left_id_and_exists_right_id (S : Type) (rS : brel S) (bS : binary_op S) :
  bop_exists_id S rS bS -> {s : S & (bop_is_left_id S rS bS s) * (bop_is_right_id S rS bS s) }.
Proof. intros [s P]. exists s; split; intro s'.
       destruct (P s') as [L R]. assumption.
       destruct (P s') as [L R]. assumption.
Qed.        



Definition ltr_preserves_right_id (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
  := ∀ (t  : T),  bop_is_right_id T rT bT t -> ∀ (s  : S),  rT t (f s t) = true.

Definition uop_is_id (S : Type) (rS : brel S) (u : unary_op S) 
  := ∀ s : S, rS s (u s) = true.

Definition ltr_preserves_right_id2 (S T: Type) (rS : brel S) (bS : binary_op S) (rT : brel T) (f : left_transform S T)
  := ∀ (s  : S),  bop_is_right_id S rS bS s -> uop_is_id T rT (f s). 


Definition bop_semidirect (S T : Type) (bS : binary_op S) (bT : binary_op T) (f : left_transform T S) : binary_op (S * T) 
:= λ x y,  
   match x, y with
    | (s1, t1), (s2, t2) => (bS s1 (f t1 s2), bT t1 t2) 
   end.


(* Examples 

Sortest Paths with Gains and Losses:

   f n c = n * c 

  (min, plus) llex-|> (min, times) 

  (a, b) |> (c, d) = (a + (b *c), b * d) 

  (plus, 0, _)   (times, 1, 0) 

Shortest Paths with Discounting:  

  f n c = c * d^n,    (fixed d, 0 < d < 1)

  (min, plus) llex-|> (min, plus) 

  (a, b) |> (c, d) = (a + (c * d^b), b + d) 

  (plus, 0, _)  (plus, 0, _) 

*) 


Section Test. 
Variable S T : Type. 
Variable rS : brel S. 
Variable rT : brel T. 

Variable bS : binary_op S. 
Variable bT: binary_op T.
Variable f  : left_transform T S.

Definition semidirect := bop_semidirect S T bS bT f.

(* all needed for associativity *)
Variable refS : brel_reflexive S rS. 
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.
Variable congS : bop_congruence S rS bS.

Variable assS : bop_associative S rS bS. 
Variable assT : bop_associative T rT bT.

(* needed for semidirct congruence *)
Variable congT : bop_congruence T rT bT.
Variable congf : ltr_congruence T S rT rS f.

(* Require IDs *)

Variable has_idS : bop_exists_id S rS bS. 
Variable has_idT : bop_exists_id T rT bT. 


(* For now, requre a very nicely behaved f *)

Variable assf  : ltr_associative T S rS bT f.            (*  f (t1 # t2) s =S f t1 (f t2 s)            f (t1 # t2) = (f t1) o (f t2) *) 
Variable disf  : ltr_distributive T S rS bS f.           (*  f t (s1 @ s2) =S (f t s1) @ (f t s2)                                    *) 
Variable ridSf : ltr_preserves_right_id T S rS bS f.     (*  ridS =S (f s ridS). *) 
Variable ridTf : ltr_preserves_right_id2 T S rT bT rS f. (*     s =S (f ridT s).                     f ridT = identity function over S*)
Variable annSf : ∀ (s  : S),  bop_is_ann S rS bS s -> ∀ (t : T),  rS s (f t s) = true. 
Variable annTf : ∀ (t  : T),  bop_is_ann T rT bT t -> ∀ (s : S),  bop_is_ann S rS bS (f t s). 


(* used in selectivity *)
Variable symT : brel_symmetric T rT.
(* used in not_left_cancel *)
Variable refT : brel_reflexive T rT.

(* Requre ANNs ? *)

(* Require preservation of ids.  
   Note that with assf and disf alone we have 

   f t s =S f (idT # t) s =S f idT (f t s) 
   f t s =S f (t # idT) s =S f t (f idT s)          

   f t s =S f t (s @ idS) =S (f t s) @ (f t idS)
   f t s =S f t (idS @ s) =S (f t idS) @ (f t s)
*) 

(* Require preservation of anns.  
   Note that with assf and disf alone we have 

   f annT s =S f (annT # t) s =S f annT (f t s) 
   f annT s =S f (t # annT) s =S f t (f annT s)          

   f t annS =S f t (s @ annS) =S (f t s) @ (f t annS)
   f t annS =S f t (annS @ s) =S (f t annS) @ (f t s)
*) 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a !=S b"  := (rS a b = false) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a == b"  := (brel_product S T rS rT a b = true) (at level 15).
Notation "a # b"  := (bT a b) (at level 15).
Notation "a @ b"  := (bS a b) (at level 15).
Notation "a |> b"  := (bop_semidirect S T bS bT f a b) (at level 15).


Lemma bop_semidirect_associative : bop_associative (S * T) (brel_product rS rT) semidirect. 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. simpl.
       apply andb_is_true_right. split. 
          (* show ((s1 @ f t1 s2) @ f (t1 # t2) s3) =S (s1 @ f t1 (s2 @ f t2 s3))

               ((s1 @ f t1 s2) @ f (t1 # t2) s3) 
            = {assf} 
               ((s1 @ f t1 s2) @ f t1 (f t2 s3))
            = {assS} 
               s1 @ ((f t1 s2) @ f t1 (f t2 s3)))
            = {diss} 
               s1 @ (f t1 (s2 @ f t2 s3))
          *) 
          assert (fact1 := assf t1 t2 s3). 
          assert (fact2 := disf t1 s2 (f t2 s3)).
          assert (fact3 := congS _ _ _ _ (refS (s1 @ f t1 s2)) fact1). 
          assert (fact4 := assS s1 (f t1 s2) (f t1 (f t2 s3))). 
          assert (fact5 := tranS _ _ _ fact3 fact4). 
          assert (fact6 := congS _ _ _ _ (refS s1) fact2). apply symS in fact6.
          assert (fact7 := tranS _ _ _ fact5 fact6). 
          assumption. 
          apply assT.
Defined.  


Lemma bop_semidirect_congruence : bop_congruence (S * T) (brel_product rS rT) semidirect.
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (andb_is_true_left _ _ H1) as [C1 C2].
       destruct (andb_is_true_left _ _ H2) as [C3 C4].
       apply andb_is_true_right. split.  
          apply congS. assumption. apply congf. assumption. assumption. 
          apply congT. assumption. assumption. 
Defined.


Lemma bop_semidirect_exists_id : bop_exists_id (S * T) (brel_product rS rT) semidirect. 
Proof. destruct (exists_id_implies_exists_left_id_and_exists_right_id _ _ _ has_idS) as [idS [is_left_idS is_right_idS]].
       destruct (exists_id_implies_exists_left_id_and_exists_right_id _ _ _ has_idT) as [idT [is_left_idT is_right_idT]].
       exists (idS, idT). intros [s2 t2].
       split; compute. 
       case_eq(rS (idS @ f idT s2) s2); intro J.
          apply is_left_idT.           
          assert (fact1 := ridTf idT is_right_idT s2). 
          assert (fact2 := congS _ _ _ _ (refS idS) fact1).
          assert (fact3 := is_left_idS s2). apply symS in fact3. 
          assert (fact4 := tranS _ _ _ fact3 fact2). apply symS in fact4.
          rewrite fact4 in J. discriminate. 
       case_eq(rS (s2 @ f t2 idS) s2 ); intro J.
          apply is_right_idT.           
          assert (fact1 := ridSf idS is_right_idS t2). apply symS in fact1.
          assert (fact2 := congS _ _ _ _ (refS s2) fact1).          
          assert (fact3 := is_right_idS s2). apply symS in fact3. apply symS in fact2.
          assert (fact4 := tranS _ _ _ fact3 fact2). apply symS in fact4.
          rewrite fact4 in J. discriminate.
Qed.           

Lemma bop_semidirect_exists_ann :
  bop_exists_ann S rS bS ->
  bop_exists_ann T rT bT ->
         bop_exists_ann (S * T) (brel_product rS rT) semidirect. 
Proof. intros [annS P] [annT Q]. exists (annS, annT). intros [s2 t2]. 
       destruct (Q t2) as [LT RT].
       split; compute.
       destruct (P (f annT s2)) as [LS _].        
       case_eq (rS (annS @ f annT s2) annS); intro J. 
          exact LT. 
          rewrite LS in J. discriminate.
       destruct (P s2) as [_ RS].                  
       case_eq (rS (s2 @ f t2 annS) annS); intro J.           
          exact RT.                                                  
          assert (fact1 := annSf annS P t2).
          assert (fact2 := congS _ _ _ _ (refS s2) fact1). apply symS in RS.
          assert (fact3 := tranS _ _ _ RS fact2). apply symS in fact3.
          rewrite fact3 in J. discriminate.
Qed.


Lemma bop_semidirect_not_exists_ann_v1 :
  bop_not_exists_ann T rT bT ->
         bop_not_exists_ann (S * T) (brel_product rS rT) semidirect. 
Proof. intros H (s, t). unfold bop_not_is_ann.
       destruct(H t) as [t' [Q | Q]]; exists (s, t'); compute.
          left. case_eq (rS (s @ f t s) s); intro J; auto. 
          right. case_eq (rS (s @ f t' s) s); intro J; auto.
Qed.

Lemma bop_semidirect_not_exists_ann_v2 :
  bop_not_exists_ann S rS bS ->
  bop_exists_ann T rT bT ->
         bop_not_exists_ann (S * T) (brel_product rS rT) semidirect. 
Proof. intros F [annT P] (s, t). compute in F. 
       destruct (F (f annT s)) as [wS Q]. exists (wS, annT). compute.
       case_eq(rS (s @ f t wS) s); intro J; case_eq(rS (wS @ f annT s) s); intro K; auto.
       destruct (annTf annT P s wS) as [L R]. 
       destruct Q as [Q | Q].
          rewrite L in Q. discriminate.           
          rewrite R in Q. discriminate.           
Qed.


Lemma bop_semidirect_idempotent : 
      ltr_idempotent T S rS bS f → 
      bop_idempotent T rT bT → 
         bop_idempotent (S * T) (brel_product rS rT) semidirect. 
Proof. 
   unfold bop_idempotent. intros L R (s, t). simpl. 
   apply andb_is_true_right. split. 
      rewrite L. reflexivity. 
      rewrite R. reflexivity. 
Defined. 


Lemma bop_semidirect_not_idempotent_v1 : 
      ltr_not_idempotent T S rS bS f → 
         bop_not_idempotent (S * T) (brel_product rS rT) semidirect. 
Proof. intros [ [t s] P]. 
       exists (s, t). simpl. 
       apply andb_is_false_right. left. assumption. 
Defined. 

Lemma bop_semidirect_not_idempotent_v2 (s : S) : 
      bop_not_idempotent T rT bT → 
         bop_not_idempotent (S * T) (brel_product rS rT) semidirect. 
Proof. intros [ t P ]. 
       exists (s, t). simpl. 
       apply andb_is_false_right. right . assumption. 
Defined. 

(* *) 
Lemma bop_semidirect_left_cancellative :
      (∀ (s1 s2 : S) (t : T), f t s1 =S f t s2  → s1 =S s2) → 
      bop_left_cancellative S rS bS  → 
      bop_left_cancellative T rT bT → 
      bop_left_cancellative (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros I L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply L in HL. apply R in HR. rewrite HR. rewrite (I s2 s3 t1 HL). auto. 
Defined. 


Lemma bop_semidirect_left_cancellative_II :
      (∀ (s s' s'': S) (t : T), (s @ (f t s')) =S (s @ (f t s''))  → s' =S s'') → 
      bop_left_cancellative T rT bT → 
      bop_left_cancellative (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros I R [s1 t1] [s2 t2] [s3 t3]; simpl; intro H. 
   apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply R in HR. rewrite HR. rewrite (I s1 s2 s3 t1 HL). auto. 
Defined. 

Lemma bop_semidirect_not_left_cancellative_v1 (s : S):
      bop_not_left_cancellative T rT bT → 
      bop_not_left_cancellative (S * T) (brel_product rS rT) semidirect. 
Proof. intros [[t1 [t2 t3]] [L R]].  exists ( (s, t1), ( (s, t2), (s, t3) ) ). compute. split. 
       rewrite (refS (s @ f t1 s)). assumption.        
       rewrite (refS s). assumption.        
Defined. 


Lemma bop_semidirect_not_left_cancellative_v2 :
      { s : S & {s' : S & {s'': S & {t : T &  (s @ (f t s')) =S (s @ (f t s'')) * (s' !=S s'')}}}} -> 
      bop_not_left_cancellative (S * T) (brel_product rS rT) semidirect. 
Proof. intros [s [s' [s'' [t [L R]]]]].  exists ( (s, t), ( (s', t), (s'', t) ) ). compute.
       rewrite R. rewrite L. rewrite (refT (t # t)). split; reflexivity. 
Defined. 


Lemma bop_semidirect_right_cancellative : 
      (∀ (s1 s2 s3 : S) (t1 t2 : T), (s2 @ (f t1 s1)) =S (s3 @ (f t2 s1)) -> s2 =S s3) -> 
      bop_right_cancellative T rT bT → 
      bop_right_cancellative (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3] ; simpl. intro H. 
   apply andb_is_true_left in H. destruct H as [HL HR]. 
   apply andb_is_true_right. split. 
      apply (L s1 s2 s3 t2 t3 HL). 
      apply R in HR. assumption. 
Qed.

(* 
Print bop_semidirect_right_cancellative. 

bop_semidirect_right_cancellative = 
λ (L : ∀ (s1 s2 s3 : S) (t1 t2 : T), (s2 @ f t1 s1) =S (s3 @ f t2 s1) → s2 =S s3) 
  (R : bop_right_cancellative T rT bT) 
  (s : S * T),
let (s1, t1) as p return (∀ t u : S * T, semidirect t p == semidirect u p → t == u) := s 
in λ t : S * T,
     let (s2, t2) as p return (∀ u : S * T, semidirect p (s1, t1) == semidirect u (s1, t1) → p == u) := t 
     in λ u : S * T,
         let (s3, t3) as p return (semidirect (s2, t2) (s1, t1) == semidirect p (s1, t1) → (s2, t2) == p) := u 
         in λ (H : rS (s2 @ f t2 s1) (s3 @ f t3 s1) && rT (t2 # t1) (t3 # t1) = true)
              (H0:(s2 @ f t2 s1) =S (s3 @ f t3 s1) * (t2 # t1) =T (t3 # t1)
                  :=andb_is_true_left (rS (s2 @ f t2 s1) (s3 @ f t3 s1)) (rT (t2 # t1) (t3 # t1)) H),
              let (HL, HR) := H0 
              in andb_is_true_right (rS s2 s3) (rT t2 t3) (L s1 s2 s3 t2 t3 HL, let HR0 := R t1 t2 t3 HR : t2 =T t3 in HR0)
     : (∀ (s1 s2 s3 : S) (t1 t2 : T), (s2 @ f t1 s1) =S (s3 @ f t2 s1) → s2 =S s3)
       → bop_right_cancellative T rT bT → bop_right_cancellative (S * T) (brel_product S T rS rT) semidirect


HERE

*) 
Lemma bop_semidirect_not_right_cancellative_v1 (s : S) : 
  bop_not_right_cancellative T rT bT →
  (∀ (s : S) (t1 t2 : T), (s @ f t1 s) =S (s @ f t2 s))  →
      bop_not_right_cancellative (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros [[t1 [t2 t3]] [L R]] K; exists ( (s, t1), ( (s, t2), (s, t3) ) ). split. 
      compute. case_eq (rS (s @ f t2 s) (s @ f t3 s)); intro J.
         exact L. 
         assert (F := K s t2 t3). rewrite F in J. discriminate. 
      compute. rewrite (refS s). exact R. 
Defined. 



Lemma bop_semidirect_is_left : 
      bop_is_left S rS bS → 
      bop_is_left T rT bT → 
      bop_is_left (S * T) (brel_product rS rT) semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_semidirect_not_is_left_v1 (t : T) : 
      bop_not_is_left S rS bS → 
      bop_not_is_left (S * T) (brel_product rS rT) semidirect. 
Proof. intros [[s s'] P]. exists ( (s, t), (s', t) ). compute.
       case_eq(rS (s @ f t s') s); intro H.
          admit. 
          reflexivity. 
Admitted.        


Lemma bop_semidirect_not_is_left_v2 (s : S) : 
      bop_not_is_left T rT bT → 
      bop_not_is_left (S * T) (brel_product rS rT) semidirect. 
Proof. intros [[t t'] P]. exists ( (s, t), (s, t') ). compute. rewrite P. 
       case_eq (rS (s @ f t s) s); intro J; auto. 
Qed. 


Lemma bop_semidirect_left_constant : 
      bop_left_constant S rS bS → 
      bop_left_constant T rT bT → 
      bop_left_constant (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. apply L. apply R. 
Defined. 


Lemma bop_semidirect_not_left_constant_v1 (s : S) :
      bop_not_left_constant T rT bT → 
      bop_not_left_constant (S * T) (brel_product rS rT) semidirect. 
Proof. intros [[t1 [t2 t3]] F]. exists ( (s, t1), ( (s, t2), (s, t3) ) ). compute.
       rewrite (refS (s @ f t1 s)). exact F. 
Qed. 

Lemma bop_semidirect_not_left_constant_v2 (t : T) :
      bop_not_left_constant S rS bS → 
      bop_not_left_constant (S * T) (brel_product rS rT) semidirect. 
Proof. intros [[s1 [s2 s3]] F]. exists ( (s1, t), ( (s2, t), (s3, t) ) ). compute.
       rewrite (refT (t # t)).
       case_eq(rS (s1 @ f t s2) (s1 @ f t s3)); intro J; auto. 
       admit. (* need (s1 @ f t s2) !=S (s1 @ f t s3)  *) 
Admitted. 


Lemma bop_semidirect_is_right_I : 
      (((bop_is_right S rS bS) * (∀ (s : S) (t: T), rS (f t s) s = true)) 
       + (∀ (s1 s2 : S) (t: T), rS (bS s1 (f t s2)) s2 = true))   → 
      bop_is_right T rT bT → 
      bop_is_right (S * T) (brel_product rS rT) semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite R. simpl.
       destruct L as [ [rcS L ] | L].
         admit. 
         rewrite L. simpl. reflexivity. 
Admitted. 


Lemma bop_semidirect_is_right_II :
       (∀ (s1 s2 : S) (t: T), s1 @ (f t s2) =S s2)   → 
      bop_is_right T rT bT → 
      bop_is_right (S * T) (brel_product rS rT) semidirect. 
Proof. intros H R (s1, t1) (s2, t2). compute.
       rewrite (H s1 s2 t1). apply R. 
Qed.        





Lemma bop_semidirect_right_constant : 
      (((bop_right_constant S rS bS) * (∀ (s : S) (t1 t2: T), rS (f t1 s) (f t2 s) = true)) 
         + (∀ (s1 s2 s3 : S) (t1 t2: T), rS (bS s2 (f t1 s1)) (bS s3 (f t2 s1)) = true)) → 
      bop_right_constant T rT bT → 
      bop_right_constant (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   apply andb_is_true_right. split. 
      destruct L as [ [rcS L ] | L].
         admit. 
         rewrite L. simpl. reflexivity. 
      apply R. 

Admitted. 

(* needs negation *) 
Lemma bop_semidirect_product_anti_left : 
      (bop_anti_left S rS bS) + (bop_anti_left T rT bT) → 
      bop_anti_left (S * T) (brel_product rS rT) semidirect. 
Proof. 
   intros [P | P] [s1 t1] [s2 t2]; simpl; apply andb_is_false_right.
      left. apply P. 
      right. apply P. 
Defined. 

(* needs negation *) 
Lemma bop_semidirect_anti_right : 
      ((bop_anti_right S rS bS) * (∀ (s : S) (t : T), rS s (f t s) = true)) 
      + (∀ (s1 s2 : S) (t : T), rS s1 (bS s2 (f t s1)) = false)
      + (bop_anti_right T rT bT) → 
      bop_anti_right (S * T) (brel_product rS rT) semidirect. 
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
    ( (s1 =S (s1 @ f t1 s2)) *  (t1 =T (t1 # t2)) ) 
       +
    ( (s2 =S (s1 @ f t1 s2)) *  (t2 =T (t1 # t2)) )

  (Q idS s t idT) simplifies to 
    (idS =S f t s)  + ( (s =S (f idT s)) *  (idT =T t) )

  (Q s idS idT t) simplifies to 
    ( (s =S (s @ f idT idS)) *  (idT =T (idT # t)) ) 
       +
    ( (idS =S (s @ f idT idS)) *  (t =T (idT # t)) )
    

Use    f (t1 # t2) s =S f t1 (f t2 s)         
       f t (s1 @ s2) =S (f t s1) @ (f t s2)       
to explore? 

    


*)

(* needs negation *) 
Lemma bop_semidirect_selective :
  (∀ (s1 s2 : S) (t1 t2 : T), 
    ( (s1 =S (s1 @ f t1 s2)) *  (t1 =T (t1 # t2)) ) 
       +
    ( (s2 =S (s1 @ f t1 s2)) *  (t2 =T (t1 # t2)) )
   ) → 
   bop_selective (S * T) (brel_product rS rT) semidirect. 
Proof. intros P [s1 t1] [s2 t2]; compute.
       assert (Q := P s1 s2 t1 t2).
       destruct Q as [[H1 H2]| [H1 H2]].
       apply symS in H1. apply symT in H2. rewrite H1, H2. left. reflexivity. 
       apply symS in H1. apply symT in H2. rewrite H1, H2. right. reflexivity.
Qed.        


(* STRANGE : s1 + (f t1 s2) = s2 + (f t2 s1) *)
Definition ltr_commutative (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := ∀ (s1 s2 : S) (t1 t2 : T), rT (bT t1 (f s1 t2)) (bT t2 (f s2 t1)) = true. 

Definition ltr_not_commutative (S T: Type) (rT : brel T) (bT : binary_op T) (f : left_transform S T)
   := { z : (S * S) * (T * T) & 
        match z with ((s1, s2), (t1, t2)) => 
              rT (bT t1 (f s1 t2)) (bT t2 (f s2 t1)) = false 
        end 
      }. 

(*
bop_commutative T rT bT → f t2 (f t1 s) s =S f t1 (f t2 s)

ltr_commutative T S rS bS f → 
    f t (s1 @ s2) =S (f t s1) @ (f t s2)
                  =S s2 @ (f t' (f t s1))
                  =S s2 @ (f (t' # t) s1)
                  =S s1 @ (f t'' s2)
Hmm, what to do with this? Contradict pres of ann? 

what if "f t idS = idS"?   
Then ltr_commutative IFF (f t s = s and @ is commutative).  

    f t s =S idS @ (f t s) 
          =S s @ (f t' idS)   (ltr_commutative) 
          =S s @ idS 
          =S s 

Require "f t idS = idS"?   

*) 
Lemma bop_semidirect_commutative :
      ltr_commutative T S rS bS f →    (* s1 @ (f t1 s2) =S s2 @ (f t2 s1) *) 
      bop_commutative T rT bT → 
         bop_commutative (S * T) (brel_product rS rT) semidirect. 
Proof. intros L R (s1, t1) (s2, t2). simpl. 
       apply andb_is_true_right. split. 
          rewrite L. reflexivity.           
          rewrite R. reflexivity. 
Defined. 

Lemma bop_semidirec_not_commutative_v1 : 
      ltr_not_commutative T S rS bS f → 
         bop_not_commutative (S * T) (brel_product rS rT) semidirect. 
Proof. intros [[ [t1 t2] [s1 s2 ] ] P]. 
       exists ((s1, t1), (s2, t2)). simpl. 
       apply andb_is_false_right. left. assumption. 
Defined. 


Lemma bop_semidirec_not_commutative_v2 (s : S) : 
      bop_not_commutative T rT bT → 
         bop_not_commutative (S * T) (brel_product rS rT) semidirect. 
Proof. intros [ [t1 t2] P]. 
       exists ((s, t1), (s, t2)). simpl. 
       apply andb_is_false_right. right. assumption. 
Defined. 


End Test. 

