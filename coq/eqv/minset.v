Require Import Coq.Lists.List.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce. 


Section Operations.

Definition below {S : Type} (lte : brel S) : brel S := λ a y, bop_and (lte y a) (uop_not(lte a y)).
  
(* Definition not_below {S : Type} (lte : brel S) : brel S := λ a y, bop_or (lte a y) (uop_not (lte y a)). *) 

Definition equiv {S : Type} (lte : brel S) : brel S := λ a b, bop_and (lte a b) (lte b a).

Definition incomp {S : Type} (lte : brel S) : brel S := λ a b, bop_and (uop_not(lte a b)) (uop_not (lte b a)).

Definition equiv_or_incomp {S : Type} (lte : brel S) : brel S := λ a b, bop_or (equiv lte a b) (incomp lte a b). 


Definition iterate_minset : ∀ {S : Type} (lte : brel S), (finite_set S)  -> (finite_set S)  -> (finite_set S) 
  := λ {S} lte,  fix f Y X  :=
      match X with
         | nil => Y
         | a :: Z => match find (below lte a) Z with
                     | None   => match find (below lte a) Y with
                                 | None   => f (a :: Y) Z 
                                 | Some _ => f Y Z 
                                 end 
                     | Some _ => f Y Z 
                     end
end.

Definition uop_minset {S : Type} (lte :brel S) : unary_op (finite_set S) 
  := λ X, iterate_minset lte nil X. 

Definition brel_minset {S : Type} (eq lte : brel S)  : brel (finite_set S)
  := λ X Y, brel_set eq (uop_minset lte X) (uop_minset lte Y).

End Operations.  

Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable fS : S -> S.                
Variable Pf : brel_not_trivial S rS fS. 

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S. 
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 

Notation "a [=] b"  := (rS a b = true)          (at level 15).
Notation "a [<>] b" := (rS a b = false)         (at level 15).
Notation "a <<= b"  := (lteS a b = true)        (at level 15).
Notation "a !<<= b" := (lteS a b = false)       (at level 15).
Notation "a << b"   := (below lteS b a = true) (at level 15).
Notation "a !<< b"  := (below lteS b a = false) (at level 15).
Notation "a [~] b"   := (equiv lteS b a = true) (at level 15).
Notation "a [!~] b"   := (equiv lteS b a = false) (at level 15).
Notation "a [#] b"   := (incomp lteS b a = true) (at level 15).
Notation "a [!#] b"   := (incomp lteS b a = false) (at level 15).
Notation "a [~|#] b"   := (equiv_or_incomp lteS b a = true) (at level 15).
Notation "a [!~|#] b"   := (equiv_or_incomp lteS b a = false) (at level 15).

Notation "a [in] b"  := (in_set rS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set rS b a = false)  (at level 15).

Notation "a [=S] b"   := (brel_set rS a b = true)         (at level 15).
Notation "a [<>S] b"  := (brel_set rS a b = false)        (at level 15).
Notation "a [=MS] b"  := (brel_minset rS lteS a b = true)        (at level 15).
Notation "a [<>MS] b" := (brel_minset rS lteS a b = false)       (at level 15).
Notation "[ms] x" := (uop_minset lteS x) (at level 15).

Definition set_congruence := brel_set_congruence S rS refS symS tranS.
Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.


Definition brel_equiv_congruence  (r : brel S) := 
       ∀ s t u v : S, s [~] u  → t [~] v → r s t = r u v. 


Definition brel_incomp_congruence  (r : brel S) := 
       ∀ s t u v : S, s [#] u  → t [#] v → r s t = r u v. 


(************** intro and elim ******************)
(**************** below *************************) 

Lemma below_intro (a b : S) : b <<= a  -> a !<<= b -> b << a. 
Proof. intros A B. unfold below. rewrite A, B. compute. auto. Qed. 

Lemma below_elim (a b : S) : b << a -> (b <<= a) * (a !<<= b). 
Proof. intros A. unfold below in A. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma below_false_intro (a b : S) : (b !<<= a  + a <<= b) -> b !<< a. 
Proof. unfold below. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lteS b a); intro B; auto. 
Qed. 

Lemma below_false_elim (a b : S) : b !<< a -> (b !<<= a  + a <<= b). 
Proof. intros A. unfold below in A. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.

(**************** equiv *************************) 

Lemma equiv_intro (a b : S) : b <<= a  -> a <<= b -> b [~] a. 
Proof. intros A B. unfold equiv. rewrite A, B. compute. auto. Qed. 

Lemma equiv_elim (a b : S) : b [~] a -> (b <<= a) * (a <<= b). 
Proof. intros A. unfold equiv in A. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma equiv_false_intro (a b : S) : (b !<<= a  + a !<<= b) -> b [!~] a. 
Proof. unfold equiv. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lteS a b); intro B; auto. 
Qed. 

Lemma equiv_false_elim (a b : S) : b [!~] a -> (b !<<= a  + a !<<= b). 
Proof. intros A. unfold equiv in A. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.

(**************** incomp *************************) 

Lemma incomp_intro (a b : S) : b !<<= a  -> a !<<= b -> b [#] a. 
Proof. intros A B. unfold incomp. rewrite A, B. compute. auto. Qed. 

Lemma incomp_elim (a b : S) : b [#] a -> (b !<<= a) * (a !<<= b). 
Proof. intros A. unfold incomp in A. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma incomp_false_intro (a b : S) : (b <<= a  + a <<= b) -> b [!#] a. 
Proof. unfold incomp. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lteS a b); intro B; auto. 
Qed. 

Lemma incomp_false_elim (a b : S) : b [!#] a -> (b <<= a  + a <<= b). 
Proof. intros A. unfold incomp in A. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.



(**************** equiv_or_incomp *************************) 
Lemma equiv_or_incomp_intro (a b : S) : (a [~] b) + (a [#] b) -> a [~|#] b.
Proof. unfold equiv_or_incomp. intros [A | A].
       rewrite A ; compute; auto.
       compute in A.  compute. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.
          rewrite B in A. discriminate A.
          rewrite B in A. rewrite C in A. discriminate A.        
Qed. 

Lemma equiv_or_incomp_elim (a b : S) : a [~|#] b -> (a [~] b) + (a [#] b).
Proof. intros A. compute in A. compute. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
       rewrite B, C in A. discriminate A.
       rewrite B, C in A. discriminate A.
Qed.

Lemma equiv_or_incomp_false_intro (a b : S) :  (a [!~] b) * (a [!#] b) -> a [!~|#] b. 
Proof. unfold equiv_or_incomp. intros [A  B]. rewrite A, B. compute; auto. Qed. 

Lemma equiv_or_incomp_false_elim (a b : S) : a [!~|#] b -> (a [!~] b) * (a [!#] b).
Proof. intros A. compute in A. compute. 
       case_eq(lteS b a); intro B; case_eq(lteS a b); intro C; auto.  
          rewrite B, C in A. discriminate A.
          rewrite B, C in A. discriminate A.       
Qed.

(************** brel properties *****************)
(**************** below *************************) 

Lemma below_congruence : brel_congruence S rS (below lteS). 
Proof. intros a b c d A B.
       unfold below. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lteS d c); intro C; case_eq(lteS c d); intro D; auto.
Qed. 

Lemma below_not_reflexive (a : S ) : a !<< a.
Proof. compute. rewrite lteRefl. rewrite lteRefl. reflexivity. Qed.

Lemma below_anti_symmetric (a b : S ) : a << b -> b !<< a.
Proof. compute. case_eq(lteS a b); intro A; case_eq(lteS b a); intro B; auto. Qed. 

Lemma below_transitive (a s t : S ) : t << a -> a << s -> t << s. 
Proof. intros A B. apply below_elim in A. apply below_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       apply below_intro.
          exact (lteTrans _ _ _ A B). 
          case_eq(lteS s t); intro E; auto. 
             assert (F := lteTrans _ _ _ B E). 
             rewrite F in C. discriminate C.
Qed. 

(**************** equiv *************************) 

Lemma equiv_congruence : brel_congruence S rS (equiv lteS). 
Proof. intros a b c d A B.
       unfold equiv. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lteS d c); intro C; case_eq(lteS c d); intro D; auto.
Qed. 

Lemma equiv_reflexive : brel_reflexive S (equiv lteS).
Proof. compute. intro s. rewrite lteRefl. exact (lteRefl s).  Qed.

Lemma equiv_symmetric (a t : S ) : t [~] a -> a [~] t. 
Proof. intros A. apply equiv_elim in A. 
       destruct A as [A B]. 
       apply equiv_intro; auto. 
Qed. 

Lemma equiv_transitive (a s t : S ) : t [~] a -> a [~] s -> t [~] s. 
Proof. intros A B. apply equiv_elim in A. apply equiv_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       apply equiv_intro.
          exact (lteTrans _ _ _ A B).
          exact (lteTrans _ _ _ D C).        
Qed. 


(**************** incomp *************************) 
Lemma incomp_congruence : brel_congruence S rS (incomp lteS). 
Proof. intros a b c d A B.
       unfold incomp. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lteS d c); intro C; case_eq(lteS c d); intro D; auto.
Qed. 

Lemma incomp_not_reflexive (a : S ) : a [!#] a.
Proof. compute. rewrite lteRefl. reflexivity. Qed. 

Lemma incomp_symmetric (a t : S ) : t [#] a -> a [#] t. 
Proof. intros A. apply incomp_elim in A. 
       destruct A as [A B]. 
       apply incomp_intro; auto. 
Qed. 

Lemma incomp_pseudo_transitive (a s t : S ) : t [#] a -> a [#] s -> (t [#] s) + (t [~] s) + (s << t ) + (t << s). 
Proof. intros A B. apply incomp_elim in A. apply incomp_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       compute.
       case_eq(lteS s t); intro E; case_eq(lteS t s); intro F; auto.
Qed. 


(**************** equiv_or_incomp *************************) 
Lemma equiv_or_incomp_congruence : brel_congruence S rS (equiv_or_incomp lteS). 
Proof. intros a b c d A B.
       unfold equiv_or_incomp. 
       rewrite (equiv_congruence _ _ _ _ A B). 
       rewrite (incomp_congruence _ _ _ _ A B). 
       compute. 
       case_eq(lteS d c); intro C; case_eq(lteS c d); intro D; auto.
Qed. 

Lemma equiv_or_incomp_reflexive : brel_reflexive S (equiv_or_incomp lteS).
Proof. compute. intro s. rewrite lteRefl. rewrite lteRefl; auto. Qed.

Lemma equiv_or_incomp_symmetric (a t : S ) : t [~|#] a -> a [~|#] t. 
Proof. intros A. apply equiv_or_incomp_elim in A.
       apply equiv_or_incomp_intro. 
       destruct A as [A | A]. 
          left. apply equiv_symmetric; auto.
          right. apply incomp_symmetric; auto.        
Qed. 

Lemma equiv_or_incomp_pseudo_transitive (a s t : S ) : t [~|#] a -> a [~|#] s -> (t [~|#] s) + (s << t) + (t << s).  
Proof. intros A B. apply equiv_or_incomp_elim in A. apply equiv_or_incomp_elim in B.
       destruct A as [A | A]; destruct B as [B | B].
          left. left. apply equiv_or_incomp_intro.
          left. exact (equiv_transitive _ _ _ A B).

          (* t [~] a -> a [#] s -> t [#] s     extract as lemma *)
          left. left. apply equiv_or_incomp_intro.          
          right. 
          apply incomp_elim in B. apply equiv_elim in A.
          case_eq(lteS t s); intro C; auto.
             destruct A as [_ A]. 
             rewrite (lteTrans _ _ _  A C) in B. destruct B as [B _].
             discriminate B.
             apply incomp_intro; auto. 
                (* s !<<= a -> a <<=t -> s !<<= t       extract *) 
                case_eq(lteS s t); intro D; auto. 
                   destruct A as [A _]. destruct B as [_ B].                               
                   rewrite (lteTrans _ _ _ D A) in B.
                   discriminate B.

          (* t [#] a -> a [~] s -> t [#] s     extract as lemma *)
          left. left. apply equiv_or_incomp_intro.                             
          right. 
          apply incomp_elim in A. apply equiv_elim in B.
          case_eq(lteS t s); intro C; auto.
             destruct B as [_ B]. 
             rewrite (lteTrans _ _ _  C B) in A. destruct A as [A _].
             discriminate A.
             apply incomp_intro; auto.
             destruct A as [_ A]. destruct B as [B _].                               
                (* t !<<= s -> a <<= s -> s !<<= t       extract *) 
                case_eq(lteS s t); intro D; auto. 
                   rewrite (lteTrans _ _ _ B D) in A.
                   discriminate A.

          assert (C := incomp_pseudo_transitive _ _ _ A B).
          destruct C as [[[C | C] | C] | C]; auto.
          left. left. apply equiv_or_incomp_intro. right; auto.
          left. left. apply equiv_or_incomp_intro. left; auto.          
Qed. 


Lemma equiv_implies_not_below (a s : S) : (a [~] s) -> a !<< s * s !<< a.
Proof. compute. case_eq(lteS a s); intro A; case_eq(lteS s a); intro B; auto. Qed. 

Lemma incomp_implies_not_below (a s : S) : (a [#] s) -> a !<< s * s !<< a.   
Proof. compute. case_eq(lteS a s); intro A; case_eq(lteS s a); intro B; auto. Qed.

Lemma equiv_or_incomp_implies_not_below (a s : S) : (a [~|#] s) -> a !<< s * s !<< a. 
Proof. compute. case_eq(lteS a s); intro A; case_eq(lteS s a); intro B; auto. Qed.

Lemma not_below_implies_equiv_or_incomp (a s : S) : a !<< s -> (s !<< a) -> (a [~|#] s). 
Proof. compute. case_eq(lteS a s); intro A; case_eq(lteS s a); intro B; auto. Qed.


Lemma below_equiv_pseudo_congruence :
  ∀ a b c d : S, a [~] c → b [~] d → (below lteS a b = below lteS c d) + ((a << b) *  (d << c)) + ((b << a) * (c << d)). 
Proof. intros a b c d A B.
       apply equiv_elim in A. apply equiv_elim in B.
       destruct A as [A1 A2]. destruct B as [B1 B2].
       compute. 
       case_eq(lteS d c); intro C; case_eq(lteS c d); intro D;
       case_eq(lteS b a); intro E; case_eq(lteS a b); intro F; auto.
          (* a~c, b~d, d~c, but b!~a  *** *)      
          assert (G := lteTrans _ _ _ A1 D). 
          assert (H := lteTrans _ _ _ G B2). 
          rewrite H in F. discriminate F. 
          (* a~c, b~d, a~b, but c!~d  *** *)        
          assert (G := lteTrans _ _ _ A2 F). 
          assert (H := lteTrans _ _ _ G B1). 
          rewrite H in D. discriminate D. 
          (* a~c, b~d, but d <<c   a#b  ***  *) 
          assert (G := lteTrans _ _ _ B1 C). 
          assert (H := lteTrans _ _ _ G A2). 
          rewrite H in E. discriminate E. 
          (* a~c, b~d, but c#d     b << a ***  *)
          assert (G := lteTrans _ _ _ B2 E). 
          assert (H := lteTrans _ _ _ G A1). 
          rewrite H in C. discriminate C. 
Qed. 


Lemma below_equiv_pseudo_congruence_v2 :
  ∀ a b c  : S, a [~] c → below lteS a b = below lteS c b. 
Proof. intros a b c A.       
       destruct (below_equiv_pseudo_congruence _ _ _ _ A (equiv_reflexive b)) as [[C | [C D]] | [C D]]; auto.
          apply equiv_elim in A. destruct A as [A B].
          assert (E := below_transitive _ _ _ C D).
          apply below_elim in E. destruct E as [E F].       
          rewrite F in B. discriminate B.
          apply equiv_elim in A. destruct A as [A B].
          assert (E := below_transitive _ _ _ D C).
          apply below_elim in E. destruct E as [E F].       
          rewrite F in A. discriminate A.
Qed.        
 


Lemma find_brel_congruence (X: finite_set S) (r : brel S) :
    brel_congruence S rS r -> ∀ (s t : S), s [=] t -> find (r s) X = find (r t) X. 
Proof. induction X.
       intros A s t B. compute; auto.
       intros A s t B.
       unfold find; fold (find (r s)); fold (find (r t)).
       rewrite (A _ _ _ _ B (refS a)). 
       rewrite (IHX A s t B).
       reflexivity. 
Qed.


Lemma find_equiv_congruence (X: finite_set S) (r : brel S) :
  brel_equiv_congruence r -> ∀ (s t : S), s [~] t -> find (r s) X = find (r t) X.
Proof. induction X.
       intros A s t B. compute; auto.
       intros A s t B.
       unfold find; fold (find (r s)); fold (find (r t)).
       rewrite (A _ _ _ _ B (equiv_reflexive a)).
       rewrite (IHX A s t B).
       reflexivity. 
Qed.


Lemma find_equiv_below_congruence (X: finite_set S):
 ∀ (s t : S), s [~] t -> find (below lteS s) X = find (below lteS t) X.
Proof. induction X.
       intros s t A. compute; auto.
       intros s t A.
       unfold find; fold (find (below lteS s)); fold (find (below lteS t)).
       rewrite (below_equiv_pseudo_congruence_v2 _ _ _  A). 
       rewrite (IHX s t A).
       reflexivity. 
Qed.


Lemma find_below_congruence (X: finite_set S) : 
  ∀ (s t : S), s [=] t -> find (below lteS s) X = find (below lteS t) X.
Proof. apply find_brel_congruence. apply below_congruence. Qed.   


Lemma filter_brel_congruence (X: finite_set S) (r : brel S) :
    brel_congruence S rS r -> ∀ (s t : S), s [=] t -> filter (r s) X = filter (r t) X. 
Proof. induction X.
       intros A s t B. compute; auto.
       intros A s t B.
       unfold filter; fold (filter (r s)); fold (filter (r t)).
       rewrite (A _ _ _ _ B (refS a)). 
       rewrite (IHX A s t B).
       reflexivity. 
Qed.

Lemma filter_equiv_or_incomp_congruence (X: finite_set S) : 
  ∀ (s t : S), s [=] t -> filter (equiv_or_incomp lteS s) X = filter (equiv_or_incomp lteS t) X.
Proof. apply filter_brel_congruence. apply equiv_or_incomp_congruence. Qed.   


Lemma find_below_none (X : finite_set S) : 
  ∀ (s : S), find (below lteS s) X = None -> ∀ (t : S), t [in] X ->  t !<< s. 
Proof. induction X.
       intros s A t B. compute in B. discriminate B. 
       intros s A t B. unfold find in A. fold (find (below lteS s)) in A.
       apply in_set_cons_elim in B; auto. destruct B as [B | B].
         compute. case_eq(lteS t s); intro C; case_eq(lteS s t); intro D; auto.
         rewrite (lteCong _ _ _ _ (refS s) (symS _ _ B)) in D.
         rewrite (lteCong _ _ _ _ (symS _ _ B) (refS s)) in C.         
         unfold below in A. rewrite D in A. rewrite C in A. simpl in A.
         discriminate A. 
         case_eq(below lteS s a); intro C; rewrite C in A. 
            discriminate A.
            apply IHX; auto. 
Qed.

Lemma find_below_some (X : finite_set S) :
      ∀ (s t : S), find (below lteS s) X = Some t -> t [in] X * (t << s).
Proof. induction X.
       intros s t A. compute in A. discriminate A.
       intros s t A. unfold find in A. fold (find (below lteS s)) in A.
       case_eq(below lteS s a); intro B; rewrite B in A. 
          assert (C : t = a ). inversion A. reflexivity. 
          rewrite C. split; auto. 
             apply in_set_cons_intro; auto. 
          destruct (IHX s t A) as [C D].
          split; auto.
          apply in_set_cons_intro; auto. 
Qed.

Lemma in_filter_brel_elim  (X : finite_set S) (r : brel S):
     brel_congruence S rS r -> 
     ∀ (s t : S), s [in] (filter (r t) X) -> (s [in] X) * (r t s = true).
Proof. induction X.
       intros C s t A. compute in A. discriminate A. 
       intros C s t A.
       unfold filter in A. fold (filter (r t)) in A. 
       case_eq (r t a); intro B.
          rewrite B in A. 
          apply in_set_cons_elim in A; auto. 
          destruct A as [A | A]. split. 
             apply in_set_cons_intro; auto.
             rewrite (C _ _ _ _ (refS t) A) in B; auto.
             destruct (IHX C s t A) as [D E].
             split; auto.
             apply in_set_cons_intro; auto.

          rewrite B in A.
          destruct (IHX C s t A) as [D E].             
             split; auto.
             apply in_set_cons_intro; auto.
Qed.              

Lemma in_filter_equiv_or_incomp_elim  (X : finite_set S) :
     ∀ (s t : S), s [in] (filter (equiv_or_incomp lteS t) X) -> (s [in] X) * (equiv_or_incomp lteS t s = true).
Proof. apply in_filter_brel_elim.  apply equiv_or_incomp_congruence. Qed. 





(** *******************  minset ********************* **)


(********** lemmas for uop_minset ***********)

Definition is_antichain (X : finite_set S) :=   ∀ (s : S), s [in] X  -> ∀ (t : S), t [in] X  -> (s [~|#] t).

Lemma brel_iterate_minset_congruence (X1 X2 Y1 Y2 : finite_set S) :
  Y1 [=S] Y2 -> X1 [=S] X2 -> 
  iterate_minset lteS Y1 X1 [=S] iterate_minset lteS Y2 X2. 
Proof. induction X1; induction X2.
          intros A B. unfold iterate_minset; auto. 

          intros A B. compute in B. discriminate B. 

          intros A B. compute in B. discriminate B.           

          intros A B. 
Admitted.  

Lemma brel_minset_congruence : uop_congruence (finite_set S) (brel_set rS) (uop_minset lteS).
Proof. unfold uop_minset. intros X Y A.
Admitted.


Lemma minset_empty : [ms] nil = nil. 
Proof. compute; auto. Qed. 

Lemma minset_singleton : ∀ (s : S), [ms] (s :: nil) = s :: nil. 
Proof. intro s. compute; auto. Qed. 



Lemma in_iterate_minset_implies_in_union (X : finite_set S) :
      ∀ (s : S) (Y : finite_set S),  s [in] iterate_minset lteS Y X -> (s [in] Y) + (s [in] X). 
Proof. induction X. 
       intros s Y A. unfold iterate_minset in A; auto. 
       intros s Y A. unfold iterate_minset in A. 
       case_eq(find (below lteS a) X).
          intros t B. rewrite B in A. 
          fold (iterate_minset lteS Y X) in A.
          destruct (IHX s Y A) as [C | C]; auto. 
             right. apply in_set_cons_intro; auto.           

          intros B. rewrite B in A.
          case_eq(find (below lteS a) Y).          
             intros t C. rewrite C in A. 
             fold (iterate_minset lteS Y X) in A.
             destruct (IHX s Y A) as [D | D]; auto. 
                right. apply in_set_cons_intro; auto.           
             intros C. rewrite C in A. 
             fold (iterate_minset lteS (a ::Y) X) in A.
             destruct (IHX s (a :: Y) A) as [D | D]; auto. 
                apply in_set_cons_elim in D; auto. 
                destruct D as [D | D]; auto. 
                   right. apply in_set_cons_intro; auto. 
                right. apply in_set_cons_intro; auto. 
Qed. 

Lemma in_minset_implies_in_set (X : finite_set S) :
      ∀ (s : S), s [in] ([ms] X) -> s [in] X. 
Proof. intros s A.
       unfold uop_minset in A.
       destruct (in_iterate_minset_implies_in_union _ _ _ A) as [B | B]; auto.
          compute in B. discriminate B.
Qed.           

Lemma empty_set_is_antichain : is_antichain nil.
Proof. intros s A t. compute in A. discriminate A. Qed. 

Lemma is_antichain_cons_intro (X : finite_set S) :
    is_antichain X -> ∀ (s : S), (∀ (t : S),  t [in] X -> s [~|#] t) -> is_antichain (s :: X). 
Proof. intros A s I t B u C.
       apply in_set_cons_elim in B; auto. apply in_set_cons_elim in C; auto. 
       destruct B as [B | B]; destruct C as [C | C].
          rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ C) (symS _ _ B)).
          apply equiv_or_incomp_reflexive.                    

          assert (K := I _ C). 
          rewrite (equiv_or_incomp_congruence _ _ _ _ (refS u) (symS _ _ B)); auto. 

          assert (K := I _ B). 
          rewrite (equiv_or_incomp_congruence  _ _ _ _  (symS _ _ C) (refS t)); auto. 
          apply equiv_or_incomp_symmetric; auto. 
          
          exact (A t B u C).
Qed.


Lemma is_antichain_cons_elim (X : finite_set S) :
  ∀ (s : S), is_antichain (s :: X) -> 
            (is_antichain X)  * (∀ (t : S),  t [in] X -> s [~|#] t). 
Proof. unfold is_antichain. intros s A. split. 
          intros u B t C. apply A. 
             apply in_set_cons_intro; auto.
             apply in_set_cons_intro; auto.           
          intros t B. apply A. 
             apply in_set_cons_intro; auto.
             apply in_set_cons_intro; auto.          
Qed.


Lemma iterate_minset_is_antichain (X : finite_set S) :
  ∀ (Y : finite_set S),
        is_antichain Y ->
        (∀ (s : S), s [in] X -> ∀ (t : S), t [in] Y → s !<< t) ->  
        is_antichain (iterate_minset lteS Y X).
Proof. induction X.
       intros Y A B. unfold iterate_minset. auto. 
       intros Y A B. unfold iterate_minset.
       assert (B' : ∀ t : S, t [in] Y → a !<< t).
          intros t C.
          assert (D : a [in] (a :: X)). apply in_set_cons_intro; auto.
          exact (B a D t C). 
       case_eq(find (below lteS a) X). 
          intros u C. 
          fold (iterate_minset lteS Y X).
          assert (D : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
             intros s E t F. apply B; auto. apply in_set_cons_intro; auto. 
          apply IHX; auto. 
 
          intros C.
          case_eq(find (below lteS a) Y).
             intros u D. 
             fold (iterate_minset lteS Y X).
             assert (E : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                intros s E t F. apply B; auto. apply in_set_cons_intro; auto.              
             apply IHX; auto.
             intros D. 
             fold (iterate_minset lteS (a :: Y) X).
             assert (F := find_below_none Y a D).                   
             assert (F' := find_below_none X a C).             
             assert (G : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t).
                intros s G t H.
                assert (I := F' s G).                 
                apply in_set_cons_elim in H; auto.
                destruct H as [H | H]; auto.
                   rewrite (below_congruence _ _ _ _ (symS _ _ H) (refS s) ); auto. 
                   apply B; auto. 
                   apply in_set_cons_intro; auto. 

                   
             assert (H : is_antichain (a :: Y)).
                unfold is_antichain. intros s H t I.
                apply in_set_cons_elim in H; auto. 
                apply in_set_cons_elim in I; auto.
                destruct H as [H | H]; destruct I as [I | I]. 
                   rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)). 
                   apply equiv_or_incomp_reflexive; auto.

                   assert (J := F t I).
                   assert (K := B' t I). 
                   rewrite (equiv_or_incomp_congruence _ _ _ _ (refS t) (symS _ _ H)).
                   apply not_below_implies_equiv_or_incomp; auto. 
                   
                   rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS s) ).
                   assert (J := B' s H).
                   apply equiv_or_incomp_intro.
                   compute. 
                   case_eq(lteS a s); intro K; case_eq(lteS s a); intro L; auto.  
                      compute in J. rewrite K in J. rewrite L in J. discriminate J. 
                      assert (M := F s H).
                      compute in M. rewrite L in M. rewrite K in M. discriminate M. 

                   exact (A _ H _ I). 
             exact (IHX (a :: Y) H G).
Qed. 

             
Lemma uop_minset_is_antichain (X : finite_set S) : is_antichain ([ms] X). 
Proof. assert (A : ∀ (s  : S), s [in] X -> ∀ (t : S), t [in] nil → s !<< t).
          intros s B t C. compute in C. discriminate C. 
       exact (iterate_minset_is_antichain X nil empty_set_is_antichain A).
Qed.   

(*
Lemma in_minset_cons_elim (X : finite_set S) :
  ∀ (u s : S), u [in] ([ms] (s :: X)) ->
               (({ t: S & find (below lteS s) X = Some t}) * (u [in] ([ms] X)))  +
               ((find (below lteS s) X = None) * (u [in] (s :: (filter (equiv_or_incomp lteS s) X)))). 
Proof. intros u s A. 
       unfold uop_minset.
       case_eq(find (below lteS s) X). 
          intros t B. left. split. 
          exists t; auto. 
          unfold uop_minset in A.  rewrite B in A; auto. 
          (* find (below lteS s) X = None *) 
          intro B.  right. split; auto. 
          unfold uop_minset in A.  rewrite B in A; auto.
Qed. 

Lemma in_minset_cons_intro (X : finite_set S) :
  ∀ (u s : S), ((({ t: S & find (below lteS s) X = Some t}) * (u [in] ([ms] X)))  +
                ((find (below lteS s) X = None) * (u [in] (s :: (filter (equiv_or_incomp lteS s) X)))))
                -> u [in] ([ms] (s :: X)). 
Proof. intros u s [A | A]. 
       destruct A as [[t B] C].
       unfold uop_minset. 
       rewrite B; auto. 
       destruct A as [B C].
       unfold uop_minset. 
       rewrite B; auto. 
Qed.


Lemma tmp (X : finite_set S) :
  ∀ (s t : S), s [#] t ->  filter (equiv_or_incomp lteS s) X = filter (equiv_or_incomp lteS t) X.
Proof. induction X.
       intros s t A. compute; auto. 
       intros s t A.  unfold filter.
       fold (filter (equiv_or_incomp lteS s)). 
       fold (filter (equiv_or_incomp lteS t)).
       rewrite (IHX _ _ A).         
       case_eq(equiv_or_incomp lteS s a); intro B; case_eq(equiv_or_incomp lteS t a); intro C; auto.
          (* a [~|#] s  and     a [!~|#] t   need ***  *)
          apply equiv_or_incomp_elim in B.
          apply equiv_or_incomp_false_elim in C.  destruct C as [C D].
          destruct B as [B | B].
             admit. (* need s [#] t -> t [~] u -> s [#] u  *) 
             admit. (* assume a [!#] t.  so find show a [~] t and get ****. 
                       show a << t or t << a or a [~] t. 
                       but how could  a << t or t << a given 
                       the context in uop_minset? *)        
          (* a [!~|#] s   and    a [~|#] t   need ***  *)
          apply equiv_or_incomp_false_elim in B. destruct B as [B D].
          apply equiv_or_incomp_elim in C.  
          destruct C as [C | C].
             admit.  (* again need s [#] t -> t [~] u -> s [#] u  *) 
             admit.  (* assume a [!#] s.  so find show a [~] s and get ****. 
                       show a << s or s << a or a [~] s. 
                       but how could  a << s or s << a given 
                       the context in uop_minset? *)                
Admitted. 

Lemma in_minset_implies_find_below_none (X : finite_set S) :
  ∀ (s : S), s [in] ([ms] X) -> find (below lteS s) X = None. 
Proof. induction X.
       intros s A. compute in A. discriminate A. 
       intros s A.  assert (A' := A). 
       unfold uop_minset in A. 
       case_eq(find (below lteS a) X). 
          intros t B.
          assert (C := find_below_some X a t B).
          destruct C as [C D]. 
          rewrite B in A.
          unfold uop_minset in IHX.
          assert (E := IHX s A).
          assert (F := find_below_none X s E).
          unfold find. fold (find (below lteS s)).
          rewrite E. 
          case_eq(below lteS s a); intro G; auto.
             assert (H : a [!in] X). 
                case_eq(in_set rS X a); intro I; auto.
                rewrite (F a I) in G. discriminate G.              
             assert (I := below_transitive _ _ _ D G).                 
             assert (J := F t C). 
             rewrite J in I. discriminate I. 

          intro B. rewrite B in A.
          unfold find. fold (find (below lteS s)).
          apply in_set_cons_elim in A; auto. 
          destruct A as [A | A].
             rewrite (find_below_congruence X _ _ A) in B. 
             case_eq(below lteS s a); intro C; auto.
             rewrite (below_congruence _ _ _ _ (refS s) A) in C. 
             rewrite below_not_reflexive in C. discriminate C.
             apply in_filter_equiv_or_incomp_elim in A.
             destruct A as [A C].
             apply equiv_or_incomp_elim in C. 
             destruct C as [C | C].
                (* a ~ s *) 
                destruct (equiv_implies_not_below _ _ C) as [D E]. rewrite E.
                rewrite (find_equiv_below_congruence X _ _ C); auto. 
                (* a # s *)
                destruct (incomp_implies_not_below _ _ C) as [D E]. rewrite E.
                assert(G := find_below_none X _ B). 
                case_eq(find (below lteS s) X); auto.  
                intros t H.
                destruct (find_below_some X _ _ H) as [I J].
                assert (K := G t I).                 
                unfold uop_minset in A'. 
                rewrite B in A'. 
                apply in_set_cons_elim in A'; auto.
                destruct A' as [A' | A'].
                   rewrite (below_congruence _ _ _ _ A' (refS t)) in K.
                   rewrite J in K. discriminate K. 
                   admit.                   

(*
                assert (F : s [in] ([ms] X)).
                   assert(G := find_below_none X _ B). 

                   unfold uop_minset in A'.
                   rewrite B in A'.
                   apply in_set_cons_elim in A'; au
to.
                   destruct A' as [A' | A'].
                      rewrite (incomp_congruence _ _ _ _ A' (refS s)) in C.
                      rewrite incomp_not_reflexive in C.  discriminate C. 
                      admit. (* need ? *)
                exact (IHX s F). 
*) 

Admitted.


 *)

Lemma in_iterate_minset_elim (X : finite_set S) :
  ∀ (Y : finite_set S), 
        is_antichain Y ->
        (∀ (s : S), s [in] X -> ∀ (t : S), t [in] Y → s !<< t) ->  
        ∀ (s : S), s [in] (iterate_minset lteS Y X) -> (∀ (t : S), (t [in] Y) + (t [in] X) -> t !<< s).
Proof. induction X.
       intros Y A B s C t [D | D].
          unfold is_antichain in A.
          unfold iterate_minset  in C.
          assert (E := A s C t D).
          apply equiv_or_incomp_elim in E.
          destruct E as [E | E]. 
             apply equiv_implies_not_below; auto. 
             apply incomp_implies_not_below; auto.              
          
          compute in D. discriminate D. 

       intros Y A B s C.
       assert (B' : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
          intros u D t E.
          assert (F : u [in] (a :: X)). apply in_set_cons_intro; auto. 
          exact (B u F t E). 
       unfold iterate_minset in C.
       case_eq(find (below lteS a) X). 
          intros t D. rewrite D in C.
          fold (iterate_minset lteS Y X) in C. 
          destruct (find_below_some X a t D) as [E F].
          assert (H := IHX _ A B' s C). 
          intros u [I | I]. 
             exact (H u (inl I)).
             destruct (in_iterate_minset_implies_in_union _ _ _ C) as [J | J].
                exact(B _ I _ J).               
                apply in_set_cons_elim in I; auto. 
                destruct I as [I | I]. 
                   rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ I)). 
                   case_eq(below lteS s a); intro K; auto.
                      assert (L := below_transitive _ _ _ F K). 
                      rewrite (H _ (inr E)) in L.  discriminate L. 
                   exact (H u (inr I)) . 
                
          intros D. rewrite D in C.
          assert (E := find_below_none _ _ D).                    
          case_eq(find (below lteS a) Y).
            intros t F. rewrite F in C.
            destruct (find_below_some _ _  _ F) as [G H]. 
            fold (iterate_minset lteS Y X) in C.
            assert (J := IHX _ A B' _ C). 
            intros u [K | K]. 
               exact (J u (inl K)). 
               apply in_set_cons_elim in K; auto.
               destruct K as [K | K]. 
                  rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ K)).
                  case_eq(below lteS s a); intro L; auto. 
                     assert (M := below_transitive _ _ _ H L). 
                     rewrite (J t (inl G)) in M. discriminate M. 
                  exact (J u (inr K)). 
               
            intros F. rewrite F in C.
            fold (iterate_minset lteS (a :: Y) X) in C.                                             
            assert (G := find_below_none _ _ F).
            assert (G' : ∀ t : S, t [in] Y → a !<< t).
                intros t H. 
                assert (K : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                exact (B a K t H).

            assert (A' : is_antichain (a :: Y)).
               intros u H v I.
               apply in_set_cons_elim in H; auto. apply in_set_cons_elim in I; auto. 
               destruct H as [H | H]; destruct I as [I | I].
                  rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)).
                  apply equiv_or_incomp_reflexive. 
                  
                  rewrite (equiv_or_incomp_congruence _ _ _ _ (refS v) (symS _ _ H)).                 
                  apply (not_below_implies_equiv_or_incomp).
                     exact (G' v I).
                     exact (G v I). 

                  rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS u) ).
                  apply (not_below_implies_equiv_or_incomp).
                     exact (G u H).
                     exact (G' u H). 

                  apply (not_below_implies_equiv_or_incomp).
                  assert (J := A u H v I). 
                  apply equiv_or_incomp_implies_not_below in J. 
                  destruct J as [J _]; auto.                   
                  assert (J := A u H v I). 
                  apply equiv_or_incomp_implies_not_below in J. 
                  destruct J as [_ J]; auto.                   

            assert (B'' : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t).
               intros u J v I.       
               apply in_set_cons_elim in I; auto.       
               destruct I as [I | I].
                  rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS u)).
                  exact (E u J). 
                  exact (B' u J v I). 

           assert (I := IHX _ A' B'' _ C).             

           intros t [J | J].
               assert (K : t [in] (a :: Y)). apply in_set_cons_intro; auto. 
               exact (I t (inl K)). 

               apply in_set_cons_elim in J; auto. 
               destruct J as [J | J].
                  assert (K : a [in] (a :: Y)). apply in_set_cons_intro; auto.
                  rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ J) ).
                  exact (I a (inl K)). 
               
                  exact (I t (inr J)).
Qed. 

          
Lemma in_minset_elim (X : finite_set S) :
  ∀ (s : S), s [in] ([ms] X) -> (s [in] X) * (∀ (t : S), t [in] X -> t !<< s).
Proof. intros s A. split. 
       exact (in_minset_implies_in_set X s A). 

       unfold uop_minset in A.
       assert (B : ∀ (s : S), s [in] X -> ∀ (t : S), t [in] nil → s !<< t).
          intros a D t E. compute in E. discriminate E. 
       assert (C := in_iterate_minset_elim X nil empty_set_is_antichain B s A).
       intros t D. exact (C t (inr D)). 
Qed. 



Lemma in_iterate_minset_intro (X : finite_set S) :
  ∀ (Y : finite_set S), 
        is_antichain Y ->
        (∀ (s : S), s [in] X -> ∀ (t : S), t [in] Y → s !<< t) ->  
        ∀ (s : S), (s [in] Y + s [in] X) * (∀ (t : S), (t [in] Y) + (t [in] X) -> t !<< s)
                   -> s [in] (iterate_minset lteS Y X). 
Proof. induction X. 
       intros Y A B s [[C | C] D].
          unfold iterate_minset; auto. 
          compute in C. discriminate C. 

       intros Y A B s [[C | C] D].
          unfold iterate_minset. 
          case_eq(find (below lteS a) X).
             intros t E.
             fold (iterate_minset lteS Y X).
             assert (F : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                intros u F v G.
                assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                exact (B u H v G).
             assert (G : ∀ t : S, t [in] Y + t [in] X → t !<< s).
                intros u [G | G].    
                   assert (H := A s C u G).
                   apply equiv_or_incomp_implies_not_below in H. 
                   destruct H as [_ H]; auto. 
                   assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                   exact (D u (inr H)). 
             exact (IHX _ A F s (inl C, G)).             
             
             intro E.
             case_eq(find (below lteS a) Y).
                intros t F. 
                fold (iterate_minset lteS Y X).
                   assert (G : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                      intros u G v H. 
                      assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                      exact (B u I v H). 
                   assert (H : ∀ t : S, t [in] Y + t [in] X → t !<< s). 
                      intros u [H | H].
                         exact (D u (inl H)). 
                         assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                         exact (D u (inr I)).
                   exact (IHX _ A G s (inl C, H)).             

                intro F.
                fold (iterate_minset lteS (a :: Y) X).
                assert (G : s [in] (a :: Y)). apply in_set_cons_intro; auto. 
                assert (A' : is_antichain (a :: Y)). 
                   unfold is_antichain. 
                   intros t H u I. 
                   apply in_set_cons_elim in H; auto. apply in_set_cons_elim in I; auto.
                   destruct H as [H | H]; destruct I as [I | I].
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)). 
                      apply equiv_or_incomp_reflexive. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (refS u) (symS _ _ H)). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J u I). 
                      assert (L := find_below_none _ _ F u I). 
                      apply not_below_implies_equiv_or_incomp; auto. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS t) ). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J t H). 
                      assert (L := find_below_none _ _ F t H). 
                      apply not_below_implies_equiv_or_incomp; auto. 

                      exact (A t H u I). 
                assert (H : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t). 
                    intros t H u I.
                    apply in_set_cons_elim in I; auto. destruct I as [I | I].
                       assert (J := find_below_none _ _ E t H). 
                       rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS t) ); auto. 
                       assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                       exact (B t J u I). 
                assert (J : ∀ t : S, t [in] (a :: Y) + t [in] X → t !<< s). 
                   intros t [I | I].
                      apply in_set_cons_elim in I; auto.  destruct I as [I | I].
                         rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ I)).
                         assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                         exact (B a J s C). 
                         assert (J := A s C t I). 
                         apply equiv_or_incomp_implies_not_below in J. 
                         destruct J as [_ J]; auto.
                         
                      assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                      exact (B t J s C). 

                exact (IHX _ A' H s (inl G, J)).                  
                

          unfold iterate_minset. 
          case_eq(find (below lteS a) X).
             intros t E.
             fold (iterate_minset lteS Y X).
             assert (F : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                intros u F v G. 
                assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                exact (B u H v G).
             assert (G : ∀ t : S, t [in] Y + t [in] X → t !<< s).
                intros u [G | G].    
                   exact (D u (inl G)). 
                   assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                   exact (D u (inr H)). 
             apply in_set_cons_elim in C; auto. destruct C as [C | C].
                destruct (find_below_some X a t E) as [H I].
                assert (J := G t (inr H)). 
                rewrite (below_congruence _ _ _ _ C (refS t)) in I. 
                rewrite I in J. discriminate J. 
                exact (IHX _ A F s (inr C, G)).             
             
             intro E.
             case_eq(find (below lteS a) Y).
                intros t F. 
                fold (iterate_minset lteS Y X).
                   assert (G : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                      intros u G v H. 
                      assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                      exact (B u I v H). 
                   assert (H : ∀ t : S, t [in] Y + t [in] X → t !<< s). 
                      intros u [H | H].
                         exact (D u (inl H)). 
                         assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                         exact (D u (inr I)).

                   apply in_set_cons_elim in C; auto. destruct C as [C | C].
                      destruct (find_below_some Y a t F) as [I J].
                      assert (K := H t (inl I)). 
                      rewrite (below_congruence _ _ _ _ C (refS t)) in J. 
                      rewrite J in K. discriminate K. 
                      exact (IHX _ A G s (inr C, H)).             

                intro F.
                fold (iterate_minset lteS (a :: Y) X).
                assert (A' : is_antichain (a :: Y)). 
                   unfold is_antichain. 
                   intros t H u I. 
                   apply in_set_cons_elim in H; auto. apply in_set_cons_elim in I; auto.
                   destruct H as [H | H]; destruct I as [I | I].
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)). 
                      apply equiv_or_incomp_reflexive. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (refS u) (symS _ _ H)). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J u I). 
                      assert (L := find_below_none _ _ F u I). 
                      apply not_below_implies_equiv_or_incomp; auto. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS t) ). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J t H). 
                      assert (L := find_below_none _ _ F t H). 
                      apply not_below_implies_equiv_or_incomp; auto. 

                      exact (A t H u I). 
                assert (H : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t). 
                    intros t H u I.
                    apply in_set_cons_elim in I; auto. destruct I as [I | I].
                       assert (J := find_below_none _ _ E t H). 
                       rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS t) ); auto. 
                       assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                       exact (B t J u I). 
               assert (J : ∀ t : S, t [in] (a :: Y) + t [in] X → t !<< s).
                  intros t [I | I].
                     apply in_set_cons_elim in I; auto. destruct I as [I | I]. 
                        rewrite (below_congruence _ _ _ _ (refS s)  (symS _ _ I) ).
                        assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                        exact (D a (inr J)).                   
                        exact (D t (inl I)).                   
                     assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                     exact (D t (inr J)).
              apply in_set_cons_elim in C; auto. destruct C as [C | C].
                 assert (K : s [in] (a :: Y)). apply in_set_cons_intro; auto.
                 exact (IHX _ A' H s (inl K, J)).                                
                 exact (IHX _ A' H s (inr C, J)).                  
Qed. 
       
Lemma in_minset_intro (X : finite_set S) :
  ∀ (s : S), (s [in] X) * (∀ (t : S), t [in] X -> t !<< s) -> s [in] ([ms] X). 
Proof. intros s [A B]. 
       unfold uop_minset. 
       assert (C : ∀ (s : S), s [in] X -> ∀ (t : S), t [in] nil → s !<< t).
          intros u C t D. compute in D. discriminate D. 
       assert (D : ∀ (t : S), (t [in] nil) + (t [in] X) -> t !<< s).
         intros t [D | D]. 
            compute in D. discriminate D. 
            exact (B t D). 
       exact (in_iterate_minset_intro X nil empty_set_is_antichain C s (inr A, D)). 
Qed.  

(*
  
Lemma minset_fact1 (X : finite_set S) :
  ∀ (s : S), s [in] ([ms] X) -> s [in] ([ms] (s :: X)).
Proof. destruct X. 
       intros s A. compute in A. discriminate A.
       intros a A.
       apply in_minset_intro.
       apply in_minset_elim in A. destruct A as [A B].
       split. apply in_set_cons_intro; auto. 
       intros t C.
       apply in_set_cons_elim in C; auto. 
       destruct C as [C | C].
          unfold below. 
          rewrite (lteCong _ _ _ _ (refS t) C). compute.
          rewrite lteRefl. 
          rewrite (lteCong _ _ _ _ C (refS t)). rewrite lteRefl.
          reflexivity. 
          exact (B t C).          
Qed. 

Lemma minset_fact1_contra (X : finite_set S) :
  ∀ (s : S), s [!in] ([ms] (s :: X)) -> s [!in] ([ms] X). 
Proof. intros s A. case_eq(in_set rS ([ms] X) s); intro B; auto. 
       apply minset_fact1 in B.
       rewrite B in A. exact A. 
Qed.

(* 
*) 
Lemma in_minset_left_congruence (X Y : finite_set S): X [=S] Y → ∀ (t : S), in_set rS ([ms] X) t = in_set rS ([ms] Y) t. 
Proof. intros A t.
       apply brel_set_elim in A. destruct A as [A B].
       assert(C := brel_subset_elim _ _ symS tranS _ _ A).
       assert(D := brel_subset_elim _ _ symS tranS _ _ B).       
       case_eq(in_set rS ([ms] X) t); intro J; 
       case_eq(in_set rS ([ms] Y) t); intro K; auto.  
          admit. 
          admit.           
Admitted. 

 *)

Lemma iterate_minset_subset (X : finite_set S) :
  ∀ (Y : finite_set S), ∀ (s : S), s [in] Y -> s [in] iterate_minset lteS Y X.
Proof. induction X.   
       intros Y s A.
       unfold iterate_minset; auto. 

       intros Y s A.
       unfold iterate_minset.
       case_eq(find (below lteS a) X).
          intros t B.
          fold (iterate_minset lteS Y X). 
          apply IHX; auto. 

          intros B.
          case_eq(find (below lteS a) Y).
             intros t C.
             fold (iterate_minset lteS Y X).
             apply IHX; auto.              

             intro C. fold (iterate_minset lteS (a :: Y) X). 
             apply IHX; auto.                           
             apply in_set_cons_intro; auto. 
Qed.


Lemma iterate_minset_cons_set_equality (X : finite_set S) :
  ∀ (Y : finite_set S) (s : S), is_antichain (s :: Y) -> (iterate_minset lteS (s :: Y) X) [=S] (s :: (iterate_minset lteS Y X)). 
Proof. induction X. 
       intro Y. unfold iterate_minset.
       intros s AC. apply set_reflexive. 
       intros Y s AC. unfold iterate_minset.
       case_eq(find (below lteS a) X).
          intros t A. 
          fold (iterate_minset lteS (s :: Y) X). 
          fold (iterate_minset lteS  Y X). 
          apply IHX; auto. 

          intro A.
          case_eq(find (below lteS a) (s :: Y)). 
             intros t B. 
             fold (iterate_minset lteS (s :: Y) X). 
             case_eq(find (below lteS a) Y).
                intros u C. 
                fold (iterate_minset lteS Y X). 
                apply IHX; auto. 
                intro C. 
                fold (iterate_minset lteS (a :: Y) X).
                destruct (find_below_some _ _ _ B) as [D E].
                apply in_set_cons_elim in D; auto. destruct D as [D | D].
                   destruct (find_below_some _ _ _ B) as [F G]. 
                   assert (H : s [in] (s :: Y)). apply in_set_cons_intro; auto.
                   assert (I := AC s H t F).
                   apply equiv_or_incomp_implies_not_below in I. 
                   destruct I as [I J].
                   assert (K := find_below_none _ _ C).
                   apply in_set_cons_elim in F; auto. destruct F as [F | F].
                      apply in_set_cons_elim in H; auto. destruct H as [H | H].
                         admit.  (* ??? something like K should be true of s, since AC! *) 
                         rewrite (below_congruence _ _ _ _ (refS a) (symS _ _ F)) in G. 
                         rewrite (K s H) in G. discriminate G. 
                      rewrite (K t F) in G. discriminate G. 
                   assert (F := find_below_none _ _ C).
                   rewrite (F t D) in E. discriminate E. 
             intros B.           
             fold (iterate_minset lteS (a :: s :: Y) X). 
             case_eq(find (below lteS a) Y).
                intros u C. 
                fold (iterate_minset lteS Y X).
                assert (D := find_below_none _ _ B). 
                destruct (find_below_some _ _ _ C) as [E F]. 
                assert (G : u [in] (s :: Y)). apply in_set_cons_intro; auto. 
                rewrite (D u G) in F. discriminate F. 
                intro C. 
                fold (iterate_minset lteS (a :: Y) X).
                assert (D : (a :: s :: Y) [=S] (s :: a :: Y)).
                   admit. 
                assert (E := brel_iterate_minset_congruence _ _ _ _ D (set_reflexive X)).
                assert (AC' : is_antichain (s :: a :: Y)).
                   intros t F u G.
                   assert (H := find_below_none _ _ B). 
                   assert (I := find_below_none _ _ C).
                   assert (T1 := in_set_left_congruence S rS symS tranS t _ _ D).
                   rewrite <- T1 in F. 
                   assert (T2 := in_set_left_congruence S rS symS tranS u _ _ D).
                   rewrite <- T2 in G.
                   apply in_set_cons_elim in F; auto. apply in_set_cons_elim in G; auto. 
                   destruct F as [F | F]; destruct G as [G | G].
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ G) (symS _ _ F)). 
                      apply equiv_or_incomp_reflexive. 

                      assert (J := H u G).
                      rewrite (below_congruence _ _ _ _ F (refS u)) in J. 
                      apply not_below_implies_equiv_or_incomp; auto.
                      case_eq(below lteS u t); intro K; auto. 
                      apply in_set_cons_elim in G; auto. destruct G as [G | G].
                         admit. 
                         assert (L := I u G). admit.  (* stuck !!! *) 
                      
                      admit. 

                      exact (AC t F u G). 
                assert (F := IHX (a :: Y) s AC').
                assert (G := set_transitive _ _ _ E F). 
                exact G. 
Admitted. 


Lemma in_set_iterate_minset_false_elim (X : finite_set S) :
  ∀ (Y : finite_set S),
    is_antichain Y ->
     (∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t) -> 
     (∀ (s : S), s [in] Y + s [in] X -> s [!in] iterate_minset lteS Y X ->
          {t : S & t [in] (iterate_minset lteS Y X) * (t << s)}).
Proof. induction X.
       intros U A A' s [B | B] C. 
          unfold iterate_minset in C. rewrite C in B. discriminate B. 
       compute in B. discriminate B.


       intros Y A A'.
       assert (A'' : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t). 
          intros s B t C.
          assert (D : s [in] (a :: X)). apply in_set_cons_intro; auto. 
          exact (A' s D t C). 
       intros s [B | B] C.
       assert (D := iterate_minset_subset X Y s B).
       unfold iterate_minset in C.              
       case_eq(find (below lteS a) X). 
          intros t E. rewrite E in C. 
          fold (iterate_minset lteS Y X) in C. 
          rewrite D in C. discriminate C. 
          intro E. rewrite E in C. 
          case_eq(find (below lteS a) Y).
             intros t F. rewrite F in C.
             fold (iterate_minset lteS Y X) in C.           
             rewrite D in C. discriminate C. 

             intros F. rewrite F in C.
             fold (iterate_minset lteS (a :: Y) X) in C.
             assert (G := in_iterate_minset_elim X Y A A'' s D).              
             exists a. split. 
                unfold iterate_minset. rewrite E. rewrite F. 
                fold (iterate_minset lteS (a :: Y) X).           
                apply iterate_minset_subset.
                apply in_set_cons_intro; auto.
                case_eq(below lteS s a); intro J; auto.
                assert (A''' : is_antichain (a :: Y)). admit.                 
                assert (K := iterate_minset_cons_set_equality X Y a A'''). admit. 
                rewrite (in_set_congruence S rS symS tranS _ _ _ _ A''' K (refS s)) in C. 
                unfold in_set in C. fold (in_set rS (iterate_minset lteS Y X) s) in C.
                rewrite D in C. compute in C. 
                case_eq(rS s a); intro L. 
                   rewrite L in C. discriminate C. 
                   rewrite L in C. discriminate C.                     
       apply in_set_cons_elim in B; auto.
       unfold iterate_minset in C. 
       case_eq(find (below lteS a) X). 
          intros t D. rewrite D in C. 
          fold (iterate_minset lteS Y X) in C. 
          destruct B as [B | B].
             case_eq(in_set rS (iterate_minset lteS Y (a :: X)) t); intro E.
                exists t. split; auto.
                   rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS t)).
                   destruct (find_below_some _ _ _ D) as [_ G]; auto. 
                unfold iterate_minset in E. rewrite D in E. 
                fold (iterate_minset lteS Y X) in E. 
                case_eq(in_set rS X t); intro F. 
                  destruct (IHX Y A A'' t (inr F) E) as [u [G H]]. 
                  exists u; split.
                     unfold iterate_minset.
                     rewrite D.                   
                     fold (iterate_minset lteS Y X); auto. 
                     destruct (find_below_some _ _ _ D) as [I J]. 
                     assert (K := below_transitive _ _ _ H J).
                     rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS u)); auto. 
                     apply find_below_some in D. destruct D as [D _].
                     rewrite D in F. discriminate F. 
             destruct (IHX Y A A'' s (inr B) C) as [u [E F]].
             exists u. split; auto. 
                unfold iterate_minset. rewrite D. 
                fold (iterate_minset lteS Y X); auto. 
          intros D. rewrite D in C.
          case_eq(find (below lteS a) Y). 
             intros u E. rewrite E in C. 
             fold (iterate_minset lteS Y X) in C. 
             destruct B as [B | B].
                exists u. split. 
                   unfold iterate_minset. rewrite D. rewrite E. 
                   fold (iterate_minset lteS Y X).
                   destruct (find_below_some Y _ _ E) as [F G]. 
                   apply iterate_minset_subset; auto.
                      
                   destruct (find_below_some Y _ _ E) as [F G]. 
                   rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS u)); auto.                   
                destruct (IHX Y A A'' s (inr B) C) as [v [F G]].
                exists v. split; auto. 
                unfold iterate_minset. rewrite D. rewrite E. 
                fold (iterate_minset lteS Y X); auto. 
                
             intro E. rewrite E in C. 
             fold (iterate_minset lteS (a :: Y) X) in C. 
             unfold iterate_minset. rewrite D. rewrite E. 
             fold (iterate_minset lteS (a :: Y) X).
             assert (F := find_below_none _  _ D).
             assert (G := find_below_none _  _ E).             
             destruct B as [B | B]. 
                assert (I : s [in] iterate_minset lteS (a :: Y) X).
                   assert (J : s [in] (a :: Y)). apply in_set_cons_intro; auto.
                   apply iterate_minset_subset; auto. 
                   rewrite I in C. discriminate C. 
                apply IHX; auto.
                   apply is_antichain_cons_intro; auto. 
                   intros t H. 
                   assert (I := G t H). 
                   assert (J : a !<< t). 
                      case_eq(below lteS t a); intro J; auto. 
                         assert (K : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                         assert (L := A' a K t H). 
                         rewrite L in J. discriminate J. 
                   apply not_below_implies_equiv_or_incomp; auto.
                   intros u H t I. 
                   apply in_set_cons_elim in I; auto.  destruct I as [I | I].
                      rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS u)). 
                      exact (F u H). 
                      exact (A'' u H t I). 
Defined.    
                                                                
Lemma in_set_minset_false_elim (X : finite_set S) :
      (∀ (s : S), s [in] X -> s [!in] ([ms] X) -> {t : S & t [in] ([ms] X) *  t << s}).
Proof. unfold uop_minset. 
       intros s A B.
       assert (C : ∀ s : S, s [in] X → ∀ t : S, t [in] nil → s !<< t).
          intros u C t D. compute in D. discriminate D. 
       exact (in_set_iterate_minset_false_elim X nil empty_set_is_antichain C s (inr A) B). 
Defined. 

       


(********** lemmas for brel_minset ***********) 

Lemma brel_minset_congruence : brel_congruence (finite_set S) (brel_minset rS lteS) (brel_minset rS lteS).
Admitted.

Lemma brel_minset_reflexive : brel_reflexive (finite_set S) (brel_minset rS lteS).
Proof. intro X.
       unfold brel_minset. 
       apply brel_set_reflexive; auto.
Qed.
  
Lemma brel_minset_symmetric : brel_symmetric (finite_set S) (brel_minset rS lteS).
Proof. intros X Y.
       unfold brel_minset. 
       apply brel_set_symmetric; auto.
Qed.


Lemma brel_minset_transitive : brel_transitive (finite_set S) (brel_minset rS lteS).
Proof. intros X Y Z. unfold brel_minset. 
       apply brel_set_transitive; auto.
Qed.


Definition brel_minset_new : unary_op (finite_set S)
  := λ X, if brel_set rS nil X then wS :: nil else nil.

Lemma brel_minset_nil_singleton (s : S) : brel_minset rS lteS nil (s :: nil) = false.
Proof. unfold brel_minset. unfold brel_reduce. rewrite uop_minset_nil. rewrite uop_minset_singleton. apply brel_set_nil_notnil. Qed. 

Lemma brel_minset_singleton_nil (s : S) : brel_minset rS lteS (s :: nil) nil = false.
Proof. apply (brel_symmetric_implies_dual _ _ brel_minset_symmetric nil (s :: nil) (brel_minset_nil_singleton s)). Qed.   


Lemma uop_minset_swap (a s : S) (X : finite_set S) : 
  (∀ a0 : S, in_set rS (uop_minset rS lteS (a :: s :: X)) a0 = true → in_set rS (uop_minset rS lteS (s :: a :: X)) a0 = true). 
Proof.  intros s0 H.
          apply in_set_minset_elim in H. destruct H as [H1 H2]. 
          apply in_set_minset_intro. split. 
             apply in_set_cons_intro; auto.
             apply in_set_cons_elim in H1; auto. 
             destruct H1 as [H1 | H1]. 
                right. apply in_set_cons_intro; auto.
                apply in_set_cons_elim in H1; auto. 
                destruct H1 as [H1 | H1]. 
                   left; auto.
                   right. apply in_set_cons_intro; auto.

             intros s1 H3.
             apply H2. 
             apply in_set_cons_elim in H3; auto.              
             apply in_set_cons_intro; auto.
             destruct H3 as [H3 | H3].
                right. apply in_set_cons_intro; auto.
                apply in_set_cons_elim in H3; auto.              
                destruct H3 as [H3 | H3].
                   left. auto. 
                   right. apply in_set_cons_intro; auto.
Qed.                    

Lemma brel_uop_minset_swap (a s : S) (X : finite_set S) : brel_set rS (uop_minset rS lteS (a :: s :: X)) (uop_minset rS lteS (s :: a :: X)) = true.
Proof. apply brel_set_intro_prop; auto. split.
       apply uop_minset_swap.
       apply uop_minset_swap.
Qed.        
          
Lemma brel_minset_cons_minimal (s : S) (X : finite_set S) :
  is_minimal_wrt rS lteS s X = true -> brel_set rS (uop_minset rS lteS (s :: X)) (uop_minset rS lteS (s :: (uop_minset rS lteS X))) = true.
Admitted.
(*
Proof. intro H.
       apply brel_set_intro_prop; auto. split; intros a aIn. 
          apply in_set_cons_intro; auto.        
          case_eq(rS s a); intro N; auto. 
             right.  apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal].
             apply in_set_cons_elim in aIn; auto. 
             destruct aIn as [E | aIn]. 
                rewrite E in N. discriminate N. 
                apply in_set_minset_intro. split; auto. 
                intros s0 s0In. 
                apply aMinimal.
                apply in_set_cons_intro; auto.

          apply in_set_minset_intro.        
          apply in_set_cons_elim in aIn; auto.           
          destruct aIn as [E | aIn]. 
             split. 
                apply in_set_cons_intro; auto. 
                intros s0 s0In. 
                apply in_set_cons_elim in s0In; auto.
                destruct s0In as [E' | s0In].
                   apply symS in E. left. exact (tranS _ _ _ E E').
                   assert (K := is_minimal_wrt_elim _ _ H s0 s0In). 
                   apply symS in E. rewrite (congS _ _ _ _ E (refS s0)).
                   rewrite (lteCong _ _ _ _ (refS s0) E). 
                   exact K. 

                split. 
                   apply in_set_cons_intro; auto. 
                   right. apply in_set_minset_elim in aIn. 
                   destruct aIn as [aIn _]; auto. 





                   intros s0 s0In. 
                   apply in_set_cons_elim in s0In; auto.
                   apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal].
                   destruct s0In as [E' | s0In].
                      apply symS in E'. rewrite (congS _ _ _ _ (refS a) E').
                      rewrite (lteCong _ _ _ _ E' (refS a)).                   
                      assert (K := is_minimal_wrt_elim _ _ H a aIn).
                      destruct K as [K | K].
                         left. apply symS; auto.
                         case_eq(rS a s); intro F1; case_eq(lteS s a); intro F2; auto.
                         admit.  (* OUCH *) 
                      apply (aMinimal s0 s0In). 
Admitted.
 *)

(* move *) 
Lemma set_is_empty (X : finite_set S) : (∀ s : S, in_set rS X s = false) -> X = nil.
Proof. induction X; intro H.
       reflexivity. 
       assert (K := H a). unfold in_set in K. rewrite refS in K. simpl in K. 
       discriminate K. 
Qed. 

Lemma brel_minset_drop_not_minimal (lteAntiSym : brel_antisymmetric S rS lteS) (s : S) (X : finite_set S) :
    is_minimal_wrt rS lteS s X = false -> brel_set rS (uop_minset rS lteS (s :: X)) (uop_minset rS lteS X) = true.
Proof. intro H. 
       apply brel_set_intro_prop; auto. split; intros a aIn. 
          apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal]. 
          apply in_set_minset_intro. split. 
             apply in_set_cons_elim in aIn; auto. destruct aIn as [E | aIn]; auto. 
                assert (aMinimal' : ∀ s0 : S, in_set rS X s0 = true → a =S s0 + s0 <<!= a). 
                   intros s0 s0In. apply aMinimal.
                   apply in_set_cons_intro; auto. 
                assert (K := is_minimal_wrt_fasle_elim s X H). 
                assert (J : ∀ s0 : S, in_set rS X s0 = false).
                   intro s0. case_eq(in_set rS X s0); intro J; auto. 
                   assert (J1 := aMinimal' s0 J).
                   assert (J2 := K s0 J).
                   destruct J2 as [L R].
                   rewrite (congS _ _ _ _ E (refS s0)) in L. rewrite (lteCong _ _ _ _ (refS s0) E) in R. 
                   rewrite L in J1. rewrite R in J1. destruct J1 as [F | F]; discriminate F. 
                   assert (L : X = nil). apply set_is_empty; auto. 
                rewrite L in H. compute in H. discriminate H. 
 
          intros s0 s0In. 
          apply aMinimal. 
          apply in_set_cons_intro; auto.

          apply in_set_minset_elim in aIn. destruct aIn as [aIn aMinimal]. 
          apply in_set_minset_intro. split. 
             apply in_set_cons_intro; auto. 
             intros s0 s0In. 
             apply in_set_cons_elim in s0In; auto.
             destruct s0In as [E | s0In].
                case_eq(rS a s0); intro F1; case_eq(lteS s0 a); intro F2; auto.
                assert (K := is_minimal_wrt_fasle_elim s X H). 
                assert (J := K a aIn). destruct J as [L R]. 
                apply symS in E. rewrite (lteCong _ _ _ _ E (refS a)) in F2.
                assert (E' := lteAntiSym _ _ F2 R). rewrite E' in L. discriminate L. 
                apply aMinimal; auto. 
Qed. 
          
Lemma tttt (s : S) (X : finite_set S) : brel_set rS nil (uop_minset rS lteS (s :: X)) = false.
Proof. induction X.
       rewrite uop_minset_singleton. compute; auto. 

       case_eq(brel_set rS nil (uop_minset rS lteS (s :: a :: X))); intro H; auto. 
       assert (K := brel_uop_minset_swap s a X).
       assert (J := brel_set_transitive S rS refS symS tranS _ _ _ H K).
          case_eq(is_minimal_wrt rS lteS a (s :: X)); intro F.
             assert (L := brel_minset_cons_minimal _ _ F).
             assert (M := brel_set_transitive S rS refS symS tranS _ _ _ J L).
             assert (N := brel_set_nil S rS _ M).
             admit.  (* OUCH discriminate N. *) 
(*
             assert (L := brel_minset_drop_not_minimal _ _ F).
             assert (M := brel_set_transitive S rS refS symS tranS _ _ _ J L).
             rewrite M in IHX. 
             exact IHX. 
*) 
Admitted. 
                                 
       
Lemma brel_minset_nil_notnil (s : S) (X : finite_set S) : brel_minset rS lteS nil (s :: X) = false.
Proof. unfold brel_minset. unfold brel_reduce. rewrite uop_minset_nil.
       assert (K : brel_set rS nil (s :: X) = false). apply brel_set_nil_notnil.
       apply tttt.
Qed.

Lemma brel_minset_notnil_nil (s : S) (X : finite_set S) : brel_minset rS lteS (s :: X) nil = false.
Proof. apply (brel_symmetric_implies_dual _ _ brel_minset_symmetric nil (s :: X) (brel_minset_nil_notnil s X)). Qed. 

Lemma brel_minset_not_trivial : brel_not_trivial (finite_set S) (brel_minset rS lteS) brel_minset_new.
Proof. unfold brel_not_trivial. intro X. 
       destruct X. 
       unfold brel_minset_new. rewrite brel_set_nil_nil. 
       rewrite brel_minset_nil_singleton. rewrite brel_minset_singleton_nil. auto. 
       unfold brel_minset_new. rewrite brel_set_nil_notnil.        
       rewrite brel_minset_nil_notnil. rewrite brel_minset_notnil_nil. auto. 
Qed. 


Lemma brel_minset_elim (X Y : finite_set S) : brel_minset rS lteS X Y = true ->
       (∀ (s : S),  (in_set rS (uop_minset rS lteS X) s = true) <-> (in_set rS (uop_minset rS lteS Y) s = true)). 
Proof. intro H. unfold brel_minset in H.  unfold brel_reduce in H. apply brel_set_elim_prop in H; auto.
       destruct H as [L R]. intro s. 
       assert (J := L s); assert (K := R s). split; auto. 
Qed. 

Lemma brel_minset_intro (X Y : finite_set S) : 
       (∀ (s : S),  (in_set rS (uop_minset rS lteS X) s = true) <-> (in_set rS (uop_minset rS lteS Y) s = true))
       -> brel_minset rS lteS X Y = true.
Proof. intro H. unfold brel_minset. unfold brel_reduce. 
       apply brel_set_intro_prop; auto; split; intros s J.
          destruct (H s) as [K _]. apply K; auto.
          destruct (H s) as [_ K]. apply K; auto.        
Qed. 


Lemma brel_minset_singleton_elim (a : S) (X : finite_set S) :
      brel_minset rS lteS (a :: nil) X = true -> (in_set rS X a = true) * (is_minimal_wrt rS lteS a X = true). 
Proof.  intro H. 
        destruct (brel_minset_elim _ _ H a) as [L R].
        assert (K : in_set rS (uop_minset rS lteS X) a = true).
           apply L. rewrite uop_minset_singleton. compute. rewrite refS; auto. 
        apply in_set_minset_elim in K.
        destruct K as [K1 K2]. split; auto.
        apply is_minimal_wrt_intro; auto. 
Qed.

Definition minset_negate ( X Y : finite_set S) :=
   match uop_minset rS lteS X, uop_minset rS lteS Y with 
   | nil, nil => wS :: nil
   | nil, t::_ => (fS t) :: nil 
   | t::_, nil => (fS t) :: nil      
   | t :: _, u :: _ => nil 
  end. 


Lemma brel_minset_negate_left (X Y : finite_set S) : brel_minset rS lteS X (minset_negate X Y) = false.
Proof. unfold brel_minset.
       unfold brel_reduce. 
       destruct X; destruct Y; unfold minset_negate; simpl.
          rewrite uop_minset_nil. rewrite uop_minset_singleton. apply brel_set_nil_notnil.
          rewrite uop_minset_nil.
             destruct (uop_minset rS lteS (s :: Y)).
                rewrite uop_minset_singleton. apply brel_set_nil_notnil.
                rewrite uop_minset_singleton. apply brel_set_nil_notnil.             
          destruct (uop_minset rS lteS (s :: X)).
             rewrite uop_minset_singleton. apply brel_set_nil_notnil.
             rewrite uop_minset_singleton. destruct f.
                compute. destruct (Pf s0) as [L R]. rewrite L. reflexivity. 
                unfold brel_set. unfold brel_and_sym. 
                apply andb_is_false_right. left. unfold brel_subset. fold (@brel_subset).
                apply andb_is_false_right. left. compute. destruct (Pf s0) as [L R]. rewrite L. reflexivity. 
          destruct (uop_minset rS lteS (s :: X)); destruct (uop_minset rS lteS (s0 :: Y)).
             rewrite uop_minset_singleton. apply brel_set_nil_notnil.
             rewrite uop_minset_singleton. apply brel_set_nil_notnil.
             rewrite uop_minset_singleton. destruct f.
                compute. destruct (Pf s1) as [L R]. rewrite L. reflexivity. 
                unfold brel_set. unfold brel_and_sym. 
                apply andb_is_false_right. left. unfold brel_subset. fold (@brel_subset).
                apply andb_is_false_right. left. compute. destruct (Pf s1) as [L R]. rewrite L. reflexivity. 
             rewrite uop_minset_nil. apply brel_set_notnil_nil. 
Qed.

Lemma brel_minset_negate_comm (X Y : finite_set S) : minset_negate X Y = minset_negate Y X.
Proof. destruct X; destruct Y; unfold minset_negate; simpl; auto.
       destruct(uop_minset rS lteS (s :: X)); destruct (uop_minset rS lteS (s0 :: Y)); auto. 
Qed.

Lemma brel_minset_negate_right (X Y : finite_set S) : brel_minset rS lteS Y (minset_negate X Y) = false.
Proof. rewrite brel_minset_negate_comm. apply brel_minset_negate_left. Qed. 

Lemma brel_minset_not_exactly_two : brel_not_exactly_two (finite_set S) (brel_minset rS lteS). 
Proof. unfold brel_not_exactly_two. exists minset_negate. 
       intros X Y. right. split.
       apply brel_minset_negate_left.
       apply brel_minset_negate_right.
Defined. 

Definition squash : list (finite_set S) -> list S
  := fix f l :=
       match l with
       | nil => nil
       | X :: rest => X ++ (f rest)
       end.


Lemma minset_lemma1 (s : S) :  brel_minset rS lteS nil (s :: nil) = false. 
Proof. unfold brel_minset. unfold brel_reduce.
       case_eq(brel_set rS (uop_minset rS lteS nil) (uop_minset rS lteS (s :: nil))); intro J; auto.
       apply brel_set_elim_prop in J; auto. destruct J as [L R].
       assert (K := R s). rewrite uop_minset_singleton  in K.
       assert (T : in_set rS (s :: nil) s = true). compute. rewrite refS; auto. 
       assert (J := K T).  compute in J. discriminate J. 
Qed. 

                                              
Lemma minset_lemma2 (s : S) (X : finite_set S) (H : brel_minset rS lteS X (s :: nil) = true) : in_set rS X s = true.
Proof. induction X. rewrite minset_lemma1 in H. discriminate H. 
       apply in_set_cons_intro; auto.
       apply brel_minset_symmetric in H; auto.
       apply brel_minset_singleton_elim in H. destruct H as [H _]. 
       apply in_set_cons_elim in H; auto. 
Qed. 

Lemma squash_lemma (s : S) (X : list (finite_set S)) (H : in_set (brel_minset rS lteS) X (s :: nil) = true) : in_set rS (squash X) s = true. 
Proof. induction X. compute in H. discriminate H.
       apply in_set_cons_elim in H.
       unfold squash; fold squash.
       apply in_set_concat_intro.
       destruct H as [H | H].       
          left. apply minset_lemma2; auto. 
          right. apply IHX; auto. 
       apply brel_minset_symmetric; auto.
Qed.        

Definition brel_minset_is_not_finite : carrier_is_not_finite S rS -> carrier_is_not_finite (finite_set S) (brel_minset rS lteS).
Proof. unfold carrier_is_not_finite.   
       intros H f.
       destruct (H (λ _, squash (f tt))) as [s Ps].
       exists (s :: nil). 
       case_eq(in_set (brel_minset rS lteS) (f tt) (s :: nil)); intro J; auto.
       apply squash_lemma in J. rewrite J in Ps. exact Ps. 
Defined.

Definition minset_enum (fS : unit -> list S) (x : unit) :=  List.map (uop_minset rS lteS) (power_set S (fS x)).

Lemma empty_set_in_minset_enum (f : unit -> list S) : in_set (brel_minset rS lteS) (minset_enum f tt) nil = true.
Admitted. 

Lemma min_set_enum_cons (f : unit -> list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (a : S) (X : finite_set S) : 
        in_set rS (f tt) a = true -> 
        in_set (brel_minset rS lteS) (minset_enum f tt) X = true -> 
        in_set (brel_minset rS lteS) (minset_enum f tt) (a :: X) = true. 
Admitted. 

Lemma minset_enum_lemma (f : unit → list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (X : finite_set S) : 
  in_set (brel_minset rS lteS) (minset_enum f tt) X = true.
Proof.  induction X. 
        apply empty_set_in_minset_enum. 
        assert (aIn := pf a). 
        apply min_set_enum_cons; auto. 
Qed. 

Definition brel_minset_is_finite : carrier_is_finite S rS -> carrier_is_finite (finite_set S) (brel_minset rS lteS).
Proof. unfold carrier_is_finite.   intros [f pf].
       exists (minset_enum f). intro X. 
       apply minset_enum_lemma; auto.
Defined. 

Definition brel_minset_finite_decidable (d : carrier_is_finite_decidable S rS) : carrier_is_finite_decidable (finite_set S) (brel_minset rS lteS)
  := match d with
     | inl fS  => inl (brel_minset_is_finite fS)
     | inr nfS => inr (brel_minset_is_not_finite nfS)                       
     end.

End Theory.



Section ACAS.

Definition eqv_proofs_brel_minset : ∀ (S : Type) (r : brel S) (lteS : brel S), eqv_proofs S r → eqv_proofs (finite_set S) (brel_minset lteS)
:= λ S r lteS eqv, 
   {| 
     A_eqv_congruence  := brel_minset_congruence S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) lteS
   ; A_eqv_reflexive   := brel_minset_reflexive S r  (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) lteS 
   ; A_eqv_transitive  := brel_minset_transitive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) lteS
   ; A_eqv_symmetric   := brel_minset_symmetric S r lteS
   |}.

Definition A_eqv_minset : ∀ (S : Type),  A_po S -> A_eqv (finite_set S) 
  := λ S poS,
  let eqvS  := A_po_eqv S poS in 
  let rS    := A_eqv_eq S eqvS in
  let wS    := A_eqv_witness S eqvS in
  let fS    := A_eqv_new S eqvS in
  let nt    := A_eqv_not_trivial S eqvS in
  let eqP   := A_eqv_proofs S eqvS in
  let congS := A_eqv_congruence S rS eqP in 
  let refS  := A_eqv_reflexive S rS eqP in  
  let symS  := A_eqv_symmetric S rS eqP in
  let trnS  := A_eqv_transitive S rS eqP in
  let lteS  := A_po_lte S poS in
  let lteP  := A_po_proofs S poS in 
  let lte_congS := A_po_congruence S rS lteS lteP in 
  let lte_refS  := A_po_reflexive S rS lteS lteP in  
(*  let lte_asymS := A_po_antisymmetric S rS lteS lteP in *) 
  let lte_trnS  := A_po_transitive S rS lteS lteP in  
   {| 
      A_eqv_eq            := brel_minset rS lteS 
    ; A_eqv_proofs        := eqv_proofs_brel_minset S rS lteS eqP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (* lte_asymS *) 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS lteS lte_refS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS lteS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS lteS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (* lte_asymS *) (A_eqv_finite_d S eqvS)
    ; A_eqv_ast           := Ast_eqv_minset (A_po_ast S poS)
   |}. 

End ACAS.


Section CAS.

Definition check_brel_minset_finite {S : Type} (rS : brel S) (lteS : brel S) (d : @check_is_finite S) : @check_is_finite (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Is_Finite (minset_enum S rS lteS fS) 
     | Certify_Is_Not_Finite => Certify_Is_Not_Finite 
     end.


Definition eqv_minset : ∀ {S : Type},  @po S -> @eqv (finite_set S)
:= λ {S} poS,
  let eqvS := po_eqv poS in  
  let rS   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in
  let fS   := eqv_new eqvS in  
  let lteS := po_lte poS in 
   {| 
      eqv_eq            := brel_minset rS lteS 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     |}  
    ; eqv_witness       := nil 
    ; eqv_new           := brel_minset_new S rS wS 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (minset_negate S rS wS fS lteS) 
    ; eqv_data          := λ l, DATA_list (List.map (eqv_data eqvS) (uop_minset rS lteS l))   
    ; eqv_rep           := λ l, List.map (eqv_rep eqvS) (uop_minset rS lteS l)
    ; eqv_finite_d      := check_brel_minset_finite rS lteS (eqv_finite_d eqvS)  
    ; eqv_ast           := Ast_eqv_minset (po_ast poS)
   |}. 
  
End CAS.

Section Verify.

Theorem correct_eqv_minset : ∀ (S : Type) (P : A_po S),  
    eqv_minset (A2C_po S P) = A2C_eqv (finite_set S) (A_eqv_minset S P).
Proof. intros S P. 
       unfold eqv_minset, A_eqv_minset, A2C_eqv; simpl. 
       destruct P; simpl.
       destruct A_po_proofs; destruct A_po_eqv; simpl.
       destruct A_eqv_finite_d as [ [fS FS] | NFS ]; simpl; auto. 
Qed.        
  
 
End Verify.   
 