Require Import Coq.Lists.List.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce. 
Require Import CAS.coq.sg.union. 

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





(** *******************  uop_minset ********************* **)

Definition is_antichain (X : finite_set S) :=   ∀ (s : S), s [in] X  -> ∀ (t : S), t [in] X  -> (s [~|#] t).


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

Lemma iterate_minset_subset_v2 (X : finite_set S) :
  ∀ (Y : finite_set S), brel_subset rS Y (iterate_minset lteS Y X) = true. 
Proof. intro Y. apply brel_subset_intro; auto.  apply iterate_minset_subset. Qed. 

Lemma in_set_iterate_minset_false_elim (X : finite_set S) :
  ∀ (Y : finite_set S),
    is_antichain Y ->
     (∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t) -> 
     (∀ (s : S), s [in] X -> s [!in] iterate_minset lteS Y X -> {t : S & t [in] (iterate_minset lteS Y X) * (t << s)}).
Proof. induction X.
       intros U A A' s B. compute in B. discriminate B.
       intros Y A A' s B C.
       assert (A'' : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t). 
          intros u D t E.
          assert (F : u [in] (a :: X)). apply in_set_cons_intro; auto. 
          exact (A' u F t E). 
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
                  destruct (IHX Y A A'' t F E) as [u [G H]]. 
                  exists u; split.
                     unfold iterate_minset.
                     rewrite D.                   
                     fold (iterate_minset lteS Y X); auto. 
                     destruct (find_below_some _ _ _ D) as [I J]. 
                     assert (K := below_transitive _ _ _ H J).
                     rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS u)); auto. 
                     apply find_below_some in D. destruct D as [D _].
                     rewrite D in F. discriminate F. 
             destruct (IHX Y A A'' s B C) as [u [E F]].
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
                destruct (IHX Y A A'' s B C) as [v [F G]].
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
       exact (in_set_iterate_minset_false_elim X nil empty_set_is_antichain C s A B). 
Defined. 

       


(********** lemmas for brel_minset ***********)

Lemma set_not_below_congruence (X1 X2 : finite_set S) (s : S): 
  X1 [=S] X2 -> (∀ t : S, t [in] X1 → t !<< s) -> ∀ t : S, t [in] X2 → t !<< s .
intros A B t C. apply set_symmetric in A. 
      rewrite (in_set_left_congruence S rS symS tranS t _ _ A) in C. exact (B t C).
Qed.

Lemma in_minset_left_congruence (X1 X2 : finite_set S) : 
  X1 [=S] X2 -> ∀ s : S, s [in] ([ms] X1) -> s [in] ([ms] X2). 
Proof. intros A s B.
       apply in_minset_elim in B.  destruct B as [B C].
       apply in_minset_intro. split. 
         rewrite (in_set_left_congruence S rS symS tranS s _ _ A) in B; auto. 
         exact (set_not_below_congruence _ _ s A C). 
Qed.

Lemma brel_uop_minset_congruence : uop_congruence (finite_set S) (brel_set rS) (uop_minset lteS).
Proof. unfold uop_congruence.
       intros X1 X2 A.
       apply brel_set_intro_prop; auto. split.
       apply in_minset_left_congruence; auto.           
       apply brel_set_symmetric in A.
       apply in_minset_left_congruence; auto.    
Qed. 

Lemma brel_minset_congruence_weak : brel_congruence (finite_set S) (brel_set rS) (brel_minset rS lteS).
Proof. unfold brel_congruence.
       intros X1 Y1 X2 Y2 A B. 
       unfold brel_minset.
       assert (C := brel_uop_minset_congruence X1 X2 A).
       assert (D := brel_uop_minset_congruence Y1 Y2 B).        
       exact (set_congruence _ _ _ _ C D). 
Qed.


(* move to sg/union.v *)

Lemma bop_union_subset_left  : ∀ (X Y: finite_set S), brel_subset rS X (bop_union rS X Y) = true.
Proof. intros X Y.
       apply brel_subset_intro; auto. 
       intros s A.        
       apply in_set_bop_union_intro; auto. 
Qed. 

Lemma bop_union_subset_right  : ∀ (X Y: finite_set S), brel_subset rS Y (bop_union rS X Y) = true.
Proof. intros X Y.
       apply brel_subset_intro; auto. 
       intros s A.        
       apply in_set_bop_union_intro; auto. 
Qed. 


Lemma bop_union_nil_v2 : ∀ (X : finite_set S), brel_set rS (bop_union rS X nil) X = true. 
Proof. intro X.
       assert (A := bop_union_commutative _ _ refS symS tranS X nil).
       assert (B := bop_union_nil _ _ refS symS tranS X).
       exact (set_transitive _ _ _ A B). 
Qed. 

Lemma bop_union_shift : ∀ (X Y : finite_set S) (a : S), bop_union rS X (a :: Y) [=S] bop_union rS (a :: X) Y. 
Proof. intros X Y a. 
       apply brel_set_intro; auto. split. 
       apply brel_subset_intro; auto. 
       intros s A.
       apply in_set_bop_union_intro; auto. 
       apply in_set_bop_union_elim in A; auto. 
       destruct A as [A | A].       
         left. apply in_set_cons_intro; auto. 
         apply in_set_cons_elim in A; auto. 
         destruct A as [A | A]. 
            left. apply in_set_cons_intro; auto.
            right; auto.
       apply brel_subset_intro; auto. 
       intros s A.
       apply in_set_bop_union_intro; auto. 
       apply in_set_bop_union_elim in A; auto. 
       destruct A as [A | A].       
          apply in_set_cons_elim in A; auto.
          destruct A as [A | A].
            right. apply in_set_cons_intro; auto.
            left; auto.           
         right. apply in_set_cons_intro; auto.
Qed.             
         
Lemma find_below_is_none_in_antichain (Y : finite_set S) : 
    is_antichain Y ->  ∀ (s : S),  s [in] Y -> ∀ (X : finite_set S), brel_subset rS X Y = true -> find (below lteS s) X = None.
Proof. intros A s B X C. 
       case_eq(find (below lteS s) X); auto. 
       intros t D.
       destruct (find_below_some X _ _ D) as [E F]. 
       assert (G := brel_subset_elim _ _ symS tranS _ _ C _ E).
       assert (H := A _ B _ G).
       apply equiv_or_incomp_implies_not_below in H. destruct H as [H1 H2].
       rewrite H2 in F. discriminate F. 
Qed.

Lemma is_antichain_congruence (X Y: finite_set S) : X [=S] Y -> is_antichain X -> is_antichain Y. 
Proof. intros A B. 
       apply  brel_set_elim_prop in A; auto.  destruct A as [L R].
       intros s C t D. 
       exact (B _ (R _ C) _ (R _ D)).
Qed.


Lemma iterate_minset_on_anichain (X: finite_set S):
  ∀ (Y : finite_set S), is_antichain (bop_union rS X Y) -> (iterate_minset lteS Y X) [=S] (bop_union rS X Y).
Proof. induction X.
       intros Y A. unfold iterate_minset.
       assert (B := bop_union_nil _ _ refS symS tranS Y).
       apply set_symmetric; auto. 

       intros Y A.
       assert (B : a [in] bop_union rS (a :: X) Y).
          apply in_set_bop_union_intro; auto.
          left. apply in_set_cons_intro; auto. 
       assert (C : find (below lteS a) X = None).
          assert (D : brel_subset rS X (bop_union rS (a :: X) Y) = true).
             assert (E : brel_subset rS X (a :: X) = true). 
                apply brel_subset_intro; auto. intros s C.
                apply in_set_cons_intro; auto.                                                        
             assert (F := bop_union_subset_left (a :: X) Y). 
             exact(brel_subset_transitive _ _ refS symS tranS _ _ _ E F). 
          exact (find_below_is_none_in_antichain _ A a B _ D).
       assert (D : find (below lteS a) Y = None).
          assert (D : brel_subset rS Y (bop_union rS (a :: X) Y) = true).
             apply bop_union_subset_right. 
          exact (find_below_is_none_in_antichain _ A a B _ D).
       unfold iterate_minset. rewrite C. rewrite D.
       fold (iterate_minset lteS (a :: Y) X). 
       assert (E : is_antichain (bop_union rS X ( a :: Y))).
          assert (E : (bop_union rS (a :: X) Y) [=S] (bop_union rS X ( a :: Y))).
             apply set_symmetric. 
             apply bop_union_shift. 
          exact (is_antichain_congruence _ _ E A). 
       assert (F := IHX (a :: Y) E). 
       assert (G : bop_union rS X (a :: Y) [=S] bop_union rS (a :: X) Y).
          apply bop_union_shift. 
       exact (set_transitive _ _ _ F G). 
Qed. 



Lemma uop_minset_on_antichain (X : finite_set S):   is_antichain X -> ([ms] X) [=S] X.
Proof. intro A. unfold uop_minset. 
       assert (B : is_antichain (bop_union rS X nil)).
          assert (C : X [=S] (bop_union rS X nil)). 
             apply set_symmetric. apply bop_union_nil_v2.  
          exact (is_antichain_congruence _ _ C A). 
       assert (C := iterate_minset_on_anichain X nil B).
       assert (D : bop_union rS X nil [=S] X). apply bop_union_nil_v2.  
       exact (set_transitive _ _ _ C D). 
Qed. 


Lemma uop_minset_idempotent (X : finite_set S):   ([ms] ([ms] X)) [=S] ([ms] X).
Proof.  assert (A := uop_minset_is_antichain X).
        exact (uop_minset_on_antichain ([ms] X) A). 
Qed. 

Lemma brel_minset_congruence : brel_congruence (finite_set S) (brel_minset rS lteS) (brel_minset rS lteS).
Proof. unfold brel_congruence.
       intros X1 Y1 X2 Y2 A B. 
       unfold brel_minset in A, B.
       assert (C := brel_minset_congruence_weak _ _ _ _ A B). 
       unfold brel_minset in C.
       assert (D := set_congruence _ _ _ _ (uop_minset_idempotent X1) (uop_minset_idempotent Y1)).
       assert (E := set_congruence _ _ _ _ (uop_minset_idempotent X2) (uop_minset_idempotent Y2)).        
       rewrite D in C. rewrite E in C. unfold brel_minset. exact C. 
Qed. 



Lemma brel_minset_reflexive : brel_reflexive (finite_set S) (brel_minset rS lteS).
Proof. intro X. unfold brel_minset. apply brel_set_reflexive; auto. Qed.
  
Lemma brel_minset_symmetric : brel_symmetric (finite_set S) (brel_minset rS lteS).
Proof. intros X Y. unfold brel_minset. apply brel_set_symmetric; auto. Qed.


Lemma brel_minset_transitive : brel_transitive (finite_set S) (brel_minset rS lteS).
Proof. intros X Y Z. unfold brel_minset. apply brel_set_transitive; auto.  Qed.


Definition brel_minset_new : unary_op (finite_set S)
  := λ X, if brel_set rS nil X then wS :: nil else nil.

Lemma brel_set_nil_singleton (s : S) (X : finite_set S) : nil [<>S] (s :: X). 
Proof. compute; auto. Qed. 

Lemma iterate_minset_singleton (Y : finite_set S) (s : S) :
    (find (below lteS s) Y = None -> iterate_minset lteS Y (s :: nil) = (s :: Y)) *
    (∀ t : S,  find (below lteS s) Y = Some t -> iterate_minset lteS Y (s :: nil) = Y). 
Proof. assert (B : find (below lteS s) nil = None). compute; auto.
       split.
       intro A. unfold iterate_minset.
       rewrite B. rewrite A. reflexivity. 
       intros t A. unfold iterate_minset.
       rewrite B. rewrite A. reflexivity. 
Qed. 

Lemma brel_minset_nil_singleton (X : finite_set S) : ∀ (s : S), nil [<>MS] (s :: X).
  Proof. unfold brel_minset. rewrite minset_empty. unfold uop_minset. 
         induction X.          
            intro s. unfold iterate_minset.
            assert (A : find (below lteS s) nil = None). compute; auto. 
            rewrite A. compute; auto. 
            intro s. unfold iterate_minset.            
            case_eq(find (below lteS s) (a :: X)).
               intros t A. 
               case_eq(find (below lteS a) X).
                  intros u B. 
                  fold(iterate_minset lteS nil X). 
                  assert (C := IHX a).                
                  unfold iterate_minset in C. rewrite B in C. 
                  fold(iterate_minset lteS nil X) in C; auto. 
                  intros B.
                  assert (C : find (below lteS a) nil = None). compute; auto. rewrite C. 
                  fold(iterate_minset lteS (a :: nil) X). 
                  case_eq(brel_set rS nil (iterate_minset lteS (a :: nil) X)); intro D; auto. 
                    assert (E : brel_subset rS (a :: nil) (iterate_minset lteS  (a :: nil) X) = true).
                      apply iterate_minset_subset_v2.
                  apply brel_set_elim in D; auto. destruct D as [_ D].
                  assert (F := brel_subset_transitive _ rS refS symS tranS _ _ _ E D). 
                  compute in F. discriminate F. 


               intros A.
               assert (C : find (below lteS s) nil = None). compute; auto. rewrite C.                   
               case_eq(find (below lteS a) X).
                  intros u B. 
                  fold(iterate_minset lteS (s :: nil) X). 
                  case_eq(brel_set rS nil (iterate_minset lteS (s :: nil) X)); intro D; auto. 
                    assert (E : brel_subset rS (s :: nil) (iterate_minset lteS  (s :: nil) X) = true).
                      apply iterate_minset_subset_v2.
                    apply brel_set_elim in D; auto. destruct D as [_ D].
                    assert (F := brel_subset_transitive _ rS refS symS tranS _ _ _ E D). 
                    compute in F. discriminate F. 


                  intro B. 
                  case_eq(find (below lteS a) (s :: nil)).
                  intros w D. 
                  fold(iterate_minset lteS (s :: nil) X).                   
                  case_eq(brel_set rS nil (iterate_minset lteS (s :: nil) X)); intro E; auto. 
                    assert (F : brel_subset rS (s :: nil) (iterate_minset lteS  (s :: nil) X) = true).
                      apply iterate_minset_subset_v2.
                    apply brel_set_elim in E; auto. destruct E as [_ E].
                    assert (G := brel_subset_transitive _ rS refS symS tranS _ _ _ F E). 
                    compute in G. discriminate G. 


                  intros D. 
                  fold(iterate_minset lteS (a :: s :: nil) X).                   
                  case_eq(brel_set rS nil (iterate_minset lteS (a :: s :: nil) X)); intro E; auto. 
                    assert (F : brel_subset rS (a :: s :: nil) (iterate_minset lteS  (a :: s :: nil) X) = true).
                      apply iterate_minset_subset_v2.
                    apply brel_set_elim in E; auto. destruct E as [_ E].
                    assert (G := brel_subset_transitive _ rS refS symS tranS _ _ _ F E). 
                    compute in G. discriminate G. 
Qed.                   
                  
Lemma brel_minset_singleton_nil (s : S) (X : finite_set S): (s :: X) [<>MS] nil.
 Proof. case_eq(brel_minset rS lteS (s :: X) nil); intro A; auto. 
       apply brel_minset_symmetric in A.
       rewrite brel_minset_nil_singleton in A.       discriminate A. 
Qed.

Lemma brel_minset_not_trivial : brel_not_trivial (finite_set S) (brel_minset rS lteS) brel_minset_new.
Proof. unfold brel_not_trivial. intro X. 
       destruct X. 
       unfold brel_minset_new. rewrite (set_reflexive nil). split; compute; auto. 
       unfold brel_minset_new. rewrite brel_set_nil_singleton.
       rewrite brel_minset_nil_singleton. rewrite brel_minset_singleton_nil; auto.  
Qed. 


Definition minset_negate ( X Y : finite_set S) :=
   match uop_minset lteS X, uop_minset lteS Y with 
   | nil, nil => wS :: nil
   | nil, t::_ => (fS t) :: nil 
   | t::_, nil => (fS t) :: nil      
   | t :: _, u :: _ => nil 
  end. 




Lemma brel_minset_negate_left (X Y : finite_set S) : brel_minset rS lteS X (minset_negate X Y) = false.
Proof. destruct X; destruct Y.
       compute; auto. 
       unfold minset_negate. rewrite minset_empty.
       case_eq([ms] (s :: Y)).
          intro A. apply brel_minset_nil_singleton.  
          intros t Z A. apply brel_minset_nil_singleton.  
       unfold minset_negate. rewrite minset_empty.       
       case_eq([ms] (s :: X)).
          intro A. unfold brel_minset.  rewrite minset_singleton. 
          case_eq(brel_set rS ([ms] (s :: X)) (wS :: nil)); intro B; auto. 
             rewrite A in B. compute in B. discriminate B. 
          intros t Z A.  unfold brel_minset.  rewrite minset_singleton. 
          case_eq(brel_set rS ([ms] (s :: X)) (fS t :: nil)); intro B; auto. 
             rewrite A in B. apply set_symmetric in B. 
             apply brel_set_elim in B; auto. destruct B as [_ B].
             assert (C := brel_subset_elim _ _ symS tranS _ _ B). 
             assert (D : t [in] (t :: Z)). apply in_set_cons_intro; auto. 
             assert (E := C _ D). compute in E.
             destruct (Pf t) as [F G].  
             rewrite F in E. discriminate E. 
       unfold minset_negate.
       case_eq([ms] (s :: X)).
          intro A.
          assert (B : nil [=MS] (s :: X)).
             unfold brel_minset. rewrite A. compute; auto. 
          rewrite brel_minset_nil_singleton  in B. discriminate B. 
          intros t Z A. 
          case_eq([ms] (s0 :: Y)). 
             intro B. unfold brel_minset. 
             rewrite A.
             case_eq(brel_set rS (t :: Z) ([ms] (fS t :: nil))); intro C; auto. 
                apply brel_set_elim in C; auto. destruct C as [C _].
                assert (D := brel_subset_elim _ _ symS tranS _ _ C). 
                assert (E : t [in] (t :: Z)). apply in_set_cons_intro; auto. 
                assert (F := D _ E). compute in F.
                destruct (Pf t) as [G H].  
               rewrite G in F. discriminate F. 
             intros u W B.
             apply brel_minset_singleton_nil.
Qed. 

Lemma brel_minset_negate_comm (X Y : finite_set S) : minset_negate X Y = minset_negate Y X.
Proof. destruct X; destruct Y; unfold minset_negate; simpl; auto.
       destruct(uop_minset lteS (s :: X)); destruct (uop_minset lteS (s0 :: Y)); auto. 
Qed.

Lemma brel_minset_negate_right (X Y : finite_set S) : brel_minset rS lteS Y (minset_negate X Y) = false.
Proof. rewrite brel_minset_negate_comm. apply brel_minset_negate_left. Qed. 


Lemma brel_minset_not_exactly_two : brel_not_exactly_two (finite_set S) (brel_minset rS lteS). 
Proof. unfold brel_not_exactly_two. exists minset_negate. 
       intros X Y. right. split.
       apply brel_minset_negate_left.
       apply brel_minset_negate_right.
Defined. 




Definition minset_enum (enum : unit -> list S) (x : unit) :=  List.map (uop_minset lteS) (power_set S (enum x)).

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


Definition squash : list (finite_set S) -> list S
  := fix f l :=
       match l with
       | nil => nil
       | X :: rest => X ++ (f rest)
       end.

Lemma brel_minset_singleton_elim (X : finite_set S) (s : S) : X [=MS] (s :: nil) → s [in] X. 
Proof. intro A.
       unfold brel_minset in A. 
       rewrite minset_singleton in A. 
       apply brel_set_elim in A; auto. destruct A as [_ A].
       assert (B := brel_subset_elim _ _ symS tranS _ _ A).
       assert (C : s [in] (s :: nil)). compute. rewrite refS; auto. 
       assert (D := B _ C).
       apply in_minset_elim in D. destruct D as [D _]; auto. 
Qed.


Lemma squash_lemma (s : S) (X : list (finite_set S)) (H : in_set (brel_minset rS lteS) X (s :: nil) = true) : in_set rS (squash X) s = true. 
Proof. induction X. compute in H. discriminate H.
       apply in_set_cons_elim in H.
       unfold squash; fold squash.
       apply in_set_concat_intro.
       destruct H as [H | H].       
          left. apply brel_minset_singleton_elim; auto. 
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

Definition brel_minset_finite_decidable (d : carrier_is_finite_decidable S rS) : carrier_is_finite_decidable (finite_set S) (brel_minset rS lteS)
  := match d with
     | inl fS  => inl (brel_minset_is_finite fS)
     | inr nfS => inr (brel_minset_is_not_finite nfS)                       
     end.

End Theory.



Section ACAS.



Definition eqv_proofs_brel_minset :
 ∀ (S : Type) (r : brel S) (lteS : brel S), eqv_proofs S r → po_proofs S r lteS → eqv_proofs (finite_set S) (brel_minset r lteS)
:= λ S r lteS eqv lteP,
  let refS := A_eqv_reflexive S r eqv in
  let symS := A_eqv_symmetric S r eqv in
  let trnS := A_eqv_transitive S r eqv in
  let lteCong := A_po_congruence _ _ _ lteP in
  let lteRefl := A_po_reflexive _ _ _ lteP in
  let lteTrns := A_po_transitive _ _ _ lteP in     
   {| 
     A_eqv_congruence  := brel_minset_congruence S r refS symS trnS lteS lteCong lteRefl lteTrns
   ; A_eqv_reflexive   := brel_minset_reflexive S r  refS symS lteS
   ; A_eqv_transitive  := brel_minset_transitive S r refS symS trnS lteS
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
    ; A_eqv_proofs        := eqv_proofs_brel_minset S rS lteS eqP lteP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS refS symS trnS lteS 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS symS trnS lteS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast           := Ast_eqv_minset (A_po_ast S poS)
   |}. 

End ACAS.

Section CAS.

Definition check_brel_minset_finite {S : Type} (lteS : brel S) (d : @check_is_finite S) : @check_is_finite (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Is_Finite (minset_enum S lteS fS) 
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
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (minset_negate S wS fS lteS) 
    ; eqv_data          := λ l, DATA_list (List.map (eqv_data eqvS) (uop_minset rS l))   
    ; eqv_rep           := λ l, List.map (eqv_rep eqvS) (uop_minset rS  l)
    ; eqv_finite_d      := check_brel_minset_finite lteS (eqv_finite_d eqvS)  
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
 