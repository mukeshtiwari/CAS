Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.

Section Compute.

Definition below {S : Type} (lte : brel S) : brel S
    := λ a y, bop_and (lte y a) (uop_not(lte a y)).
  
Definition equiv {S : Type} (lte : brel S) : brel S
  := λ a b, bop_and (lte a b) (lte b a).

Definition incomp {S : Type} (lte : brel S) : brel S
  := λ a b, bop_and (uop_not(lte a b)) (uop_not (lte b a)).

Definition equiv_or_incomp {S : Type} (lte : brel S) : brel S
  := λ a b, bop_or (equiv lte a b) (incomp lte a b). 

End Compute.  

Section Theory.

Variable S        : Type.
Variable eq       : brel S.
Variable lte     : brel S. 
Variable lteCong  : brel_congruence S eq lte.
Variable lteRefl  : brel_reflexive S lte.
Variable lteTrans : brel_transitive S lte. 

Notation "a <<= b"  := (lte a b = true)        (at level 15).
Notation "a !<<= b" := (lte a b = false)       (at level 15).
Notation "a << b"   := (below lte b a = true) (at level 15).
Notation "a !<< b"  := (below lte b a = false) (at level 15).
Notation "a [~] b"   := (equiv lte b a = true) (at level 15).
Notation "a [!~] b"   := (equiv lte b a = false) (at level 15).
Notation "a [#] b"   := (incomp lte b a = true) (at level 15).
Notation "a [!#] b"   := (incomp lte b a = false) (at level 15).
Notation "a [~|#] b"   := (equiv_or_incomp lte b a = true) (at level 15).
Notation "a [!~|#] b"   := (equiv_or_incomp lte b a = false) (at level 15).


(************** intro and elim ******************)
(**************** below *************************) 

Lemma below_intro (a b : S) : b <<= a  -> a !<<= b -> b << a. 
Proof. intros A B. unfold below. rewrite A, B. compute. auto. Qed. 

Lemma below_elim (a b : S) : b << a -> (b <<= a) * (a !<<= b). 
Proof. intros A. unfold below in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma below_false_intro (a b : S) : (b !<<= a  + a <<= b) -> b !<< a. 
Proof. unfold below. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lte b a); intro B; auto. 
Qed. 

Lemma below_false_elim (a b : S) : b !<< a -> (b !<<= a  + a <<= b). 
Proof. intros A. unfold below in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.

(**************** equiv *************************) 

Lemma equiv_intro (a b : S) : b <<= a  -> a <<= b -> b [~] a. 
Proof. intros A B. unfold equiv. rewrite A, B. compute. auto. Qed. 

Lemma equiv_elim (a b : S) : b [~] a -> (b <<= a) * (a <<= b). 
Proof. intros A. unfold equiv in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma equiv_false_intro (a b : S) : (b !<<= a  + a !<<= b) -> b [!~] a. 
Proof. unfold equiv. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lte a b); intro B; auto. 
Qed. 

Lemma equiv_false_elim (a b : S) : b [!~] a -> (b !<<= a  + a !<<= b). 
Proof. intros A. unfold equiv in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.

(**************** incomp *************************) 

Lemma incomp_intro (a b : S) : b !<<= a  -> a !<<= b -> b [#] a. 
Proof. intros A B. unfold incomp. rewrite A, B. compute. auto. Qed. 

Lemma incomp_elim (a b : S) : b [#] a -> (b !<<= a) * (a !<<= b). 
Proof. intros A. unfold incomp in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma incomp_false_intro (a b : S) : (b <<= a  + a <<= b) -> b [!#] a. 
Proof. unfold incomp. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lte a b); intro B; auto. 
Qed. 

Lemma incomp_false_elim (a b : S) : b [!#] a -> (b <<= a  + a <<= b). 
Proof. intros A. unfold incomp in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.



(**************** equiv_or_incomp *************************) 
Lemma equiv_or_incomp_intro (a b : S) : (a [~] b) + (a [#] b) -> a [~|#] b.
Proof. unfold equiv_or_incomp. intros [A | A].
       rewrite A ; compute; auto.
       compute in A.  compute. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.
          rewrite B in A. discriminate A.
          rewrite B in A. rewrite C in A. discriminate A.        
Qed. 

Lemma equiv_or_incomp_elim (a b : S) : a [~|#] b -> (a [~] b) + (a [#] b).
Proof. intros A. compute in A. compute. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. discriminate A.
       rewrite B, C in A. discriminate A.
Qed.

Lemma equiv_or_incomp_false_intro (a b : S) :  (a [!~] b) * (a [!#] b) -> a [!~|#] b. 
Proof. unfold equiv_or_incomp. intros [A  B]. rewrite A, B. compute; auto. Qed. 

Lemma equiv_or_incomp_false_elim (a b : S) : a [!~|#] b -> (a [!~] b) * (a [!#] b).
Proof. intros A. compute in A. compute. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
          rewrite B, C in A. discriminate A.
          rewrite B, C in A. discriminate A.       
Qed.

(************** brel properties *****************)
(**************** below *************************) 

Lemma below_congruence : brel_congruence S eq (below lte). 
Proof. intros a b c d A B.
       unfold below. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma below_not_reflexive (a : S ) : a !<< a.
Proof. compute. rewrite lteRefl. rewrite lteRefl. reflexivity. Qed.

Lemma below_anti_symmetric (a b : S ) : a << b -> b !<< a.
Proof. compute. case_eq(lte a b); intro A; case_eq(lte b a); intro B; auto. Qed. 

Lemma below_transitive (a s t : S ) : t << a -> a << s -> t << s. 
Proof. intros A B. apply below_elim in A. apply below_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       apply below_intro.
          exact (lteTrans _ _ _ A B). 
          case_eq(lte s t); intro E; auto. 
             assert (F := lteTrans _ _ _ B E). 
             rewrite F in C. discriminate C.
Qed. 

(**************** equiv *************************) 

Lemma equiv_congruence : brel_congruence S eq (equiv lte). 
Proof. intros a b c d A B.
       unfold equiv. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma equiv_reflexive : brel_reflexive S (equiv lte).
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
Lemma incomp_congruence : brel_congruence S eq (incomp lte). 
Proof. intros a b c d A B.
       unfold incomp. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
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
       case_eq(lte s t); intro E; case_eq(lte t s); intro F; auto.
Qed. 


(**************** equiv_or_incomp *************************) 
Lemma equiv_or_incomp_congruence : brel_congruence S eq (equiv_or_incomp lte). 
Proof. intros a b c d A B.
       unfold equiv_or_incomp. 
       rewrite (equiv_congruence _ _ _ _ A B). 
       rewrite (incomp_congruence _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma equiv_or_incomp_reflexive : brel_reflexive S (equiv_or_incomp lte).
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
          case_eq(lte t s); intro C; auto.
             destruct A as [_ A]. 
             rewrite (lteTrans _ _ _  A C) in B. destruct B as [B _].
             discriminate B.
             apply incomp_intro; auto. 
                (* s !<<= a -> a <<=t -> s !<<= t       extract *) 
                case_eq(lte s t); intro D; auto. 
                   destruct A as [A _]. destruct B as [_ B].                               
                   rewrite (lteTrans _ _ _ D A) in B.
                   discriminate B.

          (* t [#] a -> a [~] s -> t [#] s     extract as lemma *)
          left. left. apply equiv_or_incomp_intro.                             
          right. 
          apply incomp_elim in A. apply equiv_elim in B.
          case_eq(lte t s); intro C; auto.
             destruct B as [_ B]. 
             rewrite (lteTrans _ _ _  C B) in A. destruct A as [A _].
             discriminate A.
             apply incomp_intro; auto.
             destruct A as [_ A]. destruct B as [B _].                               
                (* t !<<= s -> a <<= s -> s !<<= t       extract *) 
                case_eq(lte s t); intro D; auto. 
                   rewrite (lteTrans _ _ _ B D) in A.
                   discriminate A.

          assert (C := incomp_pseudo_transitive _ _ _ A B).
          destruct C as [[[C | C] | C] | C]; auto.
          left. left. apply equiv_or_incomp_intro. right; auto.
          left. left. apply equiv_or_incomp_intro. left; auto.          
Qed. 


Lemma equiv_implies_not_below (a s : S) : (a [~] s) -> a !<< s * s !<< a.
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed. 

Lemma incomp_implies_not_below (a s : S) : (a [#] s) -> a !<< s * s !<< a.   
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed.

Lemma equiv_or_incomp_implies_not_below (a s : S) : (a [~|#] s) -> a !<< s * s !<< a. 
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed.

Lemma not_below_implies_equiv_or_incomp (a s : S) : a !<< s -> (s !<< a) -> (a [~|#] s). 
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed.


Lemma below_equiv_pseudo_congruence :
  ∀ a b c d : S, a [~] c → b [~] d → (below lte a b = below lte c d) + ((a << b) *  (d << c)) + ((b << a) * (c << d)). 
Proof. intros a b c d A B.
       apply equiv_elim in A. apply equiv_elim in B.
       destruct A as [A1 A2]. destruct B as [B1 B2].
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D;
       case_eq(lte b a); intro E; case_eq(lte a b); intro F; auto.
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
  ∀ a b c  : S, a [~] c → below lte a b = below lte c b. 
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
 
End Theory. 