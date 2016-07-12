Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_strictify.
Require Import CAS.theory.brel_subset.
Require Import CAS.theory.brel_set.
Require Import CAS.theory.brel2_in_set.
Require Import CAS.theory.bprop_forall. 



(*

Definition in_set : ∀ S : Type,  ∀ r : brel S, brel2 (finite_set S) S
:= fix f S r l s := 
   match l with 
   | nil => false 
   | a :: rest => r s a || f S r rest s
   end. 


Definition brel_subset : ∀ S : Type,  ∀ r : brel S, brel (finite_set S)
:= fix f S r set1 set2 := 
   match set1 with 
   | nil => true 
   | a :: rest => (in_set S r set2 a) && (f S r rest set2)
   end. 

Definition brel_and_sym : ∀ (S : Type), brel S -> brel S 
:= λ S r x y,  (r x y) && (r y x). 

Definition brel_set : ∀ S : Type, brel S → brel(finite_set S) 
:= λ S r,  brel_and_sym (list S) (brel_subset S r). 

Definition bProp_forall: ∀ S : Type, bProp S → bProp(finite_set S) := List.forallb. 

Definition brel2_from_brel : ∀ S : Type, (brel S) → brel2 S (finite_set S)
:= λ S r x, (bProp_forall S (r x)).


Definition is_minimal_in : ∀ S : Type, brel S → brel S → brel2 S (finite_set S)
:= λ S eq lt a X, if brel_set S eq nil X
                  then false 
                  else brel2_from_brel S (λ x, λ y, negb (lt y x)) a X. 
                                                         ^^^
                                                       (brel_strict S lt)

Why not define as 
Definition is_minimal_in_v2 : ∀ S : Type, brel S → brel S → brel2 S (finite_set S)
:= λ S eq lt a X, 
   if brel_subset S eq X nil
   then false
   else List.forallb (λ y : S, negb (lt y a)) X. 

or 

Definition is_minimal_in_v3 : ∀ S : Type, brel S → brel S → brel2 S (finite_set S)
:= λ S eq lt a X, 
   match X with 
   | nil => false 
   | _ => List.forallb (λ y : S, negb (lt y a)) X
   end. 

*) 


Lemma is_minimal_in_left_congruence : 
  ∀ (S : Type) (eq lt : brel S) (a b : S), 
    brel_reflexive S eq  →
    brel_congruence S eq lt  →
    eq a b = true → 
      ∀ (X : finite_set S), is_minimal_in S eq lt a X = is_minimal_in S eq lt b X. 
Proof. intros S eq lt a b refS cong E. induction X.  
          compute. reflexivity. 
          assert (A := cong _ _ _ _ (refS a0) E). 
          unfold is_minimal_in. simpl. 
          rewrite A. 
          unfold is_minimal_in in IHX.           
          case_eq(brel_set S eq nil X); intro J; rewrite J in IHX. 
             assert (C := brel_set_nil _ _ _ J). rewrite C. simpl. reflexivity. 
             rewrite IHX. reflexivity. 
Defined. 


Lemma is_minimal_in_right_congruence : 
  ∀ (S : Type) (eq lt : brel S) (X Y: finite_set S), 
    brel_reflexive S eq  →
    brel_symmetric S eq  →
    brel_transitive S eq  →
    brel_congruence S eq lt  →
    brel_set S eq X Y = true → 
      ∀ (a : S), is_minimal_in S eq lt a X = is_minimal_in S eq lt a Y. 
Proof. intros S eq lt X Y refS symS transS cong I a. 
       assert (A := brel_set_elim_prop S eq X Y symS transS I). destruct A as [B C].
       unfold is_minimal_in. unfold brel2_from_brel. 
       assert (ref_set := brel_set_reflexive S eq refS). 
       assert (sym_set := brel_set_symmetric S eq symS). 
       assert (trans_set := brel_set_transitive S eq refS symS transS). 
       case_eq(brel_set S eq nil X); intro H. 
          apply sym_set in I. apply sym_set in H. 
          assert (T := trans_set _ _ _ I H). apply sym_set in T. 
          assert (D := brel_set_nil _ _ _ T). rewrite D. simpl. reflexivity. 

          assert (F := brel_transititivity_implies_dual _ _ trans_set). 
          apply (brel_symmetric_implies_dual _ _ sym_set) in H. 
          assert (G := F _ _ _ I H). 
          apply (brel_symmetric_implies_dual _ _ sym_set) in G. 
          rewrite G. 
          assert (K := negb_bProp_congruence S eq lt refS cong a).
          apply (bProp_forall_bProp_congruence S eq (λ y : S, negb (lt y a)) refS symS transS K X Y); auto. 
Defined. 



Lemma is_minimal_in_bProp_congruence : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X : finite_set S),
   brel_reflexive S eq →
   brel_congruence S eq lt →
      bProp_congruence S eq (λ s : S, is_minimal_in S eq lt s X). 
Proof. intros S eq lt X refS cong. unfold bProp_congruence. intros s t E. 
       apply is_minimal_in_left_congruence; auto. 
Defined. 

(* 
Definition brel2_left_congruence (S T : Type) (r1 : brel S) (r2 : brel2 S T) := 
    ∀ (t : T) (s1 s2 : S), r1 s1 s2 = true -> r2 s1 t = r2 s2 t. 
*) 
Lemma is_minimal_in_brel2_left_congruence : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
       brel_reflexive S eq -> 
       brel_congruence S eq lt -> 
           brel2_left_congruence S (finite_set S) eq (is_minimal_in S eq lt). 
Proof. intros S eq lt refS cong. 
       unfold brel2_left_congruence. intros t s1 s3 H. 
       apply is_minimal_in_bProp_congruence; auto. 
Defined. 


Lemma is_minimal_in_true_not_nil : 
    ∀ (S : Type) (eq : brel S) (lt : brel S) (a : S) (s : finite_set S),
          is_minimal_in S eq lt a s = true -> s ≠ nil. 
Proof. intros S eq lt a s H. destruct s. compute in H. discriminate. apply cons_not_nil. Defined. 



(*
Lemma is_minimal_exists : 
    ∀ (S : Type) (eq : brel S) (lt : brel S), 
       brel_reflexive S eq -> 
       brel_congruence S eq lt -> 
       brel_irreflexive S lt -> 
          ∀ (s : finite_set S),
              s ≠ nil -> {a : S & (in_set S eq s a = true) * (is_minimal_in S eq lt a s  = true)}. 
Proof. intros S eq lt refS congS irrS. induction s; intro N.  
          elim N. reflexivity. 
          destruct s. simpl. exists a. split. 
             rewrite (refS a). simpl. reflexivity. 
             compute. rewrite (irrS a). reflexivity. 
             assert (A := cons_not_nil S s s0).
             destruct (IHs A) as [b [C D]].  exists b. split. 
                unfold in_set. fold in_set. unfold in_set in C. fold in_set in C. 
                   rewrite C. rewrite orb_comm. simpl. reflexivity. 
             unfold is_minimal_in in D. simpl in D. 
             unfold is_minimal_in. simpl. 
             apply andb_is_true_left in D. destruct D as [L R]. 
             rewrite L, R. case_eq (lt a b); intro K; simpl. 
                unfold brel2_from_brel in R. unfold bProp_forall in R. 
                unfold in_set in C. fold in_set in C. 
                case_eq(lt s b); intro J; rewrite J in L; simpl in L. 
                   discriminate. 
                   
                reflexivity.
Defined. 



Lemma uop_minset_nil : 
    ∀ (S : Type) (eq : brel S) (lt : brel S) (s : finite_set S),
        uop_minset S eq lt s = nil -> s = nil. 
Proof. intros S eq lt s. unfold uop_minset. unfold uop_filter_from_brel2. 


Lemma uop_filter_from_brel2_nil : 
    ∀ (S : Type) (eq : brel S) (r : brel2 S (finite_set S)), 
        brel2_left_congruence S (finite_set S) eq r -> 
            ∀ (s : finite_set S), uop_filter_from_brel2 S r s = nil -> s = nil. 
Proof. unfold uop_filter_from_brel2. intros S eq r cong. induction s; intro H. 
          reflexivity. 
          assert (A : bProp_congruence S eq (λ a0 : S, r a0 (a ::s))). unfold bProp_congruence. apply cong. 
          assert (B := uop_filter_nil_elim S eq _  A _ H). 
Defined. 





induction s.
          reflexivity. 
          unfold uop_minset in H. unfold uop_filter_from_brel2 in H. unfold uop_filter in H. 
          simpl in H. case_eq(is_minimal_in S eq lt a0 (a0 :: s)); intro J; rewrite J in H.
          simpl in H. apply cons_not_nil in H. contradiction. 
          simpl in H. assert (A : s = nil). apply IHs. 
          unfold uop_minset. unfold uop_filter_from_brel2. unfold uop_filter.  
          
Defined. 


*) 


Hypothesis uop_minset_nil : 
    ∀ (S : Type) (eq : brel S) (lt : brel S) (s : finite_set S),
        uop_minset S eq lt s = nil -> s = nil. 

Lemma uop_minset_nil_contrapositive : 
    ∀ (S : Type) (eq : brel S) (lt : brel S) (a : S) (s : finite_set S),
         s ≠ nil -> uop_minset S eq lt s ≠ nil. 
Proof. intros S eq lt a s H F. apply uop_minset_nil in F; auto. Defined. 

Lemma temp_lemma :    ∀ (S : Type) (r1 : brel S) (r2 : brel2 S (finite_set S)) (X : finite_set S), 
       brel_symmetric S r1 -> 
       brel2_left_congruence S (finite_set S) r1 r2 -> 
         bProp_congruence S r1 (λ a : S, r2 a X). 
Proof. intros S r f X symS cong. unfold bProp_congruence. 
       unfold brel2_left_congruence in cong. intros s t H. apply cong; auto. Defined. 
       

Lemma in_set_uop_filter_from_brel2_elim : 
   ∀ (S : Type) (r : brel S) (f : brel2 S (finite_set S)),  
       brel_symmetric S r -> 
       brel2_left_congruence S (finite_set S) r f -> 
        ∀ (a : S) (X : finite_set S),
           in_set S r (uop_filter_from_brel2 S f X) a = true -> 
              (f a X = true) * (in_set S r X a = true). 
Proof. intros S r f symS cong a X H. 
       unfold uop_filter_from_brel2 in H. 
       apply in_set_uop_filter_elim in H; auto. 
       apply temp_lemma; auto. 
Defined. 


Lemma in_set_uop_filter_from_brel2_intro : 
   ∀ (S : Type) (r : brel S) (f : brel2 S (finite_set S)),  
       brel_symmetric S r -> 
       brel2_left_congruence S (finite_set S) r f -> 
        ∀ (a : S) (X : finite_set S),
           (f a X = true) * (in_set S r X a = true) -> 
              in_set S r (uop_filter_from_brel2 S f X) a = true. 
Proof. intros S r f symS cong a X [L R]. 
       unfold uop_filter_from_brel2. 
       apply in_set_uop_filter_intro; auto. 
       apply temp_lemma; auto.        
Defined. 


Lemma in_set_uop_minset_elim : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_congruence S eq lt -> 
        ∀ (a : S) (X : finite_set S),
           in_set S eq (uop_minset S eq lt X) a = true -> 
              (is_minimal_in S eq lt a X = true) * (in_set S eq X a = true). 
Proof. intros S r f refS symS cong a X H. 
       unfold uop_minset in H. 
       apply in_set_uop_filter_from_brel2_elim  in H; auto. 
       apply is_minimal_in_brel2_left_congruence; auto. 
Defined. 


Lemma in_set_uop_minset_intro : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),  
    brel_reflexive S eq  →
    brel_symmetric S eq  →
    brel_congruence S eq lt  →
     ∀ (X : finite_set S) (a : S),
        in_set S eq X a = true →
        is_minimal_in S eq lt a X = true →
             in_set S eq (uop_minset S eq lt X) a = true. 
Proof. intros S eq lt refS symS cong X a I M. 
       unfold uop_minset.
       apply in_set_uop_filter_from_brel2_intro; auto.
       apply is_minimal_in_brel2_left_congruence; auto. 
Defined. 



Lemma uop_minset_brel_subset : 
    ∀ (S : Type) (eq : brel S) (lt : brel S), 
       brel_reflexive S eq  →  
       brel_symmetric S eq → 
       brel_transitive S eq → 
       brel_congruence S eq lt  → 
         ∀ (X : finite_set S), brel_subset S eq (uop_minset S eq lt X) X = true. 
Proof. intros S eq lt refS symS transS cong. induction X. 
       compute. reflexivity. 
       apply brel_subset_intro; auto. 
       assert (A := brel_subset_elim S eq symS transS _ _ IHX).
       intros b K. apply in_set_cons_intro. case_eq(eq b a); intro J. 
          left. reflexivity. 
          right. apply in_set_uop_minset_elim in K; auto. destruct K as [L R]. 
          apply A. apply in_set_uop_minset_intro; auto. 
          unfold in_set in R. fold in_set in R. rewrite J in R. simpl in R. assumption. 
          unfold is_minimal_in in L. simpl in L. 
          apply andb_is_true_left in L.  destruct L as [LL LR]. 
          unfold is_minimal_in.
          case_eq(brel_set S eq nil X); intro K. 
             assert (F := brel_set_nil _ _ _ K).  rewrite F in R. compute in R. rewrite J in R. 
                discriminate. 
             assumption. 
Defined. 





Definition bProp_respects_non_empty_subsets (S : Type) (eq : brel S) (f : bProp (finite_set S)) 
:= ∀ (X Y : finite_set S), X  ≠  nil -> brel_subset S eq X Y = true -> (f Y = true) -> (f X = true). 

Hypothesis is_minimal_in_respects_non_empty_subsets : 
    ∀ (S : Type) (eq : brel S) (lt : brel S) (a : S) , 
       bProp_respects_non_empty_subsets S eq (is_minimal_in S eq lt a). 
(* 
Proof. unfold bProp_respects_non_empty_subsets. intros S eq lt a. 
       induction X; induction Y; intros N J K. 
          elim N. reflexivity. 
          elim N. reflexivity. 
          compute in K. discriminate. 
          
Defined. 
*) 

Lemma is_minimal_in_idempotent : 
∀ (S : Type) (eq : brel S) (lt : brel S) (a : S) (s : finite_set S),
  brel_reflexive S eq -> 
  brel_symmetric S eq -> 
  brel_transitive S eq -> 
  brel_congruence S eq lt -> 
  is_minimal_in S eq lt a s = true -> 
       is_minimal_in S eq lt a (uop_minset S eq lt s) = true. 
Proof. intros S eq lt a s refS symS transS cong H. 
       assert (A : uop_minset S eq lt s ≠ nil). 
          apply uop_minset_nil_contrapositive; auto. 
          apply (is_minimal_in_true_not_nil S eq lt a s); auto. 
       assert (B := uop_minset_brel_subset S eq lt refS symS transS cong s). 
       assert (QED := is_minimal_in_respects_non_empty_subsets S eq lt a (uop_minset S eq lt s) s A B H). 
       assumption. 
Defined. 




