Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset.

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.


Lemma brel_set_nil : ∀ (X : finite_set S), brel_set eq nil X = true -> X = nil. 
Proof. induction X; intro H. reflexivity. compute in H. discriminate. Defined. 


Lemma brel_set_intro : ∀ (X Y : finite_set S), (brel_subset eq X Y = true) * (brel_subset eq Y X = true)  → brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. unfold brel_set. unfold brel_and_sym. apply andb_is_true_right; auto. Defined. 

Lemma brel_set_elim : ∀ (X Y : finite_set S), 
     brel_set eq X Y = true -> (brel_subset eq X Y = true) * (brel_subset eq Y X = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]; auto. 
Defined. 

Lemma brel_set_intro_prop : ∀ (X Y : finite_set S), 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true)  → 
             brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. apply brel_set_intro. split. 
          apply brel_subset_intro in H1; auto. 
          apply brel_subset_intro in H2; auto. 
Defined. 

Lemma brel_set_elim_prop : ∀ (X Y : finite_set S),
     brel_set eq X Y = true -> 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       assert (A1 := brel_subset_elim S eq symS tranS _ _ H1). 
       assert (A2 := brel_subset_elim S eq symS tranS _ _ H2); auto. 
Defined. 


Lemma brel_set_false_elim_prop : ∀ (X Y : finite_set S),
     brel_set eq X Y = false -> 
        { a : S & (in_set eq X a = true) * (in_set eq Y a = false) } 
      + { a : S & (in_set eq Y a = true) * (in_set eq X a = false) }.
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_false_left in H. destruct H as [H | H].  
          apply brel_subset_false_elim in H; auto. 
          apply brel_subset_false_elim in H; auto. 
Defined. 

(* 
   ∀ (t : S) (s1 s2 : finite_set S),
   brel_set X s1 s2 = true → in_set X s1 t = in_set X s2 t
*) 
Lemma in_set_left_congruence : brel2_left_congruence (finite_set S) S (brel_set eq) (in_set eq). 
Proof. unfold brel2_left_congruence.
       intros t s1 s2 H. 
       apply brel_set_elim_prop in H; auto. destruct H as [L R]. 
       case_eq(in_set eq s1 t); intro J; 
       case_eq(in_set eq s2 t); intro K; auto.  
          rewrite (L t J) in K. assumption. 
          rewrite (R t K) in J. discriminate. 
Defined.

Lemma in_set_left_congruence_v3 : ∀ (a : S) (X Y : finite_set S),
    brel_set eq X Y = true -> in_set eq X a = true -> in_set eq Y a = true.
Proof. intros a X Y H1 H2. 
       apply brel_set_elim in H1.
       destruct H1 as [H1 _]. 
       assert (K := brel_subset_elim _ _ symS tranS X Y H1). 
       apply K; auto. 
Qed.



(***     brel_set eqv properties   ****)

(* move and_sym lemmas? *)
Lemma brel_and_sym_relexive (T : Type) (r : brel T) (refr : brel_reflexive T r) : brel_reflexive T (brel_and_sym r). 
Proof. unfold brel_reflexive, brel_and_sym. intros s. 
       rewrite (refr s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_transitive (T : Type) (r : brel T) (tranr : brel_transitive T r) : brel_transitive T (brel_and_sym r). 
Proof. unfold brel_transitive, brel_and_sym. intros s t u H1 H2. 
       apply andb_is_true_left in H1. destruct H1 as [H1_l H1_r].        
       apply andb_is_true_left in H2. destruct H2 as [H2_l H2_r].        
       rewrite (tranr _ _ _ H1_l H2_l).
       rewrite (tranr _ _ _ H2_r H1_r ). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_symmetric (T : Type) (r : brel T) : brel_symmetric T (brel_and_sym r). 
Proof. unfold brel_symmetric, brel_and_sym. intros s t H. 
       apply andb_is_true_left in H. destruct H as [H_l H_r].        
       rewrite H_l. rewrite H_r. simpl. reflexivity. 
Defined. 



Lemma in_set_left_congruence_v2 : ∀ (X Y : finite_set S),
    brel_set eq X Y = true -> ∀ (a : S), in_set eq X a = in_set eq Y a.
Proof. intros X Y H a. 
       apply brel_set_elim in H.
       destruct H as [H1 H2]. 
       assert (K1 := brel_subset_elim _ _ symS tranS X Y H1).
       assert (K2 := brel_subset_elim _ _ symS tranS Y X H2).        
       case_eq(in_set eq X a); intro J1; case_eq(in_set eq Y a); intro J2; auto.
       apply K1 in J1. rewrite J1 in J2. exact J2.
       apply K2 in J2. rewrite J1 in J2. exact J2.       
Qed.



Lemma in_set_congruence : ∀ (a b : S) (X Y : finite_set S),
    brel_set eq X Y = true -> eq a b = true -> in_set eq X a = in_set eq Y b.
Proof. intros a b X Y H1 H2.
       assert (J1 := in_set_right_congruence S eq symS tranS _ _ X H2).
       apply symS in H2. assert (J2 := in_set_right_congruence S eq symS tranS _ _ Y H2).        
       assert (Ma := in_set_left_congruence_v2 X Y H1 a).       
       assert (Mb := in_set_left_congruence_v2 X Y H1 b).
       case_eq(in_set eq X a); intro K1; case_eq(in_set eq Y b); intro K2; auto.
       rewrite (J1 K1) in Mb. rewrite <- Mb in K2. exact K2.
       rewrite (J2 K2) in Ma. rewrite K1 in Ma. exact Ma.
Qed. 


(***)


Lemma brel_set_reflexive : brel_reflexive (finite_set S) (brel_set eq). 
Proof. unfold brel_set. 
       apply brel_and_sym_relexive. 
       apply brel_subset_reflexive; auto. 
Defined.

Lemma brel_set_transitive : brel_transitive (finite_set S) (brel_set eq). 
Proof. unfold brel_set.
       apply brel_and_sym_transitive. 
       apply brel_subset_transitive; auto. 
Defined.

Lemma brel_set_symmetric : brel_symmetric (list S) (brel_set eq). 
Proof. unfold brel_set. apply brel_and_sym_symmetric. Defined. 

Lemma brel_set_congruence : brel_congruence (finite_set S) (brel_set eq) (brel_set eq). 
Proof. apply brel_congruence_self. 
       apply brel_set_symmetric; auto.  
       apply brel_set_transitive; auto.  
Defined. 

Lemma brel_set_not_trivial (s : S) : 
   brel_not_trivial (finite_set S) (brel_set eq) (λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil). 
Proof. intro X. destruct X; compute; auto. Qed. 



Lemma brel_set_at_least_three (s : S) (f : S -> S):
  brel_not_trivial S eq f -> 
  brel_at_least_three (finite_set S) (brel_set eq).
Proof. intro nt. 
       exists (nil, (s :: nil, (f s) :: nil)).
       destruct (nt s) as [L R].
       compute. rewrite L; auto. 
Defined. 


Lemma brel_set_not_exactly_two (s : S) (f : S -> S):
  brel_not_trivial S eq f -> 
  brel_not_exactly_two (finite_set S) (brel_set eq).
Proof. intro nt. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto.
       apply (brel_set_at_least_three s f); auto. 
Defined.

Definition power_set : finite_set S -> finite_set (finite_set S)
:= fix f X := 
      match X with
         | nil => nil :: nil 
         | t :: Y => (f Y) ++ (List.map (λ Z, t :: Z) (f Y))
      end.

Definition powerset_enum (fS : unit -> list S) (x : unit) :=  power_set (fS x).

Lemma empty_set_in_powerset (X : finite_set S) : in_set (brel_set eq) (power_set X) nil = true.
Admitted.

Lemma  in_powerset_intro (a : S) (X Y : finite_set S) (H : in_set (brel_set eq) (power_set Y) X = true) (K : in_set eq Y a = true) : 
                          in_set (brel_set eq) (power_set Y) (a :: X) = true.
Admitted.   


Lemma brel_set_finite : carrier_is_finite S eq -> carrier_is_finite (finite_set S) (brel_set eq).
Proof. intros [fS pS]. unfold carrier_is_finite. exists (powerset_enum fS).
       intro X. unfold powerset_enum.
       induction X.
          apply empty_set_in_powerset. 
          assert (K := pS a).  apply in_powerset_intro; auto. 
Defined. 

Lemma brel_set_not_finite : carrier_is_not_finite S eq -> carrier_is_not_finite (finite_set S) (brel_set eq).
Proof. unfold carrier_is_not_finite. intros H f.
Admitted.

Definition brel_set_finite_decidable (d : carrier_is_finite_decidable S eq) : carrier_is_finite_decidable (finite_set S) (brel_set eq)
  := match d with
     | inl fS  => inl (brel_set_finite fS)
     | inr nfS => inr (brel_set_not_finite nfS)                       
     end.

End Theory.

Section ACAS.


Definition eqv_proofs_set : ∀ (S : Type) (r : brel S),
    eqv_proofs S r → eqv_proofs (finite_set S) (brel_set r) 
:= λ S r eqv, 
   {| 
     A_eqv_congruence  := brel_set_congruence S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) 
   ; A_eqv_reflexive   := brel_set_reflexive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) 
   ; A_eqv_transitive  := brel_set_transitive S r (A_eqv_reflexive S r eqv) (A_eqv_symmetric S r eqv) (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_set_symmetric S r
   |}. 


Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S)
:= λ S eqvS,
  let eq := A_eqv_eq S eqvS in
  let s  := A_eqv_witness S eqvS in
  let f  := A_eqv_new S eqvS in
  let nt := A_eqv_not_trivial S eqvS in
  let eqP := A_eqv_proofs S eqvS in
  let refS := A_eqv_reflexive S eq eqP in
  let symS := A_eqv_symmetric S eq eqP in
  let trnS := A_eqv_transitive S eq eqP in   
   {| 
      A_eqv_eq     := brel_set eq 
    ; A_eqv_proofs := eqv_proofs_set S eq eqP 
    ; A_eqv_witness := s :: nil 
    ; A_eqv_new     := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil
    ; A_eqv_not_trivial := brel_set_not_trivial S eq s 
    ; A_eqv_exactly_two_d := inr (brel_set_not_exactly_two S eq refS symS trnS s f nt)                              
    ; A_eqv_data   := λ d, DATA_set (List.map (A_eqv_data S eqvS) d)  
    ; A_eqv_rep    := λ d, d  (* fix this someday ... *)
    ; A_eqv_finite_d  := brel_set_finite_decidable S eq refS symS trnS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast    := Ast_eqv_set (A_eqv_ast S eqvS)
   |}. 

End ACAS.

Section CAS.

Definition brel_set_finite_checkable {S : Type} (d : @check_is_finite S) : @check_is_finite (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Is_Finite (powerset_enum S fS)
     | Certify_Is_Not_Finite => Certify_Is_Not_Finite
     end.
  

Definition eqv_set : ∀ {S : Type},  @eqv S -> @eqv (finite_set S)
:= λ {S} eqvS,
  let eq := eqv_eq eqvS in
  let s := eqv_witness eqvS in
  let f := eqv_new eqvS in   
 {| 
      eqv_eq       := brel_set eq 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     |}  
    ; eqv_witness := s :: nil 
    ; eqv_new     := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 (brel_set eq) nil (s :: nil)  ((f s):: nil))
    ; eqv_data    := λ d, DATA_set (List.map (eqv_data eqvS) d)  
    ; eqv_rep     := λ d, d  (* fix this? *)
    ; eqv_finite_d  := brel_set_finite_checkable (eqv_finite_d eqvS)
    ; eqv_ast     := Ast_eqv_set (eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.


Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S),  
    eqv_set (A2C_eqv S E) = A2C_eqv (finite_set S) (A_eqv_set S E).
Proof. intros S E. 
       unfold eqv_set, A_eqv_set, A2C_eqv; simpl.
       destruct E; simpl.  unfold brel_set_finite_checkable, brel_set_finite_decidable. 
       destruct A_eqv_finite_d; auto.
       destruct c as [fS PS]. simpl. unfold brel_set_finite. 
       reflexivity.
Qed.        

  
 
End Verify.   
  