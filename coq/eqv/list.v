Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 
Require Import CAS.coq.sg.theory. (* for plus_SS *)


Open Scope list_scope. 

Section Compuation.

Fixpoint brel_list {S : Type} (r : brel S) (x : list S) (y : list S) : bool 
:= match x, y with
         | nil, nil => true 
         | nil, _ => false 
         | _, nil => false 
         | a::tla, b::tlb => bop_and (r a b) (brel_list r tla tlb)
      end.

End Compuation. 
    
Section IntroElim.

Variable S : Type.
Variable eq : brel S.
Variable sym : brel_symmetric S eq. 

(* in_list is defined in eqv/properties.v *) 
Lemma in_list_cons_intro  : ∀ (a b : S) (X : list S),
    ((eq a b = true) + (in_list eq X b = true)) ->   in_list eq (a :: X) b = true.
Proof. intros a b X [H | H]; unfold in_list; fold (@in_list S); apply bop_or_intro; auto. Qed.        
       
Lemma in_list_cons_elim : ∀ (a b : S) (X : finite_set S),
    in_list eq (a :: X) b = true -> ((eq a b = true) + (in_list eq X b = true)). 
Proof. intros a b X H.
       unfold in_list in H. fold (@in_list S) in H. 
       apply bop_or_elim in H.
       destruct H as [H | H]; auto.
Qed.


Lemma in_list_concat_intro : ∀ (X Y : list S) (a : S),
     (in_list eq X a = true) + (in_list eq Y a = true) → in_list eq (X ++ Y) a = true. 
Proof. induction X. intros Y a [L | R]. 
             compute in L. discriminate L. 
             rewrite List.app_nil_l. exact R. 
          intros Y a0 [L | R]. 
             rewrite <- List.app_comm_cons. 
             unfold in_list. fold (@in_list S). unfold in_list in L. fold (@in_list S) in L. 
             apply bop_or_elim in L. destruct L as [L | L]. 
                rewrite L. simpl. reflexivity. 
                apply bop_or_intro. right. apply IHX. left. exact L. 

             rewrite <- List.app_comm_cons. 
             unfold in_list. fold (@in_list S). 
             apply bop_or_intro. right. apply IHX. right. exact R. 
Defined. 

Lemma in_list_concat_elim : ∀ (X Y : finite_set S) (a : S),
      in_list eq (X ++ Y) a = true → (in_list eq X a = true) + (in_list eq Y a = true). 
Proof. induction X. 
          intros U a H. rewrite List.app_nil_l in H. right. exact H. 
          intros U b H. rewrite <- List.app_comm_cons in H. 
          unfold in_list in H. fold (@in_list S) in H. 
          apply bop_or_elim in H.  destruct H as [L | R]. 
             left. unfold in_list. fold (@in_list S). rewrite L. simpl. reflexivity. 
             assert (K := IHX U b R). destruct K as [KL | KR].
                left. apply in_list_cons_intro. right. exact KL. 
                right. exact KR. 
Defined. 


End IntroElim.   

Section Theory.

Lemma brel_list_symmetric : ∀ (S : Type) (r : brel S), 
              (brel_symmetric _ r) → brel_symmetric (list S) (brel_list r). 
Proof. unfold brel_symmetric. 
       induction s; induction t; simpl; intros; auto.        
          apply bop_and_elim in H0. 
          destruct H0 as [H0_l H0_r].
          apply bop_and_intro. 
             apply (H _ _ H0_l). 
             apply (IHs t H0_r).
Qed. 

Lemma brel_list_reflexive : ∀ (S : Type) (r : brel S), 
              (brel_reflexive _ r) → brel_reflexive (list S) (brel_list r). 
Proof. unfold brel_reflexive. induction s; simpl; auto.  
       rewrite (H a). rewrite IHs. simpl. reflexivity. 
Qed.

Lemma brel_list_transitive : ∀ (S : Type) (r : brel S), 
              (brel_transitive _ r) → brel_transitive (list S) (brel_list r). 
Proof. unfold brel_transitive. 
       induction s; induction t; induction u; simpl; intros; auto.        
          discriminate. 
          apply bop_and_elim in H0. 
          apply bop_and_elim in H1. 
          destruct H0 as [H0_l H0_r]. 
          destruct H1 as [H1_l H1_r].
          apply bop_and_intro. 
             apply (H _ _ _ H0_l H1_l). 
             apply (IHs t u H0_r H1_r).
Qed. 


Lemma brel_list_congruence : ∀ (S : Type) (r : brel S), 
         brel_symmetric S r -> 
         brel_transitive S r -> 
         brel_congruence S r r -> 
              brel_congruence (list S) (brel_list r) (brel_list r). 
Proof. intros S r symS transS congS s t u v.  
       apply brel_congruence_self. 
       apply brel_list_symmetric; auto. 
       apply brel_list_transitive; auto. 
Qed. 

Open Scope nat.

Lemma cons_length : ∀ (T : Type) (t : T ) (l : list T), length (t :: l) = S(length l). 
Proof. intros T t l. simpl. reflexivity. Qed.

Lemma brel_list_true_implies_length_equal :
  ∀ (S : Type) (r : brel S) (l1 l2 : list S),
    brel_list  r l1 l2 = true -> (length l1) = (length l2).
Proof. intros S r. induction l1; induction l2; intro H. 
       reflexivity. 
       compute in H. discriminate.
       compute in H. discriminate.        
       unfold brel_list in H. fold (@brel_list S) in H.
       apply bop_and_elim in H.
       destruct H as [_ H].
       rewrite cons_length. rewrite cons_length.
       apply IHl1 in H. auto.        
Qed. 

Lemma list_length_not_equal_implies_brel_list_false :
       ∀ (S : Type) (r : brel S) (l1 l2 : list S), 
           (length l1) <> (length l2) -> 
               brel_list r l1 l2 = false. 
Proof. intros S r l1 l2 H. 
       case_eq (brel_list r l1 l2); intro F.
       apply brel_list_true_implies_length_equal in F. elim H. assumption.
       reflexivity. 
Qed. 

Lemma brel_list_not_cons_equal_left : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
                                     brel_list r (s :: l) l = false. 
Proof. intros S r l s. apply list_length_not_equal_implies_brel_list_false. 
       rewrite cons_length. assert (fact := n_Sn (length l)). 
       intro F. rewrite F in fact. elim fact. reflexivity. 
Qed.

Lemma brel_list_not_cons_equal_right : ∀ (S : Type) (r : brel S) (l : list S) (s : S), 
        brel_list r l (s :: l) = false. 
Proof. intros S r l s. apply list_length_not_equal_implies_brel_list_false. 
       rewrite cons_length. assert (fact := n_Sn (length l)). 
       intro F. rewrite <- F in fact. elim fact. reflexivity. 
Qed.


Lemma list_length_zero : ∀ (S : Type) (u : list S), length u = 0 -> u = nil.
Proof. intro S. induction u; auto. intro H.
       rewrite cons_length in H.
       assert (fact1 := PeanoNat.Nat.neq_succ_0 (length u)).  
       rewrite H in fact1.
       discriminate.
Qed. 


Lemma plus_zero_only_left_id : ∀ a b : nat, b = a + b -> a = 0. 
Proof. induction a; auto. 
       induction b; intro H.
       assert (fact1 := PeanoNat.Nat.add_0_r (S a)).
       rewrite fact1 in H. rewrite H. reflexivity.
       rewrite plus_SS in H. 
       apply eq_add_S in H.
       rewrite <- plus_Sn_m in H.
       apply IHb; auto. 
Qed. 

Lemma concat_nil_only_left_id : ∀ (S : Type) (r : brel S) (a : S) (w u : list S),  
    brel_list r w (u ++ w) = true -> brel_list r nil u = true. 
Proof. intros S r a w u H. 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H. 
       assert (fact1 := plus_zero_only_left_id (length u) (length w) H). 
       rewrite (list_length_zero _ u fact1).
       compute. reflexivity.
Qed. 

Lemma concat_cons_no_left_id : ∀ (S : Type) (a : S) (r : brel S) (s u : list S),  
    brel_list r s (u ++ a :: s) = false .
Proof. intros S r a s u.
       case_eq (brel_list a s (u ++ r :: s)); intro H.
       assert (K := H). 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H.
       rewrite cons_length in H.
       (* Oh no!  Arithmetic in Coq! *) 
       rewrite PeanoNat.Nat.add_comm in H. 
       apply Minus.plus_minus in H.
       rewrite PeanoNat.Nat.sub_succ_r in H. 
       rewrite <- Minus.minus_diag_reverse in H. 
       rewrite PeanoNat.Nat.pred_0 in H. 
       apply list_length_zero in H.  rewrite H in K. simpl in K.
       rewrite brel_list_not_cons_equal_right in K. rewrite K.
       reflexivity.        
       reflexivity. 
Qed. 

Lemma concat_cons_no_left_id_v2 : ∀ (S : Type) (a : S) (r : brel S) (s u : list S),  
       brel_list r (u ++ a :: s) s = false .   
Proof. intros S r a s u.
       case_eq (brel_list a (u ++ r :: s) s); intro H.
       assert (K := H). 
       apply brel_list_true_implies_length_equal in H.
       rewrite List.app_length in H.
       rewrite cons_length in H.
       (* Oh no!  Arithmetic in Coq! *)
       apply eq_sym in H.
       rewrite PeanoNat.Nat.add_comm in H. 
       apply  Minus.plus_minus in H.
       rewrite PeanoNat.Nat.sub_succ_r in H. 
       rewrite <- Minus.minus_diag_reverse in H. 
       rewrite PeanoNat.Nat.pred_0 in H. 
       apply list_length_zero in H.  rewrite H in K. rewrite List.app_nil_l in K. 
       rewrite brel_list_not_cons_equal_left in K. rewrite K.
       reflexivity.        
       reflexivity. 
Qed. 


Lemma brel_list_not_trivial : ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), 
              (brel_symmetric S r) → 
              (brel_not_trivial S r f) → brel_not_trivial (list S) (brel_list r) (λ (l : list S), s :: l). 
Proof. intros S r s f symS Pf l.  
       assert (F1 : brel_list r (s :: l) l = false). 
         apply brel_list_not_cons_equal_left. 
       assert (F2 : brel_list r l (s :: l) = false). 
         apply brel_symmetric_implies_dual. 
         apply brel_list_symmetric. assumption. 
         assumption. 
       rewrite F1, F2; auto. 
Defined. 


(* a few useful lemmas *) 

Lemma list_concat_cons : ∀ (S : Type) (r : brel S),
    brel_reflexive S r ->
    ∀ (a : S) (t s : list S),
        brel_list r (t ++ (a :: s)) ((t ++ (a :: nil)) ++ s) = true.
Proof. intros S r ref a.  induction t; intros s; simpl. 
       apply bop_and_intro. 
          apply ref.
          apply brel_list_reflexive; auto. 
       apply bop_and_intro. 
          apply ref.
          apply IHt. 
Qed.

Lemma brel_list_at_least_three : ∀ (S : Type) (s : S) (r : brel S),
  brel_at_least_three (list S) (brel_list r).
Proof. intros S s r. exists (nil, (s :: nil, s :: s :: nil)). 
       compute; split; auto. case_eq(r s s); intro J; auto. 
Defined. 


Lemma brel_list_not_exactly_two : ∀ (S : Type) (s : S) (r : brel S),
  brel_symmetric S r ->
  brel_transitive S r ->     
  brel_not_exactly_two (list S) (brel_list r).
Proof. intros S s r symS trnS. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_list_symmetric; auto. 
       apply brel_list_transitive; auto.
       apply brel_list_at_least_three; auto. 
Defined.

Lemma brel_list_not_finite (S : Type) (r : brel S) (s : S) : carrier_is_not_finite (list S) (brel_list r).
Proof. unfold carrier_is_not_finite. intro F.
       (* cons an s onto each of the longest lists in (F tt), then pick one... 
          the in_set should really be an in_list --- so pick the first longest in (F tt) ... 
        *)
Admitted.

End Theory.


Section ACAS.
Open Scope list_scope. 

Definition eqv_proofs_brel_list : ∀ (S : Type) (r : brel S), eqv_proofs S r → eqv_proofs (list S) (brel_list r) 
:= λ S r eqv, 
   {| 
     A_eqv_congruence  := brel_list_congruence S r 
                                  (A_eqv_symmetric S r eqv) 
                                  (A_eqv_transitive S r eqv) 
                                  (A_eqv_congruence S r eqv) 
   ; A_eqv_reflexive   := brel_list_reflexive S r  (A_eqv_reflexive S r eqv) 
   ; A_eqv_transitive  := brel_list_transitive S r (A_eqv_transitive S r eqv) 
   ; A_eqv_symmetric   := brel_list_symmetric S r  (A_eqv_symmetric S r eqv)
   |}. 


Definition A_eqv_list : ∀ (S : Type),  A_eqv S -> A_eqv (list S) 
  := λ S eqvS,
  let eq := A_eqv_eq S eqvS in
  let wS := A_eqv_witness S eqvS in
  let f  := A_eqv_new S eqvS in
  let nt := A_eqv_not_trivial S eqvS in
  let eqP  := A_eqv_proofs S eqvS in 
  let symS := A_eqv_symmetric S eq eqP in
  let trnS := A_eqv_transitive S eq eqP in     
   {| 
      A_eqv_eq     := brel_list eq 
    ; A_eqv_proofs := eqv_proofs_brel_list S eq eqP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := λ (l : list S), wS :: l
    ; A_eqv_not_trivial   := brel_list_not_trivial S eq wS f symS nt
    ; A_eqv_exactly_two_d := inr (brel_list_not_exactly_two S wS eq symS trnS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) l
    ; A_eqv_finite_d      := inr (brel_list_not_finite S eq wS) 
    ; A_eqv_ast           := Ast_eqv_list (A_eqv_ast S eqvS)
   |}. 

End ACAS.

Section CAS.

Definition eqv_list : ∀ {S : Type},  @eqv S -> @eqv (list S)
:= λ {S} eqvS,
  let eq := eqv_eq eqvS in
  let wS := eqv_witness eqvS in  
   {| 
      eqv_eq    := brel_list eq 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (list S)
     ; eqv_reflexive      := @Assert_Reflexive (list S)
     ; eqv_transitive     := @Assert_Transitive (list S)
     ; eqv_symmetric      := @Assert_Symmetric (list S)
     |}  
    ; eqv_witness := nil 
    ; eqv_new := (λ (l : list S), wS :: l)
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 (brel_list eq) nil (wS :: nil)  (wS :: wS :: nil))                   
    ; eqv_data  := λ l, DATA_list (List.map (eqv_data eqvS) l)
    ; eqv_rep   := λ l, List.map (eqv_rep eqvS) l
    ; eqv_finite_d  := Certify_Is_Not_Finite 
    ; eqv_ast   := Ast_eqv_list (eqv_ast eqvS)
   |}. 

End CAS.

Section MCAS.

Definition mcas_eqv_list {S : Type} (A : @mcas_eqv S) : @mcas_eqv (list S) :=
match A with
| EQV_eqv B    => EQV_eqv (eqv_list B)
| EQV_Error sl => EQV_Error sl
end.                  

End MCAS.

    
Section Verify.




Theorem correct_eqv_list : ∀ (S : Type) (E : A_eqv S),  
         eqv_list (A2C_eqv S E) = A2C_eqv (list S) (A_eqv_list S E). 
Proof. intros S E.
       unfold eqv_list, A_eqv_list, A2C_eqv; simpl.
       unfold brel_list_not_exactly_two. unfold brel_at_least_thee_implies_not_exactly_two. 
       reflexivity.
Qed.        
 
End Verify.   
  
