Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set. 

Section Theory.
Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.

Variable wS : S. 
Variable wT : T.

Variable conS : brel_congruence S rS rS.
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS.

Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.
Variable tranT : brel_transitive T rT.

Notation "a <+> b"  := (brel_sum a b) (at level 15).


Lemma brel_sum_not_trivial :  
        brel_not_trivial (S + T) (rS <+> rT) (λ (d : S + T), match d with | inl _ => inr wT | inr _ => inl wS end).
Proof. intros [ s | t ]; compute; auto. Defined. 


Lemma brel_sum_reflexive : brel_reflexive (S + T) (rS <+> rT). 
Proof. intros [s |  t]; simpl. rewrite (refS s). reflexivity. rewrite (refT t). reflexivity. Qed. 


Lemma brel_sum_symmetric : brel_symmetric (S + T) (rS <+> rT). 
Proof. intros [s1 | t1] [s2 | t2]; simpl; intros.  
        apply (symS _ _ H). exact H. exact H. apply (symT _ _ H).         
Qed. 

Lemma brel_sum_transitive : brel_transitive (S + T) (rS <+> rT). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl; intros.  
        apply (tranS _ _ _ H H0). 
        exact H0. discriminate H. exact H. exact H. discriminate H. exact H0. 
        apply (tranT _ _ _ H H0). 
Qed. 


Lemma brel_sum_congruence : brel_congruence (S + T) (rS <+> rT) (rS <+> rT). 
Proof. intros [s | s] [t | t] [u | u] [v | v]; simpl; intros H Q; auto; discriminate. Qed. 


Lemma brel_sum_rep_correct : 
       ∀ (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_correct S rS repS) → 
              (brel_rep_correct T rT repT) → 
                 brel_rep_correct (S + T) (rS <+> rT) (uop_sum repS repT). 
Proof. 
     intros repS repT RS RT [s | t]; compute. 
         rewrite (RS s); auto.  
         rewrite (RT t); auto.
Qed. 

Lemma brel_sum_rep_idempotent : 
       ∀ (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_idempotent S rS repS) → 
              (brel_rep_idempotent T rT repT) → 
                 brel_rep_idempotent (S + T) (rS <+> rT) (uop_sum repS repT). 
Proof. 
     intros repS repT RS RT [s | t]; compute. 
         rewrite (RS s); auto.  
         rewrite (RT t); auto.
Qed. 

Lemma brel_sum_not_total_ : ∀ (s : S) (t : T),  brel_not_total (S + T) (rS <+> rT). 
Proof. intros s t. exists ((inl _ s), (inr _ t)); simpl. split; reflexivity. Defined.


Lemma brel_sum_at_least_three (s : S) (f : S -> S) (t : T):
  brel_not_trivial S rS f ->
  brel_at_least_three (S + T) (rS <+> rT).
Proof. intro ntS. 
       exists (inl s, (inl (f s), inr t)).
       destruct (ntS s) as [LS RS].        
       compute. rewrite LS; split; auto. 
Defined. 


Lemma brel_sum_not_exactly_two (s : S) (f : S -> S) (t : T) :
  brel_not_trivial S rS f ->
  brel_not_exactly_two (S + T) (rS <+> rT).
Proof. intros ntS.
       apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_sum_symmetric; auto. 
       apply brel_sum_transitive; auto.
       apply (brel_sum_at_least_three s f t); auto. 
Defined.

Definition enumerate_sum (X : finite_set S) (Y : finite_set T) : finite_set (S + T)
  := (List.map (λ s, inl s) X) ++ (List.map (λ t, inr t) Y). 
                         
Definition sum_enum (fS : unit -> list S) (fT : unit -> list T) (x : unit) := enumerate_sum (fS tt) (fT tt).

Lemma in_set_sum_left  (s : S) (X : finite_set S) (H : in_set rS X s = true) : in_set (rS <+> rT) (List.map (λ a : S, inl a) X) (inl s) = true. 
Proof. induction X. compute in H. discriminate H.
       apply in_set_cons_elim in H; auto.
       unfold List.map. destruct H as [H | H]. 
       apply in_set_cons_intro; auto. apply brel_sum_symmetric; auto.
       apply in_set_cons_intro; auto. apply brel_sum_symmetric; auto.
Qed.

Lemma in_set_sum_right  (t : T) (X : finite_set T) (H : in_set rT X t = true) : in_set (rS <+> rT) (List.map (λ a : T, inr a) X) (inr t) = true. 
Proof. induction X. compute in H. discriminate H.
       apply in_set_cons_elim in H; auto.
       unfold List.map. destruct H as [H | H]. 
       apply in_set_cons_intro; auto. apply brel_sum_symmetric; auto.
       apply in_set_cons_intro; auto. apply brel_sum_symmetric; auto.
Qed.


Lemma brel_sum_finite : carrier_is_finite S rS -> carrier_is_finite T rT -> carrier_is_finite (S + T) (rS <+> rT).
Proof. intros [fS pS] [fT pT]. unfold carrier_is_finite. exists (sum_enum fS fT).
       unfold sum_enum. unfold enumerate_sum. 
       intros [s | t].
          assert (HS := pS s). apply in_set_concat_intro; auto.       
          left. apply in_set_sum_left; auto. 
          assert (HT := pT t). apply in_set_concat_intro; auto.       
          right. apply in_set_sum_right; auto.        
Defined. 


Definition only_left: finite_set (S + T) -> finite_set S 
  := fix f X :=
     match X with
     | nil => nil
     | (inl s) :: Y => s :: (f Y)
     | (inr _) :: Y => f Y
     end.                          

Definition only_right: finite_set (S + T) -> finite_set T
  := fix f X :=
     match X with
     | nil => nil
     | (inl _) :: Y => f Y
     | (inr t) :: Y => t :: (f Y)
     end.

Lemma in_only_left_intro (s : S) (X : finite_set (S + T)): 
  in_set (rS <+> rT) X (inl s) = true -> in_set rS (only_left X) s = true.
Proof. intro H. induction X. compute in H. discriminate H. 
       destruct a as [s' | t'].
       unfold only_left. fold only_left. apply in_set_cons_intro; auto.
       apply in_set_cons_elim in H. destruct H as [H | H].
       compute in H. left. exact H. 
       right. apply IHX; auto. 
       apply brel_sum_symmetric; auto.

       unfold only_left. fold only_left. apply IHX. 
       apply in_set_cons_elim in H. destruct H as [H | H].
       compute in H. discriminate H. 
       exact H.
       apply brel_sum_symmetric; auto.       
Qed. 

Lemma in_only_right_intro (t : T) (X : finite_set (S + T)): 
  in_set (rS <+> rT) X (inr t) = true -> in_set rT (only_right X) t = true.
Proof. intro H. induction X. compute in H. discriminate H. 
       destruct a as [s' | t'].

       unfold only_right. fold only_right. apply IHX. 
       apply in_set_cons_elim in H. destruct H as [H | H].
       compute in H. discriminate H. 
       exact H.
       apply brel_sum_symmetric; auto.       
       
       unfold only_right. fold only_left. apply in_set_cons_intro; auto.
       apply in_set_cons_elim in H. destruct H as [H | H].
       compute in H. left. exact H. 
       right. apply IHX; auto. 
       apply brel_sum_symmetric; auto.
Qed. 

Lemma brel_sum_not_finite_left : carrier_is_not_finite S rS -> carrier_is_not_finite (S + T) (rS <+> rT).
Proof. unfold carrier_is_not_finite. intro H.
       intro fST. assert (K := H (λ _, only_left (fST tt) )).
       destruct K as [s Ps]. exists (inl s).
       case_eq(in_set (rS <+> rT) (fST tt) (inl s)); intro J; auto. 
       apply in_only_left_intro in J. rewrite J in Ps. exact Ps. 
Defined. 


Lemma brel_sum_not_finite_right : carrier_is_not_finite T rT -> carrier_is_not_finite (S + T) (rS <+> rT).
Proof. unfold carrier_is_not_finite. intro H.
       intro fST. assert (K := H (λ _, only_right (fST tt) )).
       destruct K as [t Pt]. exists (inr t).
       case_eq(in_set (rS <+> rT) (fST tt) (inr t)); intro J; auto. 
       apply in_only_right_intro in J. rewrite J in Pt. exact Pt. 
Defined. 


Definition eqv_sum_finite_decidable (dS : carrier_is_finite_decidable S rS) (dT: carrier_is_finite_decidable T rT) :
    carrier_is_finite_decidable (S + T) (rS <+> rT)
  := match dS, dT with
     | inr nfS, _ => inr (brel_sum_not_finite_left nfS) 
     | _, inr nfT => inr (brel_sum_not_finite_right nfT) 
     | inl fS, inl fT => inl (brel_sum_finite fS fT)
     end. 

End Theory.

Section ACAS.

Definition eqv_proofs_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T),
        eqv_proofs S rS -> eqv_proofs T rT -> eqv_proofs (S + T) (brel_sum rS rT) 
:= λ S T rS rT eqvS eqvT, 
{|
 A_eqv_congruence  := brel_sum_congruence S T rS rT 
                        (A_eqv_congruence S rS eqvS)
                        (A_eqv_congruence T rT eqvT)
; A_eqv_reflexive   := brel_sum_reflexive S T rS rT 
                        (A_eqv_reflexive S rS eqvS) 
                        (A_eqv_reflexive T rT eqvT) 
; A_eqv_transitive  := brel_sum_transitive S T rS rT  
                        (A_eqv_transitive S rS eqvS) 
                        (A_eqv_transitive T rT eqvT) 
; A_eqv_symmetric   := brel_sum_symmetric S T rS rT  
                        (A_eqv_symmetric S rS eqvS) 
                        (A_eqv_symmetric T rT eqvT)
; A_eqv_type_ast    := Ast_type_sum
                        (A_eqv_type_ast S rS eqvS, 
                         A_eqv_type_ast T rT eqvT)                                                 
; A_eqv_brel_ast    := Ast_brel_eq_sum
                        (A_eqv_brel_ast S rS eqvS, 
                         A_eqv_brel_ast T rT eqvT)
                        
|}.


Definition A_eqv_sum : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S + T) 
:= λ S T eqvS eqvT,
  let eqS := A_eqv_eq S eqvS in
  let s  := A_eqv_witness S eqvS in
  let f  := A_eqv_new S eqvS in
  let ntS := A_eqv_not_trivial S eqvS in
  let eqT := A_eqv_eq T eqvT in
  let t  := A_eqv_witness T eqvT in
  let eqPS := A_eqv_proofs S eqvS in
  let eqPT := A_eqv_proofs T eqvT in  
  let symS := A_eqv_symmetric S eqS eqPS in
  let trnS := A_eqv_transitive S eqS eqPS in
  let symT := A_eqv_symmetric T eqT eqPT in
  let trnT := A_eqv_transitive T eqT eqPT in     
   {| 
      A_eqv_eq     := brel_sum eqS eqT  
    ; A_eqv_proofs := eqv_proofs_sum S T eqS eqT eqPS eqPT  
    ; A_eqv_witness := inl s
    ; A_eqv_new     := λ (d : S + T), match d with | inl _ => inr t | inr _ => inl s end
    ; A_eqv_not_trivial := brel_sum_not_trivial S T eqS eqT s t 
    ; A_eqv_exactly_two_d := inr (brel_sum_not_exactly_two S T eqS eqT symS trnS symT trnT s f t ntS)                                                            ; A_eqv_data  := λ d, (match d with inl s => DATA_inl (A_eqv_data S eqvS s) | inr t => DATA_inr (A_eqv_data T eqvT t) end)
    ; A_eqv_rep   := λ d, (match d with inl s => inl _ (A_eqv_rep S eqvS s) | inr t => inr _ (A_eqv_rep T eqvT t) end)
    ; A_eqv_finite_d := eqv_sum_finite_decidable S T eqS eqT symS symT (A_eqv_finite_d _ eqvS) (A_eqv_finite_d _ eqvT)
    ; A_eqv_ast   := Ast_eqv_sum (A_eqv_ast S eqvS, A_eqv_ast T eqvT)
   |}.


End ACAS.

Section CAS.

Definition eqv_sum_finite_certifiable {S T : Type} (fS : @check_is_finite S ) (fT : @check_is_finite T )
 :=  match fS, fT with
       Certify_Is_Not_Finite, _        => Certify_Is_Not_Finite
     | _, Certify_Is_Not_Finite        => Certify_Is_Not_Finite
     | Certify_Is_Finite f, Certify_Is_Finite g => Certify_Is_Finite (sum_enum S T f g)
     end. 
  

Definition eqv_sum : ∀ {S T : Type},  @eqv S -> @eqv T -> @eqv (S + T)
:= λ {S T} eqvS eqvT,
  let s := eqv_witness eqvS in
  let f := eqv_new eqvS in  
  let t := eqv_witness eqvT in
  let r := brel_sum (eqv_eq eqvS) (eqv_eq eqvT) in 
   {| 
      eqv_eq      := r
    ; eqv_certs         := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (S + T)
     ; eqv_reflexive      := @Assert_Reflexive (S + T)
     ; eqv_transitive     := @Assert_Transitive (S + T) 
     ; eqv_symmetric      := @Assert_Symmetric (S + T)
     ; eqv_type_ast       := Ast_type_sum (eqv_type_ast (eqv_certs eqvS), eqv_type_ast (eqv_certs eqvT))
     ; eqv_brel_ast       := Ast_brel_eq_sum (eqv_brel_ast (eqv_certs eqvS), eqv_brel_ast (eqv_certs eqvT))                         
     |}  
    ; eqv_witness := inl s 
    ; eqv_new     := λ (d : S + T), match d with | inl _ => inr t | inr _ => inl s end
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 r (inl s) (inl (f s)) (inr t))
    ; eqv_data  := λ d, (match d with inl s => DATA_inl (eqv_data eqvS s) | inr t => DATA_inr (eqv_data eqvT t) end)
    ; eqv_rep   := λ d, (match d with inl s => inl _ (eqv_rep eqvS s) | inr t => inr _ (eqv_rep eqvT t) end)
    ; eqv_finite_d  := eqv_sum_finite_certifiable (eqv_finite_d eqvS) (eqv_finite_d eqvT)
    ; eqv_ast   := Ast_eqv_sum (eqv_ast eqvS, eqv_ast eqvT)
   |}. 

End CAS.

Section Verify.

Lemma correct_eqv_sum_decidable (S : Type) (T : Type) (eqS : brel S) (eqT : brel T)
              (symS : brel_symmetric S eqS) (symT : brel_symmetric T eqT) 
              (FS : carrier_is_finite_decidable S eqS) 
              (FT : carrier_is_finite_decidable T eqT) : 
   eqv_sum_finite_certifiable (p2c_is_finite_check S eqS FS) (p2c_is_finite_check T eqT FT)
   =   
   p2c_is_finite_check (S + T) (brel_sum eqS eqT) (eqv_sum_finite_decidable S T eqS eqT symS symT FS FT). 
Proof. destruct FS as [[fS PS] | NFS]; destruct FT as [[fT PT]| NFT]; simpl; auto. Qed. 
  

Theorem correct_eqv_sum :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_sum (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S + T) (A_eqv_sum S T eS eT). 
Proof. intros S T eS eT.
       unfold eqv_sum, A_eqv_sum, A2C_eqv; simpl.
       unfold brel_sum_not_exactly_two.
       rewrite <- correct_eqv_sum_decidable.
       reflexivity. 
Qed. 
  
 
End Verify.   
