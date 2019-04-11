Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce. 

Section Operations.

Definition is_minimal_in : ∀ {S : Type}, brel S → brel S → brel2 S (finite_set S)
:= λ {S} eq lte a X, 
      if brel_set eq nil X
      then false 
      else (bProp_forall S (λ y, bop_or (uop_not (lte y a)) (eq y a))) X. 

Definition uop_minset : ∀ {S : Type}, brel S → brel S → unary_op (finite_set S) 
:= λ {S} eq lte X, uop_filter (λ a, is_minimal_in eq lte a X) X. 

Definition brel_minset : ∀ {S : Type}, brel S → brel S → brel (finite_set S) 
:= λ {S} eq lt,  brel_reduce (brel_set eq) (uop_minset eq lt). 

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
Variable lteAntiSym : brel_antisymmetric S rS lteS. 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a !=S b" := (rS a b = false) (at level 15).
Notation "a <<= b" := (lteS a b = true) (at level 15).
Notation "a <<!= b" := (lteS a b = false) (at level 15).

Lemma brel_minset_congruence : brel_congruence (finite_set S) (brel_minset rS lteS) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_congruence.
       apply brel_set_congruence; auto.
Qed.

Lemma brel_minset_reflexive : brel_reflexive (finite_set S) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_reflexive.
       apply brel_set_reflexive; auto.
Qed.
  
Lemma brel_minset_symmetric : brel_symmetric (finite_set S) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_symmetric.
       apply brel_set_symmetric; auto.
Qed.


Lemma brel_minset_transitive : brel_transitive (finite_set S) (brel_minset rS lteS).
Proof. unfold brel_minset. 
       apply brel_reduce_transitive.
       apply brel_set_transitive; auto.
Qed.


Definition brel_minset_new : unary_op (finite_set S)
  := λ X, if brel_set rS nil X then wS :: nil else nil.

Lemma brel_set_nil_nil : brel_set rS nil nil = true.
Proof. compute. reflexivity.   Qed.

Lemma brel_set_nil_notnil : ∀ (s : S) (X : finite_set S), brel_set rS nil (s :: X) = false.
Proof. intros s X. compute. reflexivity.   Qed.

Lemma brel_set_notnil_nil : ∀ (s : S) (X : finite_set S), brel_set rS  (s :: X) nil = false.
Proof. intros s X. apply (brel_symmetric_implies_dual _ _ (brel_set_symmetric S rS) nil (s :: X) (brel_set_nil_notnil s X)). Qed. 

Lemma is_minial_in_singleton : ∀ (s : S), is_minimal_in rS lteS s (s :: nil) = true.
Proof. intro s. unfold is_minimal_in.   rewrite brel_set_nil_notnil. unfold bProp_forall.
       unfold List.forallb. unfold bop_or. rewrite lteRefl. simpl. rewrite refS. simpl. reflexivity. 
Qed.

Lemma uop_minset_singleton (s : S) : uop_minset rS lteS (s :: nil) = s :: nil.
Proof. compute. rewrite lteRefl. rewrite refS. reflexivity. Qed.

Lemma uop_minset_nil : uop_minset rS lteS nil = nil.
Proof. compute. reflexivity. Qed.

Lemma brel_minset_nil_singleton (s : S) : brel_minset rS lteS nil (s :: nil) = false.
Proof. unfold brel_minset. unfold brel_reduce. rewrite uop_minset_nil. rewrite uop_minset_singleton. apply brel_set_nil_notnil. Qed. 

Lemma brel_minset_singleton_nil (s : S) : brel_minset rS lteS (s :: nil) nil = false.
Proof. apply (brel_symmetric_implies_dual _ _ brel_minset_symmetric nil (s :: nil) (brel_minset_nil_singleton s)). Qed.   


Lemma brel_minset_not_minimal (s : S) (X : finite_set S) (H : is_minimal_in rS lteS s X = false) :
 brel_minset rS lteS (s::X) X = true.
Admitted.   
  
Lemma uop_minset_nil_elim (X : finite_set S) : uop_minset rS lteS X = nil -> X = nil.
Proof. induction X; intro H. reflexivity.
       case_eq(is_minimal_in rS lteS a X); intro J. 
          admit.        
          apply brel_minset_not_minimal in J. 
Admitted.

Lemma in_set_nil (s : S) : in_set rS nil s = false.
Proof. compute. reflexivity. Qed.

Lemma in_set_minset_elim (a : S) (X : finite_set S) :
        in_set rS (uop_minset rS lteS X) a = true -> (in_set rS X a = true) * (∀ (s : S), in_set rS X s = true -> (rS a s = true) + (lteS s a = false)). 
Proof. intro H. 
       unfold uop_minset in H. unfold uop_filter in H. 
       apply in_set_filter_elim in H.
       destruct H as [L R]. split. 
          exact R.
          intros s K. case_eq(rS a s); intro J; auto. 
             right. 
             admit. (* Need a lemma *)           
       unfold bProp_congruence. admit. (* is_minimal_in_congruence *)
Admitted.

Lemma in_set_minset_false_elim (a : S) (X : finite_set S) :
        in_set rS (uop_minset rS lteS X) a = false -> (in_set rS X a = false) + {s : S & (in_set rS X s = true) * (rS a s = false) * (lteS s a = true)}.
Proof. intro H. 
       case_eq(in_set rS X a); intro K; auto.
          right. 
Admitted.        



(*
Lemma  uop_minset_not_empty (X : finite_set S) (H: brel_set rS nil X = false) : brel_set rS nil (uop_minset rS lteS X) = false.
Proof.  destruct X.
        compute in H. discriminate H.
        case_eq(brel_set rS nil (uop_minset rS lteS (s :: X))); intro K; auto. 
           apply brel_set_elim_prop in K; auto. destruct K as [L R].
           assert (J := R s).  rewrite in_set_nil in J.
           case_eq(in_set rS (uop_minset rS lteS (s :: X)) s); intro M.
           assert (N := J M). discriminate N. 
                      
Qed. 
*)


Lemma  uop_minset_not_empty (X : finite_set S) (H: brel_set rS nil X = false) : brel_set rS nil (uop_minset rS lteS X) = false.
Proof.  destruct X.
        compute in H. discriminate H.
        case_eq(brel_set rS nil (uop_minset rS lteS (s :: X))); intro K; auto. 
           apply brel_set_nil in K. apply uop_minset_nil_elim in K. 
           discriminate K.                       
Qed. 
           
Lemma brel_minset_nil_notnil (s : S) (X : finite_set S) : brel_minset rS lteS nil (s :: X) = false.
Proof. unfold brel_minset. unfold brel_reduce. rewrite uop_minset_nil.
       assert (K : brel_set rS nil (s :: X) = false). apply brel_set_nil_notnil. 
       apply uop_minset_not_empty; auto. 
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
Admitted.   

Lemma minset_lemma2 (s : S) (X : finite_set S) (H : brel_minset rS lteS X (s :: nil) = true) : in_set rS X s = true.
Proof. induction X. rewrite minset_lemma1 in H. discriminate H. 
       apply in_set_cons_intro; auto.
       admit. 
Admitted. 

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

Lemma minset_enum_lemma (f : unit → list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (X : finite_set S) : 
  in_set (brel_minset rS lteS) (minset_enum f tt) X = true.
Admitted. 


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

Definition eqv_proofs_brel_minset : ∀ (S : Type) (r : brel S) (lteS : brel S), eqv_proofs S r → eqv_proofs (finite_set S) (brel_minset r lteS)
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
  let lteS  := A_po_brel S poS in
  let lteP  := A_po_proofs S poS in 
  let lte_congS := A_po_congruence S rS lteS lteP in 
  let lte_refS  := A_po_reflexive S rS lteS lteP in  
  let lte_asymS := A_po_antisymmetric S rS lteS lteP in
  let lte_trnS  := A_po_transitive S rS lteS lteP in  
   {| 
      A_eqv_eq            := brel_minset rS lteS 
    ; A_eqv_proofs        := eqv_proofs_brel_minset S rS lteS eqP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS lte_asymS 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS lteS lte_refS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS lteS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS lteS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS lte_asymS (A_eqv_finite_d S eqvS)
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
  let lteS := po_brel poS in 
   {| 
      eqv_eq            := brel_minset rS lteS 
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
