
Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List. 
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties. 

Open Scope list_scope.


(*
Lemma negb_bProp_congruence :
  ∀ (S : Type) (eq r : brel S), 
    brel_reflexive S eq -> 
    brel_congruence S eq r -> 
      ∀ (a : S), bProp_congruence S eq (λ y : S, negb (r y a)). 
Proof. intros S eq r refS cong a. unfold bProp_congruence. 
       intros s t E. assert (A := cong _ _ _ _ E (refS a)). 
       rewrite A. reflexivity. 
Defined. 




Lemma idempotent_uop_uop_congruence : ∀ (S : Type) (r : brel S)  (u : unary_op S), 
      brel_symmetric S r →
      brel_transitive S r →
      uop_idempotent S r u → 
          uop_uop_congruence S r u u. 
Proof. intros S r u symS transS idem. unfold uop_uop_congruence. intros s t H. 
       assert (A := idem s). assert (B := idem t). 
       assert (C := brel_congruence_self S r symS transS _ _ _ _ A B). rewrite H in C. assumption. 
Defined. 
 *)




(* false elim? *) 
Lemma abort : ∀ S : Type,  False  → S. 
Proof. intros S F. destruct F. Qed.

Lemma cons_not_nil : ∀ (S : Type) (a : S) (X : list S), a :: X ≠ nil. 
Proof. intros S a X. discriminate. Defined. 

Lemma list_lemma1 :          
  ∀ (S : Type) (l : list S) (s : S), s :: l = (s :: nil) ++ l. 
Proof. intros S l s. rewrite <- (List.app_nil_l l) at 1. 
       rewrite List.app_comm_cons. reflexivity. 
Defined. 


Lemma bool_disj : ∀ b : bool, (b = true) + (b = false). 
Proof. induction b; auto. Defined. 

Definition equal_true (x : bool) : option (x = true) := 
    match bool_disj x with 
    | inl p => Some p 
    | inr _ => None 
    end . 
Lemma eqb_bool_to_prop  : ∀ s t: bool, eqb s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto.  Defined. 

Lemma beq_nat_to_prop  : ∀ s t: nat, beq_nat s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto; discriminate. Defined. 


(*
Lemma orb_is_true_left : ∀ b1 b2 : bool, b1 || b2 = true → (b1 = true) + (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       left; reflexivity. 
       left. reflexivity. 
       right. reflexivity. 
       left. assumption. 
Defined. 

Lemma orb_is_true_right : ∀ b1 b2 : bool, (b1 = true) + (b2 = true) → b1 || b2 = true. 
Proof. induction b1; induction b2; simpl; intros [H | H]; auto. Defined. 

Lemma orb_is_false_left : ∀ b1 b2 : bool, b1 || b2 = false → (b1 = false) * (b2 = false). 
Proof. induction b1; induction b2; simpl; intros; split.   
       assumption. assumption. assumption. reflexivity. 
       reflexivity. assumption. reflexivity. reflexivity.
Defined. 

Lemma andb_is_true_left : ∀ b1 b2 : bool, b1 && b2 = true → (b1 = true) * (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       split; reflexivity. 
       split. reflexivity. assumption. 
       split. assumption. reflexivity. 
       split. assumption. assumption. 
Defined. 

Lemma andb_is_true_right : ∀ b1 b2 : bool, (b1 = true) * (b2 = true) → b1 && b2 = true. 
Proof. induction b1; induction b2; simpl. 
       intro. reflexivity. 
       intros [_ F]. assumption. 
       intros [F _]. assumption. 
       intros [F _]. assumption. 
Defined. 


Lemma andb_is_false_left : ∀ b1 b2 : bool, b1 && b2 = false → (b1 = false) + (b2 = false). 
Proof. induction b1; induction b2; simpl; intros.  
       discriminate. 
       right. reflexivity. 
       left. reflexivity. 
       right. reflexivity. 
Defined. 

Lemma andb_is_false_right : ∀ b1 b2 : bool, (b1 = false) + (b2 = false) → b1 && b2 = false. 
Proof. induction b1; induction b2; simpl. 
       intros [F | F]. assumption. assumption. 
       intros. reflexivity. 
       intros. reflexivity. 
       intros. reflexivity. 
Defined. 
*)






(*  Note: we could use andb_true_iff here, but it is opaque and so does 
    not play well with evaluation/extraction
*) 
Lemma andb_true_implies : ∀ b1 b2 : bool, b1 && b2 = true →  (b1 = true)  ∧  (b2 = true). 
Proof. 
   induction b1; induction b2. 
   intro. split; reflexivity. 
   simpl. intro. discriminate. 
   simpl. intro. discriminate. 
   simpl. intro. discriminate. 
Defined. 




Lemma negb_true_elim : ∀ b: bool, negb b = true → b = false. 
Proof. induction b; simpl; intro H. rewrite H. reflexivity. reflexivity. Defined. 

Lemma negb_false_elim : ∀ b: bool, negb b = false → b = true. 
Proof. induction b; simpl; intro H. reflexivity. rewrite H. reflexivity. Defined. 

Lemma negb_true_intro : ∀ b: bool, b = false → negb b = true. 
Proof. induction b; simpl; intro H. rewrite H. reflexivity. reflexivity. Defined. 

Lemma negb_false_intro : ∀ b: bool, b = true → negb b = false. 
Proof. induction b; simpl; intro H. reflexivity. rewrite H. reflexivity. Defined. 


(* cas-specific facts *) 



Definition brel_symmetric_dual (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = false) → (r t s = false). 

Definition brel_transitive_dual (S : Type) (r : brel S) := 
   ∀ (s t u : S), r s t = true -> r s u = false -> r t u = false.   



(* brel_transititivity_implies_dual

       (∀ s t u : S, r s t = true → r t u = true  → r s u = true)
      → ∀ s t u : S, r s t = true → r s u = false → r t u = false
*) 

Lemma brel_transititivity_implies_dual : ∀ (S: Type) (r : brel S), 
      brel_transitive S r -> brel_transitive_dual S r. 
Proof. 
      unfold brel_transitive, brel_transitive_dual.
      intros S r Tr s t u H K. 
      case_eq (r t u); intro F.
         rewrite (Tr s t u H F) in K. assumption. 
         reflexivity. 
Defined. 



Lemma brel_symmetric_implies_dual : ∀ (S: Type) (r : brel S), 
      brel_symmetric S r -> brel_symmetric_dual S r. 
Proof. unfold brel_symmetric, brel_symmetric_dual.
       intros S r symS s t H. 
       case_eq (r t s); intro F.
          rewrite (symS t s F) in H. assumption. 
          reflexivity. 
Defined. 

Lemma brel_transitive_dual_v2 (S : Type) (eq : brel S) (sym : brel_symmetric S eq) (trans : brel_transitive S eq) : 
  ∀ s t u: S, (eq s t = false) → (eq t u = true) → (eq s u = false).
Proof. intros s t u H1 H2.
       exact (brel_symmetric_implies_dual S eq sym _ _
                  (brel_transititivity_implies_dual S eq trans t u s H2
                          (brel_symmetric_implies_dual S eq sym _ _ H1))). 
Qed.        



Lemma brel_transitive_dual_v3 (S : Type) (eq : brel S) (sym : brel_symmetric S eq) (trans : brel_transitive S eq)  : 
  ∀ s t u: S, (eq s t = true) → (eq t u = false) → (eq s u = false).
Proof. intros s t u H1 H2.
       exact (brel_transititivity_implies_dual S eq trans t s u (sym _ _ H1) H2). 
Qed.        

(* NB : this is HOW symmetric should be DEFINED ! *) 
Lemma brel_sym_lemma : ∀ (S : Type) (r : brel S) (s u : S), 
      brel_symmetric S r → r s u = r u s. 
Proof. intros S r s u symS. 
       case_eq(r s u); intro K. apply symS in K. rewrite K. reflexivity. 
       apply (brel_symmetric_implies_dual _ _ symS) in K. rewrite K. reflexivity. 
Defined.        

Lemma sym_as_rewrite : ∀ {S : Type} {rS : brel S}, brel_symmetric S rS -> ∀ s1 s2 : S,  rS s1 s2 = rS s2 s1.
Proof. intros S rS symS s1 s2.
       case_eq(rS s1 s2); intro H1; case_eq(rS s2 s1); intro H2.
       reflexivity.
       rewrite (symS _ _ H1) in H2. discriminate.
       rewrite (symS _ _ H2) in H1. discriminate.
       reflexivity.
Qed.        



Definition brel_transitive_twist (S : Type) (r : brel S) := 
    (∀ a b c : S, r a b = true → r a c = true → r b c = true). 

Lemma brel_congruence_self : ∀ (S : Type) (r : brel S),  
      brel_symmetric S r →
      brel_transitive S r →
         brel_congruence S r r.  
Proof. intros S r symS transS s u t w H Q. 
       case_eq(r s u); intro K. 
          assert (J: r s w = true). apply (transS _ _ _ K Q). 
          assert (M: r t w = true). apply symS in H. 
             apply (transS _ _ _ H J). rewrite M. reflexivity. 
       assert (J := brel_transititivity_implies_dual _ _ transS _ _ _ H K).       
       apply (brel_symmetric_implies_dual _ _ symS) in J.        
       assert (M := brel_transititivity_implies_dual _ _ transS _ _ _ Q J).       
       apply (brel_symmetric_implies_dual _ _ symS) in M. rewrite M. reflexivity. 
Defined.        



(*************************************************** *)

Definition not_ex2 {S : Type} (eq : brel S) (s : S) (t : S) (u : S) : S -> (S -> S) :=
λ x y,
  if eq x y
  then x 
  else if eq x s
       then if eq y t
            then u 
            else t 
       else (* x <> s *)
            if eq y t 
            then if eq x u
                 then s 
                 else u 
            else (* x <> s, y <> t *)
                 if eq x u
                 then if eq y s 
                      then t 
                      else s
                 else (* x <> u, x <> s, y <> t *)
                      if eq x t
                      then if eq y s 
                           then u 
                           else s 
                      else t 
  . 

Lemma brel_at_least_thee_implies_not_exactly_two :
  ∀ (T : Type) (eq : brel T),
    brel_symmetric T eq ->
    brel_transitive T eq ->     
    brel_at_least_three T eq -> brel_not_exactly_two T eq.
Proof. intros T eq sy tr nalt. 
       exists (not_ex2 eq (fst (projT1 nalt)) (fst (snd (projT1 nalt))) (snd (snd (projT1 nalt)))). 
       destruct nalt as [[s [t u] ] [[P1 P2] P3]]. simpl. 
       intros  x y.  
       case_eq(eq x y); intro J.
       left; auto. 
       right. compute. rewrite J.
       case_eq(eq x s); intro K1.
          case_eq(eq y t); intro K2. 
             apply sy in K1. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K1 P2).        
             apply sy in K2. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K2 P3). auto.
             apply sy in K1. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K1 P1). auto.                   
          case_eq(eq y t); intro K2. 
             case_eq(eq x u); intro K3.  
                apply sy in K2. apply (brel_symmetric_implies_dual T eq sy) in P1. 
                rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K2 P1). auto.
                apply sy in K2. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K2 P3). auto.
             case_eq(eq x u); intro K3.               
                case_eq(eq y s); intro K4.
                    apply sy in K4. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K4 P1). 
                    apply sy in K3. apply (brel_symmetric_implies_dual T eq sy) in P3. 
                    rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K3 P3). auto.                    
                   split; auto.
                case_eq(eq x t); intro K5. 
                   case_eq(eq y s); intro K6. 
                      apply sy in K6. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K6 P2). auto.
                      split; auto.
                   split; auto. 
Defined. 


Section Conjunction. 

Variable S  : Type. 
Variable r1 : brel S.
Variable r2 : brel S. 

Notation "a <&> b"  := (brel_conjunction a b) (at level 15).


Lemma brel_conjunction_congruence : 
         ∀ (eq : brel S), brel_congruence S eq r1  → brel_congruence S eq r2  → 
               brel_congruence S eq (r1 <&> r2). 
Proof. unfold brel_congruence, brel_conjunction. 
       intros eq C1 C2 s t u v H K. 
       rewrite (C1 _ _ _ _ H K). rewrite (C2 _ _ _ _ H K). 
       reflexivity. 
Defined.

Lemma brel_conjunction_reflexive : 
              (brel_reflexive S r1) → (brel_reflexive S r2) 
               → brel_reflexive S (r1 <&> r2). 
Proof. unfold brel_reflexive, brel_conjunction. 
       intros ref1 ref2 s. rewrite (ref1 s), (ref2 s). simpl. reflexivity. 
Defined. 

Lemma brel_conjunction_not_reflexive_left : 
              (brel_not_reflexive S r1) 
               → brel_not_reflexive S (r1 <&> r2). 
Proof. unfold brel_not_reflexive, brel_conjunction. 
       intros [s P]. exists s. rewrite P. reflexivity. 
Defined. 

(*
Lemma brel_conjunction_symmetric : 
              (brel_symmetric S r1) → (brel_symmetric S r2) 
               → brel_symmetric S (r1 <&> r2). 
Proof. unfold brel_symmetric, brel_conjunction. 
     intros sym1 sym2 s1 s2 H.  
     apply andb_is_true_left in H. destruct H as [H_l H_r].  
     rewrite (sym1 _ _ H_l). rewrite (sym2 _ _ H_r). compute. reflexivity. 
Defined. 


Lemma brel_conjunction_transitive : 
        brel_transitive S r1 -> 
        brel_transitive S r2 -> 
            brel_transitive S (r1 <&> r2). 
Proof. unfold brel_transitive, brel_conjunction.  
     intros trans1 trans2 s1 s2 s3 H1 H2. 
     apply andb_is_true_left in H1. apply andb_is_true_left in H2. 
     destruct H1 as [L1 R1]. destruct H2 as [L2 R2]. 
     rewrite (trans1 _ _ _ L1 L2). rewrite (trans2 _ _ _ R1 R2). compute. reflexivity. 
Defined. 
*)

End Conjunction.

Section Complement.


Lemma brel_complement_symmetric : ∀ (S : Type) (r : brel S), 
          brel_symmetric S r -> brel_symmetric S (brel_complement r).  
Proof. unfold brel_symmetric, brel_complement. intros S r symS s t J. 
       apply negb_true_elim in J. 
       rewrite (brel_symmetric_implies_dual S r symS _ _ J). 
       compute. reflexivity. 
Defined. 


Lemma brel_complement_congruence : ∀ (S : Type) (r1 : brel S) (r2 : brel S), 
         brel_congruence S r1 r2 -> brel_congruence S r1 (brel_complement r2). 
Proof. unfold brel_congruence, brel_complement. 
       intros S r1 r2 cong s t u v H1 H2.
       assert (fact1 :=  cong _ _ _ _ H1 H2). 
       case_eq(r2 s t); intro Q. 
          rewrite <- fact1. rewrite Q. reflexivity. 
          rewrite <- fact1. rewrite Q. reflexivity. 
Defined.


End Complement.   

(***********************************)

(* move ? *) 
Definition bProp_congruence (S : Type) (r : brel S) (P : bProp S) := ∀ (a b : S),  r a b = true -> P a = P b.

