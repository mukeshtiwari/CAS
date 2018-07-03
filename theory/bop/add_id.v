Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 

Section AddId. 

Variable S  : Type. 
Variable rS : brel S.
Variable c  : cas_constant.
Variable bS : binary_op S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable congS : bop_congruence S rS bS.
(* Variable assS : bop_associative S rS bS. *) 


Notation "a <+> b"  := (brel_add_constant b a) (at level 15).
Notation "a [+] b"  := (bop_add_id b a)        (at level 15).
  
Lemma bop_add_id_congruence : bop_congruence (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl; intros H1 H2;auto; discriminate. Qed. 

Lemma bop_add_id_associative : bop_associative S rS bS -> bop_associative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros assS [s1 | t1] [s2 | t2] [s3 | t3]; simpl; auto. Qed. 

Lemma bop_add_id_idempotent : bop_idempotent S rS bS → bop_idempotent (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros idemS [s1 | t1]; simpl; auto. Qed. 

Lemma bop_add_id_not_idempotent : bop_not_idempotent S rS bS → bop_not_idempotent (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [s P]. exists (inr _ s). simpl. assumption. Defined. 

Lemma bop_add_id_commutative : bop_commutative S rS bS → bop_commutative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros commS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_id_not_commutative : bop_not_commutative S rS bS → bop_not_commutative (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t); simpl. assumption. Defined. 

Lemma bop_add_id_selective : bop_selective S rS bS → bop_selective (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros selS [s1 | t1] [s2 | t2]; simpl; auto. Qed. 

Lemma bop_add_id_not_selective : bop_not_selective S rS bS → bop_not_selective (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. intros [ [s1 s2] P]. exists (inr _ s1, inr _ s2). simpl. assumption. Defined. 

Lemma bop_add_id_not_is_left (s : S) : bop_not_is_left (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. exists (inl _ c, inr _ s). simpl. reflexivity. Defined. 

Lemma bop_add_id_not_is_right (s : S) : bop_not_is_right (with_constant S ) (c <+> rS) (c [+] bS). 
Proof. exists (inr _ s, inl _ c). simpl. reflexivity. Defined. 

Lemma bop_add_id_exists_id : bop_exists_id (with_constant S ) (c <+> rS) (c [+] bS).
Proof. exists (inl S c). intros [a | b]; compute; auto. Defined. 

Lemma bop_add_id_exists_ann : bop_exists_ann S rS bS -> bop_exists_ann (with_constant S ) (c <+> rS) (c [+] bS).
Proof. intros [annS pS]. exists (inr _ annS). intros [s | t]; compute; auto. Defined. 

Lemma bop_add_id_not_exists_ann (s : S) : bop_not_exists_ann S rS bS -> bop_not_exists_ann (with_constant S ) (c <+> rS) (c [+] bS).
Proof. intros naS. intros [x | x]. exists (inr _ s). compute; auto. destruct (naS x) as [y D].  exists (inr _ y). compute. assumption. Defined. 


Lemma bop_add_id_left_cancellative : bop_anti_left S rS bS -> bop_left_cancellative S rS bS -> 
        bop_left_cancellative (with_constant S) (brel_add_constant rS c) (bop_add_id bS c).
Proof. intros ax lc [c1 | s1] [c2 | s2 ] [c3 | s3]; simpl; auto.  
       rewrite ax. auto. intro H. apply symS in H. rewrite ax in H. assumption. apply lc. 
Defined. 

Lemma bop_add_id_not_left_cancellative : (bop_not_left_cancellative S rS bS) + (bop_not_anti_left S rS bS) -> 
        bop_not_left_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. intros [ [ [s [ t u]]  P ]| [ [s t] P ] ].
       exists (inr _ s, (inr _ t, inr _ u)); simpl. assumption. 
       exists (inr _ s, (inr _ t, inl _ c)); simpl. apply symS in P. auto.
Defined. 

Lemma bop_add_id_right_cancellative : (bop_anti_right S rS bS) -> bop_right_cancellative S rS bS -> 
        bop_right_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. intros ax lc [c1 | s1] [c2 | s2 ] [c3 | s3]; simpl; auto.  
       rewrite ax. auto. intro H. apply symS in H. rewrite ax in H. assumption. apply lc. 
Defined. 

Lemma bop_add_id_not_right_cancellative : (bop_not_right_cancellative S rS bS) + (bop_not_anti_right S rS bS) -> 
        bop_not_right_cancellative (with_constant S) (c <+> rS) (c [+] bS).
Proof. intros [ [ [s [ t  u]] P ] | [ [s  t] P ] ].
       exists (inr _ s, (inr _ t, inr _ u)); simpl. assumption. 
       exists (inr _ s, (inr _ t, inl _ c)); simpl. apply symS in P. auto.
Defined. 

Lemma bop_add_id_not_left_constant : bop_not_left_constant (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))). simpl. destruct (Pf wS) as [L R]. assumption. Defined. 

Lemma bop_add_id_not_right_constant : bop_not_right_constant (with_constant S) (c <+> rS) (c [+] bS).
Proof. exists (inl _ c, (inr _ wS, inr _ (f wS))). simpl. destruct (Pf wS) as [L R]. assumption. Defined. 

Lemma bop_add_id_not_anti_left : bop_not_anti_left (with_constant S) (c <+> rS) (c [+] bS).
Proof. unfold bop_not_anti_left. exists (inr wS, inl c); simpl. apply refS. Defined. 

Lemma bop_add_id_not_anti_right : bop_not_anti_right (with_constant S) (c <+> rS) (c [+] bS).
Proof. unfold bop_not_anti_right. exists (inr wS, inl c); simpl. apply refS. Defined. 

(* Decide *) 

Definition bop_add_id_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable (with_constant S ) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_id_selective selS)
   | inr not_selS   => inr _ (bop_add_id_not_selective not_selS)
   end. 

Definition bop_add_id_commutative_decide :
     bop_commutative_decidable S rS bS  → bop_commutative_decidable (with_constant S) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_id_commutative commS)
   | inr not_commS => inr _ (bop_add_id_not_commutative not_commS)
   end. 

Definition bop_add_id_idempotent_decide :
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable (with_constant S ) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_id_idempotent idemS)
   | inr not_idemS => inr _ (bop_add_id_not_idempotent not_idemS)
   end. 

Definition bop_add_id_exists_ann_decide : 
     bop_exists_ann_decidable S rS bS  → bop_exists_ann_decidable (with_constant S ) (c <+> rS) (c [+] bS)
:= λ dS,  
   match dS with 
   | inl eann  => inl _ (bop_add_id_exists_ann eann)
   | inr neann => inr _ (bop_add_id_not_exists_ann wS neann)
   end. 

Definition bop_add_id_left_cancellative_decide : 
     bop_anti_left_decidable S rS bS -> bop_left_cancellative_decidable S rS bS -> 
        bop_left_cancellative_decidable (with_constant S ) (c <+> rS) (c [+] bS)
:= λ ad lcd,  
   match ad with 
   | inl anti_left     => 
        match lcd with 
        | inl lcanc     => inl _ (bop_add_id_left_cancellative anti_left lcanc)
        | inr not_lcanc => inr _ (bop_add_id_not_left_cancellative (inl _ not_lcanc))
        end 
   | inr not_anti_left => inr _ (bop_add_id_not_left_cancellative (inr _ not_anti_left))
   end. 

Definition bop_add_id_right_cancellative_decide : 
     (bop_anti_right_decidable S rS bS) -> bop_right_cancellative_decidable S rS bS -> 
        bop_right_cancellative_decidable (with_constant S ) (c <+> rS) (c [+] bS)
:= λ ad lcd,  
   match ad with 
   | inl anti_right     => 
        match lcd with 
        | inl lcanc     => inl _ (bop_add_id_right_cancellative anti_right lcanc)
        | inr not_lcanc => inr _ (bop_add_id_not_right_cancellative (inl _ not_lcanc))
        end 
   | inr not_anti_right => inr _ (bop_add_id_not_right_cancellative (inr _ not_anti_right))
   end. 

End AddId. 