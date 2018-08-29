Require Import Coq.Bool.Bool. 
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.theory.facts. 

Section Theory.

  Variable S : Type.
  Variable r : brel S.
  Variable c : cas_constant.
  Variable b1 b2 : binary_op S.

  Variable wS : S. 
  Variable refS : brel_reflexive S r. 
  Variable symS : brel_symmetric S r.

Notation "a <+> b"    := (brel_add_constant b a) (at level 15).
Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).


Lemma bops_add_id_add_ann_id_equals_ann : bops_id_equals_ann (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).   
Proof. unfold bops_id_equals_ann. 
       assert (is_id : bop_is_id (with_constant S) (c <+> r) (c [+id] b1) (inl c)). 
           intros [c' | s ]; compute; auto. 
       assert (is_ann : bop_is_ann (with_constant S) (c <+> r) (c [+ann] b2) (inl c)). 
           intros [c' | s ]; compute; auto. 
       exists (inl _ c). split; assumption. 
Defined. 

Lemma bops_add_id_add_ann_ann_equals_id :    
      bops_id_equals_ann S r b2 b1 -> 
           bops_id_equals_ann (with_constant S) (c <+> r) (c [+ann] b2) (c [+id] b1).
Proof. unfold bops_id_equals_ann. 
       intros [i [Pi Pa]].
       assert (is_id : bop_is_id (with_constant S) (c <+> r) (c [+ann] b2) (inr i)). 
           intros [c' | s ]; compute; auto. 
       assert (is_ann : bop_is_ann (with_constant S) (c <+> r) (c [+id] b1) (inr i)). 
           intros [c' | s ]; compute; auto. 
       exists (inr _ i). split; assumption. 
Defined. 


Lemma bops_add_id_add_ann_not_ann_equals_id :    
      bops_not_id_equals_ann S r b2 b1 -> 
           bops_not_id_equals_ann (with_constant S) (c <+> r) (c [+ann] b2) (c [+id] b1) .
Proof. unfold bops_not_id_equals_ann. 
       intros H [ci | s'].
       destruct (H wS) as [ [s' [P | Q] ] | [s' [P | Q] ] ]. 
       left. exists (inr _ s'). compute. left. reflexivity. 
       left. exists (inr _ s'). compute. left. reflexivity. 
       right. exists (inr _ s'). compute. left. reflexivity.
       right. exists (inr _ s'). compute. left. reflexivity.
       destruct (H s') as [ [s'' [P | Q] ] | [s'' [P | Q] ] ]. 
       left. exists (inr _ s''). compute. rewrite P. left. reflexivity. 
       left. exists (inr _ s''). compute. rewrite Q. right. reflexivity. 
       right. exists (inr _ s''). compute. rewrite P. left. reflexivity.
       right. exists (inr _ s''). compute. rewrite Q. right. reflexivity.
Defined. 


Lemma bops_add_id_add_ann_left_distributive  :
     bop_left_distributive S r b1 b2 ->   
        bop_left_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_distributive  : 
     bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 [s2 s3]] nldS]. 
       exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 

Lemma bops_add_id_add_ann_right_distributive  : 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_distributive  : 
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 [s2 s3]] nldS]. exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 
       

(* left left *) 
Lemma bops_add_id_add_ann_left_left_absorptive  : 
     bops_left_left_absorptive S r b1 b2 -> 
        bops_left_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2). 
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_left_absorptive : 
     bops_not_left_left_absorptive S r b1 b2 -> 
        bops_not_left_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

(* left right *) 
Lemma bops_add_id_add_ann_left_right_absorptive  : 
     bops_left_right_absorptive S r b1 b2 -> 
        bops_left_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_left_right_absorptive : 
     bops_not_left_right_absorptive S r b1 b2 -> 
        bops_not_left_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right left *) 
Lemma bops_add_id_add_ann_right_left_absorptive  : 
     bops_right_left_absorptive S r b1 b2 -> 
        bops_right_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_left_absorptive : 
     bops_not_right_left_absorptive S r b1 b2 -> 
        bops_not_right_left_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(* right right *) 
Lemma bops_add_id_add_ann_right_right_absorptive  : 
     bops_right_right_absorptive S r b1 b2 -> 
        bops_right_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_id_add_ann_not_right_right_absorptive : 
     bops_not_right_right_absorptive S r b1 b2 -> 
        bops_not_right_right_absorptive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

(* experiment 

Lemma bops_add_id_add_ann_left_left_dependent_distributive  : 
     bops_left_left_dependent_distributive S r b1 b2 -> 
        bops_left_left_dependent_distributive (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; intro H; auto. Qed.
*) 

(* Decide *)

Definition bops_add_zero_left_distributive_decide : 
     bop_left_distributive_decidable S r b1 b2 -> 
         bop_left_distributive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_distributive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_distributive nldS)
   end. 

Definition bops_add_zero_right_distributive_decide : 
     bop_right_distributive_decidable S r b1 b2 -> 
        bop_right_distributive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_distributive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_distributive nldS)
   end. 


Definition bops_add_zero_left_left_absorptive_decide : 
     bops_left_left_absorptive_decidable S r b1 b2 -> 
        bops_left_left_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_left_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_left_absorptive nldS)
   end. 

Definition bops_add_zero_left_right_absorptive_decide : 
     bops_left_right_absorptive_decidable S r b1 b2 -> 
        bops_left_right_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_right_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_right_absorptive nldS)
   end. 


Definition bops_add_zero_right_left_absorptive_decide : 
     bops_right_left_absorptive_decidable S r b1 b2 -> 
        bops_right_left_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_left_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_left_absorptive nldS)
   end. 

Definition bops_add_zero_right_right_absorptive_decide : 
     bops_right_right_absorptive_decidable S r b1 b2 -> 
        bops_right_right_absorptive_decidable (with_constant S) (c <+> r) (c [+id] b1) (c [+ann] b2)
:= λ dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_right_absorptive ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_right_absorptive nldS)
   end.


Definition bops_add_zero_ann_equals_id_decide :
     bops_id_equals_ann_decidable S r b2 b1 -> 
        bops_id_equals_ann_decidable (with_constant S) (c <+> r) (c [+ann] b2) (c [+id] b1)
:= λ dS, 
   match dS with 
   | inl pS  => inl _ (bops_add_id_add_ann_ann_equals_id pS)
   | inr npS => inr _ (bops_add_id_add_ann_not_ann_equals_id npS)
   end. 

End Theory.

Section ACAS.

Definition bs_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S) (s : S), 
     eqv_proofs S rS -> 
     bs_proofs S rS plusS timesS -> 
        bs_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id plusS c)
           (bop_add_ann timesS c)
:= λ S rS c plusS timesS s eqvS pS, 
{|
  A_bs_left_distributive_d    := 
     bops_add_zero_left_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_left_distributive_d S rS plusS timesS pS) 

; A_bs_right_distributive_d   := 
     bops_add_zero_right_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_right_distributive_d S rS plusS timesS pS) 

; A_bs_left_left_absorptive_d      := 
     bops_add_zero_left_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)

; A_bs_left_right_absorptive_d      := 
     bops_add_zero_left_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)

; A_bs_right_left_absorptive_d     := 
     bops_add_zero_right_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)

; A_bs_right_right_absorptive_d     := 
     bops_add_zero_right_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)

; A_bs_plus_id_is_times_ann_d := 
     inl _ (bops_add_id_add_ann_id_equals_ann S rS c plusS timesS (A_eqv_reflexive S rS eqvS))

; A_bs_times_id_is_plus_ann_d :=  
    bops_add_zero_ann_equals_id_decide S rS c plusS timesS s 
      (A_eqv_reflexive S rS eqvS)
      (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
|}. 

Definition A_bs_add_zero : ∀ (S : Type),  A_bs S -> cas_constant -> A_bs (with_constant S) 
:= λ S bsS c, 
{| 
     A_bs_eqv          := A_eqv_add_constant S (A_bs_eqv S bsS) c 
   ; A_bs_plus         := bop_add_id  (A_bs_plus S bsS) c
   ; A_bs_times        := bop_add_ann  (A_bs_times S bsS) c
   ; A_bs_plus_proofs  := sg_proofs_add_id S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_plus S bsS)
                                (A_eqv_witness S (A_bs_eqv S bsS))
                                (A_eqv_new S (A_bs_eqv S bsS))
                                (A_eqv_not_trivial S (A_bs_eqv S bsS))
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_plus_proofs S bsS) 
   ; A_bs_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_bs_eqv S bsS)) c 
                                (A_bs_times S bsS)
                                (A_eqv_witness S (A_bs_eqv S bsS))
                                (A_eqv_new S (A_bs_eqv S bsS))
                                (A_eqv_not_trivial S (A_bs_eqv S bsS))                                
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_times_proofs S bsS) 
   ; A_bs_proofs       := bs_proofs_add_zero S _ c 
                                (A_bs_plus S bsS) 
                                (A_bs_times S bsS)
                                (A_eqv_witness S (A_bs_eqv S bsS))                                
                                (A_eqv_proofs S (A_bs_eqv S bsS)) 
                                (A_bs_proofs S bsS)
   ; A_bs_plus_ast     := Ast_bop_add_id (c, A_bs_plus_ast S bsS)
   ; A_bs_times_ast    := Ast_bop_add_ann (c, A_bs_times_ast S bsS)                                                      
   ; A_bs_ast          := Ast_bs_add_zero (c, A_bs_ast S bsS)
|}. 

(*
Definition distributive_lattice_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS meet ->      
     distributive_lattice_proofs S rS join meet -> 
        distributive_lattice_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet eqvS p_meet p_dl, 
{|
  A_distributive_lattice_absorptive        := 
    bops_add_id_add_ann_left_left_absorptive S rS c join meet
       (A_eqv_reflexive S rS eqvS)
       (A_distributive_lattice_absorptive S rS join meet p_dl)
; A_distributive_lattice_absorptive_dual   := 
    bops_add_ann_add_id_left_left_absorptive S rS c meet join
      (A_eqv_symmetric S rS eqvS)
      (A_sg_CI_idempotent S rS meet p_meet)                                             
      (A_distributive_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_distributive_lattice_distributive      := 
    bops_add_id_add_ann_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_distributive_lattice_distributive S rS join meet p_dl)
|}.


Definition A_distributive_lattice_add_zero : ∀ (S : Type),  A_distributive_lattice S -> cas_constant -> A_distributive_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_distributive_lattice_eqv          := A_eqv_add_constant S (A_distributive_lattice_eqv S bsS) c 
   ; A_distributive_lattice_join         := bop_add_id (A_distributive_lattice_join S bsS) c
   ; A_distributive_lattice_meet        := bop_add_ann (A_distributive_lattice_meet S bsS) c
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_join S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                 
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_proofs S bsS) 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_meet S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                 
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_proofs S bsS) 
   ; A_distributive_lattice_proofs       := distributive_lattice_proofs_add_zero S _ c 
                                (A_distributive_lattice_join S bsS) 
                                (A_distributive_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_proofs S bsS)                                 
                                (A_distributive_lattice_proofs S bsS)
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_add_zero (c, A_distributive_lattice_ast S bsS)
|}. 


Definition lattice_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS ->
     sg_CI_proofs S rS join ->          
     sg_CI_proofs S rS meet ->      
     lattice_proofs S rS join meet -> 
        lattice_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet eqvS p_join p_meet p_dl, 
{|
  A_lattice_absorptive        := 
    bops_add_id_add_ann_left_left_absorptive S rS c join meet
       (A_eqv_reflexive S rS eqvS)
       (A_lattice_absorptive S rS join meet p_dl)
; A_lattice_absorptive_dual   := 
    bops_add_ann_add_id_left_left_absorptive S rS c meet join
      (A_eqv_symmetric S rS eqvS)
      (A_sg_CI_idempotent S rS meet p_meet)                                             
      (A_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_lattice_distributive_d      := 
     bops_add_zero_left_distributive_decide S rS c join meet 
        (A_eqv_reflexive S rS eqvS)
        (A_lattice_distributive_d S rS join meet p_dl)
; A_lattice_distributive_dual_d      := 
     bops_add_one_left_distributive_decide S rS c meet join
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (inl _ (A_sg_CI_idempotent S rS meet p_meet))
        (inl _ (A_lattice_absorptive_dual S rS join meet p_dl))
        (inl _ (bops_left_right_absorptive_implies_right_left S rS meet join
                  (A_eqv_reflexive S rS eqvS)                                                       
                  (A_eqv_transitive S rS eqvS)
                  (A_sg_CI_congruence S rS meet p_meet)
                  (A_sg_CI_commutative S rS meet p_meet)
                  (A_sg_CI_commutative S rS join p_join)
                  (bops_left_left_absorptive_implies_left_right S rS meet join
                        (A_eqv_reflexive S rS eqvS)                                                          
                        (A_eqv_transitive S rS eqvS)
                        (A_sg_CI_congruence S rS meet p_meet)
                        (A_sg_CI_commutative S rS join p_join)
                        (A_lattice_absorptive_dual S rS join meet p_dl)
                  ) 
               )
        ) 
        (A_lattice_distributive_dual_d S rS join meet p_dl)         
|}.


Definition A_lattice_add_zero : ∀ (S : Type),  A_lattice S -> cas_constant -> A_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_lattice_eqv          := A_eqv_add_constant S (A_lattice_eqv S bsS) c 
   ; A_lattice_join         := bop_add_id (A_lattice_join S bsS) c
   ; A_lattice_meet        := bop_add_ann (A_lattice_meet S bsS) c
   ; A_lattice_join_proofs  := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_join S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))                                 
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_proofs S bsS) 
   ; A_lattice_meet_proofs := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_meet S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))                                 
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_meet_proofs S bsS) 
   ; A_lattice_proofs       := lattice_proofs_add_zero S _ c 
                                (A_lattice_join S bsS) 
                                (A_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_lattice_eqv S bsS))
                                (A_lattice_join_proofs S bsS)                                                                 
                                (A_lattice_meet_proofs S bsS)                                 
                                (A_lattice_proofs S bsS)
   ; A_lattice_ast  := Ast_lattice_add_zero (c, A_lattice_ast S bsS)
|}. 

*) 
Definition semiring_proofs_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S) (s : S), 
     eqv_proofs S rS -> 
     semiring_proofs S rS join meet -> 
        semiring_proofs 
           (with_constant S) 
           (brel_add_constant rS c)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet s eqvS srp, 
{|
  A_semiring_left_distributive        :=
    bops_add_id_add_ann_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_left_distributive S rS join meet srp)
    
; A_semiring_right_distributive       :=
    bops_add_id_add_ann_right_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_right_distributive S rS join meet srp)

; A_semiring_plus_id_is_times_ann_d   :=
     inl _ (bops_add_id_add_ann_id_equals_ann S rS c join meet (A_eqv_reflexive S rS eqvS))    

; A_semiring_times_id_is_plus_ann_d   :=
    bops_add_zero_ann_equals_id_decide S rS c join meet s
      (A_eqv_reflexive S rS eqvS)
      (A_semiring_times_id_is_plus_ann_d S rS join meet srp)
                                                                     
; A_semiring_left_left_absorptive_d   :=
    bops_add_zero_left_left_absorptive_decide S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_left_left_absorptive_d S rS join meet srp)

; A_semiring_left_right_absorptive_d  :=
     bops_add_zero_left_right_absorptive_decide S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_left_right_absorptive_d S rS join meet srp)
|}.


Definition A_dioid_add_zero : ∀ (S : Type),  A_dioid S -> cas_constant -> A_dioid (with_constant S) 
:= λ S bsS c, 
{| 
     A_dioid_eqv          := A_eqv_add_constant S (A_dioid_eqv S bsS) c 
   ; A_dioid_plus         := bop_add_id (A_dioid_plus S bsS) c
   ; A_dioid_times         := bop_add_ann (A_dioid_times S bsS) c
   ; A_dioid_plus_proofs  := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_dioid_eqv S bsS)) c 
                                (A_dioid_plus S bsS)
                                (A_eqv_witness S (A_dioid_eqv S bsS))                                 
                                (A_eqv_proofs S (A_dioid_eqv S bsS)) 
                                (A_dioid_plus_proofs S bsS) 
   ; A_dioid_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_dioid_eqv S bsS)) c 
                                (A_dioid_times S bsS)
                                (A_eqv_witness S (A_dioid_eqv S bsS))
                                (A_eqv_new S (A_dioid_eqv S bsS))
                                (A_eqv_not_trivial S (A_dioid_eqv S bsS)) 
                                (A_eqv_proofs S (A_dioid_eqv S bsS)) 
                                (A_dioid_times_proofs S bsS) 
   ; A_dioid_proofs       := semiring_proofs_add_zero S _ c 
                                (A_dioid_plus S bsS) 
                                (A_dioid_times S bsS)
                                (A_eqv_witness S (A_dioid_eqv S bsS))                                
                                (A_eqv_proofs S (A_dioid_eqv S bsS))
                                (A_dioid_proofs S bsS)
   ; A_dioid_plus_ast     := Ast_bop_add_id (c, A_dioid_plus_ast S bsS)
   ; A_dioid_times_ast    := Ast_bop_add_ann (c, A_dioid_times_ast S bsS)   
   ; A_dioid_ast          := Ast_dioid_add_zero (c, A_dioid_ast S bsS)
|}. 


Definition A_semiring_add_zero : ∀ (S : Type),  A_semiring S -> cas_constant -> A_semiring (with_constant S) 
:= λ S bsS c, 
{| 
     A_semiring_eqv          := A_eqv_add_constant S (A_semiring_eqv S bsS) c 
   ; A_semiring_plus         := bop_add_id (A_semiring_plus S bsS) c
   ; A_semiring_times        := bop_add_ann (A_semiring_times S bsS) c
   ; A_semiring_plus_proofs  := sg_C_proofs_add_id S 
                                (A_eqv_eq S (A_semiring_eqv S bsS)) c 
                                (A_semiring_plus S bsS)
                                (A_eqv_witness S (A_semiring_eqv S bsS))
                                (A_eqv_new S (A_semiring_eqv S bsS))
                                (A_eqv_not_trivial S (A_semiring_eqv S bsS))                                 
                                (A_eqv_proofs S (A_semiring_eqv S bsS)) 
                                (A_semiring_plus_proofs S bsS) 
   ; A_semiring_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_semiring_eqv S bsS)) c 
                                (A_semiring_times S bsS)
                                (A_eqv_witness S (A_semiring_eqv S bsS))
                                (A_eqv_new S (A_semiring_eqv S bsS))
                                (A_eqv_not_trivial S (A_semiring_eqv S bsS))                                 
                                (A_eqv_proofs S (A_semiring_eqv S bsS)) 
                                (A_semiring_times_proofs S bsS) 
   ; A_semiring_proofs       := semiring_proofs_add_zero S _ c 
                                (A_semiring_plus S bsS) 
                                (A_semiring_times S bsS)
                                (A_eqv_witness S (A_semiring_eqv S bsS))                                
                                (A_eqv_proofs S (A_semiring_eqv S bsS))
                                (A_semiring_proofs S bsS)
   ; A_semiring_plus_ast     := Ast_bop_add_id (c, A_semiring_plus_ast S bsS)
   ; A_semiring_times_ast    := Ast_bop_add_ann (c, A_semiring_times_ast S bsS)                                
   ; A_semiring_ast          := Ast_semiring_add_zero (c, A_semiring_ast S bsS)
|}. 
 

End ACAS.

Section CAS.


Definition bops_add_zero_left_distributive_check : 
   ∀ {S : Type},  
     check_left_distributive (S := S) -> 
     check_left_distributive (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Left_Distributive => Certify_Left_Distributive (S := (with_constant S)) 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (S := (with_constant S)) (inr s1, (inr s2, inr _ s3))
   end. 

Definition bops_add_zero_right_distributive_check : 
   ∀ {S : Type},  
     check_right_distributive (S := S) -> 
     check_right_distributive (S := (with_constant S)) 
:= λ {S} dS,  
   match dS with 
   | Certify_Right_Distributive => Certify_Right_Distributive (S := (with_constant S)) 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (S := (with_constant S)) (inr _ s1, (inr _ s2, inr _ s3))
   end.

Definition bops_add_zero_distributive_dual_check : 
   ∀ {S : Type},  @check_left_distributive_dual S -> @check_left_distributive_dual (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Left_Distributive_Dual               => Certify_Left_Distributive_Dual 
   | Certify_Not_Left_Distributive_Dual (s1, (s2, s3)) => Certify_Not_Left_Distributive_Dual (inr s1, (inr s2, inr _ s3))
   end. 


Definition bops_add_zero_left_left_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive (S := (with_constant S))
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
     Certify_Not_Left_Left_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 


Definition bops_add_zero_left_right_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive (S := (with_constant S))
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
     Certify_Not_Left_Right_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_left_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive (S := (with_constant S))
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
     Certify_Not_Right_Left_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_right_absorptive_check : 
   ∀ {S : Type} (s : S), 
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := (with_constant S))
:= λ {S} s dS ,  
match dS with 
| Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive (S := (with_constant S))
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
     Certify_Not_Right_Right_Absorptive (S := (with_constant S)) (inr _ s1, inr _ s2)
end.


Definition bops_add_zero_times_id_is_plus_ann_check : 
   ∀ {S : Type}, @check_times_id_equals_plus_ann S-> @check_times_id_equals_plus_ann (with_constant S)
:= λ {S} dS,  
  match dS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann  
  end . 


Definition bs_certs_add_zero : 
  ∀ {S : Type} (s : S), bs_certificates (S := S) -> bs_certificates (S := (with_constant S))
:= λ {S} s pS, 
{|
  bs_left_distributive_d    := 
     bops_add_zero_left_distributive_check (bs_left_distributive_d pS) 
; bs_right_distributive_d   := 
     bops_add_zero_right_distributive_check (bs_right_distributive_d pS) 

; bs_left_left_absorptive_d      := 
     bops_add_zero_left_left_absorptive_check s (bs_left_left_absorptive_d pS)
; bs_left_right_absorptive_d      := 
     bops_add_zero_left_right_absorptive_check s (bs_left_right_absorptive_d pS)
; bs_right_left_absorptive_d     := 
     bops_add_zero_right_left_absorptive_check s (bs_right_left_absorptive_d pS)
; bs_right_right_absorptive_d     := 
     bops_add_zero_right_right_absorptive_check s (bs_right_right_absorptive_d pS)

; bs_plus_id_is_times_ann_d :=  Certify_Plus_Id_Equals_Times_Ann  
; bs_times_id_is_plus_ann_d :=  bops_add_zero_times_id_is_plus_ann_check (bs_times_id_is_plus_ann_d pS)
|}. 


Definition bs_add_zero : ∀ {S : Type},  @bs S -> cas_constant -> @bs (with_constant S)
  := λ {S} bsS c,
let s :=   eqv_witness (bs_eqv bsS) in
let f :=   eqv_new (bs_eqv bsS) in   
{| 
     bs_eqv         := eqv_add_constant (bs_eqv bsS) c 
   ; bs_plus        := bop_add_id (bs_plus bsS) c
   ; bs_times       := bop_add_ann (bs_times bsS) c
   ; bs_plus_certs  := sg_certs_add_id c s f (bs_plus_certs bsS) 
   ; bs_times_certs := sg_certs_add_ann c s f (bs_times_certs bsS) 
   ; bs_certs       := bs_certs_add_zero s (bs_certs bsS)
   ; bs_plus_ast    := Ast_bop_add_id (c, bs_plus_ast bsS)
   ; bs_times_ast   := Ast_bop_add_ann (c, bs_times_ast bsS)                                                    
   ; bs_ast         := Ast_bs_add_zero (c, bs_ast bsS)
|}. 


Definition semiring_certs_add_zero : 
  ∀ {S : Type} (s : S), @semiring_certificates S  -> @semiring_certificates (with_constant S) 
:= λ S s pS, 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann  
; semiring_times_id_is_plus_ann_d   :=
  match semiring_times_id_is_plus_ann_d pS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann  
  end 
; semiring_left_left_absorptive_d   := bops_add_zero_left_left_absorptive_check s (semiring_left_left_absorptive_d pS)
; semiring_left_right_absorptive_d  := bops_add_zero_left_right_absorptive_check s (semiring_left_right_absorptive_d pS)
|}.

Definition dioid_add_zero : ∀ (S : Type),  @dioid S -> cas_constant -> @dioid (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (dioid_eqv bsS) in
let f :=   eqv_new (dioid_eqv bsS) in   
{| 
     dioid_eqv         := eqv_add_constant (dioid_eqv bsS) c 
   ; dioid_plus        := bop_add_id (dioid_plus bsS) c
   ; dioid_times       := bop_add_ann (dioid_times bsS) c
   ; dioid_plus_certs  := sg_CI_certs_add_id c (dioid_plus_certs bsS)
   ; dioid_times_certs := sg_certs_add_ann c s f (dioid_times_certs bsS)
   ; dioid_certs       := semiring_certs_add_zero s (dioid_certs bsS)
   ; dioid_plus_ast    := Ast_bop_add_id (c, dioid_plus_ast bsS)
   ; dioid_times_ast   := Ast_bop_add_ann (c, dioid_times_ast bsS)
   ; dioid_ast         := Ast_dioid_add_zero (c, dioid_ast bsS)
|}. 

Definition semiring_add_zero : ∀ (S : Type),  @semiring S -> cas_constant -> @semiring (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (semiring_eqv bsS) in
let f :=   eqv_new (semiring_eqv bsS) in   
{| 
     semiring_eqv         := eqv_add_constant (semiring_eqv bsS) c 
   ; semiring_plus        := bop_add_id (semiring_plus bsS) c
   ; semiring_times       := bop_add_ann (semiring_times bsS) c
   ; semiring_plus_certs  := sg_C_certs_add_id c s f (semiring_plus_certs bsS)
   ; semiring_times_certs := sg_certs_add_ann c s f (semiring_times_certs bsS)
   ; semiring_certs       := semiring_certs_add_zero s (semiring_certs bsS)
   ; semiring_plus_ast    := Ast_bop_add_id (c, semiring_plus_ast bsS)
   ; semiring_times_ast   := Ast_bop_add_ann (c, semiring_times_ast bsS)                                                      
   ; semiring_ast         := Ast_semiring_add_zero (c, semiring_ast bsS)
|}. 

Definition distributive_lattice_certs_add_zero : 
  ∀ {S : Type} (c : cas_constant), @distributive_lattice_certificates S -> @distributive_lattice_certificates (with_constant S) 
:= λ {S} c dlc ,
{|
  distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
; distributive_lattice_distributive      := Assert_Left_Distributive 
|}.

Definition distributive_lattice_add_zero : ∀ (S : Type),  @distributive_lattice S -> cas_constant -> @distributive_lattice (with_constant S) 
:= λ S bsS c,
{| 
     distributive_lattice_eqv         := eqv_add_constant (distributive_lattice_eqv bsS) c 
   ; distributive_lattice_join        := bop_add_id (distributive_lattice_join bsS) c
   ; distributive_lattice_meet        := bop_add_ann (distributive_lattice_meet bsS) c
   ; distributive_lattice_join_certs  := sg_CI_certs_add_id c (distributive_lattice_join_certs bsS)
   ; distributive_lattice_meet_certs  := sg_CI_certs_add_ann c (distributive_lattice_meet_certs bsS)
   ; distributive_lattice_certs       := distributive_lattice_certs_add_zero c (distributive_lattice_certs bsS )
   ; distributive_lattice_join_ast    := Ast_bop_add_id (c, distributive_lattice_join_ast bsS)
   ; distributive_lattice_meet_ast    := Ast_bop_add_ann (c, distributive_lattice_meet_ast bsS) 
   ; distributive_lattice_ast         := Ast_distributive_lattice_add_zero (c, distributive_lattice_ast bsS)
|}. 


Definition lattice_certs_add_zero : 
  ∀ {S : Type}, @lattice_certificates S -> @lattice_certificates (with_constant S) 
:= λ {S} pS, 
{|
  lattice_absorptive          := Assert_Left_Left_Absorptive
; lattice_absorptive_dual     := Assert_Left_Left_Absorptive_Dual
; lattice_distributive_d      := bops_add_zero_left_distributive_check (lattice_distributive_d pS) 
; lattice_distributive_dual_d := bops_add_zero_distributive_dual_check (lattice_distributive_dual_d pS) 
|}.

Definition lattice_add_zero : ∀ (S : Type),  @lattice S -> cas_constant -> @lattice (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (lattice_eqv bsS) in
let f :=   eqv_new (lattice_eqv bsS) in   
{| 
     lattice_eqv         := eqv_add_constant (lattice_eqv bsS) c 
   ; lattice_join        := bop_add_id (lattice_join bsS) c
   ; lattice_meet        := bop_add_ann (lattice_meet bsS) c
   ; lattice_join_certs  := sg_CI_certs_add_id c (lattice_join_certs bsS)
   ; lattice_meet_certs  := sg_CI_certs_add_ann c (lattice_meet_certs bsS)
   ; lattice_certs       := lattice_certs_add_zero (lattice_certs bsS)
   ; lattice_join_ast    := Ast_bop_add_id (c, lattice_join_ast bsS)
   ; lattice_meet_ast    := Ast_bop_add_ann (c, lattice_meet_ast bsS)                             
   ; lattice_ast         := Ast_lattice_add_zero (c, lattice_ast bsS)
|}. 

End CAS.

Section Verify.


Lemma bops_add_zero_left_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)     
  (pS : bop_left_distributive_decidable S rS plusS timesS), 
  p2c_left_distributive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_left_distributive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_distributive_check (p2c_left_distributive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 [s2 s3]] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  bops_add_zero_right_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
    (eqvS : eqv_proofs S rS)         
    (pS : bop_right_distributive_decidable S rS plusS timesS), 
  p2c_right_distributive (with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_right_distributive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_distributive_check (p2c_right_distributive S rS plusS timesS pS). 
Proof. intros S c rS plusS timesS eqvS [ ldS | [ [s1 [s2 s3]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_zero_times_id_equals_plus_ann_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_id_equals_ann_decidable S rS timesS plusS), 
  p2c_times_id_equals_plus_ann (with_constant S)
     (brel_add_constant rS c)
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_ann_equals_id_decide S rS c 
        plusS timesS s (A_eqv_reflexive S rS eqvS) pS) 
  =
  bops_add_zero_times_id_is_plus_ann_check (p2c_times_id_equals_plus_ann S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ L | R]; compute; reflexivity. Qed. 



Lemma bops_add_zero_left_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_left_left_absorptive_decidable S rS plusS timesS), 
  p2c_left_left_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_left_left_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_left_absorptive_check s 
     (p2c_left_left_absorptive S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_zero_left_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_left_right_absorptive_decidable S rS plusS timesS), 
  p2c_left_right_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_left_right_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_left_right_absorptive_check s (p2c_left_right_absorptive S rS plusS timesS pS).
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  bops_add_zero_right_left_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_right_left_absorptive_decidable S rS plusS timesS), 
  p2c_right_left_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_right_left_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_left_absorptive_check s (p2c_right_left_absorptive S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma  bops_add_zero_right_right_absorbtive_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_right_right_absorptive_decidable S rS plusS timesS), 
  p2c_right_right_absorptive(with_constant S)
     (brel_add_constant rS c)                                  
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (bops_add_zero_right_right_absorptive_decide S rS c plusS timesS (A_eqv_reflexive S rS eqvS) pS)
  = 
  bops_add_zero_right_right_absorptive_check  s (p2c_right_right_absorptive S rS plusS timesS pS). 
Proof. intros S c rS s plusS timesS eqvS [ ldS | [ [s1 s2] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  correct_bs_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (bsS : bs_proofs S rS plusS timesS), 
    P2C_bs (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (bs_proofs_add_zero S rS c plusS timesS s eqvS bsS)
    =
    bs_certs_add_zero s (P2C_bs S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS. 
       unfold bs_certs_add_zero, bs_proofs_add_zero, P2C_bs, P2C_sg; simpl. 
       rewrite bops_add_zero_left_distributive_check_correct. 
       rewrite bops_add_zero_right_distributive_check_correct. 
       rewrite bops_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite (bops_add_zero_left_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_left_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_right_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_right_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       reflexivity. 
Defined. 

Theorem correct_bs_add_zero: ∀ (S : Type) (bsS: A_bs S) (c : cas_constant), 
   bs_add_zero (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_zero S bsS c). 
Proof. intros S bsS c. 
       unfold bs_add_zero, A_bs_add_zero, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_certs_add_id. 
       rewrite correct_bs_certs_add_zero. 
       reflexivity. 
Qed. 

Lemma  correct_semiring_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (bsS : semiring_proofs S rS plusS timesS), 
    P2C_semiring (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (semiring_proofs_add_zero S rS c plusS timesS s eqvS bsS)
    =
    semiring_certs_add_zero s (P2C_semiring S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS. 
       unfold semiring_certs_add_zero, semiring_proofs_add_zero, P2C_semiring, P2C_sg; simpl. 
       rewrite bops_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite (bops_add_zero_left_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (bops_add_zero_left_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       reflexivity. 
Defined. 


Theorem correct_semiring_add_zero: ∀ (S : Type) (pS: A_semiring S) (c : cas_constant), 
   semiring_add_zero S (A2C_semiring S pS) c 
   =
   A2C_semiring (with_constant S) (A_semiring_add_zero S pS c). 
Proof. intros S pS c. 
       unfold semiring_add_zero, A_semiring_add_zero, A2C_semiring; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_C_certs_add_id. 
       rewrite correct_semiring_certs_add_zero. 
       reflexivity. 
Qed. 


Theorem correct_dioid_add_zero: ∀ (S : Type) (pS: A_dioid S) (c : cas_constant), 
   dioid_add_zero S (A2C_dioid S pS) c 
   =
   A2C_dioid (with_constant S) (A_dioid_add_zero S pS c). 
Proof. intros S pS c. 
       unfold dioid_add_zero, A_dioid_add_zero, A2C_dioid; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_semiring_certs_add_zero. 
       reflexivity. 
Qed. 

(*
Lemma  correct_distributive_lattice_certs_add_zero : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (c:  cas_constant) 
    (eqvS : eqv_proofs S rS) 
    (pmeet : sg_CI_proofs S rS meet)
    (dlp : distributive_lattice_proofs S rS join meet), 
    P2C_distributive_lattice _ _ _ _ (distributive_lattice_proofs_add_zero S rS c join meet eqvS pmeet dlp)
    =
    distributive_lattice_certs_add_zero c (P2C_distributive_lattice S rS join meet dlp).
Proof. intros S rS join meet c eqvS pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_add_zero : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S) (c : cas_constant), 
   distributive_lattice_add_zero S (A2C_distributive_lattice S distributive_latticeS) c 
   =
   A2C_distributive_lattice (with_constant S) (A_distributive_lattice_add_zero S distributive_latticeS c). 
Proof. intros S distributive_latticeS c. 
       unfold distributive_lattice_add_zero, A_distributive_lattice_add_zero, A2C_distributive_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_distributive_lattice_certs_add_zero. 
       reflexivity. 
Qed. 


Lemma  correct_lattice_certs_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (joinS meetS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (pjoin : sg_CI_proofs S rS joinS)
    (pmeet : sg_CI_proofs S rS meetS) 
    (bsS : lattice_proofs S rS joinS meetS), 
    P2C_lattice (with_constant S) 
       (brel_add_constant rS c) 
       (bop_add_id joinS c) 
       (bop_add_ann meetS c) 
       (lattice_proofs_add_zero S rS c joinS meetS eqvS pjoin pmeet bsS)
    =
    lattice_certs_add_zero (P2C_lattice S rS joinS meetS bsS). 
Proof. intros S c rS s joinS meetS eqvS pjoin pmeet bsS. 
       unfold lattice_certs_add_zero, lattice_proofs_add_zero, P2C_lattice, P2C_sg; simpl. 
       rewrite bops_add_zero_left_distributive_check_correct.
       (* below, ugly! what is broken? *) 
       unfold bops_add_one_left_distributive_decide; simpl.
       unfold bops_add_zero_distributive_dual_check.
       case_eq (A_lattice_distributive_dual_d S rS joinS meetS bsS); intros b P; simpl. 
       reflexivity.
       destruct b as [ [s1 [s2 s3]] Q]. simpl. 
       reflexivity.        
Defined. 
*)   
 
End Verify.   
  