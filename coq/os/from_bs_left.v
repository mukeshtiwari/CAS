Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.

Require Import CAS.coq.theory.facts. 
Require Import CAS.coq.po.from_sg_left. 


  
Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq. 
Variable trnS : brel_transitive S eq. 


Variable plus     : binary_op S.
Variable times     : binary_op S.

Variable congP : bop_congruence S eq plus.
Variable assoP : bop_associative S eq plus.
Variable idemP : bop_idempotent S eq plus.
Variable commP : bop_commutative S eq plus.

Variable congT : bop_congruence S eq times.

Variable LD : bop_left_distributive S eq plus times.
Variable RD : bop_right_distributive S eq plus times. 

Definition lte := brel_lte_left eq plus.

Notation "a [=] b"   := (eq a b = true)          (at level 15).
Notation "a [+] b"   := (plus a b)          (at level 15).
Notation "a [*] b"   := (times a b)          (at level 15).       


Lemma os_from_bs_left_left_monotone : os_left_monotone S lte times.
Proof. intros a b c. compute. intro A. 
       assert (B := LD a b c).
       assert (C : (a [*] b) [=] (a [*] (b [+] c))).
          apply (congT _ _ _ _ (refS a) A). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        


Lemma os_from_bs_left_right_monotone : os_right_monotone S lte times.
Proof. intros a b c. compute. intro A. 
       assert (B := RD a b c).
       assert (C : (b [*] a) [=] ((b [+] c) [*] a)).
          apply (congT _ _ _ _ A (refS a)). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        




Lemma os_from_bs_left_left_increasing : 
   bops_left_left_absorptive S eq plus times -> os_left_increasing S lte times.
Proof. intros A s t. compute. auto. Qed.

Lemma os_from_bs_left_left_structly_increasing : 
   bops_left_left_absorptive S eq plus times -> os_left_strictly_increasing S lte times.
Proof. intros A s t. compute. split.
       (* need s [=] (s [+] (s [*] t))  *) 
       auto. 
       (* need eq (s [*] t) ((s [*] t) [+] s) = false 

        perhaps s [=] (s [+] (s [*] t))  * (s <> (s [*] t)) would be enough. 
       *)        
       admit. 
Admitted. 


Lemma os_from_bs_left_not_left_increasing : 
   bops_not_left_left_absorptive S eq plus times -> os_not_left_increasing S lte times.
Proof. intros [[s t] A]. exists (s, t). compute. auto. Qed. 



Definition os_from_bs_left_left_increasing_decide : 
   bops_left_left_absorptive_decidable S eq plus times -> os_left_increasing_decidable S lte times
:= λ d ,  
   match d with 
   | inl li  => inl (os_from_bs_left_left_increasing li)
   | inr nli => inr (os_from_bs_left_not_left_increasing nli)
   end. 

Lemma os_from_bs_left_right_increasing : 
   bops_left_right_absorptive S eq plus times -> os_right_increasing S lte times.
Proof. intros A s t. compute. auto. Qed. 


Lemma os_from_bs_left_not_right_increasing : 
   bops_not_left_right_absorptive S eq plus times -> os_not_right_increasing S lte times.
Proof. intros [[s t] A]. exists (s, t). compute. auto. Qed. 

Definition os_from_bs_left_right_increasing_decide : 
   bops_left_right_absorptive_decidable S eq plus times -> os_right_increasing_decidable S lte times
:= λ d ,  
   match d with 
   | inl ri  => inl (os_from_bs_left_right_increasing ri)
   | inr nri => inr (os_from_bs_left_not_right_increasing nri)
   end. 


Lemma os_from_bs_left_top_equals_ann (P : bops_id_equals_ann S eq plus times) : os_top_equals_ann S eq lte times.
Proof. destruct P as [a [A B]]. exists a; split; auto. apply po_from_sg_left_is_top; auto. Defined. 


Lemma os_from_bs_left_not_top_equals_ann (P : bops_not_id_equals_ann S eq plus times) : os_not_top_equals_ann S eq lte times.
Proof. intro s. destruct (P s) as [A | A]; auto. left. 
       destruct A as [u B].  exists u. 
       destruct B as [B | B]; compute. 
          case_eq(eq u (u [+] s)); intro C; auto.
          apply symS in C. assert (D := commP s u). 
          rewrite (trnS _ _ _ D C) in B. discriminate B.
          case_eq(eq u (u [+] s)); intro C; auto.
          apply symS in C. rewrite C in B. discriminate B.
Defined. 


Definition os_from_bs_left_top_equals_ann_decide : 
   bops_id_equals_ann_decidable S eq plus times -> os_top_equals_ann_decidable S eq lte times
:= λ d ,  
   match d with 
   | inl iea  => inl (os_from_bs_left_top_equals_ann iea)
   | inr niea => inr (os_from_bs_left_not_top_equals_ann niea)
   end. 


Lemma os_from_bs_left_bottom_equals_id (P : bops_id_equals_ann S eq times plus) : os_bottom_equals_id S eq lte times.
Proof. destruct P as [a [A B]]. exists a; split; auto. apply po_from_sg_left_is_bottom; auto. Defined. 


Lemma os_from_bs_left_not_bottom_equals_id (P : bops_not_id_equals_ann S eq times plus) : os_not_bottom_equals_id S eq lte times.
Proof. intro s. destruct (P s) as [A | A]; auto. left. 
       destruct A as [u B].  exists u. 
       destruct B as [B | B]; compute. 
          case_eq(eq s (s [+] u)); intro C; auto.
          apply symS in C. rewrite C in B. discriminate B.
          case_eq(eq s (s [+] u)); intro C; auto.
          assert (D := commP u s).  apply symS in C.
          rewrite (trnS _ _ _ D C) in B. discriminate B.
Defined. 


Definition os_from_bs_left_bottom_equals_id_decide : 
   bops_id_equals_ann_decidable S eq times plus -> os_bottom_equals_id_decidable S eq lte times
:= λ d ,  
   match d with 
   | inl iea  => inl (os_from_bs_left_bottom_equals_id iea)
   | inr niea => inr (os_from_bs_left_not_bottom_equals_id niea)
   end. 



End Theory.

Section ACAS.

Definition os_from_bs_left_proofs (S: Type) (eq : brel S) (plus times : binary_op S) :
  eqv_proofs S eq ->
  bop_congruence S eq times -> 
  semiring_proofs S eq plus times ->
  monotone_os_proofs S (brel_lte_left eq plus) times 
:= λ E tcong P,
let ref := A_eqv_reflexive S eq E in
let trn := A_eqv_transitive S eq E in  (* note: symmetry is not needed *) 
{|
  A_mos_left_monotonic     := os_from_bs_left_left_monotone S eq ref trn plus times tcong  (A_semiring_left_distributive S eq plus times P)
; A_mos_right_monotonic    := os_from_bs_left_right_monotone S eq ref trn plus times tcong  (A_semiring_right_distributive S eq plus times P)

; A_mos_left_increasing_d  := os_from_bs_left_left_increasing_decide S eq plus times (A_semiring_left_left_absorptive_d S eq plus times P)
; A_mos_right_increasing_d := os_from_bs_left_right_increasing_decide S eq plus times (A_semiring_left_right_absorptive_d S eq plus times P)
|}. 


Lemma bops_id_equals_ann_to_exists_ann (S: Type) (eq : brel S) (b1 b2 : binary_op S): 
  bops_id_equals_ann S eq b1 b2 -> (bop_exists_ann S eq b2).
Proof. intros [i [idP annP]]. exists i; auto. Defined. 



Definition from_bs_left_top_bottom_proofs (S: Type) (eq : brel S) (eqvP : eqv_proofs S eq)
           (plus : binary_op S) (times : binary_op S) (commP : bop_commutative S eq plus): 
  add_ann_mul_id_proofs S eq plus times -> top_bottom_ann_id_with_id_proofs S eq (lte S eq plus) times 
:= λ P, 
let symS := A_eqv_symmetric S eq eqvP in 
let trnS := A_eqv_transitive S eq eqvP in 
{|
  A_top_ann_d := os_from_bs_left_top_equals_ann_decide S eq symS trnS plus times commP
                          (A_add_ann_mul_id_plus_id_is_times_ann_d S eq plus times P)
; A_bottom_id :=  os_from_bs_left_bottom_equals_id S eq symS plus times
                          (A_add_ann_mul_id_times_id_is_plus_ann S eq plus times P)                                                    
|}.

(*
Definition A_monotone_mposg_from_predioid (S : Type) : A_predioid_with_id S -> A_monotone_posg S
  := λ PDWI,
let eqv   := A_pdwid_eqv S PDWI in
let eq    := A_eqv_eq S eqv in                            
let eqvP  := A_eqv_proofs S eqv in
let plus  := A_pdwid_plus S PDWI in
let times := A_pdwid_times S PDWI in                                                 
let lte   := brel_lte_left eq plus in      
let PSP   := A_pdwid_times_proofs S PDWI in
let PSR   := A_pdwid_proofs S PDWI in
let tcong := A_msg_congruence S eq times PSP in
let commP := A_sg_CI_commutative S eq plus (A_pdwid_plus_proofs S PDWI) in                                                            
let annP := bops_id_equals_ann_to_exists_ann S eq times plus 
              (A_add_ann_mul_id_times_id_is_plus_ann S eq plus times (A_pdwid_id_ann_proofs S PDWI)) in 
let id_d :=  A_add_ann_mul_id_plus_id_d S eq plus times (A_pdwid_id_ann_proofs S PDWI) in 
{|     
  A_mposg_eqv          := eqv
; A_mposg_lte          := lte 
; A_mposg_times        := A_pdwid_times S PDWI 
; A_mposg_lte_proofs   := po_from_sg_left_proofs S eq eqvP plus id_d annP (A_pdwid_plus_proofs S PDWI) 
; A_mposg_times_proofs := PSP
; A_mposg_top_bottom   := from_bs_left_top_bottom_proofs S eq eqvP plus times commP (A_pdwid_id_ann_proofs S PDWI)
; A_mposg_proofs       := os_from_bs_left_proofs S eq plus times eqvP tcong PSR
; A_mposg_ast          := Ast_mposg_from_bs (A_pdwid_ast S PDWI)  
|}.
*)
  
End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  