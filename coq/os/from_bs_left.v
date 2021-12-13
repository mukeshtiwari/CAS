Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.from_sg. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.
Require Import CAS.coq.os.theory.


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

Definition left_lte := brel_lte_left eq plus.
Definition right_lte := brel_lte_right eq plus.

Notation "a [=] b"   := (eq a b = true)          (at level 15).
Notation "a [+] b"   := (plus a b)          (at level 15).
Notation "a [*] b"   := (times a b)          (at level 15).       

(*

(* monotonicity *) 

Lemma os_lte_left_left_monotone : os_left_monotone (brel_lte_left eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := idemS s). apply symS in F0. 
       assert (F1 := congS _ _ _ _ F0 H).  
       assert (F2 : (s (+) s) (+) (t (+) u) == (s (+) t) (+) (s (+) u)).
          (* (s (+) s) (+) (t (+) u)
             assoc = s (+) (s (+) (t (+) u)) 
             assoc = s (+) ((s (+) t) (+) u) 
             comm  = s (+) ((t (+) s) (+) u) 
             assoc = s (+) (t (+) (s (+) u)) 
             assoc = (s (+) t) (+) (s (+) u)
          *) 
          assert (F4 := assoS s s (t (+) u)).           
          assert (F5 := assoS s t u). apply symS in F5.
          assert (F6 := congS _ _ _ _ (refS s) F5).          
          assert (F7 := trnS _ _ _ F4 F6). apply symS in F5.
          assert (F8 := commS s t). 
          assert (F9 := congS _ _ _ _ (refS s) (congS _ _ _ _ F8 (refS u))). 
          assert (F10 := trnS _ _ _ F7 F9).
          assert (F11 := assoS t s u).
          assert (F12 := congS _ _ _ _ (refS s) F11). 
          assert (F13 := trnS _ _ _ F10 F12).          
          assert (F14 := assoS s t (s (+) u)). apply symS in F14. 
          exact (trnS _ _ _ F13 F14).
       exact (trnS _ _ _ F1 F2). 
Qed. 

Lemma os_lte_right_left_monotone : os_left_monotone (brel_lte_right eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := os_lte_left_left_monotone s u t). compute in F0.
       assert (F1 := commS (s (+) u) (s (+) t)).
       assert (F2 := commS t u).
       assert (F3 := trnS _ _ _ H F2). 
       exact (trnS _ _ _ (F0 F3) F1). 
Qed.

Lemma os_lte_left_right_monotone : os_right_monotone (brel_lte_left eq bS) bS.
Proof. intros s t u. compute. intro H. 
       assert (F0 := os_lte_left_left_monotone s t u). compute in F0.
       assert (F1 := F0 H). 
       assert (F2 := commS t s).
       assert (F3 := commS u s).        
       assert (F4 := trnS _ _ _ F2 F1).
       assert (F5 := congS _ _ _ _ F2 F3). apply symS in F5.
       exact (trnS _ _ _ F4 F5). 
Qed. 

Lemma os_lte_right_right_monotone : os_right_monotone (brel_lte_right eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := os_lte_left_right_monotone s u t). compute in F0.
       assert (F1 := commS (u (+) s) (t (+) s)).
       assert (F2 := commS t u).
       assert (F3 := trnS _ _ _ H F2). 
       exact (trnS _ _ _ (F0 F3) F1). 
Qed.

(* bottoms *)

(* Note: New properties needed! *)

Definition os_bottom_equals_ann {S : Type} (r lte : brel S) (b : binary_op S)
:= { i : S & (brel_is_bottom S lte i) * (bop_is_ann S r b i)}.

Definition os_top_equals_id {S : Type} (r lte : brel S) (b : binary_op S)
  := { i : S & (brel_is_top S lte i) * (bop_is_id S r b i)}. 


Lemma os_lte_left_bottom_equals_ann (annS : bop_exists_ann S eq bS) : os_bottom_equals_ann eq (brel_lte_left eq bS) bS.
Proof. destruct annS as [ann P]. exists ann. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact A. 
Defined. 

Lemma os_lte_left_top_equals_id (idS : bop_exists_id S eq bS) : os_top_equals_id eq (brel_lte_left eq bS) bS.
Proof. destruct idS as [id P]. exists id. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact B. 
Defined. 

Lemma os_lte_right_bottom_equals_id (idS : bop_exists_id S eq bS) : os_exists_bottom_id_equal eq (brel_lte_right eq bS) bS.
Proof. destruct idS as [id P]. exists id. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact A. 
Defined. 

Lemma os_lte_right_top_equals_ann (annS : bop_exists_ann S eq bS) : os_exists_top_ann_equal eq (brel_lte_right eq bS) bS.
Proof. destruct annS as [ann P]. exists ann. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact B. 
Defined. 


*) 




Lemma os_from_bs_left_left_monotone
      (LD : bop_left_distributive S eq plus times) : os_left_monotone left_lte times.
Proof. intros a b c. compute.
       (* b [=] (b [+] c) → (a [*] b) [=] ((a [*] b) [+] (a [*] c)) *) 
       intro A. 
       assert (B := LD a b c).
       assert (C : (a [*] b) [=] (a [*] (b [+] c))).
          apply (congT _ _ _ _ (refS a) A). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_not_left_monotone
      (LD : bop_not_left_distributive S eq plus times) : os_not_left_monotone left_lte times.
Proof. destruct LD as [[a [b c]] A]. 
       exists (a, (b, c)). compute.
(*  b [=] (b [+] c) * (eq (a [*] b) ((a [*] b) [+] (a [*] c)) = false) *)       
Admitted.

Lemma os_from_bs_right_left_monotone
      (LD : bop_left_distributive S eq plus times) : os_left_monotone right_lte times.
Proof. intros a b c. compute.
       (* c [=] (b [+] c) → (a [*] c) [=] ((a [*] b) [+] (a [*] c)) *)
       intro A. 
       assert (B := LD a b c).
       assert (C : (a [*] c) [=] (a [*] (b [+] c))).
          apply (congT _ _ _ _ (refS a) A). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_right_monotone
      (RD : bop_right_distributive S eq plus times) : os_right_monotone left_lte times.
Proof. intros a b c. compute.
       (* b [=] (b [+] c) → (b [*] a) [=] ((b [*] a) [+] (c [*] a)) *) 
       intro A.
       assert (B := RD a b c).
       assert (C : (b [*] a) [=] ((b [+] c) [*] a)).
          apply (congT _ _ _ _ A (refS a)). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_not_right_monotone
      (RD : bop_not_right_distributive S eq plus times) : os_not_right_monotone left_lte times.
Proof. destruct RD as [[a [b c]] A]. 
       exists (a, (b, c)). compute.
(*
    b [=] (b [+] c) * (eq (b [*] a) ((b [*] a) [+] (c [*] a)) = false)
*)       
Admitted.


Lemma os_from_bs_right_right_monotone
      (RD : bop_right_distributive S eq plus times) : os_right_monotone right_lte times.
Proof. intros a b c. compute.
       (* c [=] (b [+] c) → (c [*] a) [=] ((b [*] a) [+] (c [*] a)) *) 
       intro A.
       assert (B := RD a b c).
       assert (C : (c [*] a) [=] ((b [+] c) [*] a)).
          apply (congT _ _ _ _ A (refS a)). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        


Lemma os_from_bs_left_left_increasing : 
   bops_left_left_absorptive S eq plus times -> os_left_increasing left_lte times.
Proof. intros A s t. compute. auto. Qed.

Lemma os_from_bs_left_not_left_increasing : 
   bops_not_left_left_absorptive S eq plus times -> os_not_left_increasing left_lte times.
Proof. intros [[s t] A]. exists (s, t). compute. auto. Qed. 

Lemma os_from_bs_left_right_increasing : 
   bops_left_right_absorptive S eq plus times -> os_right_increasing left_lte times.
Proof. intros A s t. compute. auto. Qed.

Lemma os_from_bs_left_not_right_increasing : 
   bops_not_left_right_absorptive S eq plus times -> os_not_right_increasing left_lte times.
Proof. intros [[s t] A]. exists (s, t). compute. auto. Qed.


(*  need "anti-absorptive, left_decreasing, ... ? 


Lemma os_from_bs_right_left_increasing : 
   bops_right_right_absorptive S eq plus times -> os_left_increasing right_lte times.
Proof. intros A s t. compute.
(*         (s [*] t) [=] (s [+] (s [*] t))  *) 
Admitted. 

Lemma os_from_bs_right_right_increasing : 
   bops_left_right_absorptive S eq plus times -> os_right_increasing right_lte times.
Proof. intros A s t. compute.
(*   (t [*] s) [=] (s [+] (t [*] s))  *)
Admitted. 
*) 



Lemma os_from_bs_left_left_structly_increasing : 
   bops_left_left_absorptive S eq plus times -> os_left_strictly_increasing left_lte times.
Proof. intros A s t. compute. split.
       (* need s [=] (s [+] (s [*] t))  *) 
       auto. 
       (* need eq (s [*] t) ((s [*] t) [+] s) = false 
        perhaps s [=] (s [+] (s [*] t))  * (s <> (s [*] t)) would be enough. 
       *)        
       admit. 
Admitted. 


Lemma os_from_bs_left_exists_top_ann_equal
      (P : bops_exists_id_ann_equal S eq plus times) :
           os_exists_top_ann_equal eq left_lte times.
Proof. destruct P as [a [A B]].
       exists a; split; auto.
       apply brel_lte_left_is_top; auto.
Defined.

Lemma os_from_bs_left_exists_top_ann_not_equal
      (P : bops_exists_id_ann_not_equal S eq plus times) :
           os_exists_top_ann_not_equal eq left_lte times.
Proof. destruct P as [[a b] [[A B] C]].
       exists (a, b). split; auto. split; auto. 
       apply brel_lte_left_is_top; auto.
Defined. 

Lemma os_from_bs_left_exists_bottom_id_equal
      (P : bops_exists_id_ann_equal S eq times plus) :
           os_exists_bottom_id_equal eq left_lte times.
Proof. destruct P as [a [A B]].
       exists a; split; auto.
       apply brel_lte_left_is_bottom; auto.
Defined. 

Lemma os_from_bs_left_exists_bottom_id_not_equal
      (P : bops_exists_id_ann_not_equal S eq times plus) :
           os_exists_bottom_id_not_equal eq left_lte times.
Proof. destruct P as [[a b] [[A B] C]].
       exists (b, a); split; auto. split; auto. 
       apply brel_lte_left_is_bottom; auto.
       case_eq(eq b a); intro H; auto. apply symS in H.
       rewrite H in C. discriminate C. 
Defined. 


End Theory.

Section ACAS.


Section Decide.

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus times : binary_op S). 
 
Definition os_from_bs_left_left_increasing_decide 
  (d : bops_left_left_absorptive_decidable S eq plus times) :
       os_left_increasing_decidable (brel_lte_left eq plus) times := 
   match d with 
   | inl li  => inl (os_from_bs_left_left_increasing S eq plus times li)
   | inr nli => inr (os_from_bs_left_not_left_increasing S eq plus times nli)
   end. 

Definition os_from_bs_left_right_increasing_decide 
  (d : bops_left_right_absorptive_decidable S eq plus times) :
       os_right_increasing_decidable (brel_lte_left eq plus) times := 
   match d with 
   | inl ri  => inl (os_from_bs_left_right_increasing S eq plus times ri)
   | inr nri => inr (os_from_bs_left_not_right_increasing S eq plus times nri)
   end.

Definition os_from_bs_left_exists_top_ann_equal_decidable
       (plus_comm : bop_commutative S eq plus)
       (P : exists_id_ann_decidable S eq plus times) :
            os_exists_top_ann_decidable S eq (brel_lte_left eq plus) times :=
  let sym := A_eqv_symmetric _ _ eqvP in
  let trn := A_eqv_transitive _ _ eqvP in   
  match P with 
  | Id_Ann_Proof_None _ _ _ _ (no_id, no_ann)         =>
       Top_Ann_Proof_None _ _ _ _ (brel_lte_left_not_exists_top S eq sym trn plus plus_comm no_id, no_ann) 
  | Id_Ann_Proof_Id_None  _ _ _ _ (exists_id, no_ann) =>
       Top_Ann_Proof_None_Ann _ _ _ _ (brel_lte_left_exists_top S eq sym trn plus plus_comm exists_id, no_ann)
  | Id_Ann_Proof_None_Ann _ _ _ _ (no_id, exists_ann) =>
       Top_Ann_Proof_Top_None _ _ _ _ (brel_lte_left_not_exists_top S eq sym trn plus plus_comm no_id, exists_ann) 
  | Id_Ann_Proof_Equal _ _ _ _ id_ann_eq              =>
       Top_Ann_Proof_Equal _ _ _ _ (os_from_bs_left_exists_top_ann_equal S eq plus times id_ann_eq) 
  | Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_eq      =>
       Top_Ann_Proof_Not_Equal _ _ _ _ (os_from_bs_left_exists_top_ann_not_equal S eq plus times id_ann_not_eq) 
end.


Definition os_from_bs_left_exists_bottom_id_equal_decidable
       (plus_comm : bop_commutative S eq plus)
       (P : exists_id_ann_decidable S eq times plus) :
            os_exists_bottom_id_decidable S eq (brel_lte_left eq plus) times :=
  let sym := A_eqv_symmetric _ _ eqvP in
  let trn := A_eqv_transitive _ _ eqvP in   
  match P with 
  | Id_Ann_Proof_None _ _ _ _ (no_id, no_ann)         =>
       Bottom_Id_Proof_None _ _ _ _ (???, no_id) 
  | Id_Ann_Proof_Id_None  _ _ _ _ (exists_id, no_ann) =>
       Bottom_Id_Proof_None_Ann _ _ _ _ (???, exists_id)
  | Id_Ann_Proof_None_Ann _ _ _ _ (no_id, exists_ann) =>
       Bottom_Id_Proof_Id_None _ _ _ _ (brel_lte_left_exists_bottom S eq sym trn plus plus_comm exists_ann, no_id)    
  | Id_Ann_Proof_Equal _ _ _ _ id_ann_eq              =>
       Bottom_Id_Proof_Equal _ _ _ _ (os_from_bs_left_exists_bottom_id_equal S r b1 b2 id_ann_eq) 
  | Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_eq      =>
       Bottom_Id_Proof_Not_Equal _ _ _ _ (os_from_bs_left_exists_bottom_id_not_equal S r b1 b2 id_ann_not_eq) 
end.
  
End Decide.     
  

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
  
