Require Import CAS.coq.common.base.

Section LatticeTheory.  (* (S, join, meet) *) 

Variable S : Type.
Variable eqv : brel S.


Variable ref : brel_reflexive S eqv. 
Variable sym : brel_symmetric S eqv.
Variable trn : brel_transitive S eqv.

Variable join : binary_op S.  
Variable meet : binary_op S.
 
Variable j_cng : bop_congruence S eqv join.
Variable j_ass : bop_associative S eqv join.
Variable j_com : bop_commutative S eqv join.
Variable j_idm : bop_idempotent S eqv join.

Variable m_cng : bop_congruence S eqv meet.
Variable m_ass : bop_associative S eqv meet.
Variable m_com : bop_commutative S eqv meet.
Variable m_idm : bop_idempotent S eqv meet.

Variable abs      : bops_left_left_absorptive S eqv join meet.
Variable abs_dual : bops_left_left_absorptive S eqv meet join. 

Notation "a == b"    := (eqv a b = true) (at level 30).
Notation "a != b"    := (eqv a b = false) (at level 15).
Notation "a (j) b"   := (join a b) (at level 15).
Notation "a (m) b"   := (meet a b) (at level 15).

(* H : a (m) b = a 
    so b (j) (a (m) b) = b (j) a (cng) 
                       = a (j) b (com)

   b = b (j) (b (m) a)  (abs) 
     = b (j) (a (m) b)  (com) 
     = a (j) b          (trn) 
*)
Lemma lattice_meet_to_join_left : ∀ (a b : S),  a == a (m) b → b == a (j) b.
Proof. intros a b H.
       assert (F1 := abs b a).
       assert (F2 := m_com a b). apply sym in F2.       
       assert (F4 := j_cng _ _ _ _ (ref b) F2).
       assert (F5 := trn _ _ _ F1 F4). apply sym in H. 
       assert (F6 := j_cng _ _ _ _ (ref b) H).
       assert (F7 := trn _ _ _ F5 F6).
       assert (F8 := j_com b a).
       assert (F9 := trn _ _ _ F7 F8).
       exact F9.
Defined. 

(* H : a = b (m) a 
   b = b (j) (b (m) a)  (abs) 
     = b (j) a          (H, cng) 
*)
Lemma lattice_meet_to_join_right : ∀ (a b : S),  a == b (m) a → b == b (j) a.
Proof. intros a b H.
       assert (F1 := abs b a).
       assert (F2 := j_cng _ _ _ _ (ref b) H). apply sym in F2. 
       assert (F3 := trn _ _ _ F1 F2). 
       exact F3.
Defined. 

(* H : a (j) b = a 
    so b (m) (a (j) b) = b (m) a (cng) 
                       = a (m) b (com)

   b = b (m) (b (j) a)  (abs) 
     = b (m) (a (j) b)  (com) 
     = a (m) b          (trn) 
*)
Lemma lattice_join_to_meet_left : ∀ (a b : S),  a == a (j) b → b == a (m) b.
Proof. intros a b H.
       assert (F1 := abs_dual b a).
       assert (F2 := j_com a b). apply sym in F2.       
       assert (F4 := m_cng _ _ _ _ (ref b) F2).
       assert (F5 := trn _ _ _ F1 F4). apply sym in H. 
       assert (F6 := m_cng _ _ _ _ (ref b) H).
       assert (F7 := trn _ _ _ F5 F6).
       assert (F8 := m_com b a).
       assert (F9 := trn _ _ _ F7 F8).
       exact F9.
Qed.

(* H : a = b (j) a 
   b = b (m) (b (j) a)  (abs_dual) 
     = b (j) a          (H, cng) 
*)
Lemma lattice_join_to_meet_right : ∀ (a b : S),  a == b (j) a → b == b (m) a.
Proof. intros a b H.
       assert (F1 := abs_dual b a).
       assert (F2 := m_cng _ _ _ _ (ref b) H). apply sym in F2. 
       assert (F3 := trn _ _ _ F1 F2). 
       exact F3.
Defined. 


Lemma lattice_one_is_join_annihilator: ∀ (i : S),  bop_is_id S eqv meet i → bop_is_ann S eqv join i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_meet_to_join_left in R.
       split.
       assert (F1 := j_com a i).
       assert (F2 := trn _ _ _ R F1).
       apply sym. exact F2.       
       apply sym. exact R.
Defined. 

Lemma lattice_join_annihilator_is_one : ∀ (i : S),  bop_is_ann S eqv join i  → bop_is_id S eqv meet i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_join_to_meet_left in L.
       split.
       apply sym. exact L.       
       assert (F1 := m_com i a).
       assert (F2 := trn _ _ _ L F1).
       apply sym. exact F2.       
Qed.        

Lemma lattice_not_one_is_not_join_annihilator: ∀ (i : S),  bop_not_is_id S eqv meet i → bop_not_is_ann S eqv join i. 
Proof. intros i H. destruct H as [w [H | H]]; exists w.
       left.
       case_eq(eqv (i (j) w) i); intro J.
          apply sym in J. apply lattice_join_to_meet_left in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
       right.
       case_eq(eqv (w (j) i) i); intro J.
          apply sym in J. apply lattice_join_to_meet_right in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
Qed.        

Lemma lattice_zero_is_meet_annihilator: ∀ (i : S),  bop_is_id S eqv join i → bop_is_ann S eqv meet i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_join_to_meet_left in R.
       split.
       assert (F1 := m_com a i).
       assert (F2 := trn _ _ _ R F1).
       apply sym. exact F2.       
       apply sym. exact R.
Qed.


Lemma lattice_meet_annihilator_is_zero : ∀ (i : S),  bop_is_ann S eqv meet i  → bop_is_id S eqv join i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_meet_to_join_left in L.
       split.
       apply sym. exact L.       
       assert (F1 := j_com i a).
       assert (F2 := trn _ _ _ L F1).
       apply sym. exact F2.       
Qed.

Lemma lattice_not_zero_is_not_meet_annihilator: ∀ (i : S),  bop_not_is_id S eqv join i → bop_not_is_ann S eqv meet i. 
Proof. intros i H. destruct H as [w [H | H]]; exists w.
       left.
       case_eq(eqv (i (m) w) i); intro J.
          apply sym in J. apply lattice_meet_to_join_left in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
       right.
       case_eq(eqv (w (m) i) i); intro J.
          apply sym in J. apply lattice_meet_to_join_right in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
Qed.        


(*
  exists meet id <-> exists join annihilator 
*) 
Lemma lattice_exists_meet_id_implies_exists_join_ann : bop_exists_id S eqv meet -> bop_exists_ann S eqv join.  
Proof. intros [i P]. exists i. apply lattice_one_is_join_annihilator; auto. Defined. 

Lemma lattice_exists_join_ann_implies_exists_meet_id :  bop_exists_ann S eqv join -> bop_exists_id S eqv meet.  
Proof. intros [a P]. exists a. apply lattice_join_annihilator_is_one; auto. Defined. 

(*
  exists join id <-> exists meet annihilator 
*) 
Lemma lattice_exists_join_id_implies_exists_meet_ann : bop_exists_id S eqv join -> bop_exists_ann S eqv meet.  
Proof. intros [i P]. exists i. apply lattice_zero_is_meet_annihilator; auto. Defined. 

Lemma lattice_exists_meet_ann_implies_exists_join_id :  bop_exists_ann S eqv meet -> bop_exists_id S eqv join.  
Proof. intros [a P]. exists a. apply lattice_meet_annihilator_is_zero; auto. Defined.

(*
  exists join id <-> join id = meet annihilator 
*) 
Lemma lattice_exists_join_id_implies_join_id_equals_meet_ann : bop_exists_id S eqv join -> bops_id_equals_ann S eqv join meet.
Proof. intros [i P]. exists i. split. exact P. apply lattice_zero_is_meet_annihilator. exact P. Qed. 

Lemma lattice_not_exists_join_id_implies_not_join_id_equals_meet_ann : bop_not_exists_id S eqv join -> bops_not_id_equals_ann S eqv join meet.
Proof. unfold bops_not_id_equals_ann, bop_not_exists_id. intros H s. right.
       apply lattice_not_zero_is_not_meet_annihilator. apply H.
Qed.        

(*
  exists meet id <-> meet id = join annihilator 
*) 
Lemma lattice_exists_meet_id_implies_meet_id_equals_join_ann : bop_exists_id S eqv meet -> bops_id_equals_ann S eqv meet join.
Proof. intros [i P]. exists i. split. exact P. apply lattice_one_is_join_annihilator. exact P. Qed. 

Lemma lattice_not_exists_meet_id_implies_not_meet_id_equals_join_ann : bop_not_exists_id S eqv meet -> bops_not_id_equals_ann S eqv meet join.
Proof. unfold bops_not_id_equals_ann, bop_not_exists_id. intros H s. right.
       apply lattice_not_one_is_not_join_annihilator. apply H.
Qed.        

(* distributive  <-> distributive dual *)

Lemma lattice_distributive_implies_distributive_dual : bop_left_distributive S eqv join meet -> bop_left_distributive S eqv meet join. 
Proof. intros D a b c. apply sym.
       assert (F0 := D (a (j) b) a c).
       assert (F1 := abs_dual a b).
       assert (F2 := m_com a (a (j) b)). 
       assert (F3 := trn _ _ _ F1 F2).  apply sym in F3. 
       assert (F4 := m_com (a (j) b) c).
       assert (F5 := D c a b).       
       assert (F6 := trn _ _ _ F4 F5).
       assert (F7 := j_cng _ _ _ _ F3 F6).
       assert (F8 := trn _ _ _ F0 F7).
       assert (F9 := m_com c a).
       assert (F10 := m_com c b).
       assert (F11 := j_cng _ _ _ _ F9 F10).
       assert (F12 := j_cng _ _ _ _ (ref a) F11).
       assert (F13 := trn _ _ _ F8 F12).
       assert (F14 := j_ass a (a (m) c) (b (m) c)). apply sym in F14.
       assert (F15 := trn _ _ _ F13 F14).
       assert (F16 := abs a c). apply sym in F16.
       assert (F17 := j_cng _ _ _ _ F16 (ref (b (m) c))).
       assert (R := trn _ _ _ F15 F17).
       exact R. 
Qed.


Lemma lattice_distributive_dual_implies_distributive : bop_left_distributive S eqv meet join -> bop_left_distributive S eqv join meet. 
Proof. intros D a b c. apply sym.
       assert (F0 := D (a (m) b) a c).
       assert (F1 := abs a b).
       assert (F2 := j_com a (a (m) b)).
       assert (F3 := trn _ _ _ F1 F2).  apply sym in F3. 
       assert (F4 := j_com (a (m) b) c).
       assert (F5 := D c a b).       
       assert (F6 := trn _ _ _ F4 F5).
       assert (F7 := m_cng _ _ _ _ F3 F6).
       assert (F8 := trn _ _ _ F0 F7).
       assert (F9 := j_com c a).
       assert (F10 := j_com c b).
       assert (F11 := m_cng _ _ _ _ F9 F10).
       assert (F12 := m_cng _ _ _ _ (ref a) F11).
       assert (F13 := trn _ _ _ F8 F12).
       assert (F14 := m_ass a (a (j) c) (b (j) c)). apply sym in F14.
       assert (F15 := trn _ _ _ F13 F14).
       assert (F16 := abs_dual a c). apply sym in F16.
       assert (F17 := m_cng _ _ _ _ F16 (ref (b (j) c))).
       assert (R := trn _ _ _ F15 F17).
       exact R. 
Qed.

(* Could be useful.  Move to ? 

proofs do not use absorption 

a == a (m) 1 
  == a (m) (1 (j) b) 
  == (a (m) 1) (j)  (a (m) b)
  == a (j) (a (m) b)
 *)
Lemma lattice_fact : bops_id_equals_ann S eqv meet join -> bop_left_distributive S eqv join meet -> bops_left_left_absorptive S eqv join meet.
Proof. intros [i [P Q]] D a b.
       destruct (P a) as [L R]. apply sym in R.
       destruct (Q b) as [U V]. apply sym in U.
       assert (F1 := m_cng _ _ _ _ (ref a) U).
       assert (F2 := D a i b).  apply sym in R.
       assert (F3 := j_cng _ _ _ _ R (ref (a (m) b))). apply sym in R.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ R F1) F2) F3). 
       exact C.
Qed.        

Lemma lattice_fact_dual : bops_id_equals_ann S eqv join meet -> bop_left_distributive S eqv meet join -> bops_left_left_absorptive S eqv meet join.
Proof. intros [i [P Q]] D a b.
       destruct (P a) as [L R]. apply sym in R.
       destruct (Q b) as [U V]. apply sym in U.
       assert (F1 := j_cng _ _ _ _ (ref a) U).
       assert (F2 := D a i b).  apply sym in R.
       assert (F3 := m_cng _ _ _ _ R (ref (a (j) b))). apply sym in R.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ R F1) F2) F3). 
       exact C.
Qed.        

End LatticeTheory.

Section ACAS.

Definition lattice_proofs_dual (S: Type) (eqv : brel S) (join meet : binary_op S) :
          lattice_proofs S eqv join meet -> lattice_proofs S eqv meet join
:= λ pfs,
{|
   A_lattice_absorptive          := A_lattice_absorptive_dual S eqv join meet pfs
 ; A_lattice_absorptive_dual     := A_lattice_absorptive S eqv join meet pfs 
 ; A_lattice_distributive_d      := A_lattice_distributive_dual_d S eqv join meet pfs 
 ; A_lattice_distributive_dual_d := A_lattice_distributive_d S eqv join meet pfs 
|}.

Definition A_lattice_dual : ∀ (S : Type), A_lattice S -> A_lattice S
:= λ S lat,
{|  
  A_lattice_eqv          := A_lattice_eqv S lat 
; A_lattice_join         := A_lattice_meet S lat 
; A_lattice_meet         := A_lattice_join S lat 
; A_lattice_join_proofs  := A_lattice_meet_proofs S lat 
; A_lattice_meet_proofs  := A_lattice_join_proofs S lat 
; A_lattice_proofs       := lattice_proofs_dual S
                               (A_eqv_eq S (A_lattice_eqv S lat))
                               (A_lattice_join S lat)
                               (A_lattice_meet S lat)
                               (A_lattice_proofs S lat)   
; A_lattice_ast          := Ast_lattice_dual (A_lattice_ast S lat) 
|}.


Definition distributive_lattice_proofs_dual (S: Type) (rS : brel S) (join meet : binary_op S) :
  eqv_proofs S rS -> 
  sg_CI_proofs S rS join ->
  sg_CI_proofs S rS meet ->      
  distributive_lattice_proofs S rS join meet ->
           distributive_lattice_proofs S rS meet join
:= λ eqv p_join p_meet pfs,
{|
   A_distributive_lattice_absorptive        := A_distributive_lattice_absorptive_dual S rS join meet pfs
 ; A_distributive_lattice_absorptive_dual   := A_distributive_lattice_absorptive S rS join meet pfs 
 ; A_distributive_lattice_distributive      := lattice_distributive_implies_distributive_dual S rS
                                                  (A_eqv_reflexive S rS eqv)
                                                  (A_eqv_symmetric S rS eqv)
                                                  (A_eqv_transitive S rS eqv) 
                                                  join meet
                                                  (A_sg_CI_congruence S rS join p_join)
                                                  (A_sg_CI_associative S rS join p_join)
                                                  (A_sg_CI_commutative S rS meet p_meet)
                                                  (A_distributive_lattice_absorptive S rS join meet pfs)
                                                  (A_distributive_lattice_absorptive_dual S rS join meet pfs)
                                                  (A_distributive_lattice_distributive S rS join meet pfs) 
(*                                                                                        
 ; A_distributive_lattice_distributive      := A_distributive_lattice_distributive_dual S eqv join meet pfs
 ; A_distributive_lattice_distributive_dual := A_distributive_lattice_distributive S eqv join meet pfs                                                  
*)
|}.

Definition A_distributive_lattice_dual : ∀ (S : Type), A_distributive_lattice S -> A_distributive_lattice S
:= λ S lat,
{|  
  A_distributive_lattice_eqv          := A_distributive_lattice_eqv S lat 
; A_distributive_lattice_join         := A_distributive_lattice_meet S lat 
; A_distributive_lattice_meet         := A_distributive_lattice_join S lat 
; A_distributive_lattice_join_proofs  := A_distributive_lattice_meet_proofs S lat 
; A_distributive_lattice_meet_proofs  := A_distributive_lattice_join_proofs S lat 
; A_distributive_lattice_proofs       := distributive_lattice_proofs_dual S
                                             (A_eqv_eq S (A_distributive_lattice_eqv S lat))
                                             (A_distributive_lattice_join S lat)
                                             (A_distributive_lattice_meet S lat)
                                             (A_eqv_proofs S (A_distributive_lattice_eqv S lat))
                                             (A_distributive_lattice_join_proofs S lat)
                                             (A_distributive_lattice_meet_proofs S lat)                                             
                                             (A_distributive_lattice_proofs S lat)                                             
; A_distributive_lattice_ast          := Ast_distributive_lattice_dual (A_distributive_lattice_ast S lat) 
|}.
  

End ACAS.

Section CAS.

Definition lattice_certs_dual {S: Type} : @lattice_certificates S  -> @lattice_certificates S 
:= λ pfs,
{|
   lattice_absorptive          := Assert_Left_Left_Absorptive
 ; lattice_absorptive_dual     := Assert_Left_Left_Absorptive_Dual
 ; lattice_distributive_d      := match lattice_distributive_dual_d pfs with
                                  | Certify_Left_Distributive_Dual => Certify_Left_Distributive
                                  | Certify_Not_Left_Distributive_Dual p => Certify_Not_Left_Distributive p                   
                                  end 
 ; lattice_distributive_dual_d := match lattice_distributive_d pfs with
                                  | Certify_Left_Distributive => Certify_Left_Distributive_Dual
                                  | Certify_Not_Left_Distributive p => Certify_Not_Left_Distributive_Dual p                   
                                  end                                     
|}. 


Definition lattice_dual : ∀ {S : Type}, @lattice S -> @lattice S
:= λ {S} lat,
{|  
  lattice_eqv          := lattice_eqv lat 
; lattice_join         := lattice_meet lat 
; lattice_meet         := lattice_join lat 
; lattice_join_certs   := lattice_meet_certs lat 
; lattice_meet_certs   := lattice_join_certs lat 
; lattice_certs        := lattice_certs_dual (lattice_certs lat)   
; lattice_ast          := Ast_lattice_dual (lattice_ast lat) 
|}.


Definition distributive_lattice_certs_dual {S: Type} :
  @distributive_lattice_certificates S -> @distributive_lattice_certificates S 
:= λ dlc,
{|
   distributive_lattice_absorptive        := Assert_Left_Left_Absorptive 
 ; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
 ; distributive_lattice_distributive      := Assert_Left_Distributive
|}.

Definition distributive_lattice_dual : ∀ {S : Type}, @distributive_lattice S -> @distributive_lattice S
:= λ {S} lat,
{|  
  distributive_lattice_eqv          := distributive_lattice_eqv lat 
; distributive_lattice_join         := distributive_lattice_meet lat 
; distributive_lattice_meet         := distributive_lattice_join lat 
; distributive_lattice_join_certs   := distributive_lattice_meet_certs lat 
; distributive_lattice_meet_certs   := distributive_lattice_join_certs lat 
; distributive_lattice_certs        := distributive_lattice_certs_dual (distributive_lattice_certs lat)
; distributive_lattice_ast          := Ast_distributive_lattice_dual (distributive_lattice_ast lat) 
|}.
  
End CAS.

Section Verify.

Lemma  correct_lattice_certs_dual : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (latticeS : lattice_proofs S rS join meet), 
    
    P2C_lattice S rS meet join (lattice_proofs_dual S rS join meet latticeS)
    =
    lattice_certs_dual (P2C_lattice S rS join meet latticeS).
Proof. intros S rS join meet latticeS. 
       unfold lattice_certs_dual, lattice_proofs_dual, P2C_lattice; simpl. 
       destruct latticeS; simpl. destruct A_lattice_distributive_d, A_lattice_distributive_dual_d; simpl; 
       reflexivity.
Qed. 

Theorem correct_lattice_dual : ∀ (S : Type) (latticeS: A_lattice S), 
   lattice_dual (A2C_lattice S latticeS) 
   =
   A2C_lattice S (A_lattice_dual S latticeS). 
Proof. intros S latticeS. 
       unfold lattice_dual, A_lattice_dual, A2C_lattice; simpl. 
       rewrite correct_lattice_certs_dual. 
       reflexivity. 
Qed. 


Lemma  correct_distributive_lattice_certs_dual : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S)
     (eqvS : eqv_proofs S rS) (pjoin : sg_CI_proofs S rS join) (pmeet : sg_CI_proofs S rS meet) 
     (dlp : distributive_lattice_proofs S rS join meet), 
    P2C_distributive_lattice S rS meet join (distributive_lattice_proofs_dual S rS join meet eqvS pjoin pmeet dlp)
    =
    distributive_lattice_certs_dual (P2C_distributive_lattice S rS join meet dlp).
Proof. intros S rS join meet eqvS pjoin pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_dual : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S), 
   distributive_lattice_dual  (A2C_distributive_lattice S distributive_latticeS)  
   =
   A2C_distributive_lattice S (A_distributive_lattice_dual S distributive_latticeS). 
Proof. intros S distributive_latticeS. 
       unfold distributive_lattice_dual, A_distributive_lattice_dual, A2C_distributive_lattice; simpl. 
       rewrite correct_distributive_lattice_certs_dual. 
       reflexivity. 
Qed. 
  
 
End Verify.   
  