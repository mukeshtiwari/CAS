Require Import Coq.Bool.Bool.
Require Import Coq.Strings.Ascii.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.structures.


Section Computation.

  Definition brel_eq_ascii : brel ascii := eqb.
  
End Computation.   
Section Theory.


Lemma brel_eq_ascii_reflexive : brel_reflexive ascii brel_eq_ascii.
Proof. unfold brel_reflexive, brel_eq_ascii. apply eqb_refl. Qed. 

Lemma brel_eq_ascii_symmetric : brel_symmetric ascii brel_eq_ascii. 
Proof. unfold brel_symmetric, brel_eq_ascii.
       intros s t A. rewrite <- A. apply eqb_sym. Qed. 

Lemma brel_eq_ascii_transitive : brel_transitive ascii brel_eq_ascii. 
Proof. unfold brel_transitive, brel_eq_ascii.
       intros s t u A B. 
       assert (C := proj1 (eqb_eq s t) A).
       assert (D := proj1 (eqb_eq t u) B).
       rewrite C. rewrite <- D.
       apply eqb_refl. 
Qed. 

Lemma brel_eq_ascii_congruence : brel_congruence ascii brel_eq_ascii brel_eq_ascii. 
Proof. unfold brel_congruence.
       intros s t u v A B. unfold brel_eq_ascii in *.
       assert (C := proj1 (eqb_eq s u) A).
       assert (D := proj1 (eqb_eq t v) B).
       rewrite C, D. 
       reflexivity. 
Qed.

Definition ascii_new (x : ascii) : ascii := if brel_eq_ascii x zero then one else zero.

Lemma brel_eq_ascii_not_trivial : brel_not_trivial ascii brel_eq_ascii ascii_new.                                                    
Proof. intro s. unfold ascii_new. unfold brel_eq_ascii.
       case_eq(eqb s zero); intro A; auto. 
       assert (B := proj1 (eqb_eq _ _) A).
       rewrite B.  compute. auto. 
Qed.

Local Open Scope list_scope. 


Definition level_1 (u : unit) := (Ascii true) :: (Ascii false) :: nil.

Definition level_2 (u : unit) := (List.map (fun f =>  f true) (level_1 u)) ++ (List.map (fun f =>  f false) (level_1 u)).

Definition level_3 (u : unit) := (List.map (fun f =>  f true) (level_2 u)) ++ (List.map (fun f =>  f false) (level_2 u)).

Definition level_4 (u : unit) := (List.map (fun f =>  f true) (level_3 u)) ++ (List.map (fun f =>  f false) (level_3 u)).

Definition level_5 (u : unit) := (List.map (fun f =>  f true) (level_4 u)) ++ (List.map (fun f =>  f false) (level_4 u)).

Definition level_6 (u : unit) := (List.map (fun f =>  f true) (level_5 u)) ++ (List.map (fun f =>  f false) (level_5 u)).

Definition level_7 (u : unit) := (List.map (fun f =>  f true) (level_6 u)) ++ (List.map (fun f =>  f false) (level_6 u)).

Definition level_8 (u : unit) := (List.map (fun f =>  f true) (level_7 u)) ++ (List.map (fun f =>  f false) (level_7 u)).


Lemma brel_eq_ascii_is_finite : carrier_is_finite ascii brel_eq_ascii. 
Proof. unfold carrier_is_finite. exists level_8.
       intro s.
       destruct s; destruct b; destruct b0; destruct b1; destruct b2; destruct b3; destruct b4; destruct b5; destruct b6;
       compute; reflexivity. 
Defined.


Lemma brel_eq_ascii_at_least_three : brel_at_least_three ascii brel_eq_ascii.
Proof. exists (one, (zero, Ascii true false true false true false true false)).  compute. auto. Defined.

Lemma brel_eq_ascii_not_exactly_two :   brel_not_exactly_two ascii brel_eq_ascii.
Proof. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_eq_ascii_symmetric; auto. 
       apply brel_eq_ascii_transitive; auto.
       apply brel_eq_ascii_at_least_three; auto. 
Defined. 



End Theory.

Section ACAS.

Definition eqv_proofs_eq_ascii : eqv_proofs ascii brel_eq_ascii  (* (uop_id ascii) *) 
:= {| 
   A_eqv_congruence     := brel_eq_ascii_congruence 
   ; A_eqv_reflexive      := brel_eq_ascii_reflexive 
   ; A_eqv_transitive     := brel_eq_ascii_transitive 
   ; A_eqv_symmetric      := brel_eq_ascii_symmetric
   |}. 


Definition A_eqv_ascii : A_eqv ascii 
:= {| 
      A_eqv_eq     := brel_eq_ascii
    ; A_eqv_proofs := eqv_proofs_eq_ascii
                      
    ; A_eqv_witness       := zero
    ; A_eqv_new           := ascii_new 
    ; A_eqv_not_trivial   := brel_eq_ascii_not_trivial
    ; A_eqv_exactly_two_d := inr brel_eq_ascii_not_exactly_two                              
    ; A_eqv_data          := λ b, DATA_ascii b 
    ; A_eqv_rep           := λ b, b
    ; A_eqv_finite_d      := inl brel_eq_ascii_is_finite
    ; A_eqv_ast           := Ast_eqv_ascii 
   |}. 


End ACAS.

Section CAS.

Definition eqv_ascii : @eqv ascii 
:= {| 
      eqv_eq    := brel_eq_ascii
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence ascii
     ; eqv_reflexive      := @Assert_Reflexive ascii
     ; eqv_transitive     := @Assert_Transitive ascii 
     ; eqv_symmetric      := @Assert_Symmetric ascii
     |}  
    ; eqv_witness := zero
    ; eqv_new   := ascii_new
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 brel_eq_ascii one zero (Ascii true false true false true false true false))
    ; eqv_data  := λ b, DATA_ascii b 
    ; eqv_rep   := λ b, b
    ; eqv_finite_d  := Certify_Is_Finite level_8
    ; eqv_ast   := Ast_eqv_ascii 
|}. 
  
End CAS.

Section Verify.

Theorem correct_eqv_ascii : eqv_ascii = A2C_eqv ascii (A_eqv_ascii). 
Proof. unfold eqv_ascii, A_eqv_ascii. unfold brel_eq_ascii_not_exactly_two. 
       unfold brel_at_least_thee_implies_not_exactly_two. 
       unfold A2C_eqv; simpl.
       destruct brel_eq_ascii_not_exactly_two as [f A];
       destruct brel_eq_ascii_is_finite as [p B]; simpl.
       reflexivity.
Qed. 
 
End Verify.   
  
