Require Import CAS.coq.common.base. 

Section Theory.

End Theory.

Section ACAS.

  
 Definition A_sg_C_proofs_option_from_sg_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), sg_proofs S eqS bS -> option (sg_C_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_sg_commutative_d S eqS bS sgS with
    | inr _ => None 
    | inl cS => Some {|
                     A_sg_C_associative      := A_sg_associative S eqS bS sgS 
                   ; A_sg_C_congruence       := A_sg_congruence S eqS bS sgS 
                   ; A_sg_C_commutative      := cS 
                   ; A_sg_C_selective_d      := A_sg_selective_d S eqS bS sgS 
                   ; A_sg_C_idempotent_d     := A_sg_idempotent_d S eqS bS sgS 
                   ; A_sg_C_cancel_d         := A_sg_left_cancel_d S eqS bS sgS 
                   ; A_sg_C_constant_d       := A_sg_left_constant_d S eqS bS sgS 
                   ; A_sg_C_anti_left_d      := A_sg_anti_left_d S eqS bS sgS 
                   ; A_sg_C_anti_right_d     := A_sg_anti_right_d S eqS bS sgS
                 |}
    end.   

Definition A_sg_C_option_from_sg : ∀ (S : Type),  A_sg S -> option (A_sg_C S) 
:= λ S sg, 
   match A_sg_C_proofs_option_from_sg_proofs _ _ _ (A_sg_proofs S sg) with 
   | None => None
   | Some sg_C_p => Some 
     {| 
         A_sg_C_eqv          := A_sg_eq S sg
       ; A_sg_C_bop          := A_sg_bop S sg
       ; A_sg_C_exists_id_d  := A_sg_exists_id_d S sg
       ; A_sg_C_exists_ann_d := A_sg_exists_ann_d S sg
       ; A_sg_C_proofs       := sg_C_p
       ; A_sg_C_ast          := Ast_sg_C_from_sg (A_sg_ast S sg)
     |}
   end.

Definition A_sg_CS_proofs_option_from_asg_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), asg_proofs S eqS bS -> option (sg_CS_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_asg_selective_d S eqS bS sgS with
    | inr _ => None 
    | inl sS => Some {|
                     A_sg_CS_associative      := A_asg_associative S eqS bS sgS 
                   ; A_sg_CS_congruence       := A_asg_congruence S eqS bS sgS 
                   ; A_sg_CS_commutative      := A_asg_commutative S eqS bS sgS 
                   ; A_sg_CS_selective        := sS
                 |}
    end.
 
 Definition A_sg_CS_proofs_option_from_sg_C_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), sg_C_proofs S eqS bS -> option (sg_CS_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_sg_C_selective_d S eqS bS sgS with
    | inr _ => None 
    | inl sS => Some {|
                     A_sg_CS_associative      := A_sg_C_associative S eqS bS sgS 
                   ; A_sg_CS_congruence       := A_sg_C_congruence S eqS bS sgS 
                   ; A_sg_CS_commutative      := A_sg_C_commutative S eqS bS sgS 
                   ; A_sg_CS_selective        := sS
                 |}
    end.

   Definition A_sg_CS_proofs_option_from_sg_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), sg_proofs S eqS bS -> option (sg_CS_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_sg_C_proofs_option_from_sg_proofs S eqS bS sgS with
    | None  => None 
    | Some sgCS => A_sg_CS_proofs_option_from_sg_C_proofs S eqS bS sgCS 
    end.   



Definition A_sg_CS_option_from_sg_C : ∀ (S : Type),  A_sg_C S -> option (A_sg_CS S) 
:= λ S sg, 
   match A_sg_CS_proofs_option_from_sg_C_proofs _ _ _ (A_sg_C_proofs S sg) with 
   | None => None
   | Some sg_CS_p => Some 
     {| 
         A_sg_CS_eqv          := A_sg_C_eqv S sg
       ; A_sg_CS_bop          := A_sg_C_bop S sg
       ; A_sg_CS_exists_id_d  := A_sg_C_exists_id_d S sg
       ; A_sg_CS_exists_ann_d := A_sg_C_exists_ann_d S sg
       ; A_sg_CS_proofs       := sg_CS_p
       ; A_sg_CS_ast          := Ast_sg_CS_from_sg_C (A_sg_C_ast S sg)
    |}
   end.


 Definition A_sg_CS_proofs_option_from_sg_CI_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), sg_CI_proofs S eqS bS -> option (sg_CS_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_sg_CI_selective_d S eqS bS sgS with
    | inr _ => None 
    | inl sS => Some {|
                     A_sg_CS_associative      := A_sg_CI_associative S eqS bS sgS 
                   ; A_sg_CS_congruence       := A_sg_CI_congruence S eqS bS sgS 
                   ; A_sg_CS_commutative      := A_sg_CI_commutative S eqS bS sgS 
                   ; A_sg_CS_selective        := sS
                 |}
    end.
 
Definition A_sg_CS_option_from_sg_CI : ∀ (S : Type),  A_sg_CI S -> option (A_sg_CS S) 
:= λ S sg, 
   match A_sg_CS_proofs_option_from_sg_CI_proofs _ _ _ (A_sg_CI_proofs S sg) with 
   | None => None
   | Some sg_CS_p => Some 
     {| 
         A_sg_CS_eqv          := A_sg_CI_eqv S sg
       ; A_sg_CS_bop          := A_sg_CI_bop S sg
       ; A_sg_CS_exists_id_d  := A_sg_CI_exists_id_d S sg
       ; A_sg_CS_exists_ann_d := A_sg_CI_exists_ann_d S sg
       ; A_sg_CS_proofs       := sg_CS_p
       ; A_sg_CS_ast          := Ast_sg_CS_from_sg_CI (A_sg_CI_ast S sg)
    |}
   end.

 Definition A_sg_CI_proofs_option_from_sg_C_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), sg_C_proofs S eqS bS -> option (sg_CI_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_sg_C_idempotent_d S eqS bS sgS with
    | inr _ => None 
    | inl iS => Some {|
                     A_sg_CI_associative      := A_sg_C_associative S eqS bS sgS 
                   ; A_sg_CI_congruence       := A_sg_C_congruence S eqS bS sgS 
                   ; A_sg_CI_commutative      := A_sg_C_commutative S eqS bS sgS 
                   ; A_sg_CI_idempotent       := iS
                   ; A_sg_CI_selective_d      := A_sg_C_selective_d S eqS bS sgS
                 |}
    end.   

Definition A_sg_CI_option_from_sg_C : ∀ (S : Type),  A_sg_C S -> option (A_sg_CI S) 
:= λ S sg, 
   match A_sg_CI_proofs_option_from_sg_C_proofs _ _ _ (A_sg_C_proofs S sg) with 
   | None => None
   | Some sg_CI_p => Some 
     {| 
         A_sg_CI_eqv          := A_sg_C_eqv S sg
       ; A_sg_CI_bop          := A_sg_C_bop S sg
       ; A_sg_CI_exists_id_d  := A_sg_C_exists_id_d S sg
       ; A_sg_CI_exists_ann_d := A_sg_C_exists_ann_d S sg
       ; A_sg_CI_proofs       := sg_CI_p
       ; A_sg_CI_ast          := Ast_sg_CI_from_sg_C (A_sg_C_ast S sg)
    |}
   end. 


 Definition A_sg_CK_proofs_option_from_sg_C_proofs :
    ∀ (S : Type) (eqS : brel S) (bS : binary_op S), sg_C_proofs S eqS bS -> option (sg_CK_proofs S eqS bS)
:= λ S eqS bS sgS,
    match  A_sg_C_cancel_d S eqS bS sgS with
    | inr _ => None 
    | inl cS => Some {|
                     A_sg_CK_associative      := A_sg_C_associative S eqS bS sgS 
                   ; A_sg_CK_congruence       := A_sg_C_congruence S eqS bS sgS 
                   ; A_sg_CK_commutative      := A_sg_C_commutative S eqS bS sgS 
                   ; A_sg_CK_cancel           := cS
                   ; A_sg_CK_anti_left_d      := A_sg_C_anti_left_d S eqS bS sgS 
                   ; A_sg_CK_anti_right_d     := A_sg_C_anti_right_d S eqS bS sgS 
                  |}
    end.   

Definition A_sg_CK_option_from_sg_C : ∀ (S : Type),  A_sg_C S -> option (A_sg_CK S) 
:= λ S sg, 
   match A_sg_CK_proofs_option_from_sg_C_proofs _ _ _ (A_sg_C_proofs S sg) with 
   | None => None
   | Some sg_CK_p => Some 
     {| 
         A_sg_CK_eqv         := A_sg_C_eqv S sg
       ; A_sg_CK_bop         := A_sg_C_bop S sg
       ; A_sg_CK_exists_id_d := A_sg_C_exists_id_d S sg                                         
       ; A_sg_CK_proofs      := sg_CK_p
       ; A_sg_CK_ast         := Ast_sg_CK_from_sg_C (A_sg_C_ast S sg)
    |}
   end.

 (* derirved *)

Definition A_sg_CS_option_from_sg : ∀ (S : Type),  A_sg S -> option (A_sg_CS S) 
:= λ S sg, 
   match A_sg_C_option_from_sg S sg with 
   | None => None
   | Some sgC => A_sg_CS_option_from_sg_C S sgC 
   end. 

Definition A_sg_CI_option_from_sg : ∀ (S : Type),  A_sg S -> option (A_sg_CI S) 
:= λ S sg, 
   match A_sg_C_option_from_sg S sg with 
   | None => None
   | Some sgC => A_sg_CI_option_from_sg_C S sgC 
   end. 
 

Definition A_sg_CK_option_from_sg : ∀ (S : Type),  A_sg S -> option (A_sg_CK S) 
:= λ S sg, 
   match A_sg_C_option_from_sg S sg with 
   | None => None
   | Some sgC => A_sg_CK_option_from_sg_C S sgC 
   end. 

End ACAS.

Section CAS.

 Definition sg_C_certs_option_from_sg_certs :
    ∀ (S : Type), @sg_certificates S -> option (@sg_C_certificates S)
:= λ S sgS,
    match sg_commutative_d sgS with
    | Certify_Not_Commutative _ => None 
    | Certify_Commutative => Some {|
                     sg_C_associative      := Assert_Associative 
                   ; sg_C_congruence       := sg_congruence sgS
                   ; sg_C_commutative      := Assert_Commutative 
                   ; sg_C_selective_d      := sg_selective_d sgS 
                   ; sg_C_idempotent_d     := sg_idempotent_d sgS 
                   ; sg_C_cancel_d         := sg_left_cancel_d sgS 
                   ; sg_C_constant_d       := sg_left_constant_d sgS 
                   ; sg_C_anti_left_d      := sg_anti_left_d sgS 
                   ; sg_C_anti_right_d     := sg_anti_right_d sgS
    |}
    end.   

  Definition sg_CS_certs_option_from_asg_certs :
    ∀ (S : Type), @asg_certificates S -> option (@sg_CS_certificates S)
:= λ S sgS,
    match asg_selective_d sgS with
    | Certify_Not_Selective _ => None 
    | Certify_Selective => Some {|
                     sg_CS_associative      := Assert_Associative 
                   ; sg_CS_congruence       := asg_congruence sgS
                   ; sg_CS_commutative      := Assert_Commutative 
                   ; sg_CS_selective        := Assert_Selective
                 |}
    end.

 
  Definition sg_CS_certs_option_from_sg_C_certs :
    ∀ (S : Type), @sg_C_certificates S -> option (@sg_CS_certificates S)
:= λ S sgS,
    match sg_C_selective_d sgS with
    | Certify_Not_Selective _ => None 
    | Certify_Selective => Some {|
                     sg_CS_associative      := Assert_Associative 
                   ; sg_CS_congruence       := sg_C_congruence sgS
                   ; sg_CS_commutative      := Assert_Commutative 
                   ; sg_CS_selective        := Assert_Selective
              |}
    end.

 Definition sg_CS_certs_option_from_sg_certs :
    ∀ (S : Type) , @sg_certificates S  -> option (@sg_CS_certificates S)
:= λ S sgS,
    match  sg_C_certs_option_from_sg_certs S sgS with
    | None  => None 
    | Some sgCS => sg_CS_certs_option_from_sg_C_certs S sgCS 
    end.   



  Definition sg_CS_certs_option_from_sg_CI_certs :
    ∀ (S : Type), @sg_CI_certificates S -> option (@sg_CS_certificates S)
:= λ S sgS,
    match sg_CI_selective_d sgS with
    | Certify_Not_Selective _ => None 
    | Certify_Selective => Some {|
                     sg_CS_associative      := Assert_Associative 
                   ; sg_CS_congruence       := sg_CI_congruence sgS
                   ; sg_CS_commutative      := Assert_Commutative 
                   ; sg_CS_selective        := Assert_Selective
               |}
    end.   

Definition sg_CI_certs_option_from_sg_C_certs :
    ∀ (S : Type), @sg_C_certificates S -> option (@sg_CI_certificates S)
:= λ S sgS,
    match sg_C_idempotent_d sgS with
    | Certify_Not_Idempotent _ => None 
    | Certify_Idempotent => Some {|
                     sg_CI_associative      := Assert_Associative 
                   ; sg_CI_congruence       := sg_C_congruence sgS
                   ; sg_CI_commutative      := Assert_Commutative
                   ; sg_CI_idempotent       := Assert_Idempotent                               
                   ; sg_CI_selective_d      := sg_C_selective_d sgS
                 |}
    end.   


Definition sg_CK_certs_option_from_sg_C_certs :
    ∀ (S : Type), @sg_C_certificates S -> option (@sg_CK_certificates S)
:= λ S sgS,
    match sg_C_cancel_d sgS with
    | Certify_Not_Left_Cancellative _ => None 
    | Certify_Left_Cancel => Some {|
                     sg_CK_associative      := Assert_Associative 
                   ; sg_CK_congruence       := sg_C_congruence sgS
                   ; sg_CK_commutative      := Assert_Commutative
                   ; sg_CK_left_cancel      := Assert_Left_Cancellative
                   ; sg_CK_anti_left_d      := sg_C_anti_left_d sgS 
                   ; sg_CK_anti_right_d     := sg_C_anti_right_d sgS                                                                     
                |}
    end.   

 (******************)

Definition sg_C_option_from_sg : ∀ (S : Type),  @sg S -> option (@sg_C S) 
:= λ S sg, 
   match sg_C_certs_option_from_sg_certs _ (sg_certs sg) with 
   | None => None
   | Some sg_C_p => Some 
     {| 
         sg_C_eqv          := sg_eq sg
       ; sg_C_bop          := sg_bop sg
       ; sg_C_exists_id_d  := sg_exists_id_d sg
       ; sg_C_exists_ann_d := sg_exists_ann_d sg 
       ; sg_C_certs        := sg_C_p       
       ; sg_C_ast          := Ast_sg_C_from_sg (sg_ast sg)
    |}
   end.

 Definition sg_CI_option_from_sg_C : ∀ (S : Type),  @sg_C S -> option (@sg_CI S) 
:= λ S sg, 
   match sg_CI_certs_option_from_sg_C_certs _ (sg_C_certs sg) with 
   | None => None
   | Some sg_CS_p => Some 
     {| 
         sg_CI_eqv          := sg_C_eqv sg
       ; sg_CI_bop          := sg_C_bop sg
       ; sg_CI_exists_id_d  := sg_C_exists_id_d sg
       ; sg_CI_exists_ann_d := sg_C_exists_ann_d sg 
       ; sg_CI_certs        := sg_CS_p      
       ; sg_CI_ast          := Ast_sg_CI_from_sg_C (sg_C_ast sg)
    |}
   end.

Definition sg_CK_option_from_sg_C : ∀ (S : Type),  @sg_C S -> option (@sg_CK S) 
:= λ S sg, 
   match sg_CK_certs_option_from_sg_C_certs _ (sg_C_certs sg) with 
   | None => None
   | Some sg_CS_p => Some 
     {| 
         sg_CK_eqv         := sg_C_eqv sg
       ; sg_CK_bop         := sg_C_bop sg
       ; sg_CK_exists_id_d := sg_C_exists_id_d sg
       ; sg_CK_certs       := sg_CS_p
       ; sg_CK_ast         := Ast_sg_CK_from_sg_C (sg_C_ast sg)
    |}
   end.

Definition sg_CS_option_from_sg_CI : ∀ (S : Type),  @sg_CI S -> option (@sg_CS S) 
:= λ S sg, 
   match sg_CS_certs_option_from_sg_CI_certs _ (sg_CI_certs sg) with 
   | None => None
   | Some sg_CS_p => Some 
     {| 
         sg_CS_eqv          := sg_CI_eqv sg
       ; sg_CS_bop          := sg_CI_bop sg
       ; sg_CS_exists_id_d  := sg_CI_exists_id_d sg
       ; sg_CS_exists_ann_d := sg_CI_exists_ann_d sg 
       ; sg_CS_certs        := sg_CS_p
       ; sg_CS_ast          := Ast_sg_CS_from_sg_CI (sg_CI_ast sg)
    |}
   end.


Definition sg_CS_option_from_sg_C : ∀ (S : Type),  @sg_C S -> option (@sg_CS S) 
:= λ S sg, 
   match sg_CS_certs_option_from_sg_C_certs _ (sg_C_certs sg) with 
   | None => None
   | Some sg_CS_p => Some 
     {| 
         sg_CS_eqv          := sg_C_eqv sg
       ; sg_CS_bop          := sg_C_bop sg
       ; sg_CS_exists_id_d  := sg_C_exists_id_d sg
       ; sg_CS_exists_ann_d := sg_C_exists_ann_d sg 
       ; sg_CS_certs        := sg_CS_p
       ; sg_CS_ast          := Ast_sg_CS_from_sg_C (sg_C_ast sg)
    |}
   end.
 

 

 (* derirved *)

Definition sg_CS_option_from_sg : ∀ (S : Type),  @sg S -> option (@sg_CS S) 
:= λ S sg, 
   match sg_C_option_from_sg S sg with 
   | None => None
   | Some sgC => sg_CS_option_from_sg_C S sgC 
   end. 

Definition sg_CI_option_from_sg : ∀ (S : Type),  @sg S -> option (@sg_CI S) 
:= λ S sg, 
   match sg_C_option_from_sg S sg with 
   | None => None
   | Some sgC => sg_CI_option_from_sg_C S sgC 
   end. 
 

Definition sg_CK_option_from_sg : ∀ (S : Type),  @sg S -> option (@sg_CK S) 
:= λ S sg, 
   match sg_C_option_from_sg S sg with 
   | None => None
   | Some sgC => sg_CK_option_from_sg_C S sgC 
   end. 
 

End CAS.

Section Verify.

Lemma correct_sg_C_certs_option_from_sg_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_proofs S r b), 
       sg_C_certs_option_from_sg_certs S (P2C_sg S r b sgS)
       = 
       P2C_sg_C_option S r b (A_sg_C_proofs_option_from_sg_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_C_certs_option_from_sg_certs, A_sg_C_proofs_option_from_sg_proofs, 
              P2C_sg, P2C_sg_C_option; simpl. 
       destruct A_sg_commutative_d as [C | [ [s1 s2] NC]]; unfold P2C_sg_C; simpl. reflexivity. 
       reflexivity. 
Defined. 


Lemma correct_sg_CI_certs_option_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_C_proofs S r b), 
       sg_CI_certs_option_from_sg_C_certs S (P2C_sg_C S r b sgS)
       = 
       P2C_sg_CI_option S r b (A_sg_CI_proofs_option_from_sg_C_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CI_certs_option_from_sg_C_certs, A_sg_CI_proofs_option_from_sg_C_proofs, 
              P2C_sg_C, P2C_sg_CI_option; simpl. 
       destruct A_sg_C_idempotent_d as [I | [s0 NI]]; 
       simpl; reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_option_from_sg_CI_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_CI_proofs S r b), 
       sg_CS_certs_option_from_sg_CI_certs S (P2C_sg_CI S r b sgS)
       = 
       P2C_sg_CS_option S r b (A_sg_CS_proofs_option_from_sg_CI_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CS_certs_option_from_sg_CI_certs, A_sg_CS_proofs_option_from_sg_CI_proofs, 
              P2C_sg_CI, P2C_sg_CS_option; simpl. 
       destruct A_sg_CI_selective_d as [sel | [ [s1 s2] nsel]]; 
       simpl; reflexivity. 
Defined. 


Lemma correct_sg_CS_certs_option_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_C_proofs S r b), 
       sg_CS_certs_option_from_sg_C_certs S (P2C_sg_C S r b sgS)
       = 
       P2C_sg_CS_option S r b (A_sg_CS_proofs_option_from_sg_C_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CS_certs_option_from_sg_C_certs, A_sg_CS_proofs_option_from_sg_C_proofs, 
              P2C_sg_C, P2C_sg_CS_option; simpl. 
       destruct A_sg_C_selective_d as [sel | [ [s1 s2] nsel]]; 
       simpl; reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_option_from_asg_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : asg_proofs S r b), 
       sg_CS_certs_option_from_asg_certs S (P2C_asg S r b sgS)
       = 
       P2C_sg_CS_option S r b (A_sg_CS_proofs_option_from_asg_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CS_certs_option_from_asg_certs, A_sg_CS_proofs_option_from_asg_proofs, 
              P2C_asg, P2C_sg_CS_option; simpl. 
       destruct A_asg_selective_d as [sel | [ [s1 s2] nsel]]; 
       simpl; reflexivity. 
Defined. 


Lemma correct_sg_CK_certs_option_from_sg_C_certs : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (sgS : sg_C_proofs S r b), 
       sg_CK_certs_option_from_sg_C_certs S (P2C_sg_C S r b sgS)
       = 
       P2C_sg_CK_option S r b (A_sg_CK_proofs_option_from_sg_C_proofs S r b sgS). 
Proof. intros S r b sgS. destruct sgS. 
       unfold sg_CK_certs_option_from_sg_C_certs, A_sg_CK_proofs_option_from_sg_C_proofs, 
              P2C_sg_C, P2C_sg_CK_option; simpl. 
       destruct A_sg_C_cancel_d as [C | NC];
       simpl; reflexivity. 
Defined.

(**********)

Theorem correct_sg_C_option_from_sg : ∀ (S : Type) (P : A_sg S),  
         sg_C_option_from_sg S (A2C_sg S P) = A2C_sg_C_option S (A_sg_C_option_from_sg S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg, A2C_sg_C_option, sg_C_option_from_sg, A_sg_C_option_from_sg. simpl.  
       unfold A2C_sg_C, option_map.  
       rewrite correct_sg_C_certs_option_from_sg_certs. 
       case (A_sg_C_proofs_option_from_sg_proofs S (A_eqv_eq S A_sg_eq) A_sg_bop); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 


Theorem correct_sg_CI_option_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
        sg_CI_option_from_sg_C S (A2C_sg_C S P) = A2C_sg_CI_option S (A_sg_CI_option_from_sg_C S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_C, A2C_sg_CI_option, sg_CI_option_from_sg_C, A_sg_CI_option_from_sg_C; simpl.  
       rewrite correct_sg_CI_certs_option_from_sg_C_certs. 
       case (A_sg_CI_proofs_option_from_sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop A_sg_C_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined.

Theorem correct_sg_CS_option_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
        sg_CS_option_from_sg_C S (A2C_sg_C S P) = A2C_sg_CS_option S (A_sg_CS_option_from_sg_C S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_C, A2C_sg_CS_option, sg_CS_option_from_sg_C, A_sg_CS_option_from_sg_C; simpl.  
       rewrite correct_sg_CS_certs_option_from_sg_C_certs. 
       case (A_sg_CS_proofs_option_from_sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop A_sg_C_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined.


Theorem correct_sg_CK_option_from_sg_C : ∀ (S : Type) (P : A_sg_C S),  
        sg_CK_option_from_sg_C S (A2C_sg_C S P) = A2C_sg_CK_option S (A_sg_CK_option_from_sg_C S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_C, A2C_sg_CK_option, 
              sg_CK_option_from_sg_C, A_sg_CK_option_from_sg_C; simpl.  
       rewrite correct_sg_CK_certs_option_from_sg_C_certs. 
       case (A_sg_CK_proofs_option_from_sg_C_proofs S (A_eqv_eq S A_sg_C_eqv)
               A_sg_C_bop A_sg_C_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 

Theorem correct_sg_CS_option_from_sg_CI : ∀ (S : Type) (P : A_sg_CI S),  
         sg_CS_option_from_sg_CI S (A2C_sg_CI S P) = A2C_sg_CS_option S (A_sg_CS_option_from_sg_CI S P). 
Proof. intros S P. destruct P. 
       unfold A2C_sg_CI, A2C_sg_CS_option, sg_CS_option_from_sg_CI, A_sg_CS_option_from_sg_CI; simpl.  
       rewrite correct_sg_CS_certs_option_from_sg_CI_certs. 
       case (A_sg_CS_proofs_option_from_sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop A_sg_CI_proofs); simpl. 
          intro s. reflexivity. 
          reflexivity. 
Defined. 
 
End Verify.   
  