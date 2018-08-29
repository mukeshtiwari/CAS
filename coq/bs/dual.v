Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.lattice_theory. 

Section Theory.
  
  (* see  CAS.coq.theory.lattice_theory. *)
  
End Theory.   

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
; A_lattice_join_ast     := A_lattice_meet_ast S lat
; A_lattice_meet_ast     := A_lattice_join_ast S lat                                           
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
; A_distributive_lattice_join_ast     := A_distributive_lattice_meet_ast S lat
; A_distributive_lattice_meet_ast     := A_distributive_lattice_join_ast S lat                                              
; A_distributive_lattice_ast          := Ast_distributive_lattice_dual (A_distributive_lattice_ast S lat) 
|}.
  

Definition selective_distributive_lattice_proofs_dual (S: Type) (rS : brel S) (join meet : binary_op S) :
  eqv_proofs S rS -> 
  sg_CS_proofs S rS join ->
  sg_CS_proofs S rS meet ->      
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
                                                  (A_sg_CS_congruence S rS join p_join)
                                                  (A_sg_CS_associative S rS join p_join)
                                                  (A_sg_CS_commutative S rS meet p_meet)
                                                  (A_distributive_lattice_absorptive S rS join meet pfs)
                                                  (A_distributive_lattice_absorptive_dual S rS join meet pfs)
                                                  (A_distributive_lattice_distributive S rS join meet pfs) 
|}.

Definition A_selective_distributive_lattice_dual : ∀ (S : Type), A_selective_distributive_lattice S -> A_selective_distributive_lattice S
:= λ S lat,
{|  
  A_selective_distributive_lattice_eqv          := A_selective_distributive_lattice_eqv S lat 
; A_selective_distributive_lattice_join         := A_selective_distributive_lattice_meet S lat 
; A_selective_distributive_lattice_meet         := A_selective_distributive_lattice_join S lat 
; A_selective_distributive_lattice_join_proofs  := A_selective_distributive_lattice_meet_proofs S lat 
; A_selective_distributive_lattice_meet_proofs  := A_selective_distributive_lattice_join_proofs S lat 
; A_selective_distributive_lattice_proofs       := selective_distributive_lattice_proofs_dual S
                                             (A_eqv_eq S (A_selective_distributive_lattice_eqv S lat))
                                             (A_selective_distributive_lattice_join S lat)
                                             (A_selective_distributive_lattice_meet S lat)
                                             (A_eqv_proofs S (A_selective_distributive_lattice_eqv S lat))
                                             (A_selective_distributive_lattice_join_proofs S lat)
                                             (A_selective_distributive_lattice_meet_proofs S lat)                                             
                                             (A_selective_distributive_lattice_proofs S lat)
; A_selective_distributive_lattice_join_ast     := A_selective_distributive_lattice_meet_ast S lat
; A_selective_distributive_lattice_meet_ast     := A_selective_distributive_lattice_join_ast S lat
; A_selective_distributive_lattice_ast          := Ast_selective_distributive_lattice_dual (A_selective_distributive_lattice_ast S lat) 
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
; lattice_join_ast     := lattice_meet_ast lat
; lattice_meet_ast     := lattice_join_ast lat                                           
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
; distributive_lattice_join_ast     := distributive_lattice_meet_ast lat
; distributive_lattice_meet_ast     := distributive_lattice_join_ast lat                                                                                
; distributive_lattice_ast          := Ast_distributive_lattice_dual (distributive_lattice_ast lat) 
|}.


Definition selective_distributive_lattice_dual : ∀ {S : Type}, @selective_distributive_lattice S -> @selective_distributive_lattice S
:= λ {S} lat,
{|  
  selective_distributive_lattice_eqv          := selective_distributive_lattice_eqv lat 
; selective_distributive_lattice_join         := selective_distributive_lattice_meet lat 
; selective_distributive_lattice_meet         := selective_distributive_lattice_join lat 
; selective_distributive_lattice_join_certs   := selective_distributive_lattice_meet_certs lat 
; selective_distributive_lattice_meet_certs   := selective_distributive_lattice_join_certs lat 
; selective_distributive_lattice_certs        := distributive_lattice_certs_dual (selective_distributive_lattice_certs lat)
; selective_distributive_lattice_join_ast     := selective_distributive_lattice_meet_ast lat
; selective_distributive_lattice_meet_ast     := selective_distributive_lattice_join_ast lat
; selective_distributive_lattice_ast          := Ast_selective_distributive_lattice_dual (selective_distributive_lattice_ast lat) 
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



Lemma  correct_selective_distributive_lattice_certs_dual : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S)
     (eqvS : eqv_proofs S rS) (pjoin : sg_CS_proofs S rS join) (pmeet : sg_CS_proofs S rS meet) 
     (dlp : distributive_lattice_proofs S rS join meet), 
    P2C_distributive_lattice S rS meet join (selective_distributive_lattice_proofs_dual S rS join meet eqvS pjoin pmeet dlp)
    =
    distributive_lattice_certs_dual (P2C_distributive_lattice S rS join meet dlp).
Proof. intros S rS join meet eqvS pjoin pmeet dlp. compute. reflexivity. Qed.


Theorem correct_selective_distributive_lattice_dual : ∀ (S : Type) (selective_distributive_latticeS: A_selective_distributive_lattice S), 
   selective_distributive_lattice_dual  (A2C_selective_distributive_lattice S selective_distributive_latticeS)  
   =
   A2C_selective_distributive_lattice S (A_selective_distributive_lattice_dual S selective_distributive_latticeS). 
Proof. intros S selective_distributive_latticeS. 
       unfold selective_distributive_lattice_dual, A_selective_distributive_lattice_dual, A2C_selective_distributive_lattice; simpl. 
       rewrite correct_selective_distributive_lattice_certs_dual. 
       reflexivity. 
Qed. 

 
End Verify.   

