Require Import CAS.coq.common.base. 
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.bs.dual. 
Require Import CAS.coq.theory.facts. 
Section Theory.

End Theory.

Section ACAS.

Definition A_bs_from_bs_C : ∀ (S : Type),  A_bs_C S -> A_bs S 
:= λ S s, 
{| 
  A_bs_eqv          := A_bs_C_eqv S s
; A_bs_plus         := A_bs_C_plus S s
; A_bs_times        := A_bs_C_times S s
; A_bs_plus_proofs  := A_sg_proofs_from_sg_C_proofs S 
                            (A_eqv_eq S (A_bs_C_eqv S s))
                            (A_bs_C_plus S s)
                            (A_eqv_witness S (A_bs_C_eqv S s))
                            (A_eqv_new S (A_bs_C_eqv S s))
                            (A_eqv_not_trivial S (A_bs_C_eqv S s))                            
                            (A_eqv_proofs S (A_bs_C_eqv S s)) 
                            (A_bs_C_plus_proofs S s)  
; A_bs_times_proofs := A_bs_C_times_proofs S s
; A_bs_proofs       := A_bs_C_proofs S s 
; A_bs_ast          := Ast_bs_from_bs_C (A_bs_C_ast S s)
|}. 


Definition A_bs_C_from_bs_CS : ∀ (S : Type),  A_bs_CS S -> A_bs_C S 
:= λ S s, 
{| 
  A_bs_C_eqv          := A_bs_CS_eqv S s
; A_bs_C_plus         := A_bs_CS_plus S s
; A_bs_C_times        := A_bs_CS_times S s
; A_bs_C_plus_proofs  := A_sg_C_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_bs_CS_eqv S s))
                            (A_bs_CS_plus S s)
                            (A_eqv_witness S (A_bs_CS_eqv S s))
                            (A_eqv_new S (A_bs_CS_eqv S s))
                            (A_eqv_not_trivial S (A_bs_CS_eqv S s))
                            (A_eqv_proofs S (A_bs_CS_eqv S s))                            
                            (A_bs_CS_plus_proofs S s)  
; A_bs_C_times_proofs := A_bs_CS_times_proofs S s
; A_bs_C_proofs       := A_bs_CS_proofs S s 
; A_bs_C_ast          := Ast_bs_C_from_bs_CS (A_bs_CS_ast S s)
|}. 


Definition A_bs_C_from_bs_CI : ∀ (S : Type),  A_bs_CI S -> A_bs_C S 
:= λ S s, 
{| 
  A_bs_C_eqv          := A_bs_CI_eqv S s
; A_bs_C_plus         := A_bs_CI_plus S s
; A_bs_C_times        := A_bs_CI_times S s
; A_bs_C_plus_proofs  := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_bs_CI_eqv S s))
                            (A_bs_CI_plus S s)
                            (A_eqv_witness S (A_bs_CI_eqv S s))
                            (A_eqv_new S (A_bs_CI_eqv S s))
                            (A_eqv_not_trivial S (A_bs_CI_eqv S s))
                            (A_eqv_proofs S (A_bs_CI_eqv S s))                            
                            (A_bs_CI_plus_proofs S s)  
; A_bs_C_times_proofs := A_bs_CI_times_proofs S s
; A_bs_C_proofs       := A_bs_CI_proofs S s 
; A_bs_C_ast          := Ast_bs_C_from_bs_CI (A_bs_CI_ast S s)
|}. 





Definition bs_proofs_from_semiring_proofs :
  ∀ (S: Type) (eq : brel S) (plus times : binary_op S),
    eqv_proofs S eq -> sg_C_proofs S eq plus ->
        semiring_proofs S eq plus times -> bs_proofs S eq plus times
:= λ S eq plus times eqv sg sr,
let tranS := A_eqv_transitive S eq eqv   in 
let plusS_comm := A_sg_C_commutative S eq plus sg in
{|
  A_bs_left_distributive_d      := inl _ (A_semiring_left_distributive S eq plus times sr)
; A_bs_right_distributive_d     := inl _ (A_semiring_right_distributive S eq plus times sr)

; A_bs_plus_id_is_times_ann_d   := A_semiring_plus_id_is_times_ann_d S eq plus times sr
; A_bs_times_id_is_plus_ann_d   := A_semiring_times_id_is_plus_ann_d S eq plus times sr

; A_bs_left_left_absorptive_d   := A_semiring_left_left_absorptive_d S eq plus times sr
; A_bs_left_right_absorptive_d  := A_semiring_left_right_absorptive_d S eq plus times sr
                                                                      
; A_bs_right_left_absorptive_d  := bops_right_left_absorptive_decide_I S eq plus times tranS plusS_comm (A_semiring_left_left_absorptive_d S eq plus times sr)
; A_bs_right_right_absorptive_d := bops_right_right_absorptive_decide_I S eq plus times tranS plusS_comm (A_semiring_left_right_absorptive_d S eq plus times sr)
|}.


Definition A_bs_C_from_semiring :∀ (S: Type), A_semiring S -> A_bs_C S
:= λ S s,
let eqv := A_semiring_eqv S s in
let eqvP := A_eqv_proofs S eqv in
let eq := A_eqv_eq S eqv in
let plus := A_semiring_plus S s in
let times := A_semiring_times S s in
let sg_plusP := A_semiring_plus_proofs S s in 
{| 
  A_bs_C_eqv          := eqv
; A_bs_C_plus         := plus
; A_bs_C_times        := times
; A_bs_C_plus_proofs  := sg_plusP
; A_bs_C_times_proofs := A_semiring_times_proofs S s
; A_bs_C_proofs       := bs_proofs_from_semiring_proofs S eq plus times eqvP sg_plusP (A_semiring_proofs S s) 
; A_bs_C_ast          := Ast_bs_C_from_semiring (A_semiring_ast S s)
|}.
     
Definition A_semiring_from_dioid :∀ (S: Type), A_dioid S -> A_semiring S
:= λ S dS,
let eqv := A_dioid_eqv S dS in
let eqvP := A_eqv_proofs S eqv in
let eq := A_eqv_eq S eqv in
let plus := A_dioid_plus S dS in
let w := A_eqv_witness S eqv in
let f := A_eqv_new S eqv in
let nt := A_eqv_not_trivial S eqv in
{|
  A_semiring_eqv          := eqv 
; A_semiring_plus         := plus
; A_semiring_times        := A_dioid_times S dS
; A_semiring_plus_proofs  := A_sg_C_proofs_from_sg_CI_proofs S eq plus w f nt eqvP (A_dioid_plus_proofs S dS)
; A_semiring_times_proofs := A_dioid_times_proofs S dS
; A_semiring_proofs       := A_dioid_proofs S dS
; A_semiring_ast          := Ast_semiring_from_dioid (A_dioid_ast S dS)
|}.  




Definition distributive_lattice_proofs_to_semiring_proofs :
  ∀ (S: Type) (eq : brel S) (plus : binary_op S) (times : binary_op S),
       eqv_proofs S eq -> 
       sg_CI_proofs S eq plus -> sg_CI_proofs S eq times -> 
             distributive_lattice_proofs S eq plus times -> semiring_proofs S eq plus times
:= λ S eq plus times eqvP plusP timesP dlp,
let refS  := A_eqv_reflexive S eq eqvP in
let symS  := A_eqv_symmetric S eq eqvP in     
let tranS := A_eqv_transitive S eq eqvP in
let cong_plus  := A_sg_CI_congruence S eq plus plusP in   
let comm_plus  := A_sg_CI_commutative S eq plus plusP in
let cong_times := A_sg_CI_congruence S eq times timesP in   
let comm_times := A_sg_CI_commutative S eq times timesP in   
let ld  := A_distributive_lattice_distributive S eq plus times dlp in   
let la  := A_distributive_lattice_absorptive S eq plus times dlp in
let lad := A_distributive_lattice_absorptive_dual S eq plus times dlp in 
{|
  A_semiring_left_distributive        := ld 
; A_semiring_right_distributive       := bop_left_distributive_implies_right S eq plus times tranS cong_plus comm_plus comm_times ld

; A_semiring_plus_id_is_times_ann_d   := match A_sg_CI_exists_id_d S eq plus plusP with
                                         | inl id => inl (lattice_exists_join_id_implies_join_id_equals_meet_ann
                                                            S eq refS symS tranS plus times comm_plus cong_times comm_times lad id) 
                                         | inr nid => inr (lattice_not_exists_join_id_implies_not_join_id_equals_meet_ann
                                                            S eq refS symS tranS plus times cong_plus comm_plus comm_times la nid)
                                         end 
; A_semiring_times_id_is_plus_ann_d   := match A_sg_CI_exists_id_d S eq times timesP with
                                         | inl id => inl (lattice_exists_meet_id_implies_meet_id_equals_join_ann
                                                            S eq refS symS tranS plus times cong_plus comm_plus comm_times la id)
                                         | inr nid => inr (lattice_not_exists_meet_id_implies_not_meet_id_equals_join_ann
                                                            S eq refS symS tranS plus times comm_plus cong_times comm_times lad nid)
                                         end 
                                                                     
; A_semiring_left_left_absorptive_d   := inl la 
; A_semiring_left_right_absorptive_d  := inl (bops_left_left_absorptive_implies_left_right S eq plus times refS tranS cong_plus comm_times la)
|}.


Definition A_dioid_from_distributive_lattice :∀ (S: Type), A_distributive_lattice S -> A_dioid S
:= λ S dS,
let eqv   := A_distributive_lattice_eqv S dS in
let eqvP  := A_eqv_proofs S eqv in
let eq    := A_eqv_eq S eqv in
let plus  := A_distributive_lattice_join S dS in
let plusP := A_distributive_lattice_join_proofs S dS in
let times := A_distributive_lattice_meet S dS in
let timesP:= A_distributive_lattice_meet_proofs S dS in
let dPS   := A_distributive_lattice_proofs S dS in 
let w     := A_eqv_witness S eqv in
let f     := A_eqv_new S eqv in
let nt    := A_eqv_not_trivial S eqv in
{|
  A_dioid_eqv          := eqv 
; A_dioid_plus         := plus
; A_dioid_times        := times 
; A_dioid_plus_proofs  := plusP 
; A_dioid_times_proofs := A_sg_proofs_from_sg_CI_proofs S eq times w f nt eqvP timesP
; A_dioid_proofs       := distributive_lattice_proofs_to_semiring_proofs S eq plus times eqvP plusP timesP dPS
; A_dioid_ast          := Ast_dioid_from_distributive_lattice (A_distributive_lattice_ast S dS)
|}.  


Definition A_bs_from_dioid :∀ (S: Type), A_dioid S -> A_bs S 
:= λ S sS,  (A_bs_from_bs_C S (A_bs_C_from_semiring S (A_semiring_from_dioid S sS))). 

Definition A_bs_from_distributive_lattice :∀ (S: Type), A_distributive_lattice S -> A_bs S 
:= λ S dS,  A_bs_from_dioid S (A_dioid_from_distributive_lattice S dS). 

End ACAS.

Section CAS.

Definition bs_from_bs_C : ∀ {S : Type},  @bs_C S -> @bs S 
:= λ {S} s, 
{| 
  bs_eqv          := bs_C_eqv s
; bs_plus         := bs_C_plus s
; bs_times        := bs_C_times s
; bs_plus_certs  := sg_certs_from_sg_C_certs 
                            (eqv_eq (bs_C_eqv s))
                            (bs_C_plus s)
                            (eqv_witness (bs_C_eqv s))
                            (eqv_new (bs_C_eqv s))                             
                            (bs_C_plus_certs s)  
; bs_times_certs := bs_C_times_certs s
; bs_certs       := bs_C_certs  s 
; bs_ast          := Ast_bs_from_bs_C (bs_C_ast s)
|}. 




Definition bs_C_from_bs_CS : ∀ {S : Type},  @bs_CS S -> @bs_C S
:= λ {S} s, 
{| 
  bs_C_eqv          := bs_CS_eqv s
; bs_C_plus         := bs_CS_plus s
; bs_C_times        := bs_CS_times s
; bs_C_plus_certs  := sg_C_certs_from_sg_CS_certs 
                      (eqv_eq  (bs_CS_eqv s))
                      (bs_CS_plus s)                      
                      (eqv_witness (bs_CS_eqv s))
                      (eqv_new (bs_CS_eqv s))                             
                      (bs_CS_plus_certs s)  
; bs_C_times_certs := bs_CS_times_certs s
; bs_C_certs       := bs_CS_certs s 
; bs_C_ast         := Ast_bs_C_from_bs_CS (bs_CS_ast s)
|}.


Definition bs_C_from_bs_CI : ∀ {S : Type},  @bs_CI S -> @bs_C S
:= λ {S} s, 
{| 
  bs_C_eqv          := bs_CI_eqv s
; bs_C_plus         := bs_CI_plus s
; bs_C_times        := bs_CI_times s
; bs_C_plus_certs  := sg_C_certs_from_sg_CI_certs 
                      (eqv_eq  (bs_CI_eqv s))
                      (bs_CI_plus s)                      
                      (eqv_witness (bs_CI_eqv s))
                      (eqv_new (bs_CI_eqv s))                             
                      (bs_CI_plus_certs s)  
; bs_C_times_certs := bs_CI_times_certs s
; bs_C_certs       := bs_CI_certs s 
; bs_C_ast         := Ast_bs_C_from_bs_CI (bs_CI_ast s)
|}.


Definition bs_certs_from_semiring_certs :
  ∀ {S: Type},  @semiring_certificates S -> @bs_certificates S 
:= λ S sr,
{|
  bs_left_distributive_d      := Certify_Left_Distributive
; bs_right_distributive_d     := Certify_Right_Distributive

; bs_plus_id_is_times_ann_d   := semiring_plus_id_is_times_ann_d sr
; bs_times_id_is_plus_ann_d   := semiring_times_id_is_plus_ann_d sr

; bs_left_left_absorptive_d   := semiring_left_left_absorptive_d sr
; bs_left_right_absorptive_d  := semiring_left_right_absorptive_d sr
                                                                      
; bs_right_left_absorptive_d  := match semiring_left_left_absorptive_d sr with
                                 | Certify_Left_Left_Absorptive => Certify_Right_Left_Absorptive 
                                 | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive (s1, s2) 
                                 end 
; bs_right_right_absorptive_d := match semiring_left_right_absorptive_d sr with
                                 | Certify_Left_Right_Absorptive => Certify_Right_Right_Absorptive
                                 | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive (s1, s2) 
                                 end 
|}.


Definition bs_C_from_semiring : ∀ {S : Type},  @semiring S -> @bs_C S
:= λ {S} s, 
{| 
  bs_C_eqv         := semiring_eqv s
; bs_C_plus        := semiring_plus s
; bs_C_times       := semiring_times s
; bs_C_plus_certs  := semiring_plus_certs s
; bs_C_times_certs := semiring_times_certs s
; bs_C_certs       := bs_certs_from_semiring_certs (semiring_certs s) 
; bs_C_ast         := Ast_bs_C_from_semiring (semiring_ast s)
|}. 



Definition semiring_from_dioid :∀ {S: Type}, @dioid S -> @semiring S
:= λ S dS,
{|
  semiring_eqv          := dioid_eqv dS 
; semiring_plus         := dioid_plus dS
; semiring_times        := dioid_times dS
; semiring_plus_certs   := sg_C_certs_from_sg_CI_certs (eqv_eq (dioid_eqv dS))
                                                       (dioid_plus dS)
                                                       (eqv_witness (dioid_eqv dS))
                                                       (eqv_new (dioid_eqv dS))
                                                       (dioid_plus_certs dS)
; semiring_times_certs  := dioid_times_certs dS
; semiring_certs        := dioid_certs dS
; semiring_ast          := Ast_semiring_from_dioid (dioid_ast dS)
|}.


Definition distributive_lattice_certs_to_semiring_certs :
  ∀ {S: Type}, @sg_CI_certificates S  -> @sg_CI_certificates S-> @distributive_lattice_certificates S -> @semiring_certificates S 
:= λ S plusP timesP dlp,
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 

; semiring_plus_id_is_times_ann_d   := match sg_CI_exists_id_d plusP with
                                       | Certify_Exists_Id _ => Certify_Plus_Id_Equals_Times_Ann 
                                       | Certify_Not_Exists_Id => Certify_Not_Plus_Id_Equals_Times_Ann 
                                       end 
; semiring_times_id_is_plus_ann_d   := match sg_CI_exists_id_d timesP with
                                       | Certify_Exists_Id _ => Certify_Times_Id_Equals_Plus_Ann 
                                       | Certify_Not_Exists_Id => Certify_Not_Times_Id_Equals_Plus_Ann 
                                       end 
                                                                     
; semiring_left_left_absorptive_d   := Certify_Left_Left_Absorptive 
; semiring_left_right_absorptive_d  := Certify_Left_Right_Absorptive 
|}.


Definition dioid_from_distributive_lattice :∀ {S: Type}, @distributive_lattice S -> @dioid S
:= λ S dS,
let eqv   := distributive_lattice_eqv dS in
let eq    := eqv_eq eqv in
let plus  := distributive_lattice_join dS in
let plusP := distributive_lattice_join_certs dS in
let times := distributive_lattice_meet dS in
let timesP:= distributive_lattice_meet_certs dS in
let dPS   := distributive_lattice_certs dS in 
let w     := eqv_witness eqv in
let f     := eqv_new eqv in
{|
  dioid_eqv          := eqv 
; dioid_plus         := plus
; dioid_times        := times 
; dioid_plus_certs   := plusP 
; dioid_times_certs  := sg_certs_from_sg_CI_certs eq times w f timesP
; dioid_certs        := distributive_lattice_certs_to_semiring_certs plusP timesP dPS
; dioid_ast          := Ast_dioid_from_distributive_lattice (distributive_lattice_ast dS)
|}.  



Definition bs_from_dioid :∀ {S: Type}, @dioid S -> @bs S 
:= λ S sS,  (bs_from_bs_C (bs_C_from_semiring (semiring_from_dioid sS))). 

Definition bs_from_distributive_lattice :∀ {S: Type}, @distributive_lattice S -> @bs S 
:= λ S dS,  bs_from_dioid (dioid_from_distributive_lattice dS). 


End CAS.

Section Verify.


Lemma correct_bs_certs_from_semiring_certs :   
∀(S : Type)
  (eq : brel S) 
  (eqvP : eqv_proofs S eq)
  (plus times : binary_op S) 
  (plusP : sg_C_proofs S eq plus)
  (srP : semiring_proofs S eq plus times), 
  P2C_bs S eq plus times (bs_proofs_from_semiring_proofs S eq plus times eqvP plusP srP)
  = 
  bs_certs_from_semiring_certs (P2C_semiring S eq plus times srP). 
Proof. intros. destruct srP. 
       unfold bs_certs_from_semiring_certs, bs_proofs_from_semiring_proofs, P2C_semiring; simpl.
       destruct A_semiring_left_left_absorptive_d as [lla | [[s1 s2] nlla]];
       destruct A_semiring_left_right_absorptive_d as [X | [[s3 s4] nlra]]; 
       unfold bops_right_left_absorptive_decide_I, bops_right_right_absorptive_decide_I; compute; auto.
Qed.

Lemma correct_distributive_lattice_certs_to_semiring_certs : 
∀ (S : Type)
  (eqvS : A_eqv S)
  (plus  times : binary_op S)
  (plusP : sg_CI_proofs S (A_eqv_eq S eqvS) plus)
  (timesP : sg_CI_proofs S (A_eqv_eq S eqvS ) times)
  (dP : distributive_lattice_proofs S (A_eqv_eq S eqvS) plus times), 
  P2C_semiring S (A_eqv_eq S eqvS) plus times 
                 (distributive_lattice_proofs_to_semiring_proofs S (A_eqv_eq S eqvS) plus times (A_eqv_proofs S eqvS) plusP timesP dP)
  =                                      
  distributive_lattice_certs_to_semiring_certs
                   (P2C_sg_CI S (A_eqv_eq S eqvS) plus plusP)
                   (P2C_sg_CI S (A_eqv_eq S eqvS) times timesP)
                   (P2C_distributive_lattice S (A_eqv_eq S eqvS) plus times dP). 
Proof. intros. destruct dP. destruct plusP, timesP. 
       unfold distributive_lattice_proofs_to_semiring_proofs,
            distributive_lattice_certs_to_semiring_certs, P2C_sg_CI, P2C_distributive_lattice, P2C_semiring; simpl.
       destruct A_sg_CI_exists_id_d; destruct A_sg_CI_exists_id_d0; compute; auto.   
Qed.

Theorem correct_bs_from_bs_C : ∀ (S : Type) (P : A_bs_C S),  
    bs_from_bs_C (A2C_bs_C S P) = A2C_bs S (A_bs_from_bs_C S P).
Proof. intros S P. destruct P.
       unfold bs_from_bs_C, A_bs_from_bs_C, A2C_bs_C, A2C_bs; simpl.
       rewrite <-correct_sg_certs_from_sg_C_certs; auto.        
Defined. 


Theorem correct_bs_from_bs_CS : ∀ (S : Type) (P : A_bs_CS S),  
    bs_C_from_bs_CS (A2C_bs_CS S P) = A2C_bs_C S (A_bs_C_from_bs_CS S P).
Proof. intros S P. destruct P.
       unfold bs_C_from_bs_CS, A_bs_C_from_bs_CS, A2C_bs_CS, A2C_bs_C; simpl.
       rewrite <-correct_sg_C_certs_from_sg_CS_certs; auto.   
Qed. 


Theorem correct_bs_C_from_bs_CI : ∀ (S : Type) (P : A_bs_CI S),  
    bs_C_from_bs_CI (A2C_bs_CI S P) = A2C_bs_C S (A_bs_C_from_bs_CI S P).
Proof. intros S P. destruct P.
       unfold bs_C_from_bs_CI, A_bs_C_from_bs_CI, A2C_bs_CI, A2C_bs_C; simpl.
       rewrite <-correct_sg_C_certs_from_sg_CI_certs; auto.      
Qed. 


Theorem correct_bs_C_from_semiring : ∀ (S : Type) (P : A_semiring S),  
    bs_C_from_semiring (A2C_semiring S P) = A2C_bs_C S (A_bs_C_from_semiring S P).
Proof. intros S P. destruct P.
       unfold bs_C_from_semiring, A_bs_C_from_semiring, A2C_semiring, A2C_bs_C; simpl.
       rewrite correct_bs_certs_from_semiring_certs; auto.
Qed.  


Theorem correct_semiring_from_dioid : ∀ (S : Type) (P : A_dioid S),  
    semiring_from_dioid (A2C_dioid S P) = A2C_semiring S (A_semiring_from_dioid S P).
Proof. intros S P. destruct P.
       unfold semiring_from_dioid, A_semiring_from_dioid, A2C_semiring, A2C_dioid; simpl.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Qed. 

Theorem correct_bs_from_dioid : ∀ (S : Type) (P : A_dioid S),  
    bs_from_dioid (A2C_dioid S P) = A2C_bs S (A_bs_from_dioid S P).
Proof. intros S P.
       unfold bs_from_dioid, A_bs_from_dioid.
       rewrite correct_semiring_from_dioid. 
       rewrite correct_bs_C_from_semiring.
       rewrite correct_bs_from_bs_C; auto. 
Qed. 

Theorem correct_dioid_from_distributive_lattice : ∀ (S : Type) (P : A_distributive_lattice S),  
    dioid_from_distributive_lattice (A2C_distributive_lattice S P) = A2C_dioid S (A_dioid_from_distributive_lattice S P).
Proof. intros S P. destruct P.
       unfold dioid_from_distributive_lattice, A_dioid_from_distributive_lattice.
       unfold A2C_distributive_lattice, A2C_dioid. simpl.
       rewrite <- correct_sg_certs_from_sg_CI_certs.
       rewrite correct_distributive_lattice_certs_to_semiring_certs; auto.
Qed. 

Theorem correct_bs_from_distributive_lattice : ∀ (S : Type) (P : A_distributive_lattice S),  
    bs_from_distributive_lattice (A2C_distributive_lattice S P) = A2C_bs S (A_bs_from_distributive_lattice S P).
Proof. intros S P. unfold bs_from_distributive_lattice, A_bs_from_distributive_lattice.
       rewrite correct_dioid_from_distributive_lattice.        
       rewrite correct_bs_from_dioid. 
       reflexivity. 
Qed. 



  
 
End Verify.   
  