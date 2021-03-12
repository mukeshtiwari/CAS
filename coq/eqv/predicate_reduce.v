Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.reduction.predicate.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.set.

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.
  Variable s : S.   
  Variable P : pred S. 

Lemma brel_predicate_reduce_congruence : brel_congruence S eq eq -> brel_congruence S (brel_predicate_reduce s P eq) (brel_predicate_reduce s P eq). 
Proof. apply brel_reduce_congruence. Qed. 
  

Lemma brel_predicate_reduce_reflexive : brel_reflexive S (brel_predicate_reduce s P eq). 
Proof. apply brel_reduce_reflexive; auto. Qed. 

Lemma brel_predicate_reduce_symmetric : brel_symmetric S (brel_predicate_reduce s P eq). 
Proof. apply brel_reduce_symmetric; auto. Qed. 

Lemma brel_reduce_transitive : brel_transitive S (brel_predicate_reduce s P eq). 
Proof. apply brel_reduce_transitive; auto. Qed. 



End Theory.

Section ACAS.

Definition eqv_proofs_predicate_reduce : ∀ (S : Type) (eq : brel S) (s : S) (P : pred S) (brel_ast : ast_brel),
    eqv_proofs S eq → eqv_proofs S (brel_predicate_reduce s P eq) 
:= λ S eq s P brel_ast eqv, 
   {| 
     A_eqv_congruence  := brel_predicate_reduce_congruence S eq s P (A_eqv_congruence S eq eqv) 
   ; A_eqv_reflexive   := brel_predicate_reduce_reflexive S eq (A_eqv_reflexive S eq eqv) s P
   ; A_eqv_transitive  := brel_predicate_reduce_transitive S s P eq (A_eqv_transitive S eq eqv)
   ; A_eqv_symmetric   := brel_predicate_reduce_symmetric S eq (A_eqv_symmetric S eq eqv)  s P
   ; A_eqv_type_ast    := A_eqv_type_ast S eq eqv
   ; A_eqv_brel_ast    := brel_ast                                                           
   |}. 


Definition A_eqv_predicate_reduce
           (S : Type)
           (eqvS : A_eqv S)
           (s : S)
           (P : pred S)           
           (f : S -> S)
           (nt: brel_not_trivial S (brel_predicate_reduce s P (A_eqv_eq S eqvS)) f)
           (ex2 : brel_exactly_two_decidable S (brel_predicate_reduce s P (A_eqv_eq S eqvS)))
           (fnd : carrier_is_finite_decidable S (brel_predicate_reduce s P (A_eqv_eq S eqvS)))
           (brel_ast : ast_brel)           
           (ast : ast_eqv)
           : A_eqv S
:= 
  let eq  := A_eqv_eq S eqvS          in
  let wS  := A_eqv_witness S eqvS     in
  let eqP := A_eqv_proofs S eqvS      in
  let r   := uop_predicate_reduce s P in 
   {| 
      A_eqv_eq            := brel_predicate_reduce s P eq 
    ; A_eqv_proofs        := eqv_proofs_predicate_reduce S eq s P brel_ast eqP 
    ; A_eqv_witness       := r wS
    ; A_eqv_new           := f 
    ; A_eqv_not_trivial   := nt 
    ; A_eqv_exactly_two_d := ex2 
    ; A_eqv_data          := λ d, A_eqv_data S eqvS (r d)  
    ; A_eqv_rep           := r
    ; A_eqv_finite_d      := fnd 
    ; A_eqv_ast           := ast 
   |}. 


End ACAS.

Section CAS.


Definition eqv_predicate_reduce {S : Type}
     (s : S) (P : pred S) (f : S -> S) (ex2 : @check_exactly_two S) (fnd : @check_is_finite S)(eqvS : @eqv S) (brel_ast : ast_brel) (ast : ast_eqv) : @eqv S
:= 
  let eq := eqv_eq eqvS in
  let wS := eqv_witness eqvS in
  let r   := uop_predicate_reduce s P in   
 {| 
       eqv_eq       := brel_predicate_reduce s P eq
     ; eqv_certs    :=
     {|
       eqv_congruence     := @Assert_Brel_Congruence S 
     ; eqv_reflexive      := @Assert_Reflexive S
     ; eqv_transitive     := @Assert_Transitive S
     ; eqv_symmetric      := @Assert_Symmetric S
     ; eqv_type_ast       := eqv_type_ast (eqv_certs eqvS)                                               
     ; eqv_brel_ast       := brel_ast
     |}  
    ; eqv_witness := r wS
    ; eqv_new     := f 
    ; eqv_exactly_two_d := ex2 
    ; eqv_data    := λ d, eqv_data eqvS (r d)  
    ; eqv_rep     := r
    ; eqv_finite_d := fnd 
    ; eqv_ast     := ast
   |}. 

End CAS.

Section Verify.

Theorem correct_eqv_predicate_reduce : ∀ (S : Type) (E : A_eqv S) (s : S) (P : pred S) (f : S -> S) 
      (nt: brel_not_trivial S (brel_predicate_reduce s P (A_eqv_eq S E)) f)
      (ex2 :  brel_exactly_two_decidable S (brel_predicate_reduce s P (A_eqv_eq S E)))
      (fnd :  carrier_is_finite_decidable S (brel_predicate_reduce s P (A_eqv_eq S E)))
      (brel_ast : ast_brel)        
      (ast : ast_eqv),  
    eqv_predicate_reduce s P f (p2c_exactly_two_check _ _ ex2) (p2c_is_finite_check _ _ fnd) (A2C_eqv S E) brel_ast ast 
    =
    A2C_eqv S(A_eqv_predicate_reduce S E s P f nt ex2 fnd brel_ast ast).
Proof. intros S E s P f nt ex2 fnd brel_ast ast. destruct E; compute; auto. Qed.        

End Verify.   
  