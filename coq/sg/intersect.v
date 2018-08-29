
Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.sg.add_id. 

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S eq f. 
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.

Lemma in_set_bop_intersect_intro : ∀ (X Y : finite_set S) (a : S),
       (in_set eq X a = true) * (in_set eq Y a = true) → in_set eq (bop_intersect eq X Y) a = true. 
Proof. intros X Y a H. unfold bop_intersect. 
       apply in_set_filter_intro; auto.
       apply in_set_bProp_congruence; auto.
Qed. 


Lemma in_set_bop_intersect_elim : ∀ (X Y : finite_set S) (a : S),
       in_set eq (bop_intersect eq X Y) a = true  → (in_set eq X a = true) * (in_set eq Y a = true). 
Proof. intros X Y a H. 
       unfold bop_intersect in H. 
       apply in_set_filter_elim in H. assumption.
       apply in_set_bProp_congruence; auto. 
Qed. 

(* 

Issue with intersect : If the carrier set S is infinite, 
then the id for intersect is not a finite set. 
Even if S is a finite set, it can be enormous, with no good way 
of representing it.  Therefore, we define a constructon 
that forces the definition of a new constant representing 
the id. 


The "bop_intersect_..._raw" results below capture the properties 
of union before the id is added. 

*) 





Lemma bop_intersect_congruence_raw : bop_congruence (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. unfold bop_intersect. unfold bop_congruence. 
       assert (fact := brel_set_congruence S eq refS symS tranS). 
       intros s1 s2 t1 t2 H1 H2. 
       unfold brel_congruence in fact. 
       apply brel_set_intro_prop; auto. 
       split. 
          intros a J. 
          apply in_set_filter_intro; auto.
          apply in_set_bProp_congruence; auto.
          apply in_set_filter_elim in J. destruct J as [JL JR].
          assert(fact1 := in_set_left_congruence S eq symS tranS a _ _ H1).
          assert(fact2 := in_set_left_congruence S eq symS tranS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 
          apply in_set_bProp_congruence; auto. 
          intros a J. 
          apply in_set_filter_intro; auto.
          apply in_set_bProp_congruence; auto. 
          apply in_set_filter_elim in J. destruct J as [JL JR]. 
          assert(fact1 := in_set_left_congruence S eq symS tranS a _ _ H1).
          assert(fact2 := in_set_left_congruence S eq symS tranS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 
       apply in_set_bProp_congruence; auto. 
Qed. 

(* simplify?  theorems about composition? *) 
Lemma bop_intersect_associative_raw : bop_associative (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intros s t u. apply brel_set_intro_prop; auto. 
       split. 
          intros a H.
          assert (J : bProp_congruence S eq (in_set eq s)). apply in_set_bProp_congruence; auto.
          assert (K : bProp_congruence S eq (in_set eq t)). apply in_set_bProp_congruence; auto.          
         apply in_set_filter_intro; auto. 
         apply in_set_filter_elim in H; auto.  
         destruct H as [HL HR]. apply in_set_filter_elim in HL; auto. 
         destruct HL as [HLL HLR]. 
         split;auto.            
            apply in_set_filter_intro; auto. 
            apply in_set_bProp_congruence; auto.

         intros a H. 
         apply in_set_filter_intro; auto. 
         apply in_set_bProp_congruence; auto.
         assert (J : bProp_congruence S eq (in_set eq s)). apply in_set_bProp_congruence; auto.
         assert (K : bProp_congruence S eq (in_set eq t)). apply in_set_bProp_congruence; auto.          
         apply in_set_filter_elim in H; auto. 
         destruct H as [HL HR]. apply in_set_filter_elim in HR; auto. 
         destruct HR as [HRL HRR]. 
         split; auto. 
            apply in_set_filter_intro; auto. 
Qed. 

Lemma bop_intersect_idempotent_raw : bop_idempotent (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intro s. destruct s. 
          compute. reflexivity.
          unfold brel_set. unfold brel_and_sym. apply andb_is_true_right. 
          split.
             apply brel_subset_intro; auto. 
             intros x H. 
             apply in_set_filter_elim in H.
             destruct H as [HL HR]. assumption. 
             apply in_set_bProp_congruence; auto.
             apply brel_subset_intro; auto. 
             intros x H. 
             apply in_set_filter_intro; auto. 
             apply in_set_bProp_congruence; auto.
Qed. 

Lemma uop_filter_false_is_nil : ∀ (X : finite_set S), filter (λ _ : S, false) X = nil.
Proof. unfold uop_filter. induction X; compute; auto. Qed. 

Lemma bop_intersect_commutative_raw : bop_commutative(finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intros s t. destruct s; destruct t. 
          compute; auto.
          unfold bop_intersect.  unfold in_set at 1. 
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          unfold bop_intersect.  unfold in_set at 2.           
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          apply brel_set_intro_prop; auto. 
          split; intros x H. 
             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro; auto.
             apply in_set_bProp_congruence; auto.
             apply in_set_bProp_congruence; auto.             

             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro; auto.
             apply in_set_bProp_congruence; auto.
             apply in_set_bProp_congruence; auto.             
Qed. 

Lemma bop_intersect_not_selective_raw : bop_not_selective (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists ((wS ::nil), ((f wS) :: nil)).
       destruct (ntS wS) as [L R].
       split; unfold bop_intersect; unfold uop_filter; unfold filter; unfold in_set; rewrite R; compute; auto. 
Defined. 

Lemma bop_intersect_nil :  ∀ (X : finite_set S), brel_set eq (bop_intersect eq nil X) nil = true. 
Proof. intro X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_intersect_elim in H; auto. 
       destruct H as [HL  HR]. 
       assumption. 
       apply brel_subset_intro; auto. 
       intros a H. compute in H. discriminate. 
Defined. 


Lemma bop_intersect_nil_is_ann : bop_is_ann (finite_set S) (brel_set eq) (bop_intersect eq) nil. 
Proof. unfold bop_is_ann. 
       intro s. 
       assert (fact1 : brel_set eq (bop_intersect eq nil s) nil = true). 
          apply bop_intersect_nil; auto. 
       assert (fact2 : brel_set eq (bop_intersect eq s nil) (bop_intersect eq nil s) = true). 
          apply bop_intersect_commutative_raw; auto. 
       assert (fact3 : brel_set eq (bop_intersect eq s nil) nil = true). 
          apply (brel_set_transitive S eq refS symS tranS _ _ _ fact2 fact1). 
       rewrite fact1, fact3. auto. 
Defined. 


Lemma bop_intersect_exists_ann_raw : bop_exists_ann (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists nil. apply bop_intersect_nil_is_ann. Defined. 


(* ************************************* cooked ************************************* *) 

Variable c : cas_constant. 

Lemma bop_intersect_associative : 
        bop_associative
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_associative; auto. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_associative_raw; auto. 
Qed. 


Lemma bop_intersect_congruence : 
        bop_congruence
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_congruence; auto.
       apply brel_set_symmetric; auto.        
       apply bop_intersect_congruence_raw; auto.        
Qed. 


Lemma bop_intersect_commutative : 
        bop_commutative
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_commutative; auto. 
       apply brel_set_reflexive; auto. 
       apply bop_intersect_commutative_raw; auto. 
Qed. 

Lemma bop_intersect_idempotent : 
        bop_idempotent
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_idempotent. apply bop_intersect_idempotent_raw; auto. Qed. 

Lemma bop_intersect_not_selective : 
        bop_not_selective
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_not_selective. apply bop_intersect_not_selective_raw; auto. Defined. 

Lemma bop_intersect_exists_id : 
        bop_exists_id
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_exists_id.  apply brel_set_reflexive; auto. Defined. 


Lemma bop_intersect_exists_ann : 
        bop_exists_ann
            (with_constant (finite_set S)) 
            (@brel_add_constant (finite_set S) (brel_set eq) c)
            (@bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. apply bop_add_id_exists_ann; auto. 
       apply brel_set_reflexive; auto.        
       apply bop_intersect_exists_ann_raw; auto. 
Defined. 

(* not needed as intersect is sg_CI ?
Lemma bop_intersect_not_is_left : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_is_left
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply bop_commutative_implies_not_is_left. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply brel_add_constant_symmetric; auto.      
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_transitive; auto.      
       apply brel_set_transitive; auto. 
       apply bop_intersect_commutative; auto. 
Defined. 



Lemma bop_intersect_not_is_right : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_is_right
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply bop_commutative_implies_not_is_right. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply brel_add_constant_symmetric; auto.      
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_transitive; auto.      
       apply brel_set_transitive; auto. 
       apply bop_intersect_commutative; auto. 
Defined. 



Lemma bop_intersect_not_left_cancellative : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_left_cancellative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_ann_implies_not_left_cancellative. 
       apply brel_add_constant_reflexive. 
       apply brel_set_reflexive; auto. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_ann; auto. 
Defined. 



Lemma bop_intersect_not_right_cancellative : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_right_cancellative
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_ann_implies_not_right_cancellative. 
       apply brel_add_constant_reflexive. 
       apply brel_set_reflexive; auto. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_ann; auto. 
Defined. 


Lemma bop_intersect_not_left_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_left_constant
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_id_implies_not_left_constant. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_right_constant : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_nontrivial S eq -> 
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_right_constant
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c ntS refS symS transS. 
       apply exists_id_implies_not_right_constant. 
       apply brel_add_constant_congruence. 
       apply brel_set_congruence; auto. 
       apply brel_add_constant_nontrivial. 
       apply brel_set_nontrivial; auto. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_anti_left : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_anti_left
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c refS symS transS. 
       apply exists_id_implies_not_anti_left. 
       apply brel_add_constant_symmetric; auto.
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_witness. 
       apply brel_set_witness. 
       apply bop_intersect_exists_id; auto. 
Defined. 


Lemma bop_intersect_not_anti_right : ∀ (S : Type) (r : brel S) (c : cas_constant),
       brel_reflexive S eq -> 
       brel_symmetric S eq -> 
       brel_transitive S eq -> 
        bop_not_anti_right
            (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set eq) c)
            (bop_add_id (finite_set S) (bop_intersect eq) c). 
Proof. intros S eq c refS symS transS. 
       apply exists_id_implies_not_anti_right. 
       apply brel_add_constant_symmetric; auto.
       apply brel_set_symmetric; auto. 
       apply brel_add_constant_witness. 
       apply brel_set_witness. 
       apply bop_intersect_exists_id; auto. 
Defined. 

*) 

End Theory.

Section ACAS.

Definition sg_CI_proofs_intersect : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS ->
        sg_CI_proofs (with_constant (finite_set S)) (brel_add_constant (brel_set rS) c) (bop_add_id (bop_intersect rS) c)
:= λ S rS c s f ntS eqvS,
   let refS := A_eqv_reflexive S rS eqvS in
   let symS := A_eqv_symmetric S rS eqvS in
   let tranS := A_eqv_transitive S rS eqvS in                                                            
{|
  A_sg_CI_associative        := bop_intersect_associative S rS refS symS tranS c
; A_sg_CI_congruence         := bop_intersect_congruence S rS  refS symS tranS c 
; A_sg_CI_commutative        := bop_intersect_commutative S rS refS symS tranS c
; A_sg_CI_idempotent         := bop_intersect_idempotent S rS refS symS tranS c
; A_sg_CI_selective_d        := inr _ (bop_intersect_not_selective S rS s f ntS c)
; A_sg_CI_exists_id_d        := inl _ (bop_intersect_exists_id S rS refS symS c)
; A_sg_CI_exists_ann_d       := inl _ (bop_intersect_exists_ann S rS refS symS tranS c)
|}. 


Definition A_sg_CI_intersect : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_sg_CI (with_constant (finite_set S)) 
  := λ S c eqv,
  let eqS := A_eqv_eq S eqv in
  let s   := A_eqv_witness S eqv in
  let f   := A_eqv_new S eqv in
  let ntS := A_eqv_not_trivial S eqv in       
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant (finite_set S) (A_eqv_set S eqv) c  
   ; A_sg_CI_bop       := bop_add_id (bop_intersect eqS) c
   ; A_sg_CI_proofs    := sg_CI_proofs_intersect S eqS c s f ntS (A_eqv_proofs S eqv)
   ; A_sg_CI_bop_ast   := Ast_bop_add_id(c, Ast_bop_intersect (A_eqv_ast S eqv)) 
   ; A_sg_CI_ast       := Ast_sg_CI_intersect_with_id (c, A_eqv_ast S eqv)
   |}. 
  


End ACAS.

Section CAS.

Definition sg_CI_certs_intersect : ∀ {S : Type},  cas_constant -> S -> (S -> S) -> @sg_CI_certificates (with_constant (finite_set S))
:= λ {S} c s f,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := Certify_Not_Selective (inr (s :: nil), inr ((f s) :: nil))
; sg_CI_exists_id_d        := Certify_Exists_Id  (inl c) 
; sg_CI_exists_ann_d       := Certify_Exists_Ann  (inr nil) 
|}. 



Definition sg_CI_intersect : ∀ {S : Type} (c : cas_constant), @eqv S -> @sg_CI (with_constant (finite_set S)) 
:= λ {S} c eqvS,
  let eqS := eqv_eq eqvS in
  let s   := eqv_witness eqvS in
  let f   := eqv_new eqvS in
   {| 
     sg_CI_eqv       := eqv_add_constant (eqv_set eqvS) c  
   ; sg_CI_bop       := bop_add_id (bop_intersect eqS) c
   ; sg_CI_certs     := sg_CI_certs_intersect c s f
   ; sg_CI_bop_ast   := Ast_bop_add_id(c, Ast_bop_intersect (eqv_ast eqvS))                                               
   ; sg_CI_ast       := Ast_sg_CI_intersect_with_id (c, eqv_ast eqvS)
   |}. 

End CAS.

Section Verify.

Variable S : Type.
Variable c : cas_constant.

Theorem bop_intersect_certs_correct : 
    ∀ (eqvS : A_eqv S), 
      sg_CI_certs_intersect c (A_eqv_witness S eqvS) (A_eqv_new S eqvS)
      =                        
      P2C_sg_CI (with_constant (finite_set S))
                (brel_add_constant (brel_set (A_eqv_eq S eqvS)) c)
                (bop_add_id (bop_intersect (A_eqv_eq S eqvS)) c)
                (sg_CI_proofs_intersect S (A_eqv_eq S eqvS) c
                                    (A_eqv_witness S eqvS)
                                    (A_eqv_new S eqvS)
                                    (A_eqv_not_trivial S eqvS)
                                    (A_eqv_proofs S eqvS)).
Proof. intro eqvS.
       destruct eqvS.
       unfold sg_CI_certs_intersect, sg_CI_proofs_intersect. unfold P2C_sg_CI. simpl.
       reflexivity. 
Qed. 


    
Theorem bop_intersect_correct : 
    ∀ (eqvS : A_eqv S), 
         sg_CI_intersect c (A2C_eqv S eqvS)  
         = 
         A2C_sg_CI (with_constant (finite_set S)) (A_sg_CI_intersect S c eqvS). 
Proof. intro eqvS. unfold sg_CI_intersect, A_sg_CI_intersect. unfold A2C_sg_CI. simpl.
       unfold add_constant.A_eqv_add_constant, add_constant.eqv_add_constant; simpl. unfold A2C_eqv. simpl. 
       rewrite bop_intersect_certs_correct. 
       reflexivity. 
Qed.
 
End Verify.   
  