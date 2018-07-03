Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 


Section Product. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.
Variable refS : brel_reflexive S rS. 
Variable refT : brel_reflexive T rT. 

Notation "a <*> b"  := (brel_product a b) (at level 15).


(*

Lemma brel_product_witness : (brel_witness S rS) -> (brel_witness T rT) -> brel_witness (S * T) (rS <*> rT). 
Proof. intros wS wT. destruct wS as [s PS]; destruct wT as [t PT]. 
       exists (s, t); compute. rewrite PS, PT. auto. 
Defined. 



Lemma brel_product_negate : 
              (brel_negate S rS) → (brel_negate T rT) 
              → brel_negate (S * T) (rS <*> rT). 
Proof. 
     intros [fS PS] [fT PT]. 
     exists (λ (p : S * T), let (x, y) := p in (fS x, fT y)).
     intros (s, t). simpl. 
     destruct (PS s) as [LS RS]; destruct (PT t) as [LT RT].
     rewrite LS, RS, LT, RT; auto. 
Defined.




Definition brel_product_nontrivial : (brel_nontrivial S rS) → (brel_nontrivial T rT) → 
         brel_nontrivial (S * T) (rS <*> rT)
:= λ ntS ntT, 
   {| 
      brel_nontrivial_witness  := brel_product_witness 
                                     (brel_nontrivial_witness S rS ntS)
                                     (brel_nontrivial_witness T rT ntT)
    ; brel_nontrivial_negate   := brel_product_negate 
                                     (brel_nontrivial_negate S rS ntS)
                                     (brel_nontrivial_negate T rT ntT)
   |}. 


Lemma brel_product_rep_correct : 
       ∀ (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_correct S rS repS) → 
              (brel_rep_correct T rT repT) → 
                 brel_rep_correct (S * T) (rS <*> rT) (uop_product repS repT). 
Proof. 
     intros repS repT RS RT [s t]. compute. 
     rewrite (RS s), (RT t). reflexivity. 
Defined. 

Lemma brel_product_rep_idempotent : 
       ∀ (repS : unary_op S) (repT : unary_op T),  
              (brel_rep_idempotent S rS repS) → 
              (brel_rep_idempotent T rT repT) → 
                 brel_rep_idempotent (S * T) (rS <*> rT) (uop_product repS repT). 
Proof. 
     intros repS repT RS RT [s t]. compute. 
     rewrite (RS s), (RT t). reflexivity. 
Defined. 
*) 

Lemma brel_product_not_trivial (f : S -> S) : 
              (brel_not_trivial S rS f) → brel_not_trivial (S * T) (rS <*> rT) (λ (p : S * T), let (s, t) := p in (f s, t)).
Proof. intros Pf [s t]. simpl. destruct (Pf s) as [L R].
     rewrite L, R. rewrite (refT t). simpl. auto. 
Defined.


Lemma brel_product_congruence : 
         ∀ (r1 : brel S) (r2 : brel T),  brel_congruence S rS r1  → brel_congruence T rT r2  → 
               brel_congruence (S * T) (rS <*> rT) (r1 <*> r2). 
Proof. unfold brel_congruence. intros r1 r2 C1 C2. 
       intros [s1 s2] [t1 t2] [u1 u2] [v1 v2]. unfold brel_product. 
       intros H1 H2. 
       apply andb_is_true_left in H1. destruct H1 as [L1 R1]. 
       apply andb_is_true_left in H2. destruct H2 as [L2 R2]. 
       rewrite (C1 _ _ _ _ L1 L2). 
       rewrite (C2 _ _ _ _ R1 R2). reflexivity. 
Defined.





(* **** *)


Lemma brel_product_transitive : 
              (brel_transitive _ rS) → (brel_transitive _ rT) → brel_transitive (S * T) (rS <*> rT). 
Proof. unfold brel_transitive. intros RS RT [s1 t1] [s2 t2] [s3 t3]; simpl. 
     intros.           
     apply andb_is_true_right. 
     apply andb_is_true_left in H. 
     apply andb_is_true_left in H0. 
     destruct H as [H_l H_r]. 
     destruct H0 as [H0_l H0_r]. 
     split. 
        apply (RS _ _ _ H_l H0_l). 
        apply (RT _ _ _ H_r H0_r). 
Defined. 




Lemma brel_product_reflexive : 
              (brel_reflexive _ rS) → (brel_reflexive _ rT) 
               → brel_reflexive (S * T) (rS <*> rT). 
Proof. unfold brel_reflexive. intros RS RT [s t].
       simpl. rewrite (RS s), (RT t). simpl. reflexivity. 
Defined. 


Lemma brel_product_not_reflexive_left : ∀ (t : T),   (brel_not_reflexive _ rS) 
               → brel_not_reflexive (S * T) (rS <*> rT). 
Proof. unfold brel_not_reflexive. intros t [s P]. 
        exists (s, t). compute. rewrite P. reflexivity. 
Defined. 

Lemma brel_product_not_reflexive_right : ∀ (s : S),   (brel_not_reflexive _ rT) 
               → brel_not_reflexive (S * T) (rS <*> rT). 
Proof. unfold brel_not_reflexive. intros s [t P]. 
        exists (s, t). compute. rewrite P. case_eq(rS s s); intro H; auto. 
Defined. 

Definition brel_product_reflexive_decide: 
   ∀ (s : S) (t : T),    
     brel_reflexive_decidable S rS → 
     brel_reflexive_decidable T rT → 
        brel_reflexive_decidable (S * T) (rS <*> rT)
:= λ s t dS dT,  
       match dS with 
       | inl refS => 
         match dT with 
         | inl refT     => inl _ (brel_product_reflexive refS refT)
         | inr not_refT => inr _ (brel_product_not_reflexive_right s not_refT)
         end 
       | inr not_refS   => inr _ (brel_product_not_reflexive_left t not_refS)
       end. 

Lemma brel_product_irreflexive_left : brel_irreflexive S rS -> brel_irreflexive (S * T) (rS <*> rT). 
Proof. unfold brel_irreflexive. intros irr [s t]. compute. rewrite (irr s). reflexivity. Defined. 

Lemma brel_product_irreflexive_right : brel_irreflexive T rT -> brel_irreflexive (S * T) (rS <*> rT). 
Proof. unfold brel_irreflexive. intros irr [s t]. compute. rewrite (irr t). case_eq(rS s s); intro H; auto. Defined. 

Lemma brel_product_not_irreflexive : brel_not_irreflexive S rS -> brel_not_irreflexive T rT -> 
           brel_not_irreflexive (S * T) (rS <*> rT). 
Proof. unfold brel_not_irreflexive. intros [s P] [t Q]. exists (s, t). compute. rewrite P, Q; auto. Defined. 

Definition brel_product_irreflexive_decide: 
     brel_irreflexive_decidable S rS → 
     brel_irreflexive_decidable T rT → 
        brel_irreflexive_decidable (S * T) (rS <*> rT)
:= λ dS dT,  
       match dS with 
       | inl irrS => inl _ (brel_product_irreflexive_left irrS)
       | inr not_irrS   => 
         match dT with 
         | inl irrT     => inl _ (brel_product_irreflexive_right irrT)
         | inr not_irrT => inr _ (brel_product_not_irreflexive not_irrS not_irrT)
         end 
       end. 



Lemma brel_product_symmetric : (brel_symmetric _ rS) → (brel_symmetric _ rT) → brel_symmetric (S * T) (rS <*> rT). 
Proof. unfold brel_symmetric. intros RS RT [s1 t1] [s2 t2]; simpl. 
     intros.           
     apply andb_is_true_right. 
     apply andb_is_true_left in H. 
     destruct H as [H_l H_r].  
     split. 
        apply (RS _ _ H_l). 
        apply (RT _ _ H_r). 
Defined. 


Lemma brel_product_not_symmetric_left : brel_not_symmetric S rS → T → 
         brel_not_symmetric (S * T) (rS <*> rT). 
Proof. unfold brel_not_symmetric. 
       intros [ [s1 s2] [P1 P2]] t. 
       exists ((s1, t), (s2, t)). compute. 
       rewrite P1, P2, (refT t). auto. 
Defined. 


Lemma brel_product_not_symmetric_right : brel_not_symmetric T rT → S → 
         brel_not_symmetric (S * T) (rS <*> rT). 
Proof. unfold brel_not_symmetric. intros [ [t1 t2] [P1 P2]] s. 
       exists ((s, t1), (s, t2)). compute. rewrite P1, P2, (refS s). auto. 
Defined. 

Definition brel_product_symmetric_decide: 
     S -> T -> brel_symmetric_decidable S rS → brel_symmetric_decidable T rT → 
        brel_symmetric_decidable (S * T) (rS <*> rT)
:= λ wS wT dS dT,  
       match dS with 
       | inl symS => 
         match dT with 
         | inl symT     => inl _ (brel_product_symmetric symS symT)
         | inr not_symT => inr _ (brel_product_not_symmetric_right not_symT wS)
         end 
       | inr not_symS   => inr _ (brel_product_not_symmetric_left not_symS wT)
       end.

Lemma brel_product_not_total (s : S) (f : S -> S) (t : T): 
  brel_not_trivial S rS f ->
      brel_not_total (S * T) (rS <*> rT). 
Proof. intros Pf. exists ((s, t), (f s, t)). compute. 
       destruct (Pf s) as [sL sR]. 
       rewrite sL, sR. auto. 
Defined. 

Close Scope nat_scope. 

Lemma brel_total_split (s : S) ( f : S -> S) : 
      brel_total S rS -> 
      brel_not_trivial S rS f -> 
      brel_antisymmetric S rS rS -> 
      {s1 : S & {s2 : S & (rS s2 s1 = true) * (rS s1 s2 = false) }}. 
Proof. intros totS Pf antiS. 
       unfold brel_antisymmetric in antiS. 
       destruct (Pf s) as [L R].
       case_eq(rS s (f s)); intro F1;  case_eq(rS (f s) s); intro F2. 
          rewrite (antiS _ _ F1 F2) in L. discriminate. 
          exists (f s); exists s; split; assumption. 
          exists s; exists (f s); split; assumption. 
          destruct (totS s (f s)) as [F | F].          
             rewrite F in F1. discriminate.
             rewrite F in F2. discriminate.
Defined. 

(*
Lemma brel_product_total_decide_v2 : 
   ∀ (eqS : brel S) 
     (eqT : brel T),  
      brel_nontrivial S eqS -> 
      brel_nontrivial T eqT ->      
      brel_antisymmetric S eqS rS -> 
      brel_antisymmetric T eqT rT -> 
      brel_total_decidable S rS -> 
      brel_total_decidable T rT -> 
           brel_total_decidable (S * T) (rS <*> rT). 
Proof. 
  intros eqS eqT ntS ntT antiS antiT.
  destruct (brel_nontrivial_witness S eqS ntS) as [s QS]. 
  destruct (brel_nontrivial_witness T eqT ntT) as [t QT]. 
  destruct (brel_nontrivial_negate S eqS ntS) as [fS fSP]. 
  destruct (brel_nontrivial_negate T eqT ntT) as [fT fTP]. 
  intros [ totS | [ [s1 s2] [SL SR]]] [ totT | [ [t1 t2] [TL TR]]]. 
     destruct (brel_total_split totS ntS antiS) as [s1 [s2 [sP1 sP2]]]. 
     destruct (brel_total_split totT ntT antiT) as [t1 [t2 [tP1 tP2]]]. 
     right. exists ((s1, t2), (s2, t1)). simpl.  
     rewrite sP2, tP2. simpl. rewrite andb_comm. simpl. auto. 
     right. exists ((s, t1), (s, t2)); simpl. rewrite TL, TR. rewrite andb_comm; compute; auto.
     right. exists ((s1, t), (s2, t)); simpl. rewrite SL, SR. compute; auto.
     right. exists ((s, t1), (s, t2)); simpl. rewrite TL, TR. rewrite andb_comm; compute; auto.
Defined. 




Lemma brel_product_asymmetric_left : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_asymmetric S rS) → 
                  brel_asymmetric (S * T) (rS <*> rT). 
Proof. unfold brel_asymmetric. 
     intros S T rS rT AS [s1 t1] [s2 t2]. simpl. intro H. 
     apply andb_is_false_right. apply andb_is_true_left in H. destruct H as [L R]. 
     left. rewrite (AS _ _ L). reflexivity. 
Defined. 

Lemma brel_product_asymmetric_right : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_asymmetric T rT) → 
                  brel_asymmetric (S * T) (rS <*> rT). 
Proof. unfold brel_asymmetric. 
     intros S T rS rT AT [s1 t1] [s2 t2]. simpl. intro H. 
     apply andb_is_false_right. apply andb_is_true_left in H. destruct H as [L R]. 
     right. rewrite (AT _ _ R). reflexivity. 
Defined. 


Lemma brel_product_not_asymmetric : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_not_asymmetric S rS) → 
              (brel_not_asymmetric T rT) → 
                  brel_not_asymmetric (S * T) (rS <*> rT). 
Proof. unfold brel_not_asymmetric. 
     intros S T rS rT [ [s1 s2] [P1 P2]] [ [t1 t2] [Q1 Q2]]. 
     exists ((s1, t1), (s2, t2)); simpl. rewrite P1, P2, Q1, Q2. simpl. auto. 
Defined. 


Definition brel_product_asymmetric_decide: 
   ∀ (S T: Type) 
     (rS : brel S) 
     (rT : brel T),   
     brel_asymmetric_decidable S rS → 
     brel_asymmetric_decidable T rT → 
        brel_asymmetric_decidable (S * T) (rS <*> rT)
:= λ S T rS rT dS dT,  
       match dS with 
       | inl asymS       => inl _ (brel_product_asymmetric_left S T rS rT asymS)
       | inr not_asymS   => 
         match dT with 
         | inl asymT     => inl _ (brel_product_asymmetric_right S T rS rT asymT)
         | inr not_asymT => inr _ (brel_product_not_asymmetric S T rS rT not_asymS not_asymT)
         end 
       end. 


Lemma brel_product_has_2_chain : 
         ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_has_2_chain S rS) → 
              (brel_has_2_chain T rT) → 
                  brel_has_2_chain (S * T) (rS <*> rT). 
                  
Proof. intros S T rS rT [ [s1 [s2 s3]] [P1 P2] ] [ [t1 [t2 t3]] [Q1 Q2] ]. 
       exists ((s1, t1), ((s2, t2), (s3, t3))); simpl. 
       rewrite P1, P2, Q1, Q2. simpl. auto. 
Defined. 

Lemma brel_product_not_has_2_chain_left : 
         ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_not_has_2_chain S rS) → 
                  brel_not_has_2_chain (S * T) (rS <*> rT). 
Proof. unfold brel_not_has_2_chain. intros S T rS rT C [s1 t1] [s2 t2] [s3 t3]. simpl. 
       intro H. apply andb_is_true_left in H. destruct H as [L R]. 
       apply andb_is_false_right. left. rewrite (C _ _ s3 L). reflexivity. 
Defined. 

Lemma brel_product_not_has_2_chain_right : 
         ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_not_has_2_chain T rT) → 
                  brel_not_has_2_chain (S * T) (rS <*> rT). 
Proof. unfold brel_not_has_2_chain. intros S T rS rT C [s1 t1] [s2 t2] [s3 t3]. simpl. 
       intro H. apply andb_is_true_left in H. destruct H as [L R]. 
       apply andb_is_false_right. right. rewrite (C _ _ t3 R). reflexivity. 
Defined. 



Definition brel_product_has_2_chain_decide: 
   ∀ (S T: Type) 
     (rS : brel S) 
     (rT : brel T),   
     brel_has_2_chain_decidable S rS → 
     brel_has_2_chain_decidable T rT → 
        brel_has_2_chain_decidable (S * T) (rS <*> rT)
:= λ S T rS rT dS dT,  
       match dS with 
       | inl h2cS       => 
         match dT with 
         | inl h2cT     => inl _ (brel_product_has_2_chain S T rS rT h2cS h2cT)
         | inr not_h2cT => inr _ (brel_product_not_has_2_chain_right S T rS rT not_h2cT)
         end 
       | inr not_h2cS   => inr _ (brel_product_not_has_2_chain_left S T rS rT not_h2cS)
       end. 


Lemma brel_product_transitive_left : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_not_has_2_chain S rS) → 
                  brel_transitive (S * T) (rS <*> rT). 
Proof. 
     intros S T rS rT C [s1 t1] [s2 t2] [s3 t3]. simpl.  intros H1 H2. 
     apply andb_is_true_left in H1. destruct H1 as [L R]. 
     rewrite (C _ _ s3 L) in H2. simpl in H2. discriminate. 
Defined. 


Lemma brel_product_transitive_right : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_not_has_2_chain T rT) → 
                  brel_transitive (S * T) (rS <*> rT). 
Proof. 
     intros S T rS rT C [s1 t1] [s2 t2] [s3 t3]. simpl.  intros H1 H2. 
     apply andb_is_true_left in H1. destruct H1 as [L R]. 
     rewrite (C _ _ t3 R) in H2. rewrite andb_comm in H2. simpl in H2. discriminate. 
Defined. 


Lemma brel_product_not_transitive_right : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_has_2_chain S rS) → 
              (brel_not_transitive T rT) → 
                  brel_not_transitive (S * T) (rS <*> rT). 
Proof. intros S T rS rT [ [s1 [s2 s3]] [P1 P2] ] [ [t1 [t2 t3]] [[Q1 Q2] Q3] ]. 
       exists ((s1, t1), ((s2, t2), (s3, t3))); simpl. 
       rewrite P1, P2, Q1, Q2, Q3. simpl. rewrite andb_comm. simpl. auto. 
Defined. 

Lemma brel_product_not_transitive_left : ∀ (S T: Type) (rS : brel S) (rT : brel T),  
              (brel_not_transitive S rS) → 
              (brel_has_2_chain T rT) → 
                  brel_not_transitive (S * T) (rS <*> rT). 
Proof. intros S T rS rT [ [s1 [s2 s3]] [ [P1 P2] P3 ] ] [ [t1 [t2 t3]] [Q1 Q2] ]. 
       exists ((s1, t1), ((s2, t2), (s3, t3))); simpl. 
       rewrite P1, P2, P3, Q1, Q2. simpl. auto. 
Defined. 

Definition brel_product_transitive_decide : 
   ∀ (S T: Type) 
     (rS : brel S) 
     (rT : brel T),   
     brel_has_2_chain_decidable S rS →  
     brel_has_2_chain_decidable T rT →  
     brel_transitive_decidable S rS → 
     brel_transitive_decidable T rT → 
        brel_transitive_decidable (S * T) (rS <*> rT)
:= λ S T rS rT h2S h2T dS dT,  
       match dS with 
       | inl transS => 
         match dT with 
         | inl transT     => inl _ (brel_product_transitive S T rS rT transS transT)
         | inr not_transT => 
           match h2S with 
           | inl h2cS     => inr _ (brel_product_not_transitive_right S T rS rT h2cS not_transT)
           | inr not_h2cS => inl _ (brel_product_transitive_left S T rS rT not_h2cS)
           end 
         end 
       | inr not_transS   => 
           match h2T with 
           | inl h2cT     => inr _ (brel_product_not_transitive_left S T rS rT not_transS h2cT)
           | inr not_h2cT => inl _ (brel_product_transitive_right S T rS rT not_h2cT) 
           end 
       end. 

Lemma brel_product_antisymmetric : 
         ∀ (S T: Type) (r_eq1 : brel S) (r_eq2 : brel T) (r1 : brel S) (r2 : brel T),  
              (brel_antisymmetric S r_eq1 r1) → 
              (brel_antisymmetric T r_eq2 r2) → 
              brel_antisymmetric (S * T) 
                  (brel_product S T r_eq1 r_eq2)
                  (brel_product S T r1 r2). 
Proof. 
     intros S T r_eq1 r_eq2 r1 r2 asS asT [s1 t1] [s2 t2]; simpl. intros H1 H2.                
     destruct (andb_is_true_left _ _ H1) as [L1 R1]; destruct (andb_is_true_left _ _ H2) as [L2 R2].
     rewrite (asS s1 s2 L1 L2). rewrite (asT t1 t2 R1 R2). auto. 
Defined. 


Lemma brel_product_with_reflexivity_not_antisymmetric_left : 
         ∀ (S T: Type) (r_eq1 : brel S) (r_eq2 : brel T) (r1 : brel S) (r2 : brel T) (t : T),  
              (brel_reflexive T r2) → 
              (brel_not_antisymmetric S r_eq1 r1) → 
              brel_not_antisymmetric (S * T) 
                  (brel_product S T r_eq1 r_eq2)
                  (brel_product S T r1 r2). 
Proof. unfold brel_not_antisymmetric. 
     intros S T r_eq1 r_eq2 r1 r2 t refT [ [s1 s2] [[H1 H2] H3] ]; simpl. 
     exists ((s1, t), (s2, t)); simpl. 
     rewrite H1, H2, H3. simpl. rewrite (refT t); auto. 
Defined.


Lemma brel_product_with_reflexivity_not_antisymmetric_right : 
         ∀ (S T: Type) (eq1 : brel S) (eq2 : brel T) (r1 : brel S) (r2 : brel T) (s : S),  
              brel_reflexive S r1 → 
              brel_not_antisymmetric T eq2 r2 → 
              brel_not_antisymmetric (S * T) 
                  (brel_product S T eq1 eq2)
                  (brel_product S T r1 r2). 
Proof. 
     intros S T eq1 eq2 r1 r2 s refS [ [t1 t2] [[H1 H2] H3] ]; simpl. 
     exists ((s, t1), (s, t2)); simpl. 
     rewrite H1, H2, H3. simpl. rewrite (refS s). simpl; auto. 
     rewrite andb_comm. simpl; auto. 
Defined.


Definition brel_product_with_reflexivity_antisymmetric_decide : 
   ∀ (S T: Type) 
     (eqS : brel S) 
     (eqT : brel T)
     (rS : brel S) 
     (rT : brel T),   
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_reflexive S rS -> 
     brel_reflexive T rT -> 
     brel_antisymmetric_decidable S eqS rS → 
     brel_antisymmetric_decidable T eqT rT → 
        brel_antisymmetric_decidable (S * T) (brel_product S T eqS eqT) (rS <*> rT)
:= λ S T eqS eqT rS rT ntS ntT refS refT dS dT,  
  let s := brel_get_nontrivial_witness S rS ntS in 
  let t := brel_get_nontrivial_witness T rT ntT in 
       match dS with 
       | inl asymS => 
         match dT with 
         | inl asymT     => inl _ (brel_product_antisymmetric S T  eqS eqT rS rT asymS asymT)
         | inr not_asymT => inr _ (brel_product_with_reflexivity_not_antisymmetric_right S T eqS eqT rS rT s refS not_asymT)
         end 
       | inr not_asymS   => inr _ (brel_product_with_reflexivity_not_antisymmetric_left S T  eqS eqT rS rT t refT not_asymS)
       end.


Lemma brel_product_antisymmetric_left : 
         ∀ (S T: Type) (eqS : brel S) (eqT : brel T) (rS : brel S) (rT : brel T),  
              brel_asymmetric S rS → 
              brel_antisymmetric (S * T) 
                  (brel_product S T eqS eqT)
                  (rS <*> rT). 
Proof. unfold brel_antisymmetric, brel_asymmetric. 
     intros S T eqS eqT rS rT asS [s1 t1] [s2 t2] H1 H2.  simpl in H1, H2.
     apply andb_is_true_left in H1. destruct H1 as [L R]. 
     rewrite (asS _ _ L) in H2. simpl in H2. discriminate. 
Defined. 


Lemma brel_product_antisymmetric_right : 
         ∀ (S T: Type) (eqS : brel S) (eqT : brel T) (rS : brel S) (rT : brel T),  
              brel_asymmetric T rT → 
              brel_antisymmetric (S * T) 
                  (brel_product S T eqS eqT)
                  (rS <*> rT). 
Proof. unfold brel_antisymmetric, brel_asymmetric. 
     intros S T eqS eqT rS rT asT [s1 t1] [s2 t2] H1 H2.  simpl in H1, H2.
     apply andb_is_true_left in H2. destruct H2 as [L R]. 
     rewrite (asT _ _ R) in H1. rewrite andb_comm in H1.  simpl in H1. discriminate. 
Defined. 


Lemma brel_product_not_antisymmetric_left : 
         ∀ (S T: Type) (eqS : brel S) (eqT : brel T) (rS : brel S) (rT : brel T),  
              brel_not_asymmetric T rT → 
              brel_not_antisymmetric S eqS rS → 
              brel_not_antisymmetric (S * T) 
                  (brel_product S T eqS eqT)
                  (rS <*> rT). 
Proof. unfold brel_not_antisymmetric, brel_not_asymmetric. 
     intros S T eqS eqT rS rT [ [t1 t2] [P1 P2] ] [ [s1 s2] [[H1 H2] H3] ]. 
     exists ((s1, t1), (s2, t2)); simpl. 
     rewrite P1, P2, H1, H2, H3; simpl. auto. 
Defined.


Lemma brel_product_not_antisymmetric_right : 
         ∀ (S T: Type) (eqS : brel S) (eqT : brel T) (rS : brel S) (rT : brel T),  
              brel_not_asymmetric S rS → 
              brel_not_antisymmetric T eqT rT → 
              brel_not_antisymmetric (S * T) 
                  (brel_product S T eqS eqT)
                  (rS <*> rT). 
Proof. unfold brel_not_antisymmetric, brel_not_asymmetric. 
     intros S T eqS eqT rS rT [ [s1 s2] [P1 P2] ] [ [t1 t2] [[H1 H2] H3] ]. 
     exists ((s1, t1), (s2, t2)); simpl. 
     rewrite P1, P2, H1, H2, H3; simpl. rewrite andb_comm. simpl. auto. 
Defined.

Definition brel_product_antisymmetric_decide : 
   ∀ (S T: Type) 
     (eqS : brel S) 
     (eqT : brel T)
     (rS : brel S) 
     (rT : brel T),   
     brel_asymmetric_decidable S rS →  
     brel_asymmetric_decidable T rT →  
     brel_antisymmetric_decidable S eqS rS → 
     brel_antisymmetric_decidable T eqT rT → 
        brel_antisymmetric_decidable (S * T) (brel_product S T eqS eqT) (rS <*> rT)
:= λ S T eqS eqT rS rT adS adT dS dT,  
       match dS with 
       | inl anti_symS => 
         match dT with 
         | inl anti_symT     => inl _ (brel_product_antisymmetric S T  eqS eqT rS rT anti_symS anti_symT)
         | inr not_anti_symT => 
           match adS with 
           | inl asymS     => inl _ (brel_product_antisymmetric_left S T  eqS eqT rS rT asymS)
           | inr not_asymS => inr _ (brel_product_not_antisymmetric_right S T eqS eqT rS rT not_asymS not_anti_symT)
           end 
         end 
       | inr not_anti_symS   => 
           match adT with 
           | inl asymT     => inl _ (brel_product_antisymmetric_right S T  eqS eqT rS rT asymT)
           | inr not_asymT => inr _ (brel_product_not_antisymmetric_left S T eqS eqT rS rT not_asymT not_anti_symS)
           end 
       end. 

*) 
End Product. 








