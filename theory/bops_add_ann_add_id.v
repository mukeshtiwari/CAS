Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.properties. 

(*

I( + ), C( + ), LA( +,* ), LD( +,* ) -> LD( add_id( +,c ), add_ann( *,c ) )

   i( + )    -> ld( add_id( +,c ), add_ann( *,c ) )
   la( +,* ) -> ld( add_id( +,c ), add_ann( *,c ) )
   ld( +,* ) -> ld( add_id( +,c ), add_ann( *,c ) )


   DECIDE(), DECIDE() -> DECIDE()

*) 

(* note how nicely left absorption works out here .... *) 
Lemma bops_add_ann_add_id_left_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_congruence S r r -> 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bop_commutative S r b1 -> 
     bops_left_absorption S r b1 b2 -> 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 congS refS symS idemS commS absS ld [c1 | s1] [c2 | s2] [c3 | s3]; 
       compute; auto. 
       assert (fact1 := commS s1 (b2 s1 s2)). 
       rewrite <- (congS _ _ _ _ (refS s1) fact1). 
       apply absS. 
Qed. 

Lemma bops_add_ann_add_id_left_distributive_EXPLICIT  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_congruence S r r -> 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 ->          (* NB *) 
     bop_commutative S r b1 ->         (* NB *) 
     bops_left_absorption S r b1 b2 -> (* NB *) 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 congS refS symS idemS commS absS ld [c1 | s1] [c2 | s2] [c3 | s3]; 
       compute. 
          reflexivity. (* true = true *) 
          reflexivity. (* true = true *) 
          reflexivity. (* true = true *) 
          apply refS.  (* r (b1 s2 s3) (b1 s2 s3) = true *) 
          rewrite symS. (* s1 : S, c2 c3 : cas_constant |- r s1 (b1 s1 s1) = true *) 
             reflexivity. apply idemS. 
          apply absS.  (* s1, s3 : S, c2 : cas_constant |- r s1 (b1 s1 (b2 s1 s3)) = true *) 
                       (* s1, s2 : S, c3 : cas_constant |- r s1 (b1 (b2 s1 s2) s1) = true*) 
          assert (fact1 := commS s1 (b2 s1 s2)). 
            rewrite <- (congS _ _ _ _ (refS s1) fact1). 
            apply absS. 
          apply ld.    (* s1, s2, s3 : S *) 
Qed. 


Lemma bops_add_ann_add_id_not_left_distributive_v1 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_left_distributive S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_left_distributive_v2 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 


Lemma bops_add_ann_add_id_not_left_distributive_v3 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_absorption S r b1 b2 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 



(* what about ... ? 
Lemma bops_add_ann_add_id_not_left_distributive_v4 : 
   ∀ (S : Type) (r : brel S) (s1 s2 s3 : S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_commutative S r b1 -> 
        bop_not_left_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 


Do we need ? 

     bops_left_left_absorption 
     bops_left_right_absorption 
     bops_right_left_absorption 
     bops_right_right_absorption 
*) 

Definition bops_left_left_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_left_right_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_right_left_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 s t) s) = true.

Definition bops_right_right_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.


Lemma bops_add_ann_add_id_left_distributive_NEW  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_congruence S r r -> 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 ->          
     bops_left_left_absorption S r b1 b2 -> 
     bops_right_left_absorption S r b1 b2 -> 
     bop_left_distributive S r b1 b2 -> 
        bop_left_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 congS refS symS idemS laS raS ld. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; simpl. 
       reflexivity. 
       reflexivity. 
       reflexivity. 
       apply refS. 
       apply symS. apply idemS. 
       apply laS. 
       apply raS. 
       apply ld. 
Qed. 


(* note how nicely right absorption works out here .... *) 
Lemma bops_add_ann_add_id_right_distributive  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_congruence S r r -> 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bop_commutative S r b1 ->
     bops_right_absorption S r b1 b2 -> 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 congS refS symS idemS commS absS rd [c1 | s1] [c2 | s2] [c3 | s3]; 
       compute; auto. 
       assert (fact1 := commS s1 (b2 s2 s1)). 
       rewrite <- (congS _ _ _ _ (refS s1) fact1). 
       apply absS. 
Qed. 


(* ND : Go in this direction??? *) 
Lemma bops_add_ann_add_id_right_distributive_NEW  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_congruence S r r -> 
     brel_reflexive S r -> 
     brel_symmetric S r -> 
     bop_idempotent S r b1 ->          
     bops_left_right_absorption S r b1 b2 -> 
     bops_right_right_absorption S r b1 b2 -> 
     bop_right_distributive S r b1 b2 -> 
        bop_right_distributive (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 congS refS symS idemS laS raS rd. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; simpl. 
       reflexivity. 
       reflexivity. 
       reflexivity. 
       apply refS. 
       apply symS. apply idemS. 
       apply laS. 
       apply raS. 
       apply rd. 
Qed. 



Lemma bops_add_ann_add_id_not_right_distributive_v1 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bop_not_right_distributive S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_distributive_v2 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma bops_add_ann_add_id_not_right_distributive_v3 : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_absorption S r b1 b2 -> 
        bop_not_right_distributive (with_constant S) (brel_add_constant S r c) 
             (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 



Lemma bops_add_ann_add_id_id_equals_ann :    
      ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S), 
      brel_reflexive S r -> 
      bops_id_equals_ann S r b1 b2 -> 
           bops_id_equals_ann 
              (with_constant S) 
              (brel_add_constant S r c) 
              (bop_add_ann S b1 c) 
              (bop_add_id S b2 c). 
Proof. unfold bops_id_equals_ann. 
       intros S r c b1 b2 refS [[i Pi] [[a Pa] H]]. 
       simpl in H. 
       assert (fact1 : bop_is_id (with_constant S) (brel_add_constant S r c) (bop_add_ann S b1 c) (inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       assert (fact2 : bop_is_ann (with_constant S) (brel_add_constant S r c) (bop_add_id S b2 c) (inr _ a)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       exists (existT _ (inr _ i) fact1). exists (existT _ (inr _ a) fact2). 
       compute. assumption. 
Defined. 


Lemma bops_add_ann_add_id_left_absorption  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bops_left_absorption S r b1 b2 -> 
        bops_left_absorption (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_left_absorption_v1  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_left_absorption S r b1 b2 -> 
        bops_not_left_absorption (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. 
       exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


Lemma bops_add_ann_add_id_not_left_absorption_v2  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bops_not_left_absorption (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 


Lemma bops_add_ann_add_id_right_absorption  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_idempotent S r b1 -> 
     bops_right_absorption S r b1 b2 -> 
        bops_right_absorption (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma bops_add_ann_add_id_not_right_absorption_v1  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     bops_not_right_absorption S r b1 b2 -> 
        bops_not_right_absorption (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 [ [s1 s2] nldS]. 
       exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


Lemma bops_add_ann_add_id_not_right_absorption_v2  : 
   ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
     brel_symmetric S r -> 
     bop_not_idempotent S r b1 -> 
        bops_not_right_absorption (with_constant S) (brel_add_constant S r c) 
           (bop_add_ann S b1 c) (bop_add_id S b2 c). 
Proof. intros S r c b1 b2 symS [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 
