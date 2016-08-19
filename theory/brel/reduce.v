Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.theory.brel_properties.
Require Import CAS.theory.uop_properties.
Require Import CAS.theory.bop_properties.
Require Import CAS.theory.facts. 

Lemma brel_reduce_reflexive : ∀ (S : Type) (r : brel S) (u : unary_op S), 
              (brel_reflexive S r) → brel_reflexive S (brel_reduce S r u). 
Proof. intros S r u refS s. unfold brel_reduce. apply refS. Defined. 


Lemma brel_reduce_symmetric : ∀ (S : Type) (r : brel S)  (u : unary_op S), 
              (brel_symmetric S r) → brel_symmetric S (brel_reduce S r u). 
Proof. intros S r u symS. unfold brel_symmetric, brel_reduce. intros s t. apply symS. Defined. 

Lemma brel_reduce_transitive : ∀ (S : Type) (r : brel S) (u : unary_op S), 
        (brel_transitive _ r) → brel_transitive S (brel_reduce S r u). 
Proof. intros S r u transS. unfold brel_transitive, brel_reduce. intros s t V. apply transS. Defined.          

Lemma brel_reduce_antisymmetric : ∀ (S : Type) (r : brel S)  (u : unary_op S), 
              uop_injective S r u  → 
              brel_antisymmetric S r (brel_reduce S r u). 
Proof. intros S r u injS . unfold brel_antisymmetric. intros s t H1 _. 
       apply injS in H1. assumption. 
Defined. 

Lemma brel_reduce_witness : ∀ (S : Type) (r : brel S)  (u : unary_op S), 
              brel_reflexive S r -> 
              brel_witness S r -> 
              brel_witness S (brel_reduce S r u). 
Proof. unfold brel_witness, brel_reduce. 
       intros S r u refS [s P]. exists (u s). apply refS. 
Defined. 


(* this should be case-by-case .... 


Lemma brel_reduce_negate : ∀ (S : Type) (r : brel S)  (u : unary_op S), 
              (∀ (y : S), r (u (u y)) (u y) = true) -> 
              brel_reflexive S r -> 
              brel_negate S r -> 
              brel_negate S (brel_reduce S r u). 
Proof. unfold brel_negate, brel_reduce. 
       intros S r u ax refS [f P]. 
       exists (λ x : S, u (f (u x))). intro s. 
       assert (H := P (u s)). 


  H : (r (u s)     (f (u s)) = false) * (r     (f (u s)) (u s) = false)
  ============================
      (r (u s) (u (f (u s))) = false) * (r (u (f (u s))) (u s) = false)

      ??????????
Defined. 
*) 

(* ************ *) 

Lemma brel_reduce_congruence : ∀ (S : Type) (r : brel S) (u : unary_op S), 
        brel_congruence S r r -> 
        brel_congruence S (brel_reduce S r u) (brel_reduce S r u). 
Proof. intros S r u congS. compute. intros s t w v H1 H2. 
       apply congS; auto. 
Qed. 


Lemma brel_reduce_uop_congruence : ∀ (S : Type) (eq : brel S)  (u : unary_op S) (f : unary_op S), 
      uop_uop_congruence S eq u f  → 
          uop_congruence S (brel_reduce S eq u) f. 
Proof. intros S eq u f cong. 
       unfold uop_congruence.  
       unfold brel_reduce. 
       apply cong. 
Defined. 


Lemma brel_reduce_bop_congruence : ∀ (S : Type) (eq : brel S)  (u : unary_op S) (b : binary_op S), 
       bop_uop_congruence S eq u b  → 
          bop_congruence S (brel_reduce S eq u) b. 
Proof. intros S eq u b cong. 
       unfold bop_congruence.  
       unfold brel_reduce. 
       apply cong. 
Defined. 

Lemma brel_reduce_bop_idempotent : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b :binary_op S), 
   brel_reflexive S r    → 
   uop_congruence S r u  → 
   bop_idempotent S r b  → 
       bop_idempotent S (brel_reduce S r u) b. 
Proof. intros S r u b refS cong_u idem_b. unfold brel_reduce, bop_idempotent. intro s. 
       assert (A := idem_b s). 
       assert (B := cong_u _ _ A). assumption. 
Defined. 


Lemma brel_reduce_bop_commutative : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b :binary_op S), 
   brel_reflexive S r    → 
   uop_congruence S r u  → 
   bop_commutative S r b  → 
       bop_commutative S (brel_reduce S r u) b. 
Proof. intros S r u b refS cong_u comm_b. unfold brel_reduce, bop_commutative. intros s t. 
       assert (A := comm_b s t). 
       assert (B := cong_u _ _ A). assumption. 
Defined. 


Lemma brel_reduce_preserves_left_positive : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (u : unary_op S), 
   brel_transitive S eq →
   uop_congruence S eq u →
   uop_idempotent S eq u →
   uop_preserves_left_positive S (brel_reduce S eq u) u. 
Proof. intros S eq lt u transS cong idem. unfold uop_preserves_left_positive. unfold brel_reduce. 
       unfold uop_congruence in cong. intros s t H. 
       assert (A := idem s). 
       assert (B := transS _ _ _ A H). assumption. 
Defined. 


Lemma brel_reduce_preserves_left_negative : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (u : unary_op S), 
   brel_symmetric S eq →
   brel_transitive S eq →
   uop_congruence S eq u →
   uop_idempotent S eq u →
   uop_preserves_left_negative S (brel_reduce S eq u) u. 
Proof. intros S eq lt u symS transS cong idem. 
       unfold uop_preserves_left_negative. unfold brel_reduce. 
       unfold uop_congruence in cong. intros s t H. 
       assert (A := idem s). apply symS in A. 
       assert (B := brel_transititivity_implies_dual _ _ transS _ _ _ A H). assumption. 
Defined. 


(*
    u (u (s + t) + v) = u (s + u (t + v))

    u (u (s + t) + v) = u ((s + t) + v)      () 
                      = u (s + (t + v))      () 
                      = u (s + u(t + v))     () 
*) 
Lemma brel_reduce_uop_bop_associative : 
  ∀ (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S),
    brel_symmetric S eq →
    brel_transitive S eq →
    bop_associative S eq b →
    uop_congruence S eq u →
    uop_bop_left_invariant S eq u b →
    uop_bop_right_invariant S eq u b →
      uop_bop_associative S (brel_reduce S eq u) u b. 
Proof. intros S eq u b symS transS assS cong_u Li Ri. 
       unfold brel_reduce, uop_bop_associative. intros s t v. 
       assert (A := assS s t v). 
       assert (B := Li (b s t) v). apply symS in B. 
       assert (C := Ri s (b t v)). 
       assert (D := cong_u _ _ A). 
       assert (T := transS _ _ _ B D). 
       assert (QED := transS _ _ _ T C). assumption. 
Defined. 

