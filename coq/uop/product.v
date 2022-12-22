Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.product. 
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.reduce. 

Section Computation.

Definition uop_product : ∀ {S T : Type}, unary_op S → unary_op T → unary_op (S * T) 
:= λ {S} {T} f g p,  
   match p with
    | (s, t) => (f s, g t) 
   end.

End Computation. 
Section Theory. 

  Variable S T: Type. 
  Variable b1 : binary_op S.
  Variable b2 : binary_op T.
  Variable r1 : unary_op S.
  Variable r2 : unary_op T.
  Variable eqS    : brel S.
  Variable eqT    : brel T.    

  (* r1 is a reduction over S *) 
  Variable r1_cong  : uop_congruence S eqS r1. 
  Variable r1_idem  : uop_idempotent S eqS r1.
  Variable r1_left  : bop_left_uop_invariant S eqS (bop_reduce r1 b1) r1.  
  Variable r1_right : bop_right_uop_invariant S eqS (bop_reduce r1 b1) r1.

  (* r2 is a reduction over T *) 
  Variable r2_cong  : uop_congruence T eqT r2. 
  Variable r2_idem  : uop_idempotent T eqT r2.
  Variable r2_left  : bop_left_uop_invariant T eqT (bop_reduce r2 b2) r2.  
  Variable r2_right : bop_right_uop_invariant T eqT (bop_reduce r2 b2) r2.

  Local Notation "eq1 [*] eq2" := (brel_product eq1 eq2) (at level 70).
  Local Notation "f1 [[*]] f2"   := (uop_product f1 f2) (at level 60).
  Local Notation "f1 <<*>> f2"   := (bop_product f1 f2) (at level 60).

  Lemma product_congruence : uop_congruence (S * T) (eqS [*] eqT) (r1 [[*]] r2). 
  Proof. intros [s t] [s' t'] H. unfold uop_product.
         apply brel_product_elim in H. destruct H as [H1 H2]. 
         apply brel_product_intro.
         - apply r1_cong; auto.
         - apply r2_cong; auto. 
  Qed.
  
  Lemma product_idempotent : uop_idempotent (S * T) (eqS [*] eqT) (r1 [[*]] r2). 
  Proof. intros [s t]. unfold uop_product. 
         apply brel_product_intro.
         - apply r1_idem; auto.
         - apply r2_idem; auto. 
  Qed.
  
  Lemma product_left_uop_invariant :
    bop_left_uop_invariant (S * T) (eqS [*] eqT) (bop_reduce (r1 [[*]] r2) (b1 <<*>> b2)) (r1 [[*]] r2). 
  Proof. intros [s t] [s' t']. 
         apply brel_product_intro.
         - apply r1_left; auto.
         - apply r2_left; auto. 
  Qed.

  Lemma product_right_uop_invariant :
    bop_right_uop_invariant (S * T) (eqS [*] eqT) (bop_reduce (r1 [[*]] r2) (b1 <<*>> b2)) (r1 [[*]] r2). 
  Proof. intros [s t] [s' t']. 
         apply brel_product_intro.
         - apply r1_right; auto.
         - apply r2_right; auto. 
  Qed.
  
End Theory. 
