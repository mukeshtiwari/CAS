Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.reduce. 
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.reduce. 
(*
   Sequential composition of reductions 

   (S, =, (x)) ------------
   |                      |
   r1                     |
   |                      | 
   \/                     | 
  (S_r1, =, (x)_r1)       | r2 o r1  
   |                      | 
   r2                     | 
   |                      |
   \/                     \/
  ((S_r1)_r2, =, ((x)_r1)_r2) 


  Two steps: 

      a ((x)_r1)_r2 b = r2(a (x)_r1 b). 
                      = r2(r1(a (x) b)). 

    (S_r1)_r2 = {a in S_r1 | r2(a) = a}
              = {a in {a in S | r1(a) = a} | r2(a) = a} 
              = {a in S | r1(a) = a and r2(a) = a} 

        So, r1(r2(a)) = r2(r1(a))

   Equality in "OCaml"? 

        a (=_r1)_r2 b <-> r2(a) =_r1 r2(b) 
                      <-> r1(r2(a)) = r1(r2(b)) 
        Note: r1(r2(a)) seemas "backwards"
    

  One step: 

      a (x)_(r2 o r1) b = (r2 o r1)(a (x) b). 
                        = r2(r1(a (x) b)). 

      S_(r2 o r1) = {a in S | (r2 o r1)(a) = a}
                  = {a in S | r2(r1(a)) = a}

   Equality in "OCaml"? 

        a =_(r2 o r1) b <-> r2(r1(a)) = r2(r1(b)) 

   So, require r1(r2(a)) = r2(r1(a)). 


*) 
Section Computation.
Definition bop_sequential_compose : ∀ {S : Type}, unary_op S → unary_op S → binary_op S → binary_op S 
  := λ {S} r2 r1 b, bop_reduce r2 (bop_reduce r1 b).

(* Note: 

Compute uop_sequential_compose.
= λ (x x0 : unary_op ?S) (x1 : binary_op ?S) (x2 x3 : ?S), x (x0 (x1 x2 x3))
  : unary_op ?S → unary_op ?S → binary_op ?S → binary_op ?S

So, "bop_sequential_compose r2 r1 b" is really the same as 

    bop_reduce (uop_compose r2 r1) b

where uop_compose is defined in commutative_composition.v. 
However, I want to be a bit more careful here....
*) 

End Computation. 

Section Theory.

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r1 : unary_op S.
  Variable r2       : unary_op S.
  Variable eqS    : brel S.    

  (* r1 is a reduction over S *) 
  Variable r1_cong  : uop_congruence S eqS r1. 
  Variable r1_idem  : uop_idempotent S eqS r1.
  Variable r1_left  : bop_left_uop_invariant S eqS (bop_reduce r1 b) r1.  
  Variable r1_right : bop_right_uop_invariant S eqS (bop_reduce r1 b) r1.

  (* r2 is just idempotent *) 
  Variable r2_cong  : uop_congruence S eqS r2. 
  Variable r2_idem  : uop_idempotent S eqS r2.

  Definition eqS_r1 : brel S      := brel_reduce eqS r1. 
  Definition b_r1   : binary_op S := bop_reduce r1 b.

  (* Now, let's use r2 to try to build a reduction over ((S, eqS_r1), b_r1) *) 

  (* NB : this does not require that r2 and r1 commute *) 
  Lemma r2_idempotent : uop_idempotent S eqS_r1 r2.  
  Proof. intro s. compute.
         assert (H1 := r2_idem s). 
         apply r1_cong in H1.
         exact H1. 
  Qed.
  
  Lemma r2_left_uop_invariant :
    (* H0 : ∀ s1 s2 : S, eqS (r1 (b (r2 s1) s2)) (r1 (b s1 s2)) = true *) 
    bop_left_uop_invariant S eqS b_r1 r2 -> 
      bop_left_uop_invariant S eqS_r1 (bop_sequential_compose r2 r1 b) r2.  
  Proof. intros H0 s t. compute.
         assert (H1 : eqS (r1 (b (r2 s) t)) (r1 (b s t)) = true).
         {
           assert (H2 := H0 s t). compute in H2.
           exact H2. 
         } 
         apply r2_cong in H1. apply r1_cong in H1.
         exact H1. 
  Qed. 

  Lemma r2_right_uop_invariant :
    (* H0 : ∀ s1 s2 : S, eqS (r1 (b s1 (r2 s2))) (r1 (b s1 s2)) = true *)
    bop_right_uop_invariant S eqS b_r1 r2 -> 
      bop_right_uop_invariant S eqS_r1 (bop_sequential_compose r2 r1 b) r2.  
  Proof. intros H0 s t. compute.
         assert (H1 : eqS (r1 (b s (r2 t))) (r1 (b s t)) = true).
         {
           assert (H2 := H0 s t). compute in H2.
           exact H2. 
         } 
         apply r2_cong in H1. apply r1_cong in H1.
         exact H1. 
  Qed.


End Theory.

