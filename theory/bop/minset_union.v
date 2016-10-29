Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.combined. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.uop_properties. 
Require Import CAS.theory.brel.and_sym. 
Require Import CAS.theory.brel.reduce. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.in_set.
Require Import CAS.theory.brel.subset.
Require Import CAS.theory.brel.set.
Require Import CAS.theory.uop.duplicate_elim. 
Require Import CAS.theory.bop.union. 

Require Import CAS.theory.uop.filter. 
Require Import CAS.theory.brel.is_minimal_in. 
(*
Require Import CAS.theory.bop.reduce. 
*) 
Require Import CAS.theory.brel.minset. 
(*
Require Import CAS.theory.bprop.forall. 
*) 

Section NewEQV. 

Section EQV. 

Require Import CAS.code.ast.
Require Import CAS.code.data.


(*

eqv_struct :  (S, eq, f, rep) 

   Need proofs with this.  Minimal set? 

    ∀ x : S, f(rep x) = true. 
    {x : S, f x = true } 
    { g : S -> S & ∀ x : S, g x = true  -> f(g x) = true * eq x (g x) = false } 
    

eqv : (T, eqv_T, eqv_proofs) 

[| (S, eq, f, rep) |] = (T, eqv_T, eqv_proofs) 

    T = {x : S & f x = true } 
    ref : ∀ x : S, f x = true -> eq x x = true  
    sym : ∀ x y: S, f x = true -> f y = true -> eq x y = true  eq y x = true  
    sym : ∀ x y z: S, f x = true -> f y = true -> -> f z = true -> 
                    eq x y = true  eq y z = true  -> eq x z = true 


    What does congruence mean ? 

   ∀ (s, ps) (t, pt) (u, pu) (v, pv) : {x : S & f x = true }, 
       eq s u = true → eq t v = true → eq s t = eq u v. 
    
Ocaml Code : only has (S, eq, f, rep) . 



Definition brel_reflexive (S : Type) (r : brel S) := ∀ s : S, brel_reflexive_pred S r s. 

Definition brel_transitive (S : Type) (r : brel S) := ∀ s t u: S, brel_transitive_pred S r s t u. 

Definition brel_symmetric (S : Type) (r : brel S) := ∀ s t : S, brel_symmetric_pred S r s t. 


bop_idempotent = 
λ (S : Type) (r : brel S) (b : binary_op S), ∀ s : S, r (b s s) s = true
     : ∀ S : Type, brel S → binary_op S → Prop


suppose S = {t : T & r(t) = t}
{X : finite_set S &  [min] X === X } = {X : finite_set {t : T & r(t) = t} &  [min] X === X }


Want for D1 a "datatype" S1 = {x : D1 & P1(x)} 

      now S2 = {y in S1 | P2(y) } 
             = {y in  {x in [| D1 |] | P1(x)}  | P2(y) } 
             = {x in [| D1 |] | P1(x) & P2(y) } 


      product : 
             {x in D1 | P1(x) } * {y in D2 | P2(y) } == {(x, y) : D1 * D2 | P1(x) & P2(y) } 
      sum : 
             {x in D1 | P1(x) } + {y in D2 | P2(y) } == {d : D1 + D2 | casd d of inr(x) -> P1(x) | inr(u) ->  P2(y) } 

      let  (D, f : D -> bool) represent S = {x : D | f(x) = true} 

      so [| (D, f : D -> bool) |] = {x : D & f(x) = true } 

      Now, we have rep : D -> D so that ∀ x : D, f(rep x) = true. 


    What kind of code do we want out of minset_union? 

       sg_CI (finite_set D) = 
          sg_CI_eqv   : eqv (finite_set D)
                        X === Y  iff min X == min Y 
                        rep : D -> D 
          sg_CI_bop   : (finite_set D) -> (finite_set D) -> (finite_set D)
          sg_CI_certs : sg_CI_certificates (finite_set D)

          what is bop?    bop = bop_minset_union 
          what does idempotence mean? 

          ∀  X : (finite_set D), min (rep X u rep X) === rep X    ????? 

          ∀  X : (finite_set D), min (X u X) === X    ????? 

     
         ∀ z : {x : D & f(x) = true}, P(projT1 z)
         ∀ z : D,  f(x) = true) -> P(z)
         ∀ z : D,  P(rep z). 

change 
Definition bop_idempotent (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s : S, r (b s s) s = true. 

to 

Definition bop_idempotent (S : Type) (r : a_eqv S) (b : binary_op S) 
    := ∀ s : S, (inset (s eqv)) -> (eqv r) (b s s) s = true). 


Definition bop_not_idempotent (S : Type) (r : a_eqv S) (b : binary_op S) 
    := {s : S, (inset (s eqv)) * ((eqv r) (b s s) s = false) } . 


     [(D, eq, f, r)] ----> ({x : D & f(x) = true}, EQ) 
           |
           |
          \/
      (D, eq_r, r) 
                      


need to prove closure: a in S b in S -> a + b in S 
For reductions, use r idempotent 

*) 

Definition brel_congruence_pred (S : Type) (eq : brel S) (s t u v: S ):= 
       eq s u = true → eq t v = true → eq s t = eq u v. 

Definition brel_reflexive_pred (S : Type) (r : brel S) (s : S) := 
    r s s = true. 

Definition brel_transitive_pred (S : Type) (r : brel S) (s t u: S ):= 
    (r s t = true) → (r t u = true) → (r s u = true). 

Definition brel_symmetric_pred (S : Type) (r : brel S) (s t : S) := 
    (r s t = true) → (r t s = true). 


Record eqv_proofs (S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool):= 
{
  A_eqv_not_empty      : {x : S & f(x) = true} 
; A_eqv_not_trivial    : {g : S -> S & ∀ x : S, (f(x) = true) * (f(g x) = true) * (eq x (g x) = false)}; A_eqv_rep_in_set     : ∀ x :S, f(rep x) = true 
; A_eqv_rep_equal      : ∀ P :{ x : S & f x = true}, eq (projT1 P) (rep (projT1 P)) = true
; A_eqv_rep_idempotent : ∀ x :S, eq (rep (rep x)) (rep x) = true 
; A_eqv_congruence     : ∀ (P1 P2 P3 P4 : { x : S & f x = true}), brel_congruence_pred S eq (projT1 P1) (projT1 P2) (projT1 P3) (projT1 P4)
; A_eqv_reflexive      : ∀ P : { x : S & f x = true}, brel_reflexive_pred S eq (projT1 P)
; A_eqv_transitive     : ∀ (P1 P2 P3 : { x : S & f x = true}), brel_transitive_pred S eq (projT1 P1) (projT1 P2) (projT1 P3)
; A_eqv_symmetric      : ∀ (P1 P2 : { x : S & f x = true}), brel_symmetric_pred S eq (projT1 P1) (projT1 P2)
}.


Record A_eqv (S : Type) := {
  A_eqv_eq      : brel S 
; A_eqv_data    : S -> data (* for printing in ocaml-land *) 
; A_eqv_def     : S -> bool 
; A_eqv_rep     : S -> S    
; A_eqv_proofs  : eqv_proofs S A_eqv_eq A_eqv_rep A_eqv_def
; A_eqv_ast     : ast_eqv 
}.


Record eqv_proofs2 (S : Type) (eq : brel S) (rep : unary_op S):= 
{
  eqv_not_empty      : { s : S & eq (rep s) (rep s) = true } 
; eqv_not_trivial    : { g : S -> S & ∀ s : S, eq (rep s) (g (rep s)) = false }
; eqv_rep_idempotent : ∀ s : S, eq (rep s) (rep (rep s)) = true
; eqv_congruence     : ∀ (s t u v : S), brel_congruence_pred S eq (rep s) (rep t) (rep u) (rep v) 
; eqv_reflexive      : ∀ (s : S), brel_reflexive_pred S eq (rep s) 
; eqv_transitive     : ∀ (s t u : S), brel_transitive_pred S eq (rep s) (rep t) (rep u) 
; eqv_symmetric      : ∀ (s t : S), brel_symmetric_pred S eq (rep s) (rep t) 
}.


Lemma lemma_not_trivial : ∀(S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool), 
    ({g : S -> S & ∀ x : S, (f(x) = true) * (f(g x) = true) * (eq x (g x) = false)}) 
    -> 
    ({ g : S -> S & ∀ s : S, eq (rep s) (g (rep s)) = false }). 
Proof. intros S eq rep f [g P]. 
       exists g. intro s. destruct (P (rep s)) as [[H1 H2] H3]. 
       assumption. 
Defined. 


Lemma lemma_congruence : ∀(S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool), 
 (∀ x :S, f(rep x) = true) -> 
 (∀ (P1 P2 P3 P4 : { x : S & f x = true}), brel_congruence_pred S eq (projT1 P1) (projT1 P2) (projT1 P3) (projT1 P4))
  -> 
 (∀ (s t u v : S), brel_congruence_pred S eq (rep s) (rep t) (rep u) (rep v) ). 
Proof. intros S eq rep f H1 H2 s t u v. 
       assert (fact1 := H2 (existT _ (rep s) (H1 s)) (existT _ (rep t) (H1 t)) (existT _ (rep u) (H1 u)) (existT _ (rep v) (H1 v))).  
       simpl in fact1. 
       assumption.        
Defined. 


Lemma lemma_reflexive : ∀(S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool), 
 (∀ x :S, f(rep x) = true) -> 
 (∀ P : { x : S & f x = true}, brel_reflexive_pred S eq (projT1 P))
  -> 
 (∀ (s : S), brel_reflexive_pred S eq (rep s)). 
Proof. intros S eq rep f H1 H2 s. 
       assert (fact1 := H2 (existT _ (rep s) (H1 s))). 
       simpl in fact1. 
       assumption.        
Defined. 

Lemma lemma_symmetric : ∀(S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool), 
 (∀ x :S, f(rep x) = true) -> 
 (∀ (P1 P2 : { x : S & f x = true}), brel_symmetric_pred S eq (projT1 P1) (projT1 P2))
  -> 
 (∀ (s t : S), brel_symmetric_pred S eq (rep s) (rep t)). 
Proof. intros S eq rep f H1 H2 s t. 
       assert (fact1 := H2 (existT _ (rep s) (H1 s)) (existT _ (rep t) (H1 t))). 
       simpl in fact1. 
       assumption.        
Defined. 


Lemma lemma_transitive : ∀(S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool), 
 (∀ x :S, f(rep x) = true) -> 
 (∀ (P1 P2 P3 : { x : S & f x = true}), brel_transitive_pred S eq (projT1 P1) (projT1 P2) (projT1 P3))
  -> 
 (∀ (s t u : S), brel_transitive_pred S eq (rep s) (rep t) (rep u) ). 
Proof. intros S eq rep f H1 H2 s t u. 
       assert (fact1 := H2 (existT _ (rep s) (H1 s)) (existT _ (rep t) (H1 t)) (existT _ (rep u) (H1 u))).  
       simpl in fact1. 
       assumption.        
Defined. 

Lemma lemma_rep_idempotent : ∀(S : Type) (eq : brel S) (rep : unary_op S) (f : S -> bool), 
       (∀ x :S, f(rep x) = true) -> 
       (∀ (P1 P2 : { x : S & f x = true}), brel_symmetric_pred S eq (projT1 P1) (projT1 P2)) -> 
       (∀ x :S, eq (rep (rep x)) (rep x) = true) -> 
              ∀ s : S, eq (rep s) (rep (rep s)) = true.
Proof. intros S eq rep f H1 H2 H3 s. 
      assert (fact1  := lemma_symmetric S eq rep f H1 H2).
      assert (fact2  := H3 s). apply fact1 in fact2. 
      assumption. 
Defined. 

Lemma lemma_not_empty : ∀(S : Type) (eq : brel S) (rep : unary_op S) (inSet : S -> bool), 
           (∀ x :S, eq (rep (rep x)) (rep x) = true) -> 
           {x : S & inSet(x) = true} -> 
           (∀ x :S, inSet (rep x) = true) -> 
           (∀ P :{ x : S & inSet x = true}, eq (projT1 P) (rep (projT1 P)) = true) -> 
            (∀ (P1 P2 P3 : { x : S & inSet x = true}), brel_transitive_pred S eq (projT1 P1) (projT1 P2) (projT1 P3)) -> 
              { s : S & eq (rep s) (rep s) = true }. 
Proof. intros S eq rep inSet H0 H1 H2 H3 H4. destruct H1 as [x J]. 
       assert (transS := lemma_transitive S eq rep inSet H2 H4).
       assert (fact1 := H2 x). 
       assert (fact2 := H3 (existT _ (rep x) fact1)). simpl in fact2. 
       assert (fact3 := H0 x). 
       assert (fact4 := transS _ _ _ fact2 fact3). 
       exists x. assumption. 
Defined. 


Definition proof_to_proof2 : ∀(S : Type) (eq : brel S) (rep : unary_op S) (inSet : S -> bool), 
               eqv_proofs S eq rep inSet -> eqv_proofs2 S eq rep 
:= λ S eq rep inSet eqv, 
{|
  eqv_not_empty      := lemma_not_empty S eq rep inSet 
                            (A_eqv_rep_idempotent _ _ _ _ eqv) 
                            (A_eqv_not_empty _ _ _ _ eqv) 
                            (A_eqv_rep_in_set _ _ _ _ eqv) 
                            (A_eqv_rep_equal _ _ _ _ eqv) 
                            (A_eqv_transitive _ _ _ _ eqv) 
; eqv_not_trivial    := lemma_not_trivial S eq rep inSet 
                            (A_eqv_not_trivial _ _ _ _ eqv) 
; eqv_rep_idempotent := lemma_rep_idempotent S eq rep inSet 
                            (A_eqv_rep_in_set _ _ _ _ eqv) 
                            (A_eqv_symmetric _ _ _ _ eqv) 
                            (A_eqv_rep_idempotent _ _ _ _ eqv) 
; eqv_congruence     := lemma_congruence S eq rep inSet 
                            (A_eqv_rep_in_set _ _ _ _ eqv) 
                            (A_eqv_congruence _ _ _ _ eqv) 
; eqv_reflexive      := lemma_reflexive S eq rep inSet 
                            (A_eqv_rep_in_set _ _ _ _ eqv) 
                            (A_eqv_reflexive _ _ _ _ eqv) 
; eqv_transitive     := lemma_transitive S eq rep inSet 
                            (A_eqv_rep_in_set _ _ _ _ eqv) 
                            (A_eqv_transitive _ _ _ _ eqv) 
; eqv_symmetric      := lemma_symmetric S eq rep inSet 
                            (A_eqv_rep_in_set _ _ _ _ eqv) 
                            (A_eqv_symmetric _ _ _ _ eqv) 
|}.





End EQV. 

Section Nat. 
End Nat. 

Section Product. 

Variable S : Type. 
Variable eqS : brel S. 
Variable repS : unary_op S. 
Variable inS : S -> bool. 
Variable not_emptyS : {x : S & inS(x) = true}. 
Variable rep_in_setS : ∀ x :S, inS(repS x) = true. 
Variable eqv_rep_equalS : ∀ P :{ x : S & inS x = true}, eqS (projT1 P) (repS (projT1 P)) = true. 
Variable eqv_reflexiveS : ∀ P : { x : S & inS x = true}, brel_reflexive_pred S eqS (projT1 P).

Variable T : Type. 
Variable eqT : brel T. 
Variable repT : unary_op T. 
Variable inT : T -> bool. 
Variable not_emptyT : {x : T & inT(x) = true}.
Variable rep_in_setT : ∀ x :T, inT(repT x) = true. 
Variable eqv_rep_equalT : ∀ P :{ x : T & inT x = true}, eqT (projT1 P) (repT (projT1 P)) = true. 
Variable eqv_reflexiveT : ∀ P : { x : T & inT x = true}, brel_reflexive_pred T eqT (projT1 P).

Definition inProduct (p : S * T) := let (x, y) := p in bop_and (inS x) (inT y). 
Definition repProduct (p : S * T) := let (x, y) := p in (repS x, repT y). 
Definition eqProduct := brel_product S T eqS eqT. 

Lemma eqv_product_not_empty : {p : S * T & inProduct(p) = true}. 
Proof. destruct not_emptyS as [s Ps]; destruct not_emptyT as [t Pt]. exists (s, t); compute. 
       rewrite Ps, Pt; auto. 
Defined. 

Lemma eqv_product_rep_equal : ∀ P : { p : S * T & inProduct p = true},  
                 eqProduct  (projT1 P) (repProduct (projT1 P)) = true. 
Proof. intros [[s t] Pr]. compute. unfold inProduct in Pr. unfold bop_and in Pr. 
       apply andb_is_true_left in Pr. destruct Pr as [L R]. 
       assert (fact1 := eqv_rep_equalS (existT _ s L)). simpl in fact1.
       assert (fact2 := eqv_rep_equalT (existT _ t R)). simpl in fact2.
       rewrite fact1, fact2; auto. 
Defined. 

(*
Lemma eqv_product_reflexiveT : ∀ P : { p : S * T & inProduct p = true}, 
         brel_reflexive_pred (S * T) eqProduct (projT1 P).
*) 

End Product. 

Section SetEQV. 
End SetEQV. 


Section Minset. 
End Minset. 

Section Bops. 

(*
Definition bop_commutative (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) (b t s) = true. 

*) 

Definition commutative (S : Type) (eqv : A_eqv S) (b : binary_op S) 
    := ∀ s t : {x : S & A_eqv_def _ eqv x = true}, (A_eqv_eq S eqv) 
           (b (projT1 s) (projT1 t)) (b (projT1 t) (projT1 s)) = true. 

Lemma test : ∀ (S : Type) (eqv : A_eqv S) (b : binary_op S),  
        bop_commutative S (A_eqv_eq S eqv) b -> 
           commutative S eqv b. 
Proof. intros S eqv b H [s Ps] [t Pt]. simpl. apply H. Qed. 
   
End Bops. 

End NewEQV. 






(* Someday prove these in 

Require Import CAS.theory.uop.minset. 

Definition uop_minset : ∀ S : Type, brel S → brel S → unary_op (finite_set S) 
:= λ S eq lte X, uop_filter S (λ a, is_minimal_in S eq lte a X) X. 


Definition is_minimal_in : ∀ (S : Type), brel S → brel S → brel2 S (finite_set S)
:= λ S eq lte a X, 
      if brel_set S eq nil X
      then false 
      else (bProp_forall S (λ y, bop_or (uop_not (lte y a)) (eq y a))) X. 


*) 



Hypothesis is_minimal_in_elim : ∀ (S : Type) (eq : brel S) (lte : brel S) (a : S) (X : finite_set S),
      is_minimal_in S eq lte a X = true -> 
      (in_set S eq X a = true) * 
      (∀ (b : S), in_set S eq X b = true -> bop_or (uop_not (lte b a)) (eq b a) = true). 

Hypothesis is_minimal_in_intro : ∀ (S : Type) (eq : brel S) (lte : brel S) (a : S) (X : finite_set S),
      (in_set S eq X a = true) -> 
      (∀ (b : S), in_set S eq X b = true -> bop_or (uop_not (lte b a)) (eq b a) = true) -> 
      is_minimal_in S eq lte a X = true. 

Hypothesis in_minset_elim : ∀ (S : Type) (eq : brel S) (lte : brel S) (a : S) (X : finite_set S),
      in_set S eq (uop_minset S eq lte X) a = true -> 
      (in_set S eq X a = true) * (is_minimal_in S eq lte a X = true). 

Hypothesis in_minset_intro : ∀ (S : Type) (eq : brel S) (lte : brel S) (a : S) (X : finite_set S),
      (in_set S eq X a = true) ->  (is_minimal_in S eq lte a X = true) -> 
      in_set S eq (uop_minset S eq lte X) a = true. 
      


Hypothesis uop_minset_congruence : ∀ (S : Type) (eq : brel S) (lt : brel S),
   uop_congruence (finite_set S) (brel_set S eq) (uop_minset S eq lt). 

Hypothesis uop_minset_idempotent :  ∀ (S : Type) (eq : brel S) (lt : brel S),
   brel_reflexive S eq -> 
   brel_symmetric S eq -> 
   brel_transitive S eq -> 
   brel_congruence S eq lt -> 
   uop_idempotent (finite_set S) (brel_set S eq) (uop_minset S eq lt). 


Definition bop_reduce2 : ∀ (S : Type) (u : unary_op S) (b : binary_op S), binary_op S 
:= λ S u b x y,  u (b x y). 


Definition bop_minset_union : ∀ S : Type, brel S → brel S → binary_op (finite_set S) 
:= λ S eq lte, bop_reduce2 (finite_set S) (uop_minset S eq lte) (bop_union S eq). 


Hypothesis uop_minset_brel_set_congruence : 
    ∀ (S : Type) (eq : brel S) (lte : brel S),
       uop_congruence (finite_set S) (brel_set S eq) (uop_minset S eq lte). 


(*
u(s + t) = u (t + s)
         = u (t + (u s))
         = u ((u s) + t)
*) 
Lemma bop_commutative_right_implies_left_invariant : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S),
     brel_symmetric S r →
     brel_transitive S r →
     bop_commutative S r b →
     uop_congruence S r u →
     uop_bop_right_invariant S r u b →
        uop_bop_left_invariant S r u b.  
Proof. intros S r u b symS transS comm_b cong_u. 
       unfold uop_bop_left_invariant, uop_bop_right_invariant. 
       intros H s t. 
       assert (A := comm_b s t). 
       assert (B := comm_b t (u s)). 
       assert (Au := cong_u _ _ A). 
       assert (Bu := cong_u _ _ B). 
       assert (Hu := H t s). 
       assert (T1 := transS _ _ _ Au Hu). 
       assert (T2 := transS _ _ _ T1 Bu). assumption. 
Defined. 





Section MinsetUnion. 

Variable S  : Type. 
Variable eq : brel S. 
Variable lte : brel S. 

Variable refS    : brel_reflexive S eq. 
Variable symS    : brel_symmetric S eq. 
Variable transS  : brel_transitive S eq.
Variable cong_eq : brel_congruence S eq eq. 
Variable cong_lte : brel_congruence S eq lte. 

Notation "a [U] b"  := (bop_union S eq a b) (at level 15).
Notation "a [MU] b"  := (bop_minset_union S eq lte a b) (at level 15).
Notation "[min] a"  := (uop_minset S eq lte a) (at level 15).
Notation "a != b"  := (eq a b = false) (at level 15).
Notation "a == b"  := (eq a b = true) (at level 15).
Notation "a === b"  := (brel_set S eq a b = true) (at level 15).
Notation "a ==== b"  := (brel_minset S eq lte a b = true) (at level 15).


(*
Variable ref_lte : brel_reflexive S lte. 
Variable trans_lte  : brel_transitive S lte.  
Variable cong_lte: brel_congruence S rS lte. 
*) 

Lemma bop_minset_union_congruence : 
       bop_congruence (finite_set S) (brel_set S eq) (bop_minset_union S eq lte).
Proof. intros X Y Z W H1 H2. unfold bop_minset_union. unfold bop_reduce2. 
       apply uop_minset_congruence; auto.  
       apply bop_union_congruence_raw; auto. 
Qed. 
(*
    minset(A U B) = minset(A U (minset B))
*) 
Lemma  bop_union_uop_minset_right_invariant : 
       uop_bop_right_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lte) (bop_union S eq). 
Proof. unfold uop_bop_right_invariant. intros X Y. apply brel_set_intro_prop; auto. split. 

          intros z H. 
          apply in_minset_elim in H. destruct H as [L R]. 
          apply in_minset_intro.  
             apply in_set_bop_union_elim in L; auto. destruct L as [L | L]. 
                apply in_set_bop_union_intro; auto. 
               (* need : 
  L : in_set S eq Y z = true
  R : is_minimal_in S eq lte z (X[U]Y) = true
  ============================
   in_set S eq (X[U]([min]Y)) z = true
*)  
                apply in_set_bop_union_intro; auto. 
                apply is_minimal_in_elim in R. destruct R as [R1 R2].
                apply in_set_bop_union_elim in R1; auto. destruct R1 as [R1 | R1]. 
                   left; auto. 
                   right. apply in_minset_intro; auto. 
                          apply is_minimal_in_intro; auto. 
                          intros b H. 
                          assert (fact1 : in_set S eq (X[U]Y) b = true). apply in_set_bop_union_intro; auto. 
                          apply (R2 b fact1). 

             apply in_set_bop_union_elim in L; auto. destruct L as [L | L]. 
                (* need 
  L : in_set S eq X z = true
  R : is_minimal_in S eq lte z (X[U]Y) = true
  ============================
   is_minimal_in S eq lte z (X[U]([min]Y)) = true
*) 

                apply is_minimal_in_intro; auto. 
                apply is_minimal_in_elim in R. destruct R as [R1 R2].
                apply in_set_bop_union_intro; auto. 
                intros b H. 
                apply is_minimal_in_elim in R. destruct R as [R1 R2].
                assert(fact1 : in_set S eq (X[U]Y) b = true). 
                   apply in_set_bop_union_elim in H; auto. 
                   apply in_set_bop_union_intro; auto. 
                   destruct H as [H | H] ; auto. 
                   apply in_minset_elim in H. destruct H as [H _]; auto. 
                apply (R2 b fact1). 

                (* need : 
  L : in_set S eq Y z = true
  R : is_minimal_in S eq lte z (X[U]Y) = true
  ============================
   is_minimal_in S eq lte z (X[U]([min]Y)) = true

*) 
             apply is_minimal_in_elim in R. destruct R as [R1 R2].
             apply is_minimal_in_intro; auto. 
                apply in_set_bop_union_intro; auto.     
                right. 
                apply in_minset_intro;auto. 
                apply is_minimal_in_intro; auto. 
                intros b H. 
                assert(fact1 : in_set S eq (X[U]Y) b = true).
                   apply in_set_bop_union_intro; auto.                
                apply (R2 b fact1). 
                              
                intros b H. 
                assert(fact1 : in_set S eq (X[U]Y) b = true). 
                   apply in_set_bop_union_intro; auto.     
                   apply in_set_bop_union_elim in H; auto. destruct H as [H | H]; auto.
                   apply in_minset_elim in H. destruct H as [H _]; auto. 
                apply (R2 b fact1). 


          intros z H. 
          apply in_minset_elim in H. destruct H as [L R]. 
          apply in_minset_intro. 
             apply in_set_bop_union_elim in L; auto. destruct L as [L | L]. 
                apply in_set_bop_union_intro; auto. 
                apply in_minset_elim in L. destruct L as [H1 H2]. 
                apply in_set_bop_union_intro; auto. 
             (* need :
  L : in_set S eq (X[U]([min]Y)) z = true
  R : is_minimal_in S eq lte z (X[U]([min]Y)) = true
  ============================
   is_minimal_in S eq lte z (X[U]Y) = true
*) 
                apply is_minimal_in_elim in R. destruct R as [R1 R2].
                apply is_minimal_in_intro. 
                apply in_set_bop_union_intro; auto. 
                apply in_set_bop_union_elim in L; auto. destruct L as [L | L]; auto. 
                right. 
                apply in_minset_elim in L. destruct L as [L _]; auto. 
           
(* An INTERESTING CASE *) 
                intros b H. 
                apply in_set_bop_union_elim in H; auto. destruct H as [H | H]; auto.
                assert(fact1 : in_set S eq (X[U]([min]Y)) b = true).
                   apply in_set_bop_union_intro; auto.                
                   apply (R2 b fact1). 
                   case_eq(in_set S eq ([min] Y) b); intro J. 
                      assert(fact1 : in_set S eq (X[U]([min]Y)) b = true).
                        apply in_set_bop_union_intro; auto.                
                        apply (R2 b fact1). 
                      case_eq(lte b z); intro Q; case_eq(eq b z); intro P; simpl; auto. 

                        assert (fact1 : {w : S & (in_set S eq ([min]Y) w = true) * 
                                                 (bop_and (lte w b) (uop_not (eq w b)) = true) }). admit. 
                        destruct fact1 as [w [I N]]. 
                        assert(fact2 : in_set S eq (X[U]([min]Y)) w = true). admit.
                        assert(fact3 := R2 w fact2). 
                        case_eq(lte w b); intro F1; case_eq(eq w b); intro F2. 
                           admit. 
                           admit. 
                           admit. 
                           admit. 
Qed. 

(*
    minset(A U B) = minset((minset A) U B)
*) 

Lemma bop_union_uop_minset_left_invariant : 
       uop_bop_left_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lte) (bop_union S eq). 
Proof. apply bop_commutative_right_implies_left_invariant; auto. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto.
       apply uop_minset_brel_set_congruence. 
       apply bop_union_uop_minset_right_invariant; auto.  
Defined. 


Lemma bop_minset_union_associative : 
      bop_associative (finite_set S) (brel_set S eq) (bop_minset_union S eq lte).
Proof. intros X Y Z. unfold bop_minset_union. unfold bop_reduce2. 
       assert(set_trans := brel_set_transitive S eq refS symS transS).
       assert(set_sym := brel_set_symmetric S eq symS).
       apply set_sym. 
       assert(fact1 := bop_union_uop_minset_right_invariant X (Y [U] Z)).  apply set_sym in fact1. 
       assert(fact2 := bop_union_associative_raw S eq refS symS transS X Y Z). 
       assert(fact3 := uop_minset_congruence S eq lte _ _ fact2). apply set_sym in fact3. 
       assert(fact4 := set_trans _ _ _ fact1 fact3).       
       assert(fact5 := bop_union_uop_minset_left_invariant (X [U] Y) Z).
       assert(fact6 := set_trans _ _ _ fact4 fact5).       
       assumption. 
Defined. 

(*

*) 

Lemma bop_minset_union_idempotent_Attempt_01 : 
           ∀ (P : {X : finite_set S & brel_set S eq (uop_minset S eq lte X) X = true }), 
               brel_set S eq (bop_minset_union S eq lte (projT1 P) (projT1 P)) (projT1 P) = true. 
Proof. intros [X J]. simpl. unfold bop_minset_union. unfold bop_reduce2. 
       assert(set_trans := brel_set_transitive S eq refS symS transS).
       assert (fact1 :    ([min](X[U]X)) === [min] X). 
           apply uop_minset_congruence; auto. 
           apply bop_union_idempotent_raw; auto. 
       assert (fact2 := set_trans _ _ _ fact1 J). 
       assumption. 
Defined. 


Lemma bop_minset_union_idempotent_Attempt_02 : (* just notation *) 
      ∀ (P : {X : finite_set S &  [min] X === X }), (projT1 P) [MU] (projT1 P) === (projT1 P). 
Proof. intros [X J]. simpl. unfold bop_minset_union. unfold bop_reduce2. 
       assert(set_trans := brel_set_transitive S eq refS symS transS).
       assert (fact1 :    ([min](X[U]X)) === [min] X). 
           apply uop_minset_congruence; auto. 
           apply bop_union_idempotent_raw; auto. 
       assert (fact2 := set_trans _ _ _ fact1 J). 
       assumption. 
Defined. 





Lemma bop_minset_union_commutative : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
   (brel_reflexive S eq) → 
   (brel_symmetric S eq) → 
   (brel_transitive S eq) → 
   brel_congruence S eq lt → 
      bop_commutative (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong. 
       unfold brel_minset, bop_minset_union. 
       apply bop_reduction_commutative. 
       apply brel_set_transitive; auto. 
       apply brel_set_symmetric; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply uop_minset_idempotent; auto. 
       apply bop_union_commutative; auto. 
Defined. 


End MinsetUnion. 



Hypothesis tmp5 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : finite_set S),
   brel_subset S eq (uop_minset S eq lt (bop_union S eq (uop_minset S eq lt s) t))
                     (uop_minset S eq lt (bop_union S eq s t)) = true. 

Hypothesis tmp4 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S)  (s t : finite_set S),
   brel_reflexive S eq →
   brel_symmetric S eq →
   brel_transitive S eq →
   brel_congruence S eq lt →
    brel_subset S eq (uop_minset S eq lt (bop_union S eq s t))
                     (uop_minset S eq lt (bop_union S eq (uop_minset S eq lt s) t)) = true. 
(* 


Hypothesis zzzz :    

∀ (S : Type) (eq : brel S) (lt : brel S)  (a : S) (s t : finite_set S),
     is_minimal_in S eq lt a (bop_union S eq s t) = true  →
     in_set S eq s a = true  →
         in_set S eq (uop_minset S eq lt s) a = true. 


Proof. intros S eq lt s t refS symS transS cong. 
       apply brel_subset_intro; auto. 
       intros a J.  
       apply in_set_uop_minset_intro; auto.
       apply in_set_uop_minset_elim in J; auto.
       apply in_set_bop_union_intro; auto. destruct J as [JL JR].
       apply in_set_bop_union_elim in JR; auto.
       destruct JR as [JR | JR].
          left. apply (zzzz _ _ _ _ _ _ JL); auto. 
          right. assumption. 
       apply in_set_uop_minset_elim in J; auto. destruct J as [JL JR].
              
Defined. 
*) 


(*
    minset(A U B) = minset((minset A) U B)
*) 

(* DELETE *) 
Lemma bop_union_uop_minset_left_invariant : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt  →
      uop_bop_left_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. unfold uop_bop_left_invariant. 
       intros s t. apply brel_set_intro. split. 
          apply tmp4; auto. 
          apply tmp5. 
Defined. 

Lemma minset_union_uop_bop_left_reduction : 
   ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt  →
      uop_bop_left_reduction (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. unfold uop_bop_left_reduction. 
       intros s t. apply brel_set_intro. split. 
          apply tmp4; auto. 
          apply tmp5. 
Defined. 




(* 
     ∀ s1 s2, min (s1 U s2) =set= min ((min s1) U (min s2)) 
*) 
Lemma uop_minset_bop_union_uop_bop_invariant : 
       ∀ (S : Type) (eq : brel S) (lt : brel S),
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt →
           uop_bop_invariant (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. 
       apply uop_bop_invariant_left_intro. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_commutative_raw; auto. 
       apply uop_minset_brel_set_congruence; auto. 
       apply bop_union_uop_minset_left_invariant; auto. 
Defined. 


(* 
   min s1 = min t1 -> min s2 = min t2 -> min (s1 U s2) = min (t1 U t2) 
*) 
Lemma bop_union_uop_minset_congruence : ∀ (S : Type) (eq : brel S) (lt : brel S), 
     brel_reflexive S eq →
     brel_symmetric S eq →
     brel_transitive S eq →
     brel_congruence S eq lt →
       bop_uop_congruence (finite_set S) (brel_set S eq) (uop_minset S eq lt) (bop_union S eq). 
Proof. intros S eq lt refS symS transS cong. 
       unfold bop_uop_congruence. intros s1 s2 t1 t2 H1 H2. 
       (* 
         A : min (s1 U s2) = min (min(s1) U min(s2))    
         B : min (t1 U t2) = min (min(t1) U min(t2)) 
         C : min(s1) U min(s2) = min(t1) U min(t2)               (U congruence) 
         D : min(min(s1) U min(s2)) = min(min(t1) U min(t2))     (minset congruence) 

             result then follows by transitivity. 

         T   : min (s1 U s2) = min(min(t1) U min(t2))            (from A, D)
         QED : min (s1 U s2) = min (t1 U t2)                     (from T, B)
       *) 
       assert (A := uop_minset_bop_union_uop_bop_invariant _ _ lt refS symS transS cong s1 s2). 
       assert (B := uop_minset_bop_union_uop_bop_invariant _ _ lt refS symS transS cong t1 t2). 
       assert (C := bop_union_congruence_raw S eq refS symS transS _ _ _ _ H1 H2). 
       assert (D := uop_minset_brel_set_congruence S eq lt (* refS symS transS cong *) _ _ C ). 
       assert (T := brel_set_transitive S eq refS symS transS _ _ _ A D). 
       apply (brel_set_symmetric S eq symS) in B. 
       assert (QED := brel_set_transitive S eq refS symS transS _ _ _ T B). assumption. 
Defined. 


(* RATHER LATE *) 




Hypothesis cong1 : ∀ (S : Type) (eq : brel S) (lt : brel S), 
   uop_congruence_positive (finite_set S)
     (brel_reduce (finite_set S) (brel_set S eq) (uop_minset S eq lt))
     (uop_minset S eq lt). 

Hypothesis cong2 : ∀ (S : Type) (eq : brel S) (lt : brel S), 
 bop_congruence (finite_set S)
   (brel_reduce (finite_set S) (brel_set S eq) (uop_minset S eq lt))
   (bop_union S eq). 




Lemma brel_subset_false_intro : ∀ (S : Type) (r : brel S), 
     brel_reflexive S r ->
     brel_symmetric S r -> 
     brel_transitive S r -> 
        ∀ (x w : finite_set S), 
          { a:S & (in_set S r x a = true)  * (in_set S r w a = false)} -> 
               brel_subset S r x w = false. 
Proof. intros S r refS symS transS. induction x; intros w [s [P1 P2]]. 
       compute in P1. discriminate. 
       unfold brel_subset. fold brel_subset. 
       unfold in_set in P1. fold in_set in P1. 
       apply orb_is_true_left in P1. destruct P1 as [P1 | P1].
       assert (fact1 := in_set_bProp_congruence S r symS transS w _ _ P1). 
       rewrite P2 in fact1. 
       rewrite <- fact1. simpl. reflexivity. 
       assert (fact1 : brel_subset S r x w = false). 
          apply IHx. exists s; auto. 
       rewrite fact1. apply andb_comm. 
Defined. 

Lemma brel_set_false_intro : ∀ (S : Type) (eq : brel S) (X Y : finite_set S), 
     ((brel_subset S eq X Y = false) + (brel_subset S eq Y X = false))  → brel_set S eq X Y = false. 
Proof. unfold brel_set. unfold brel_and_sym. intros S eq X Y [H | H]. 
       rewrite H. simpl. reflexivity. 
       rewrite H. apply andb_comm. 
Defined. 


Hypothesis in_set_minset_intro : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
   is_minimal_in S eq lt a X = true -> in_set S eq (uop_minset S eq lt X) a = true. 

Hypothesis in_set_minset_false_intro : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
   is_minimal_in S eq lt a X = false -> in_set S eq (uop_minset S eq lt X) a = false. 

Hypothesis in_set_minset_false_intro_v2 : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
   in_set S eq X a = false -> in_set S eq (uop_minset S eq lt X) a = false. 

Hypothesis is_minimal_in_implies_in_set : ∀ (S : Type) (eq lt : brel S) (X : finite_set S) (a : S), 
  is_minimal_in S eq lt a X = true -> in_set S eq X a = true. 


Lemma brel_minset_false_intro : ∀ (S : Type) (eq lt : brel S) (X Y : finite_set S), 
      brel_reflexive S eq -> 
      brel_symmetric S eq -> 
      brel_transitive S eq -> 
      brel_congruence S eq lt -> 
      ({a : S & (in_set S eq X a = true) * (is_minimal_in S eq lt a X = true) * 
           ((is_minimal_in S eq lt a Y = false) + (in_set S eq Y a = false))} 
       + 
       {a : S & (in_set S eq Y a = true) * (is_minimal_in S eq lt a Y = true) * 
           ((is_minimal_in S eq lt a X = false) + (in_set S eq X a = false))}) -> 
            brel_minset S eq lt X Y = false. 
Proof. intros S eq lt X Y refS symS transS lt_cong D. 
       unfold brel_minset, brel_reduce. 
       apply brel_set_false_intro. 
       destruct D as [ [a [[P1 P2] [P3 | P4] ]] | [a [[P1 P2] [P3 | P4]]] ]. 
          left. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro; auto. 

          left. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro_v2; auto. 
 
          right. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro; auto. 


          right. 
          apply brel_subset_false_intro; auto. exists a. split. 
             apply in_set_minset_intro; auto. 
             apply in_set_minset_false_intro_v2; auto. 
Qed. 




Lemma support_lemma_1 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
    brel_symmetric S eq     → 
    brel_asymmetric S lt    → 
    brel_irreflexive S lt   → 
    brel_strict S eq lt     → 
    lt s t = true           →  (* NB !!! *) 
        is_minimal_in S eq lt s (bop_minset_union S eq lt (t :: nil) (s :: nil)) = true. 
Proof. intros S eq lt s t symS asym irr str P. 
       unfold bop_minset_union, bop_then_unary, bop_union, bop_concat. 
       unfold bop_then_unary, app, uop_duplicate_elim, in_set.  
       rewrite (brel_symmetric_implies_dual _ _ symS _ _ (str s t P)). simpl. 
       unfold uop_minset, uop_filter_from_brel2, uop_filter, filter. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl. 
       rewrite (irr t), P. simpl. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl.   
       rewrite (irr s), (asym _ _ P). compute. 
       rewrite (irr s). reflexivity. 
Defined. 



Lemma support_lemma_2 : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
    brel_symmetric S eq     → 
    brel_asymmetric S lt    → 
    brel_irreflexive S lt   → 
    brel_strict S eq lt     → 
    lt s t = true           →  (* NB !!! *) 
        is_minimal_in S eq lt s (bop_minset_union S eq lt (s :: nil) (t :: nil)) = true. 
Proof. intros S eq lt s t symS asym irr str P. 
       unfold bop_minset_union, bop_then_unary, bop_union, bop_concat. 
       unfold bop_then_unary, app, uop_duplicate_elim, in_set.  
       rewrite (str s t P). simpl. 
       unfold uop_minset, uop_filter_from_brel2, uop_filter, filter. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl. 
       rewrite irr, (asym _ _ P).  simpl. 
       unfold is_minimal_in at 2, brel_set, brel_and_sym. simpl.   
       rewrite (irr t), P. compute. 
       rewrite (irr s). reflexivity. 
Defined. 


Lemma bop_minset_union_not_is_left : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_reflexive S eq → 
    brel_symmetric S eq  → 
    brel_transitive S eq → 
    brel_congruence S eq lt → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
    ({ s1 : S & { s2 : S & lt s1 s2 = true}}) →  (* NB !!! *) 
      bop_not_is_left (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong_lt asym irr str [s [t P]]. 
       exists (t :: nil, s :: nil). 
       apply brel_minset_false_intro; auto. left. exists s. 
       assert (fact1 : is_minimal_in S eq lt s (bop_minset_union S eq lt (t :: nil) (s :: nil)) 
                       = true). 
          apply support_lemma_1; auto. 
       split. split.
          apply (is_minimal_in_implies_in_set S eq lt); auto. 
          assumption. 
          right. compute. rewrite (str s t P). reflexivity. 
Defined. 


Lemma bop_minset_union_not_is_right : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_reflexive S eq → 
    brel_symmetric S eq  → 
    brel_transitive S eq → 
    brel_congruence S eq lt → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
    ({ s1 : S & { s2 : S & lt s1 s2 = true}}) →  (* NB !!! *) 
      bop_not_is_right (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt refS symS transS cong_lt asym irr str [s [t P]]. 
       exists (s :: nil, t :: nil). 
       apply brel_minset_false_intro; auto. left. exists s. 
       assert (fact1 : is_minimal_in S eq lt s (bop_minset_union S eq lt (s :: nil) (t :: nil)) 
                       = true). 
          apply support_lemma_2; auto. 
       split. split.
          apply (is_minimal_in_implies_in_set S eq lt); auto. 
          assumption. 
          right. compute. rewrite (str s t P). reflexivity. 
Defined. 



Definition brel_strict_total (S : Type) (eq r : brel S) := 
    ∀ s t : S, eq s t = false -> (r s t = true) + (r t s = true). 

Definition brel_not_strict_total (S : Type) (eq r : brel S) := 
    {s : S & { t : S & (eq s t = false) * (r s t = false) * (r t s = false)}}. 


Hypothesis bop_minset_total  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt   → 
    brel_strict_total S eq lt → 
     ∀ (X : finite_set S), 
       (brel_minset S eq lt nil X = true) + 
       { s : S & brel_minset S eq lt (s::nil) X = true}. 
(* 
Proof. intros S eq lt symS asym irr str tot X Y. 
       unfold bop_selective. intros s t. 
Defined. 
*) 

Hypothesis bop_minset_union_nil_left : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S), 
   brel_minset S eq lt nil X = true -> 
     brel_minset S eq lt (bop_minset_union S eq lt X Y) Y = true. 

(*
assert (minset_ref   := brel_minset_reflexive S eq lt refS symS transS). 
assert (minset_sym   := brel_minset_symmetric S eq lt symS). 
assert (minset_trans := brel_minset_transitive S eq lt refS symS transS). 
assert (minset_union_cong := bop_minset_union_congruence S eq lt refS symS transS cong_lt). 

   assert (fact1 := minset_union_cong _ _ _ _ nilX nilY). 
   assert (fact2 : brel_minset S eq lt nil (bop_minset_union S eq lt nil nil) = true). 
      compute. reflexivity. 
   assert (fact3 := minset_trans _ _ _ fact2 fact1).  
   apply minset_sym in fact3. 
   assert (fact4 := minset_trans _ _ _ fact3 nilX).  
   assumption. 
*) 

Hypothesis bop_minset_union_nil_right : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (X Y : finite_set S), 
   brel_minset S eq lt nil X = true -> 
     brel_minset S eq lt (bop_minset_union S eq lt Y X) Y = true. 


Lemma bop_minset_union_selective  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
brel_reflexive S eq
          → brel_symmetric S eq
            → brel_transitive S eq
              → brel_congruence S eq lt → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
    brel_strict_total S eq lt → 
      bop_selective (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. 
intros S eq lt refS symS transS cong_lt asym irr str tot X Y. unfold bop_selective. 
assert (factX := bop_minset_total S eq lt asym irr str tot X). 
assert (factY := bop_minset_total S eq lt asym irr str tot Y). 
destruct factX as [nilX | [x pX]]; destruct factY as [nilY | [y pY]]. 
left. apply bop_minset_union_nil_right; auto. 
right. apply bop_minset_union_nil_left; auto. 
left. apply bop_minset_union_nil_right; auto. 
case_eq(eq x y); intro E. 
   admit. 
   destruct (tot _ _ E) as [H | H]. 
      left. admit. 
      right. admit. 
Defined. 


(* want A, B such that 

min(min A U min B) <> min A
min(min A U min B) <> min B

s < t < v 

A = {s, v} 

min {s} = {s} 
min {t} = {t} 

*) 
Hypothesis aux_lemma1  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
      lt s t = false -> lt t s = false -> 
         bop_minset_union S eq lt (s :: nil) (t :: nil) = s :: t :: nil. 
(* n
Proof. intros S eq lt s t L R. 
       unfold bop_minset_union. 
       unfold bop_then_unary. 
       unfold bop_union, bop_concat. unfold bop_then_unary. 
Defined.
*) 

Hypothesis aux_lemma2  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
      lt s t = false -> lt t s = false -> 
         brel_minset S eq lt (s :: t :: nil) (s :: nil) = false. 

Hypothesis aux_lemma3  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S) (s t : S), 
      lt s t = false -> lt t s = false -> 
         brel_minset S eq lt (s :: t :: nil) (t :: nil) = false. 


Lemma bop_minset_union_not_selective  : 
   ∀ (S : Type) (eq : brel S) (lt : brel S), 
    brel_symmetric S eq  → 
    brel_asymmetric S lt  → 
    brel_irreflexive S lt → 
    brel_strict S eq lt → 
   (brel_not_total S lt) → 
      bop_not_selective (finite_set S) (brel_minset S eq lt) (bop_minset_union S eq lt).
Proof. intros S eq lt symS asym irr str [ [s t] [L R]]. 
       unfold bop_not_selective. 
       exists (s :: nil, t :: nil).
       rewrite aux_lemma1; auto. 
       rewrite aux_lemma2; auto. 
       rewrite aux_lemma3; auto. 
Defined. 

(* 

id ann

*) 


(* 

Definition ltr_set_scalar_product : ∀ S : Type, binary_op S → left_transform S (finite_set S) 
:= λ S b x Y, List.map (λ y, b x y) Y. 

Definition ltr_set_map : ∀ S : Type, binary_op S → left_transform (finite_set S) (finite_set (finite_set S))
:= λ S b x Y, List.map (λ y, b x y) Y. 

Definition bop_set_product : ∀ S T : Type, binary_op S → binary_op (finite_set S) 
:= λ S b X Y, 
   List.map (λ x, List.map (λ y, b x y) Y) X. 

*) 

























