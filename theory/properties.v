Require Import CAS.code.basic_types. 

Close Scope nat. 

(* bProp *) 

Definition bProp_congruence (S : Type) (eq : brel S) (P : bProp S) := 
   ∀ s t : S, eq s t = true → P s = P t. 

Definition brel_congruence (S : Type) (eq : brel S) (r : brel S) := 
   ∀ s t u v : S, eq s u = true → eq t v = true → r s t = r u v. 



(* brel *) 

(* 

Old definition of "not trivial" was 

Definition brel_not_true (S : Type) (r : brel S) 
    := {s : S & {t : S & r s t = false}}. 

Definition brel_not_false (S : Type) (r : brel S) 
    := {s : S & {t : S & r s t = true}}. 

Record brel_not_trivial (S : Type) (r : brel S) := {
  brel_not_trivial_not_true  : brel_not_true S r 
; brel_not_trivial_not_false : brel_not_false S r 
}.  

*) 

(* 

    Do we need to change the definition of "not trivial"? 
    
    Candidate: 
      
        (1) { s : S & r s s = true }
        (2) ∀ (i : S), { s : S & r i s = false }

    or (2) could be 

        (2') { f : S -> S & ∀ (i : S), r i (f i) = false }


   Something like this seems to be needed here since 

        bop_not_exists_id S r (bop_left S).

   expands to 

        ∀ i : S, {s : S & (r i s = false) + (r s s = false)}


   bop_not_exists_id S r (bop_right S).

   expands to 

   ∀ i : S, {s : S & (r s s = false) + (r i s = false)}


  bop_not_exists_ann S r (bop_left S).

  expands to 

  ∀ a : S, {s : S & (r a a = false) + (r s a = false)}

                                           ^^^^^^^^^^^^^
                                           NB 

    Do we need to change the definition of "not trivial"? 
    
    Candidate: 
      
        (1) { s : S & r s s = true }
        (2) ∀ (i : S), { s : S & (r i s = false) * (r s i = false) }

    or (2) could be 

        (2') { f : S -> S & ∀ (i : S), (r i (f i) = false) * (r (f i) i = false)  }

*) 


Definition brel_witness (S : Type) (r : brel S) 
    := {s : S & r s s = true}. 

Definition brel_negate (S : Type) (r : brel S) 
    := {f : S -> S & ∀ s : S, (r s (f s) = false) * (r (f s) s = false) }. 

Record brel_nontrivial (S : Type) (r : brel S) := {
  brel_nontrivial_witness   : brel_witness S r 
; brel_nontrivial_negate    : brel_negate S r 
}.  


(*

Definition prefix_injective (S : Type) (n : nat) (f : nat -> S) (r : brel S), 
    := ∀ s t : nat, s <= n -> t <= n -> r (f s) (f t) = true -> s = t. 

Definition brel_finite (S : Type) (r : brel S) 
    := { n : nat & {f : nat -> S & ∀ s : S { m : nat & (m <= n) * (r (f m) s = true)}}}

Definition brel_not_finite (S : Type) (r : brel S) 
    := ∀ n : nat, ∀ f : nat -> S, {s : S &  ∀ m : nat , (m <= n)  -> (r (f m) s = false} ) }}

*) 


Definition brel_strict (S : Type) (r : brel S) (lt : brel S) := 
   ∀ s t : S, lt s t = true → r s t = false. 

Definition brel_not_strict (S : Type) (r : brel S) (lt : brel S) 
(*    {s : S & { t : S & (lt s t = true) * (r s t = true)}}. *) 
   := { z : S * S & match z with (s, t) => (lt s t = true) * (r s t = true) end}. 

Definition brel_strict_decidable (S : Type) (r : brel S) (lt : brel S) := 
   (brel_strict S r lt) + (brel_not_strict S r lt). 

Lemma brel_strict_covered : forall (S : Type) (r : brel S) (lt : brel S),  
   ((brel_strict S r lt) * (brel_not_strict S r lt)) -> False.  
Proof. intros S r lt [str [[s t] [L R]]]. rewrite (str s t L) in R. discriminate. Defined. 

(* 
    asymmetric iff  anti-symmetric  and irreflexive
               iff brel_strict S r r 
*) 
Definition brel_asymmetric (S : Type) (r : brel S) := 
   ∀ s t : S, r s t = true → r t s = false. 

Definition brel_not_asymmetric (S : Type) (r : brel S) 
(*   {s : S & {t : S & (r s t = true) * (r t s = true)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = true) end}. 


Definition brel_asymmetric_decidable (S : Type) (r : brel S) := 
   (brel_asymmetric S r) + (brel_not_asymmetric S r). 


Definition brel_reflexive (S : Type) (r : brel S) := 
    ∀ s : S, r s s = true. 

Definition brel_not_reflexive (S : Type) (r : brel S) := 
    {s : S &  r s s = false}. 

Definition brel_reflexive_decidable (S : Type) (r : brel S) := 
    (brel_reflexive S r) + (brel_not_reflexive S r). 

Lemma brel_reflexive_covered : forall (S : Type) (r : brel S), 
    ((brel_reflexive S r) * (brel_not_reflexive S r)) -> False. 
Proof. intros S r [refS [s P]].  rewrite (refS s) in P. discriminate. Defined. 


Definition brel_transitive (S : Type) (r : brel S) := 
    ∀ s t u: S, (r s t = true) → (r t u = true) → (r s u = true). 

(* aka intransitive *) 
Definition brel_not_transitive (S : Type) (r : brel S) 
(*    {s : S & {t : S & {u: S & (r s t = true) * (r t u = true) * (r s u = false)}}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r s t = true) * (r t u = true) * (r s u = false)  end}. 

Definition brel_transitive_decidable (S : Type) (r : brel S) := 
   (brel_transitive S r) + (brel_not_transitive S r). 


Lemma brel_transitive_covered : forall (S : Type) (r : brel S), 
   ((brel_transitive S r) * (brel_not_transitive S r)) -> False. 
Proof. intros S r [transS [ [s [t u]] [[A B] C]]]. rewrite (transS _ _ _ A B) in C. 
       discriminate. 
Defined. 

Definition brel_symmetric (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = true) → (r t s = true). 

Definition brel_not_symmetric (S : Type) (r : brel S) 
(*    {s : S & {t : S & (r s t = true) * (r t s = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = false) end}. 

Definition brel_symmetric_decidable (S : Type) (r : brel S) := 
   (brel_symmetric S r) + (brel_not_symmetric S r).


Definition brel_total (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = true) + (r t s = true). 

Definition brel_not_total (S : Type) (r : brel S) 
(*     {s : S & { t : S & (r s t = false) * (r t s = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = false) * (r t s = false) end}. 

Definition brel_total_decidable (S : Type) (r : brel S) := 
    (brel_total S r) + (brel_not_total S r).

Definition brel_irreflexive (S : Type) (r : brel S) := 
    ∀ s : S, r s s = false. 

Definition brel_not_irreflexive (S : Type) (r : brel S) := 
    {s : S & r s s = true}. 

Definition brel_irreflexive_decidable (S : Type) (r : brel S) := 
   (brel_irreflexive S r) + (brel_not_irreflexive S r). 


Definition brel_has_2_chain (S : Type) (r : brel S) 
  (*  {s : S & {t : S & {u : S & (r s t = true) * (r t u = true)}}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) =>  (r s t = true) * (r t u = true) end}. 

Definition brel_not_has_2_chain (S : Type) (r : brel S) := 
   ∀ s t u : S, r s t = true → r t u = false. 

Definition brel_has_2_chain_decidable (S : Type) (r : brel S) := 
   (brel_has_2_chain S r) + (brel_not_has_2_chain S r). 


Definition brel_bop_compatible_right (S : Type) (r : brel S) (b : binary_op S) := 
   ∀ (s u v : S), r s u = true -> r s v = true -> r s (b u v) = true.


(* r2 w.r.t r1*) 


Definition brel_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) := 
    ∀ s t : S, (r2 s t = true) → (r2 t s = true) → (r1 s t = true). 


Definition brel_not_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) 
(*   {s : S & {t : S & (r2 s t = true) * (r2 t s = true) * (r1 s t = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r2 s t = true) * (r2 t s = true) * (r1 s t = false) end}. 

Definition brel_antisymmetric_decidable (S : Type) (r1 : brel S) (r2 : brel S) := 
   (brel_antisymmetric S r1 r2) + (brel_not_antisymmetric S r1 r2). 


(* brel2 *) 


Definition brel2_left_congruence (S T : Type) (r1 : brel S) (r2 : brel2 S T) := 
    ∀ (t : T) (s1 s2 : S), r1 s1 s2 = true -> r2 s1 t = r2 s2 t. 
(*

Definition brel2_left_congruence (S T : Type) (r1 : brel S) (r2 : brel2 S T) := 
    ∀ (s1 s2 : S) (t : T), r1 s1 s2 = true -> r2 s1 t = true ->  r2 s2 t = true. 
*) 

Definition brel2_right_congruence (S T : Type) (r1 : brel T) (r2 : brel2 S T) := 
    ∀ (s : S) (t1 t2 : T), r1 t1 t2 = true -> r2 s t1 = true ->  r2 s t2 = true. 

Definition brel2_congruence (S T : Type) (rS : brel S) (rT : brel T) (r : brel2 S T) := 
    ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> r s1 t1 = r s2 t2. 


(* uop *) 

Definition uop_bop_left_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b (u s) t)) = true. 

Definition uop_bop_right_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b s (u t))) = true. 

Definition uop_bop_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b (u s) (u t))) = true. 

Definition uop_cancellative (S : Type) (r : brel S) (u : unary_op S)
    := ∀ s t : S, r (u s) (u t) = true -> r s t = true.

Definition uop_not_cancellative (S : Type) (r : brel S) (u : unary_op S)
   := { z : S * S & match z with (s, t) => (r (u s) (u t) = true) * (r s t = false) end }. 

Definition uop_cancellative_decidable  (S : Type) (r : brel S) (u : unary_op S) := 
    (uop_cancellative S r u) + (uop_not_cancellative S r u). 


Definition uop_preserves_brel (S : Type) (u : unary_op S) (r : brel S) := 
        ∀ (s : S), r (u s) s = true. 

Definition uop_injective (S : Type) (r : brel S) (u : unary_op S) := 
  ∀ s t : S, r (u s) (u t) = true -> r s t = true. 

(* Need this? *) 
Definition uop_congruence_positive (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r (u s) (u t) = true.

(* Need this?  THIS IS uop_injective_contrapositive !!!!  

constructively, if we have 

P = A -> B 

then we have 

Q = not B -> not A 


*) 
Definition uop_congruence_negative (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = false -> r (u s) (u t) = false.

Definition uop_congruence (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r (u s) (u t) = true.

Definition uop_uop_congruence (S : Type) (r : brel S) (u : unary_op S) (f : unary_op S) := 
   ∀ s t : S, r (u s) (u t) = true → r (u (f s)) (u (f t)) = true. 

Definition uop_idempotent (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ s : S, r (u (u s)) (u s) = true. 
 
Definition uop_not_trivial (S : Type) (r : brel S) (u : unary_op S)  
(*   {s : S & {t : S & r (u s) (u t) = false}}.  *) 
   := { z : S * S & match z with (s, t) => r (u s) (u t) = false end }. 

(* 
     u (s + t) = u ((u s) + t) 
or 
     u (s + t) <= u ((u s) + t)
*) 
Definition uop_bop_left_invariant (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
    ∀ (s t : S), r (u (b s t)) (u (b (u s) t)) = true. 

Definition uop_bop_right_invariant (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
    ∀ (s t : S), r (u (b s t)) (u (b s (u t))) = true. 

Definition uop_bop_invariant (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
    ∀ (s t : S), r (u (b s t)) (u (b (u s) (u t))) = true. 


(* NEED? 
Definition uop_congruence_right (S T : Type) (r : brel2 S T) (u : unary_op T) := 
   ∀ (s : S) (t : T), r s t = true -> r s (u t) = true.
*) 


Definition uop_preserves_left_positive (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r (u s) t = true.

Definition uop_preserves_left_negative (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = false -> r (u s) t = false.

Definition uop_preserves_right_positive (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = true -> r s (u t) = true.

Definition uop_preserves_right_negative (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ (s t : S), r s t = false -> r s (u t) = false.


Definition uop_brel2_preserves_left_positive (S T: Type) (r : brel2 S T) (u : unary_op S) := 
   ∀ (s : S) (t : T), r s t = true -> r (u s) t = true.

Definition uop_brel2_preserves_left_negative (S T : Type) (r : brel2 S T) (u : unary_op S) := 
   ∀ (s : S) (t : T), r s t = false -> r (u s) t = false.

(* Need? 
Definition uop_brel2_preserves_right (S T : Type) (r : brel2 S T) (u : unary_op T) := 
   ∀ (s : S) (t : T), r s t = true -> r s (u t) = true.

Definition uop_brel2_preserves_right_false (S T : Type) (r : brel2 S T) (u : unary_op T) := 
   ∀ (s : S) (t : T), r s t = false -> r s (u t) = false.
*) 

(*  
   u(s + t) + v   =  s + u (t + v)
*)  
Definition uop_bop_associative (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) 
    := ∀ s t v : S, r (b (u (b s t)) v) (b s (u (b t v))) = true. 



(* bop *) 


Definition bop_congruence (S : Type) (r : brel S) (b : binary_op S) := 
   ∀ (s1 s2 t1 t2 : S), r s1 t1 = true -> r s2 t2 = true -> r (b s1 s2) (b t1 t2) = true.

Definition bop_uop_congruence (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
   ∀ (s1 s2 t1 t2 : S), r (u s1) (u t1) = true -> r (u s2) (u t2) = true 
          -> r (u (b s1 s2)) (u (b t1 t2)) = true.


Definition bop_associative (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t u : S, r (b (b s t) u) (b s (b t u)) = true. 




(* Commutativity *) 


Definition bop_commutative (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) (b t s) = true. 

Definition bop_not_commutative(S : Type) (r : brel S) (b : binary_op S) 
(*    := {s : S & {t : S & r (b s t) (b t s) = false}}. *) 
    := { z : S * S & match z with (s, t) => r (b s t) (b t s) = false end }. 

Definition bop_commutative_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_commutative S r b) + (bop_not_commutative S r b). 


(* Selectivity *) 

(* bop_selective : ∀ S : Type, brel S → binary_op S → Type *) 
Definition bop_selective (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, (r (b s t) s = true) + (r (b s t) t = true).

Definition bop_not_selective (S : Type) (r : brel S) (b : binary_op S) 
(*    := {s : S & {t : S & prod (r (b s t) s = false) (r (b s t) t = false)}}. *) 
    := { z : S * S & match z with (s, t) =>  (r (b s t) s = false)  * (r (b s t) t = false) end }. 


Definition bop_selective_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_selective S r b) + (bop_not_selective S r b). 


(* ruptured dioids my result in idempotance *) 

Definition bop_idempotent (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s : S, r (b s s) s = true. 

Definition bop_not_idempotent (S : Type) (r : brel S) (b : binary_op S) 
    := {s : S & r (b s s) s = false}.

Definition bop_idempotent_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_idempotent S r b) + (bop_not_idempotent S r b). 


(* Left/Right *) (* CLEAN UP ! 

    P(x) 

          P                   not_P 
    ∀ x, P(x) = true     {x & P(x) = false } 

        anti_P                not_anti_P 
    ∀ x, P(x) = false    {x & P(x) = true } 
    ??

    for nontrivial carriers we have 

    P  not_P   anti_P    not_anti_P 
    -------------------------------
   T   F        F           T        always P 
   F   T        T           F        never P 
   F   T        F           T        sometimes P, somtimes not P 

*) 

(* 
bop_is_left           r (b s t) s = true. 
bop_anti_left         r (b s t) s = false. 
bop_is_id             r (b s i) s = true
                      r (b i s) s = true
bop_is_ann            r (b a s) a = true
                      r (b s a) a = true
bop_left_cancellative r (b s t) (b s u) = true -> r t u = true.
bop_left_constant     r (b s t) (b s u) = true. 
*) 

(* needed for selectivity of product *) 
Definition bop_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = true. 

Definition bop_not_is_left (S : Type) (r : brel S) (b : binary_op S) 
(*    := {s : S & {t : S & r (b s t) s = false}}. *) 
    := { z : S * S & match z with (s, t) =>  r (b s t) s = false end }. 


Definition bop_is_left_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_is_left S r b) + (bop_not_is_left S r b). 

Definition bop_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) t = true. 

Definition bop_not_is_right (S : Type) (r : brel S) (b : binary_op S) 
(*    := {s : S & {t : S & r (b s t) t = false}}. *) 
    := { z : S * S & match z with (s, t) =>  r (b s t) t = false end }. 

Definition bop_is_right_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_is_right S r b) + (bop_not_is_right S r b). 

(* needed for not_trivial of brel_llte_llt.v 

   this is same as bop_not_anti_right


Definition bop_somewhere_left (S : Type) (r : brel S) (b : binary_op S) 
(*    := {s : S & {t : S & r (b s t) s = true}}. *) 
    := { z : S * S & match z with (s, t) => r (b s t) s = true end }. 

Definition bop_not_somewhere_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = false. 
*) 


(* needed by bop_add_id_left_cancellative, right_cancellative *) 
Definition bop_anti_left (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b s t) = false. 

Definition bop_not_anti_left (S : Type) (r : brel S) (b : binary_op S) 
(* := {s: S & {t : S &  r s (b s t) = true}}. *) 
   := { z : S * S & match z with (s, t) => r s (b s t) = true end }. 

Definition bop_anti_left_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_anti_left S r b) + (bop_not_anti_left S r b). 

Definition bop_anti_right (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b t s) = false. 

Definition bop_not_anti_right (S : Type) (r : brel S) (b : binary_op S) 
(*   :=  {s: S & {t : S &  r s (b t s) = true}}. *) 
   := { z : S * S & match z with (s, t) => r s (b t s) = true end }. 

Definition bop_anti_right_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_anti_right S r b) + (bop_not_anti_right S r b). 



(* IDs Annihilators 

  LEFT and RIGHT versions? 
*) 

Definition bop_is_id (S : Type) (r : brel S) (b : binary_op S) (i : S) 
    := ∀ s : S, (r (b i s) s = true) * (r (b s i) s = true).

Definition bop_not_is_id (S : Type) (r : brel S) (b : binary_op S) (i : S)
    := {s : S & (r (b i s) s = false) + (r (b s i) s = false)}.

Definition bop_exists_id (S : Type) (r : brel S) (b : binary_op S) 
    := {i : S & bop_is_id S r b i}.

Definition bop_not_exists_id (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ i : S, bop_not_is_id S r b i.

Definition bop_exists_id_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_exists_id S r b) + (bop_not_exists_id S r b). 

Definition bop_is_ann (S : Type) (r : brel S) (b : binary_op S) (a : S)
    :=  ∀ s : S, (r (b a s) a = true) * (r (b s a) a = true).

Definition bop_not_is_ann (S : Type) (r : brel S) (b : binary_op S) (a : S)
    := {s : S & (r (b a s) a = false) + (r (b s a) a = false)}.

Definition bop_exists_ann (S : Type) (r : brel S) (b : binary_op S) 
    := {a : S & bop_is_ann S r b a }.

Definition bop_not_exists_ann (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ a : S, bop_not_is_ann S r b a. 

Definition bop_exists_ann_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_exists_ann S r b) + (bop_not_exists_ann S r b). 

(* Cancellativity *) 

Definition bop_left_cancellative (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true -> r t u = true.

Definition bop_not_left_cancellative (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S & (r (b s t) (b s u) = true) * (r t u = false) }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r (b s t) (b s u) = true) * (r t u = false) end }. 

Definition bop_left_cancellative_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_left_cancellative S r b) + (bop_not_left_cancellative S r b). 

Definition bop_right_cancellative (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b t s) (b u s) = true -> r t u = true. 

Definition bop_not_right_cancellative (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S & (r (b t s) (b u s) = true) * (r t u = false) }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) =>  (r (b t s) (b u s) = true) * (r t u = false) end }. 

Definition bop_right_cancellative_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_right_cancellative S r b) + (bop_not_right_cancellative S r b). 


(* Condensed ("constant") *) 

Definition bop_left_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true. 

Definition bop_not_left_constant (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S &  r (b s t) (b s u) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (b s t) (b s u) = false  end }. 

Definition bop_left_constant_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_left_constant S r b) + (bop_not_left_constant S r b). 

Definition bop_right_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b t s) (b u s) = true. 

Definition bop_not_right_constant (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S &  r (b t s) (b u s) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (b t s) (b u s) = false end }. 

Definition bop_right_constant_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_right_constant S r b) + (bop_not_right_constant S r b). 


(* Interaction of multiple binary ops *) 

Definition bop_left_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := ∀ s t u : S, r (mul s (add t u)) (add (mul s t) (mul s u)) = true. 

Definition bop_not_left_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
(*    := {s : S & {t : S & {u : S & r (mul s (add t u)) (add (mul s t) (mul s u)) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (mul s (add t u)) (add (mul s t) (mul s u)) = false end }. 

Definition bop_left_distributive_decidable (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := (bop_left_distributive S r add mul) + (bop_not_left_distributive S r add mul). 

Definition bop_right_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
    := ∀ s t u : S, r (mul (add t u) s) (add (mul t s) (mul u s)) = true. 

Definition bop_not_right_distributive (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S)    
(*   := {s : S & {t : S & {u : S & r (mul (add t u) s) (add (mul t s) (mul u s)) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (mul (add t u) s) (add (mul t s) (mul u s)) = false end }. 

Definition bop_right_distributive_decidable (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := (bop_right_distributive S r add mul) + (bop_not_right_distributive S r add mul). 


Definition bops_id_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { eI : bop_exists_id S r b1 & 
   { eA : bop_exists_ann S r b2 & r (projT1 eI) (projT1 eA)  = true }}. 

Definition bops_not_id_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:=  ∀ (i a : S), bop_is_id S r b1 i -> bop_is_ann S r b2 a -> r i a = false. 

Definition bops_id_equals_ann_decidable 
   (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
   := (bops_id_equals_ann S r b1 b2) + (bops_not_id_equals_ann S r b1 b2). 

Definition bops_id_equals_id (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { eI : bop_exists_id S r b1 & 
   { eA : bop_exists_id S r b2 & r (projT1 eI) (projT1 eA)  = true }}. 

Definition bops_not_id_equals_id (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:=  ∀ (i a : S), bop_is_id S r b1 i -> bop_is_id S r b2 a -> r i a = false. 

Definition bops_id_equals_id_decidable 
   (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
   := (bops_id_equals_id S r b1 b2) + (bops_not_id_equals_id S r b1 b2). 


Definition bops_ann_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:= { eI : bop_exists_ann S r b1 & 
   { eA : bop_exists_ann S r b2 & r (projT1 eI) (projT1 eA)  = true }}. 

Definition bops_not_ann_equals_ann (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
:=  ∀ (i a : S), bop_is_ann S r b1 i -> bop_is_ann S r b2 a -> r i a = false. 

Definition bops_ann_equals_ann_decidable 
   (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
   := (bops_ann_equals_ann S r b1 b2) + (bops_not_ann_equals_ann S r b1 b2). 


Definition bops_left_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_not_left_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 s t)) = false end }. 

Definition bops_left_absorption_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_left_absorption S r b1 b2) + (bops_not_left_absorption S r b1 b2). 


Definition bops_right_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_not_right_absorption (S : Type) (r : brel S) (b1 b2 : binary_op S)
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 t s)) = false end }. 

Definition bops_right_absorption_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_right_absorption S r b1 b2) + (bops_not_right_absorption S r b1 b2). 









