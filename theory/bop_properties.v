Require Import CAS.code.basic_types. 


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

Definition bop_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = true. 

Definition bop_not_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := { z : S * S & match z with (s, t) =>  r (b s t) s = false end }. 


Definition bop_is_left_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_is_left S r b) + (bop_not_is_left S r b). 

Definition bop_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) t = true. 

Definition bop_not_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := { z : S * S & match z with (s, t) =>  r (b s t) t = false end }. 

Definition bop_is_right_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_is_right S r b) + (bop_not_is_right S r b). 

Definition bop_anti_left (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b s t) = false. 

Definition bop_not_anti_left (S : Type) (r : brel S) (b : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b s t) = true end }. 

Definition bop_anti_left_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_anti_left S r b) + (bop_not_anti_left S r b). 

Definition bop_anti_right (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b t s) = false. 

Definition bop_not_anti_right (S : Type) (r : brel S) (b : binary_op S) 
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


