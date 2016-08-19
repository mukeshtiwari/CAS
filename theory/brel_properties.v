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


(* top and bottom 

  LEFT and RIGHT versions? 
*) 

Definition brel_is_bottom (S : Type) (lte : brel S) (b : S) 
    := ∀ s : S, (lte b s = true).

Definition brel_not_is_bottom (S : Type) (lte : brel S) (b : S)
    := {s : S & lte b s = false }.

Definition brel_exists_bottom (S : Type) (r : brel S)
    := {b : S & brel_is_bottom S r b}.

Definition brel_not_exists_bottom (S : Type) (r : brel S)
    := ∀ b : S, brel_not_is_bottom S r b.

Definition brel_exists_bottom_decidable  (S : Type) (r : brel S) := 
    (brel_exists_bottom S r) + (brel_not_exists_bottom S r). 

Definition brel_is_top (S : Type) (lte : brel S) (b : S) 
    := ∀ s : S, (lte s b = true).

Definition brel_not_is_top (S : Type) (lte : brel S) (b : S)
    := {s : S & lte s b = false }.

Definition brel_exists_top (S : Type) (r : brel S) 
    := {b : S & brel_is_top S r b}.

Definition brel_not_exists_top (S : Type) (r : brel S)
    := ∀ b : S, brel_not_is_top S r b.

Definition brel_exists_top_decidable  (S : Type) (r : brel S) := 
    (brel_exists_top S r) + (brel_not_exists_top S r). 

