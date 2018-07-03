Require Import Coq.Bool.Bool.    (* eqb *) 
Require Coq.Arith.EqNat.         (* beq_nat *) 
Require Import Coq.Arith.Arith.
Require Import CAS.code.basic_types. 
Require Import Coq.Strings.String. 

(* Notes on eqiv relation    a ~ b  over S 

   refl, sym, trans 

   <a> = rep 

   <a> ~ a 


*) 

Open Scope list_scope.
Open Scope string_scope. 

(* INFINITY ! *) 
Definition cas_infinity : cas_constant := "INFINITY". 
Definition brel_eq_bool : brel bool := eqb. 
Definition brel_eq_nat  : brel nat  := Arith.EqNat.beq_nat.
Definition brel_to_nat  : brel nat  := Coq.Arith.Compare_dec.leb.  

(* total order on bool : false < true 
   x y <=
   ======
   t t t 
   f t t 
   t f f 
   f f t 
*) 
Definition brel_to_bool : brel bool 
:= λ x y, if y then true else if x then false else true. 


(* was dual *) 
Definition brel_complement : ∀ {S : Type}, brel S -> brel S 
:= λ {S} r x y,  if (r x y) then false else true. 

Definition brel2_complement : ∀ {S T : Type}, brel2 S T -> brel2 S T
:= λ {S} {T} r x y,  if (r x y) then false else true. 

(* was reverse *) 
Definition brel_dual : ∀ {S : Type}, brel S -> brel S := λ {S} r x y,  r y x. 

Definition brel2_dual : ∀ {S T : Type}, brel2 S T -> brel2 T S := λ {S} {T} r x y,  r y x. 

Definition brel_conjunction : ∀ {S : Type}, brel S -> brel S -> brel S 
:= λ {S} r1 r2 x y,  (r1 x y) && (r2 x y). 

Definition brel2_conjunction : ∀ {S T : Type}, brel2 S T-> brel2 S T -> brel2 S T
:= λ {S} {T} r1 r2 x y,  (r1 x y) && (r2 x y). 



(*
Definition brel_conj : ∀ (S : Type), brel S -> brel S -> brel S 
:= λ S r1 r2 x y, (r1 x y) && (r2 x y). 
*) 

Definition brel_disjunction : ∀ {S : Type}, brel S -> brel S -> brel S 
:= λ {S} r1 r2 x y,  (r1 x y) || (r2 x y). 

Definition brel2_disjunction : ∀ {S T : Type}, brel2 S T-> brel2 S T -> brel2 S T
:= λ {S} {T} r1 r2 x y,  (r1 x y) || (r2 x y). 


(* 
Definition brel_disj : ∀ (S : Type), brel S -> brel S -> brel S 
:= λ S r1 r2 x y,  (r1 x y) || (r2 x y). 
*) 

Definition brel_strictify : ∀ {S : Type}, brel S -> brel S 
:= λ {S} r,  brel_conjunction r (brel_complement (brel_dual r)). 


Definition brel_list : ∀ {S : Type}, brel S → brel(list S)
:= fix f {S} U x y := 
      match x, y with
         | nil, nil => true 
         | nil, _ => false 
         | _, nil => false 
         | a::tla, b::tlb => andb (U a b) (f U tla tlb)
      end.

(* This is forallb from List.v.  Define it here 
   rather than in List.v so as not to pull in that file in extraction. 
 *)

Definition bProp_lift_list : ∀ {A : Type}, (bProp A) -> bProp (list A) 
:= fix f {A} p l := 
      match l with
	| nil     => true
	| a::rest => p a && f p rest
      end.

Definition dominates_set : ∀ {S : Type}, brel S → brel S → brel2 (finite_set S) S 
:= λ {S} eq lte X a, bProp_lift_list  (λ x, brel_complement (brel_strictify lte) x a) X.                 

(* was called bProp_forall    proofs in bprop_forall.v 

Definition bProp_lift_set : ∀ {A : Type}, (bProp A) -> bProp (finite_set A) 
:= bProp_lift_list. 
*)

Definition bProp_from_brel_left : ∀ {S : Type}, brel S -> S -> bProp S
:= λ {S} r a x, r x a.  

Definition bProp_from_brel_right : ∀ {S : Type}, brel S -> S -> bProp S
:= λ {S} r a x, r a x.  


Definition brel_product : ∀ {S T : Type}, brel S → brel T → brel (S * T)
:= λ {S} {T} U V x y, 
   match x, y with
   | (x1, x2), (y1, y2) => andb (U x1 y1) (V x2 y2) 
   end.

Definition brel2_product : ∀ {S T U V : Type}, brel2 S U → brel2 T V → brel2 (S * T) (U * V)
:= λ {S} {T} {U} {V} r q x y, 
   match x, y with
   | (x1, x2), (y1, y2) => andb (r x1 y1) (q x2 y2) 
   end.


Definition brel_sum : ∀ {S T : Type}, brel S → brel T → brel (S + T)
:= λ  {S} {T} U V x y, 
   match x, y with
   | (inl a), (inl b) => U a b 
   | (inl _), (inr _) => false 
   | (inr _), (inl _) => false 
   | (inr a), (inr b) => V a b
   end.

Definition brel_add_constant : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} rS c x y, 
   match x, y with
   | (inl a), (inl b) => true (* all constants equal! *) 
   | (inl _), (inr _) => false 
   | (inr _), (inl _) => false 
   | (inr a), (inr b) => rS a b 
   end.

Definition brel_add_bottom : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} rS c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => true  (* new bottom ! *) 
   | (inr _), (inl _) => false 
   | (inr a), (inr b) => rS a b 
   end.

Definition brel_add_top : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} rS c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => false 
   | (inr _), (inl _) => true  (* new top ! *) 
   | (inr a), (inr b) => rS a b 
   end.


(* DELETE 
Definition brel_from_bop_left : ∀ (S : Type) (r : brel S) (b : binary_op S), brel S 
:= λ S r b x y, r x (b x y). 

(* DELETE *) 
(* r' x y = true  <-> r y (b x y) *) 
Definition brel_from_bop_right : ∀ (S : Type) (r : brel S) (b : binary_op S), brel S 
:= λ S r b x y, r y (b x y). 

(* DELETE *) 
(* r' x y = true  <-> r x (b x y) *) 
Definition brel_bop_to_lte_left : ∀ S : Type, brel S → binary_op S → brel S 
:= λ S eq b x y, eq x (b x y). 

(* DELETE *) 
Definition brel_bop_to_lt_left : ∀ S : Type, brel S → binary_op S → brel S 
:= λ S eq b x y, (brel_bop_to_lte_left S eq b x y) && (negb (eq y (b x y))). 
 *)


(* NEW DEFS *) 


(* r' x y = true  <-> r x (b x y) *) 
Definition brel_llte : ∀ {S : Type}, brel S → binary_op S → brel S 
:= λ {S} eq b x y, eq x (b x y). 

Definition brel_llt : ∀ {S : Type}, brel S → binary_op S → brel S 
:= λ {S} eq b, brel_conjunction (brel_llte eq b) (brel_complement eq). 

(* r' x y = true  <-> r y (b x y) *) 
Definition brel_rlte : ∀ {S : Type}, brel S → binary_op S → brel S 
:= λ {S} eq b x y, eq y (b x y). 

Definition brel_rlt : ∀ {S : Type}, brel S → binary_op S → brel S 
:= λ {S} eq b, brel_conjunction (brel_rlte eq b) (brel_complement eq). 


Definition brel_and_sym : ∀ {S : Type}, brel S -> brel S 
:= λ {S} r x y,  (r x y) && (r y x). 

Definition brel_or_sym : ∀ {S : Type}, brel S -> brel S 
:= λ {S} r x y,  (r x y) || (r y x). 

Definition in_list : ∀ {S : Type},  brel S -> brel2 (list S) S
:= fix f {S} r l s := 
   match l with 
   | nil => false 
   | a :: rest => r s a || f r rest s
   end. 

Definition in_set : ∀ {S : Type},  brel S -> brel2 (finite_set S) S
:= fix f {S} r l s := 
   match l with 
   | nil => false 
   | a :: rest => r s a || f r rest s
   end. 

Definition brel_subset : ∀ {S : Type},  brel S -> brel (finite_set S)
:= fix f {S} r set1 set2 := 
   match set1 with 
   | nil => true 
   | a :: rest => (in_set r set2 a) && (f r rest set2)
   end. 

Definition brel_set : ∀ {S : Type}, brel S → brel(finite_set S) 
:= λ {S} r,  brel_and_sym (brel_subset r). 

Definition brel_reduce : ∀ {S : Type}, brel S → unary_op S → brel S
:= λ {S} r u x y,  r (u x) (u y). 


(* brel2 *) 


(* DELETE brel2_from_brel.v ... 

Definition brel2_from_brel : ∀ {S : Type}, (brel S) → brel2 S (finite_set S)
:= λ {S} r x, (bProp_lift_list S (r x)).


Definition is_minimal_in : ∀ {S : Type}, brel S → brel S → brel2 S (finite_set S)
:= λ {S} eq lt a X, if brel_set S eq nil X
                  then false 
                  else brel2_from_brel S (λ x, λ y, negb ((brel_strictify S lt) y x)) a X. 


Definition is_minimal_in : ∀ {S : Type}, brel S → brel S → brel2 (finite_set S) S 
:= λ {S} eq lte, brel2_conjunction (finite_set S) S 
                  (in_set S eq)
                  (brel2_lift_set_left S (brel_complement S (brel_strictify S lte))).                  

*) 