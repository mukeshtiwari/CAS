Require Export Coq.Unicode.Utf8.
Require Import Coq.Strings.String. 
Require Import Coq.Bool.Bool.    (* eqb *) 
Require Coq.Arith.EqNat.         (* beq_nat *) 
Require Import Coq.Arith.Arith.

Section BasicTypes.
  
Close Scope nat_scope. 
Record cas_constant :=
{
  constant_ascii : string
; constant_latex : string                      
}.

Definition make_constant (s1 s2: string) := {| constant_ascii := s1; constant_latex := s2 |}. 
Definition with_constant (S : Type)     := cas_constant + S.  
Definition brel (S : Type)              := S → S → bool.  
Definition brel2 (S T : Type)           := S → T → bool.
Definition bProp (S : Type)             := S → bool. (* replace with pred *) 
Definition pred (S : Type)              := S → bool. 
Definition unary_op (S : Type)          := S → S. 
Definition binary_op (S : Type)         := S → S → S.  
Definition ltr_type (L S : Type)  := L → S → S.  
Definition rtr_type (L S : Type) := S → L → S. 
Definition finite_set (S : Type)        := list S.     (* improve someday ... *) 

End BasicTypes.


Section BooleanPredicates.

Definition bProp_forall : forall (S : Type),  bProp S → bProp(finite_set S) := List.forallb. 

End BooleanPredicates.

Section BooleanRelations. 

(* Notes on eqiv relation    a ~ b  over S 
   refl, sym, trans 
   <a> = rep 
   <a> ~ a 
*) 

Open Scope list_scope.
Open Scope string_scope. 

(* INFINITY ! *) 
Definition infinity : cas_constant := {| constant_ascii := "INFINITY"; constant_latex := "\infty" |}. 
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



(* This is forallb from List.v.  Define it here 
   rather than in List.v so as not to pull in that file in extraction. 
 *)

Definition bProp_lift_list : ∀ {A : Type}, (bProp A) -> bProp (list A) 
:= fix f {A} p l := 
      match l with
	| nil     => true
	| a::rest => p a && f p rest
      end.

(*
Definition dominates_set : ∀ {S : Type}, brel S → brel S → brel2 (finite_set S) S 
:= λ {S} eq lte X a, bProp_lift_list  (λ x, brel_complement (brel_strictify lte) x a) X.                 
*) 
(* was called bProp_forall    proofs in bprop_forall.v 

Definition bProp_lift_set : ∀ {A : Type}, (bProp A) -> bProp (finite_set A) 
:= bProp_lift_list. 
*)

Definition bProp_from_brel_left : ∀ {S : Type}, brel S -> S -> bProp S
:= λ {S} r a x, r x a.  

Definition bProp_from_brel_right : ∀ {S : Type}, brel S -> S -> bProp S
:= λ {S} r a x, r a x.  


Definition brel2_product : ∀ {S T U V : Type}, brel2 S U → brel2 T V → brel2 (S * T) (U * V)
:= λ {S} {T} {U} {V} r q x y, 
   match x, y with
   | (x1, x2), (y1, y2) => andb (r x1 y1) (q x2 y2) 
   end.




Definition brel_add_top : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} rS c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => false 
   | (inr _), (inl _) => true  (* new top ! *) 
   | (inr a), (inr b) => rS a b 
   end.



(* NEW DEFS *)

Definition brel_and_sym : ∀ {S : Type}, brel S -> brel S 
:= λ {S} r x y,  (r x y) && (r y x). 

Definition brel_or_sym : ∀ {S : Type}, brel S -> brel S 
:= λ {S} r x y,  (r x y) || (r y x). 


Definition brel_reduce : ∀ {S : Type}, brel S → unary_op S → brel S
:= λ {S} r u x y,  r (u x) (u y). 


(* brel2 *) 



End BooleanRelations.


Section UnaryOperators.

Open Scope list_scope. 

Definition uop_not : unary_op bool := λ b, if b then false else true.  

Definition uop_id : ∀ {S : Type}, (unary_op S) := λ {S} s, s.  


Definition uop_with_constant : ∀ {S : Type}, unary_op S → unary_op (with_constant S)
:= λ {S} g x ,  
      match x with
         | (inl _) => x 
         | (inr s) => inr _ (g s) 
      end.

Definition uop_list_map : ∀ {S : Type}, unary_op S → unary_op (list S) 
:= λ {S} f,  
  fix map (l : list S) : list S :=
  match l with
  | nil => nil
  | a :: t => f a :: map t
  end. 

Definition uop_product : ∀ {S T : Type}, unary_op S → unary_op T → unary_op (S * T) 
:= λ {S} {T} f g p,  
   match p with
    | (s, t) => (f s, g t) 
   end.

Definition uop_sum : ∀ {S T : Type}, unary_op S → unary_op T → unary_op (S + T)
:= λ {S} {T} f g x ,  
      match x with
         | (inl s) => inl _ (f s)
         | (inr t) => inr _ (g t) 
      end.


(* copied here from Coq.Lists.List.v    
   so that extraction does not construct a 
   List module (which conflicts with Ocaml's 
*) 
Fixpoint filter {A : Type} (f : A -> bool) (l:list A) : list A :=
      match l with
	| nil => nil
	| x :: l => if f x then x::(filter f l) else filter f l
      end.

Definition uop_filter : ∀ {S : Type}, (bProp S) → unary_op (finite_set S) := λ {S}, @filter S. 

Definition uop_filter_from_brel2 : ∀ {S : Type}, (brel2 S (finite_set S)) → unary_op (finite_set S)
:= λ {S} r X, uop_filter (λ a, r a X) X.

(*
Definition uop_minset :  ∀ S : Type, brel S -> brel S -> unary_op (finite_set S) 
:= λ S rS lte, uop_filter_from_brel2 S (λ a X, dominates_set S rS lte X a).
*) 
  

End UnaryOperators.   


Section BinaryOperators.

Open Scope list_scope.

(* BASE *) 



Definition bop_plus   : binary_op nat := plus.
Definition bop_times  : binary_op nat := mult.
Definition bop_min    : binary_op nat := min.
Definition bop_max    : binary_op nat := max.
Definition bop_left   : ∀ {S : Type}, binary_op S := λ {S} l r,  l.
Definition bop_right  : ∀ {S : Type}, binary_op S := λ {S} l r,  r. 
Definition bop_concat : ∀ {S : Type}, binary_op (list S) := λ {S} x y,  x ++ y. 


(* Combinators *) 

Definition bop_then_unary : ∀ {S : Type} (u : unary_op S) (b : binary_op S), binary_op S 
:= λ {S} u b x y,  u (b x y). 

(*
Definition bop_reduce : ∀ {S : Type} (u : unary_op S) (b : binary_op S), binary_op S 
  := λ {S} u b x y,  u (b (u x) (u y)).
*) 

Definition bop_reduce {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  r (b x y).

Definition bop_reduce_args {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  b (r x) (r y).   

Definition bop_full_reduce {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  r(b (r x) (r y)).   



Definition ltran_list_product : ∀ {S : Type} (bs : binary_op S), ltr_type S (list S) 
:= fix f {S} bs a y := 
      match y with
         | nil => nil 
         | b :: rest => (bs a b ) :: (f bs a rest)
      end.

Definition rtran_list_product : ∀ {S : Type} (bS : binary_op S), rtr_type S (list S) 
:= fix f {S} bS Y a := 
      match Y with
         | nil => nil 
         | b :: rest => (bS b a) :: (f bS rest a)
      end.

Definition bop_list_product_left : ∀ {S : Type} (bs : binary_op S), binary_op(list S) 
:= fix f {S} bs x y := 
      match x with
         | nil => nil 
         | a :: rest => (ltran_list_product bs a y) ++ (f bs rest y) 
      end.

Definition bop_list_product_right : ∀ {S : Type} (bs : binary_op S), binary_op(list S) 
:= fix f {S} bs x y := 
      match x with
         | nil => nil 
         | a :: rest =>  (rtran_list_product bs y a) ++ (f bs rest y)
      end.


End BinaryOperators.


Section CombinedOperators.

(* Sets 

Currently implemented as lists

*) 

Open Scope list_scope.

Definition is_empty : ∀ {S : Type}, bProp (finite_set S) 
:= λ {S} X,  match X with nil => true | _ => false end. 

Definition singleton : ∀ {S : Type}, S → finite_set S 
:= λ {S} s, s :: nil. 



End CombinedOperators.


Section CEF.


(*
** CEF = Counter Example Function 
** WIF = WItness Function ? 
*) 

Definition cef_idempotent_implies_not_anti_left {S : Type} (s : S) := (s, s). 

Definition cef_idempotent_implies_not_anti_right {S : Type} (s : S) := (s, s). 

Definition cef_commutative_implies_not_is_left {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) 
   := if (r (b (f s) s) s) then (f s, s) else (s, f s). 

Definition cef_commutative_implies_not_is_right {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) 
   := if (r (b (f s) s) s) then (s, f s) else (f s, s). 


Definition cef_selective_and_commutative_imply_not_left_cancellative {S : Type} 
          (r : brel S) (b : binary_op S) (s : S) (f : S -> S) 
   := if (r (b s (f s)) s) then (s, (s, f s)) else (f s, (f s, s)). 

(* same as above ? *) 
Definition cef_selective_and_commutative_imply_not_right_cancellative {S : Type} 
          (r : brel S) (b : binary_op S) (s : S) (f : S -> S) 
   := if (r (b s (f s)) s) then (s, (s, f s)) else (f s, (f s, s)). 

Definition cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative {S : Type} 
          (b : binary_op S) (s1 s2 : S) 
   := (b s1 s2, (s1, s2)). 

(* correct ? *) 
Definition cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative {S : Type} 
          (b : binary_op S) (s1 s2 : S) 
   := (b s1 s2, (s1, s2)). 


Definition cef_not_idempotent_implies_not_selective {S : Type} (s : S) 
   := (s, s). 

Definition cef_left_cancellative_implies_not_left_constant {S : Type} (s : S) (f : S -> S) 
   := (s, (s, f s)). 

Definition cef_right_cancellative_implies_not_right_constant {S : Type} (s : S) (f : S -> S) 
   := (s, (s, f s)). 


Definition cef_cancellative_and_exists_id_imply_not_idempotent {S : Type} (r : brel S) (s i : S) (f : S -> S)
   := if r s i then (f s) else s.

Definition cef_idempotent_and_commutative_imply_not_left_constant {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) 
   := if (r (b (f s) s) s) then (f s, (s, f s)) else (s, (f s, s)). 

Definition cef_idempotent_and_commutative_imply_not_right_constant {S : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) 
   := if (r (b (f s) s) s) then (f s, (s, f s)) else (s, (f s, s)). 



End CEF.   
