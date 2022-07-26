Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties. 


Section ACAS. 



Close Scope nat. 
(* Interaction of multiple binary ops *)


(* if this decidable property is added to bs, then we can get an iff rule for 
    (plus, times) ->(left_order plus, times) and olt_left_monotone. 
    First, try pushing bop_left_monotone through all bs combinators ... 
*) 
Definition bop_left_monotone (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := ∀ s t u : S, r t (add t u) = true -> r (mul s t) (add (mul s t) (mul s u)) = true. 

Definition bop_not_left_monotone (S : Type) (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r t (add t u) = true) * (r (mul s t) (add (mul s t) (mul s u)) = false) end }.


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

(*  id-ann pairs 

   b1 id        b2 ann 
   ----------------------
1) not exists   not exists 
2)     exists   not exists 
3) not exists       exists         
4)     exists       exists   equal
5)     exists       exists   not equal

*)   



Definition bops_exists_id_ann_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
  := { i : S & (bop_is_id S r b1 i) * (bop_is_ann S r b2 i)}.

Definition bops_exists_id_ann_not_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
  := { z : S * S & match z with (i, a) => (bop_is_id S r b1 i) * (bop_is_ann S r b2 a) * (r i a = false) end}.

Definition extract_exist_id_from_exists_id_ann_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : bops_exists_id_ann_equal S r b1 b2) : bop_exists_id S r b1 := 
  existT (λ x : S, bop_is_id S r b1 x) (projT1 P) (fst (projT2 P)).

Definition extract_exist_ann_from_exists_id_ann_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : bops_exists_id_ann_equal S r b1 b2) : bop_exists_ann S r b2 := 
  existT (λ x : S, bop_is_ann S r b2 x) (projT1 P) (snd (projT2 P)).


Definition extract_exist_id_from_exists_id_ann_not_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : bops_exists_id_ann_not_equal S r b1 b2) : bop_exists_id S r b1 :=
  match P with
  existT _ (i, a) p =>     
     existT (λ x : S, bop_is_id S r b1 x) i (fst (fst p))
  end. 

Definition extract_exist_ann_from_exists_id_ann_not_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : bops_exists_id_ann_not_equal S r b1 b2) : bop_exists_ann S r b2 := 
  match P with
  existT _ (i, a) p =>     
     existT (λ x : S, bop_is_ann S r b2 x) a (snd (fst p))
  end. 

Inductive exists_id_ann_decidable (S : Type) (eq : brel S) (b1 : binary_op S) (b2 : binary_op S)  : Type :=
| Id_Ann_Proof_None      : (bop_not_exists_id S eq b1) * (bop_not_exists_ann S eq b2) -> exists_id_ann_decidable S eq b1 b2
| Id_Ann_Proof_Id_None   : (bop_exists_id S eq b1) * (bop_not_exists_ann S eq b2)     -> exists_id_ann_decidable S eq b1 b2
| Id_Ann_Proof_None_Ann  : (bop_not_exists_id S eq b1) * (bop_exists_ann S eq b2)     -> exists_id_ann_decidable S eq b1 b2
| Id_Ann_Proof_Equal     : bops_exists_id_ann_equal S eq b1 b2                        -> exists_id_ann_decidable S eq b1 b2
| Id_Ann_Proof_Not_Equal : bops_exists_id_ann_not_equal S eq b1 b2                    -> exists_id_ann_decidable S eq b1 b2. 

Definition extract_exists_id_decidable_from_exists_id_ann_decidable
           (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : exists_id_ann_decidable S r b1 b2) : bop_exists_id_decidable S r b1 :=
match P with
| Id_Ann_Proof_None _ _ _ _ (no_id, _)          => inr no_id 
| Id_Ann_Proof_Id_None  _ _ _ _ (exists_id, _ ) => inl exists_id 
| Id_Ann_Proof_None_Ann _ _ _ _ (no_id, _)      => inr no_id 
| Id_Ann_Proof_Equal _ _ _ _ id_ann_eq          => inl (extract_exist_id_from_exists_id_ann_equal S r b1 b2 id_ann_eq) 
| Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_eq  => inl (extract_exist_id_from_exists_id_ann_not_equal S r b1 b2 id_ann_not_eq) 
end.

Definition extract_exists_ann_decidable_from_exists_id_ann_decidable
           (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : exists_id_ann_decidable S r b1 b2) : bop_exists_ann_decidable S r b2 :=
match P with
| Id_Ann_Proof_None _ _ _ _ (_, no_ann)         => inr no_ann
| Id_Ann_Proof_Id_None  _ _ _ _ (_, no_ann)     => inr no_ann
| Id_Ann_Proof_None_Ann _ _ _ _ (_, exists_ann) => inl exists_ann
| Id_Ann_Proof_Equal _ _ _ _ id_ann_eq          => inl (extract_exist_ann_from_exists_id_ann_equal S r b1 b2 id_ann_eq) 
| Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_eq  => inl (extract_exist_ann_from_exists_id_ann_not_equal S r b1 b2 id_ann_not_eq) 
end.



(* Absorptivity *) 

Definition bops_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_not_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 s t)) = false end }. 

Definition bops_left_left_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_left_left_absorptive S r b1 b2) + (bops_not_left_left_absorptive S r b1 b2). 

Definition bops_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_not_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S)
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 t s)) = false end }. 

Definition bops_left_right_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_left_right_absorptive S r b1 b2) + (bops_not_left_right_absorptive S r b1 b2). 

Definition bops_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
  ∀ (s t : S), r s (b1 (b2 s t) s) = true.



(* Strict-Absorptivity 
   Let's assume b1 is commutative, so only two properties instead of four. 
*)


Definition bops_left_strictly_absorptive 
  (S : Type) (eq : brel S) (b₁ b₂ : binary_op S) := 
  ∀ (s t : S), 
  (eq s (b₁ s (b₂ s t)) = true) *
  (eq (b₂ s t) (b₁ s (b₂ s t)) = false).


Definition bops_not_left_strictly_absorptive 
  (S : Type) (eq : brel S) (b₁ b₂ : binary_op S) := 
  {z : S * S & 
    match z with 
    | (s, t) => 
        (eq s (b₁ s (b₂ s t)) = false) + 
        (eq (b₂ s t) (b₁ s (b₂ s t)) = true)
    end
  }.

Definition bops_left_strictly_absorptive_decidable 
  (S : Type) (eq : brel S) (b₁ b₂ : binary_op S) :=
  (bops_left_strictly_absorptive S eq b₁ b₂) + 
  (bops_not_left_strictly_absorptive S eq b₁ b₂).


Definition bops_right_strictly_absorptive 
  (S : Type) (eq : brel S) (b₁ b₂ : binary_op S) := 
  ∀ (s t : S), 
  (eq s (b₁ s (b₂ t s)) = true) *
  (eq (b₂ t s) (b₁ s (b₂ t s)) = false).

Definition bops_not_right_strictly_absorptive 
  (S : Type) (eq : brel S) (b₁ b₂ : binary_op S) := 
  {z : S * S & 
    match z with 
    | (s, t) => 
        (eq s (b₁ s (b₂ t s)) = false) + 
        (eq (b₂ t s) (b₁ s (b₂ t s)) = true)
    end
  }.


Definition bops_right_strictly_absorptive_decidable 
  (S : Type) (eq : brel S) (b₁ b₂ : binary_op S) :=
  (bops_right_strictly_absorptive S eq b₁ b₂) + 
  (bops_not_right_strictly_absorptive S eq b₁ b₂).

(* Experimental. *)
Definition bops_left_strictly_absorptive_absurd (S : Type) 
   (eq : brel S) (b1 b2 : binary_op S) :=
   bops_left_strictly_absorptive S eq b1 b2 -> False.

(* Experimental *)
Definition bops_right_strictly_absorptive_absurd (S : Type) 
   (eq : brel S) (b1 b2 : binary_op S) :=
   bops_right_strictly_absorptive S eq b1 b2 -> False.


(*** introduced for st/left/from_bs.v 

Definition bops_strictly_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), (r s (b1 s (b2 t s)) = true) * (r (b2 t s) (b1 s (b2 t s)) = false). 

Definition bops_not_strictly_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S)
   := { z : S * S & match z with (s, t) => (r s (b1 s (b2 t s)) = false) + (r (b2 t s) (b1 s (b2 t s)) = true) end }. 

Definition bops_left_right_strictly_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_strictly_left_right_absorptive S r b1 b2) + (bops_not_strictly_left_right_absorptive S r b1 b2). 

*)
(***)

Definition bops_not_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) =>  r s (b1 (b2 s t) s) = false end }. 

Definition bops_right_left_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_right_left_absorptive S r b1 b2) + (bops_not_right_left_absorptive S r b1 b2). 

Definition bops_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.

Definition bops_not_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) =>  r s (b1 (b2 t s) s) = false end }. 

Definition bops_right_right_absorptive_decidable  (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    (bops_right_right_absorptive S r b1 b2) + (bops_not_right_right_absorptive S r b1 b2). 

(* *)


End ACAS. 

Section CAS.


Inductive assert_left_distributive {S : Type} := 
| Assert_Left_Distributive : @assert_left_distributive S. 

Inductive check_left_distributive {S : Type} := 
| Certify_Left_Distributive : @check_left_distributive S
| Certify_Not_Left_Distributive : (S * (S * S)) → @check_left_distributive S.

Inductive check_left_distributive_dual {S : Type} := 
| Certify_Left_Distributive_Dual : @check_left_distributive_dual S
| Certify_Not_Left_Distributive_Dual : (S * (S * S)) → @check_left_distributive_dual S. 

Inductive assert_right_distributive {S : Type} := 
| Assert_Right_Distributive : @assert_right_distributive S. 

Inductive check_right_distributive {S : Type} := 
| Certify_Right_Distributive : @check_right_distributive S
| Certify_Not_Right_Distributive : (S * (S * S)) → @check_right_distributive S.


Inductive assert_exists_id_ann_equal {S : Type} := 
| Assert_Exists_Id_Ann_Equal : S → @assert_exists_id_ann_equal S. 

Inductive assert_exists_id_ann_not_equal {S : Type} := 
| Assert_Exists_Id_Ann_Not_Equal : (S * S) → @assert_exists_id_ann_not_equal S.

Inductive exists_id_ann_certificate {S : Type} : Type :=
| Id_Ann_Cert_None      : @exists_id_ann_certificate S
| Id_Ann_Cert_Id_None   : S -> @exists_id_ann_certificate S
| Id_Ann_Cert_None_Ann  : S -> @exists_id_ann_certificate S
| Id_Ann_Cert_Equal     : S -> @exists_id_ann_certificate S
| Id_Ann_Cert_Not_Equal : (S * S) -> @exists_id_ann_certificate S.

(*
Definition assert_exist_id_from_exists_id_ann_equal {S : Type} 
           (P : @assert_exists_id_ann_equal S) : @assert_exists_id S:=
  match P with
  | Assert_Exists_Id_Ann_Equal id => Assert_Exists_Id id 
  end. 

Definition assert_exist_ann_from_exists_id_ann_equal {S : Type} 
           (P : @assert_exists_id_ann_equal S) : @assert_exists_ann S := 
  match P with
  | Assert_Exists_Id_Ann_Equal id => Assert_Exists_Ann id 
  end. 

Definition assert_exist_id_from_exists_id_ann_not_equal {S : Type} 
           (P : @assert_exists_id_ann_not_equal S) : @assert_exists_id S :=
  match P with
  | Assert_Exists_Id_Ann_Not_Equal (id, _) => Assert_Exists_Id id 
  end. 

Definition assert_exist_ann_from_exists_id_ann_not_equal {S : Type}
           (P : @assert_exists_id_ann_not_equal S) : @assert_exists_ann S :=           
  match P with
  | Assert_Exists_Id_Ann_Not_Equal (_,ann) => Assert_Exists_Ann ann
  end. 
 *)


Definition extract_exists_id_certifiable_from_exists_id_ann_certifiable
           {S : Type} (P : @exists_id_ann_certificate S ) : @check_exists_id S  :=
match P with
| Id_Ann_Cert_None               => Certify_Not_Exists_Id 
| Id_Ann_Cert_Id_None id         => Certify_Exists_Id id
| Id_Ann_Cert_None_Ann ann       => Certify_Not_Exists_Id 
| Id_Ann_Cert_Equal id_ann       => Certify_Exists_Id id_ann
| Id_Ann_Cert_Not_Equal (id,ann) => Certify_Exists_Id id
end.

Definition extract_exists_ann_certifiable_from_exists_id_ann_certifiable
           {S : Type} (P : @exists_id_ann_certificate S ) : @check_exists_ann S  :=
match P with
| Id_Ann_Cert_None               => Certify_Not_Exists_Ann 
| Id_Ann_Cert_Id_None id         => Certify_Not_Exists_Ann 
| Id_Ann_Cert_None_Ann ann       => Certify_Exists_Ann ann 
| Id_Ann_Cert_Equal id_ann       => Certify_Exists_Ann id_ann
| Id_Ann_Cert_Not_Equal (id,ann) => Certify_Exists_Ann ann 
end.

Inductive assert_left_left_absorptive {S : Type} := 
| Assert_Left_Left_Absorptive : @assert_left_left_absorptive S.

Inductive assert_left_left_absorptive_dual {S : Type} := 
| Assert_Left_Left_Absorptive_Dual : @assert_left_left_absorptive_dual S. 


Inductive check_left_left_absorptive {S : Type} := 
| Certify_Left_Left_Absorptive : @check_left_left_absorptive S
| Certify_Not_Left_Left_Absorptive : (S * S) → @check_left_left_absorptive S.


Inductive assert_left_right_absorptive {S : Type} := 
| Assert_Left_Right_Absorptive : @assert_left_right_absorptive S. 

Inductive check_left_right_absorptive {S : Type} := 
| Certify_Left_Right_Absorptive : @check_left_right_absorptive S
| Certify_Not_Left_Right_Absorptive : (S * S) → @check_left_right_absorptive S.


Inductive assert_right_left_absorptive {S : Type} := 
| Assert_Right_Left_Absorptive : @assert_right_left_absorptive S. 

Inductive check_right_left_absorptive {S : Type} := 
| Certify_Right_Left_Absorptive : @check_right_left_absorptive S
| Certify_Not_Right_Left_Absorptive : (S * S) → @check_right_left_absorptive S.


Inductive assert_right_right_absorptive {S : Type} := 
| Assert_Right_Right_Absorptive : @assert_right_right_absorptive S. 

Inductive check_right_right_absorptive {S : Type} := 
| Certify_Right_Right_Absorptive : @check_right_right_absorptive S
| Certify_Not_Right_Right_Absorptive : (S * S) → @check_right_right_absorptive S.

End CAS.

Section Translation.

Definition p2c_left_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_left_absorptive_decidable S r b1 b2 -> @check_left_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Left_Absorptive 
   | inr p => Certify_Not_Left_Left_Absorptive (projT1 p)                                             
   end. 


Definition p2c_left_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_left_right_absorptive_decidable S r b1 b2 -> @check_left_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Right_Absorptive
   | inr p => Certify_Not_Left_Right_Absorptive (projT1 p)
   end. 


Definition p2c_right_left_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_left_absorptive_decidable S r b1 b2 -> @check_right_left_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Left_Absorptive
   | inr p => Certify_Not_Right_Left_Absorptive (projT1 p)
   end. 


Definition p2c_right_right_absorptive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bops_right_right_absorptive_decidable S r b1 b2 -> @check_right_right_absorptive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Right_Absorptive 
   | inr p => Certify_Not_Right_Right_Absorptive (projT1 p)
   end. 

Definition p2c_left_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b1 b2 -> @check_left_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive 
   | inr p => Certify_Not_Left_Distributive (projT1 p) 
   end. 

Definition p2c_right_distributive : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_right_distributive_decidable S r b1 b2 -> @check_right_distributive S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Right_Distributive
   | inr p => Certify_Not_Right_Distributive (projT1 p)
   end. 

Definition p2c_left_distributive_dual : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S), 
       bop_left_distributive_decidable S r b2 b1 -> @check_left_distributive_dual S 
:= λ S eq b1 b2 d, 
   match d with 
   | inl _ => Certify_Left_Distributive_Dual 
   | inr p => Certify_Not_Left_Distributive_Dual (projT1 p) 
   end. 



Definition p2c_exists_id_ann_equal
           (S : Type) (r : brel S) (b1 b2 : binary_op S) (P : bops_exists_id_ann_equal S r b1 b2) : 
             @assert_exists_id_ann_equal S 
:= Assert_Exists_Id_Ann_Equal (projT1 P).

Definition p2c_exists_id_ann_not_equal
           (S : Type) (r : brel S) (b1 b2 : binary_op S) (P : bops_exists_id_ann_not_equal S r b1 b2) : 
             @assert_exists_id_ann_not_equal S 
:= Assert_Exists_Id_Ann_Not_Equal (projT1 P).

Definition p2c_exists_id_ann
           (S : Type) (eq : brel S) (b1 : binary_op S) (b2 : binary_op S) (P : exists_id_ann_decidable S eq b1 b2) :
             @exists_id_ann_certificate S
:= match P with 
| Id_Ann_Proof_None _ _ _ _ (_, _)     => Id_Ann_Cert_None
| Id_Ann_Proof_Id_None _ _ _ _ (Q, _)  => Id_Ann_Cert_Id_None (projT1 Q)
| Id_Ann_Proof_None_Ann _ _ _ _ (_, Q) => Id_Ann_Cert_None_Ann (projT1 Q)
| Id_Ann_Proof_Equal _ _ _ _ Q         => Id_Ann_Cert_Equal (projT1 Q)
| Id_Ann_Proof_Not_Equal _ _ _ _ Q     => Id_Ann_Cert_Not_Equal (projT1 Q)
end. 

End Translation.

Section Verify.


Lemma correct_extract_exists_id_certifiable_from_exists_id_ann_certifiable
        (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
        (P : exists_id_ann_decidable S r b1 b2) : 
    p2c_exists_id_check _ _ _ (extract_exists_id_decidable_from_exists_id_ann_decidable S r b1 b2 P)
    = 
    extract_exists_id_certifiable_from_exists_id_ann_certifiable (p2c_exists_id_ann _ _ _ _ P). 
Proof. unfold p2c_exists_id_check, p2c_exists_id_ann.
       unfold extract_exists_id_certifiable_from_exists_id_ann_certifiable, 
              extract_exists_id_decidable_from_exists_id_ann_decidable. 
       destruct P; simpl.
       destruct p as [A B]; reflexivity. 
       destruct p as [[id A] B]; reflexivity. 
       destruct p as [A [ann B]]; reflexivity. 
       reflexivity. 
       destruct b as [[id ann] B]. compute. reflexivity. 
Qed.


Lemma correct_extract_exists_ann_certifiable_from_exists_id_ann_certifiable
        (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
        (P : exists_id_ann_decidable S r b1 b2) : 
    p2c_exists_ann_check _ _ _ (extract_exists_ann_decidable_from_exists_id_ann_decidable S r b1 b2 P)
    = 
    extract_exists_ann_certifiable_from_exists_id_ann_certifiable (p2c_exists_id_ann _ _ _ _ P). 
Proof. unfold p2c_exists_ann_check, p2c_exists_id_ann.
       unfold extract_exists_ann_certifiable_from_exists_id_ann_certifiable, 
              extract_exists_ann_decidable_from_exists_id_ann_decidable. 
       destruct P; simpl.
       destruct p as [A B]; reflexivity. 
       destruct p as [[id A] B]; reflexivity. 
       destruct p as [A [ann B]]; reflexivity. 
       reflexivity. 
       destruct b as [[id ann] B]. compute. reflexivity. 
Qed.


End Verify.   
