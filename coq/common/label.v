Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.theory.facts.

Require Import CAS.coq.common.brel_properties. 
Require Import CAS.coq.common.bop_properties. 
Require Import CAS.coq.common.tr_properties. 
Require Import CAS.coq.common.str_properties.

(* A_label : for "label types" *) 

Inductive ast_label : Type :=
   | Ast_label_unit        : ast_label  
   | Ast_label_bool        : ast_label
   | Ast_label_nat         : ast_label
   | Ast_label_list        : ast_label → ast_label
   | Ast_label_product     : ast_label * ast_label → ast_label
   | Ast_label_sum         : ast_label * ast_label → ast_label
   | Ast_label_functions   : ast_label  → ast_label                                                       
.

Record label {L : Type} := {
  label_witness : L         (* not empty *) 
; label_data    : L -> data (* for printing in ocaml-land *) 
; label_ast     : ast_label 
}.

Inductive unit_type : Type :=
  | Unit : unit_type.           

Definition label_unit : @label unit_type :=
{|
  label_witness := Unit
; label_data    := λ n, DATA_nat 0 (* fix me *) 
; label_ast     := Ast_label_unit 
|}.

Open Scope nat. 
Definition label_nat : @label nat :=
{|
  label_witness := 0
; label_data    := λ n, DATA_nat n 
; label_ast     := Ast_label_nat 
|}.

Close Scope nat. 

Definition label_bool : @label bool :=
{|
  label_witness := true
; label_data    := λ b, DATA_bool b 
; label_ast     := Ast_label_bool 
|}.


Definition label_product {L1 L2 : Type} (l1 : @label L1) (l2 : @label L2) : @label (L1 * L2) :=
{|
  label_witness := (label_witness l1, label_witness l2)
; label_data    := λ p, DATA_pair (label_data l1 (fst p), label_data l2 (snd p))
; label_ast     := Ast_label_product (label_ast l1, label_ast l2) 
|}.

Definition label_sum {L1 L2 : Type} (l1 : @label L1) (l2 : @label L2) : @label (L1 + L2) :=
{|
  label_witness := inl (label_witness l1)                                 
; label_data    := λ d, (match d with inl s => DATA_inl (label_data l1 s) | inr t => DATA_inr (label_data l2 t) end)
; label_ast     := Ast_label_sum (label_ast l1, label_ast l2)
                                 
|}.

Definition label_funtions {L S : Type} (l : @label L) (l2 : @label (L + (S -> L))) :=
{|
  label_witness := inr L (λ (s : S), inl (S -> L) (label_witness l))
; label_data    := λ d, (match d with inl s => DATA_inl (label_data l s) | inr t => DATA_inr (DATA_nat 0 (* fix me *)) end)
; label_ast     := Ast_label_functions (label_ast l) 
|}.


Definition policy {L S : Type} (ltr : L -> (S -> S)) (d : L + (S -> L)) (s : S) :=
  match d with
  | inl l => ltr l s 
  | inr f => ltr (f s)  s
  end .


Section Policy.

  Variable S : Type.
  Variable L : Type.   

  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.   
  Variable symS : brel_symmetric S eq. 
  Variable trnS : brel_transitive S eq.

  Variable wS : S.
  Variable newS : S -> S. 
  Variable ntS : brel_not_trivial S eq newS. 
  
  Variable add : binary_op S.
  Variable add_cong : bop_congruence S eq add. 
  
  Variable ltr : L -> (S -> S).
  
Lemma sltr_absorptive_policy : sltr_absorptive S L eq add ltr -> sltr_absorptive S (L + (S -> L)) eq add (policy ltr).
Proof. intros H l s. destruct l as [l | f]; simpl; apply H. Qed. 

Lemma sltr_distributive_policy_iff :
  ((sltr_distributive S L eq add ltr) *
   (∀ t u f, eq (ltr (f (add t u)) (add t u)) (add (ltr (f t) t) (ltr (f u) u)) = true)) <-> 
      sltr_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. split.
          intros [D P] [l | f] t u; compute.
             apply D.
             apply P. 
          intro D. split. 
             intros l t u. assert (A := D (inl l) t u). compute in A. exact A. 
             intros t u f. assert (A := D (inr f) t u). compute in A. exact A. 
Qed.

Lemma sltr_not_distributive_policy_v1 :
  sltr_not_distributive S L eq add ltr -> sltr_not_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. intros [[l [t u]] P]. exists (inl l, (t, u)). compute. exact P. Defined. 

Lemma sltr_not_distributive_policy_v2 :
  ({z : S * (S * (S -> L)) & match z with (t, (u, f)) => eq (ltr (f (add t u)) (add t u)) (add (ltr (f t) t) (ltr (f u) u)) = false end }) ->
  sltr_not_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. intros [[t [u f]] P]. exists (inr f, (t, u)). compute. exact P. Defined. 
   

Lemma policy_distributive_v1 :  
    ltr_is_right L S eq ltr -> sltr_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. intros irS [l | f] t u; compute.
       assert (J1 := irS l (add t u)).
       assert (J2 := irS l t).
       assert (J3 := irS l u).
       assert (J4 := add_cong _ _ _ _ J2 J3).  apply symS in J4.
       assert (J5 := trnS _ _ _ J1 J4).
       exact J5.
       assert (J1 := irS (f (add t u)) (add t u)).
       assert (J2 := irS (f t) t).
       assert (J3 := irS (f u) u).
       assert (J4 := add_cong _ _ _ _ J2 J3).  apply symS in J4.
       assert (J5 := trnS _ _ _ J1 J4).
       exact J5.
Qed. 

Lemma policy_distributive_v2 
      (lrS : ltr_right_constant L S eq ltr)
      (ldS : sltr_distributive S L eq add ltr) :
  sltr_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. unfold sltr_distributive. intros [l | f] t u; compute.
       apply ldS. 
       assert (J1 := ldS (f (add t u)) t u). 
       assert (J2 := lrS (f (add t u)) (f t) t).
       assert (J3 := lrS (f (add t u)) (f u) u).
       assert (J4 := add_cong _ _ _ _ J2 J3). 
       assert (J5 := trnS _ _ _ J1 J4).
       exact J5.
Qed.

Definition sltr_exists_id_label (S L : Type) (eq : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { l : L  & ∀ (s : S), bop_is_id S eq add (ltr l s)}. 

Definition sltr_not_exists_id_label (S L : Type) (eq : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ l : L,  { s : S & bop_not_is_id S eq add (ltr l s)}. 

Definition sltr_exists_id_label_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := (sltr_exists_id_label S L r add ltr) + (sltr_not_exists_id_label S L r add ltr).


(* need l |> zero = zero ? *) 

Definition sltr_exists_nontrivial_label (S L : Type) (eq : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ s : S,  (bop_is_id S eq add s) + ((bop_not_is_id S eq add s) * { l : L & bop_not_is_id S eq add (ltr l s)}). 

Lemma policy_not_distributive_new 
      (idl : sltr_exists_id_label S L eq add ltr)
      (enl : sltr_exists_nontrivial_label S L eq add ltr) :
  sltr_not_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. destruct idl as [l Q].
       assert (P := Q wS). 
       destruct (ntS (ltr l wS)) as [H1 H2].
       destruct (enl (newS (ltr l wS))) as [J | [K1 [l' K2]]].
          assert (M := bop_is_id_equal S eq symS trnS add _ _ P J). rewrite H1 in M. discriminate M.
          exists (inr (λ x, if eq x wS then l else l'), (wS, newS (ltr l wS))).
          compute.
          destruct (P (newS (ltr l wS))) as [I1 I2]. rewrite refS. 
          case_eq(eq (add wS (newS (ltr l wS))) wS); intro H3;
          case_eq(eq (newS (ltr l wS)) wS); intro H4; auto. 
Admitted.


(* IR(ltr) + (RC(ltr) * D(add, ltr)) -> D 

Lemma policy_not_distributive_v2 (S L : Type)
      (s : S)              
      (eq : brel S)
      (add : binary_op S)
      (idem : bop_idempotent S eq add) 
      (ltr : L -> (S -> S))
      (dS  : sltr_distributive S L eq add ltr) 
      (nir : ltr_not_is_right L S eq ltr)
      (nrc : ltr_not_right_constant L S eq ltr) :
  sltr_not_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. destruct nir as [[l1 s1] Q].
       destruct nrc as [[l2 [l3 s2]] P]. 
       exists (let a := s1 in
               let b := s2 in
               let c := ltr l1 s1 in
               let d := ltr l2 s2 in
               let e := ltr l2 s2 in                              
               if eq a (add a b) 
               then 
               else if eq b (add a b) 
                    then
                    else 
       compute.
       apply P. 
Defined. 
*) 


(*
  want f, a, b such that 

  ltr (f (add a b)) (add a b) <> add (ltr (f a) a) (ltr (f b) b)
  
  know (ltr l1 s1) <> s1 
       (ltr l2 s2) <> (ltr l3 s2) 

  assume add is idempotent 
  add, ltr dist. 

  ltr (f (add s1 s2)) (add s1 s2) = add (ltr (f (add s1 s2)) s1) (ltr (f (add s1 s2)) s2)
                                 <> add (ltr (f      s1)     s1) (ltr (f          s2) s2)

 if s1 = s2 
 then if s1 = (ltr l2 s2)
      then if (ltr l1 s1) = (ltr l3 s2)
           then 
           else 
      else 
 else 



  let a = s 
      b = (ltr l s)

  if a = add a b 
  then λ x, if x = a then l else id 
  else if b = add a b 
       then λ x, if x = b then id else l 
       else λ x, id  
*) 
Lemma test3 (S L : Type)
            (eq : brel S)
            (add : binary_op S) (ltr : L -> (S -> S))
            (refS : brel_reflexive S eq) 
            (symS : brel_symmetric S eq) :   
            (ltr_not_is_right L S eq ltr) -> 
            (sltr_exists_id_label S L eq add ltr) -> 
  sltr_not_distributive S (L + (S -> L)) eq add (policy ltr).
Proof. unfold sltr_not_distributive. intros [[l s] P] [id idP]. 
       exists (if eq s (add s (ltr l s))
               then (inr (λ x, if eq x s then l else id), (s, ltr l s))
               else if eq (ltr l s) (add s (ltr l s))
                    then (inr (λ x, if eq x (ltr l s) then id else l), (s, ltr l s))
                    else (inr (λ z, id), (s, ltr l s))). 
       case_eq(eq s (add s (ltr l s))); intro H1.
          compute. rewrite P. rewrite refS. apply symS in H1. rewrite H1.
          admit.
          case_eq(eq (ltr l s) (add s (ltr l s))); intro H2.
          compute. rewrite refS. apply symS in H2. rewrite H2.
          case_eq(eq s (ltr l s)); intro H3.
          admit.
          admit.
          compute. 
Admitted. 

End Policy. 