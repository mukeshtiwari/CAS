Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.min. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.max_min.
Require Import CAS.coq.bs.left. 
Require Import CAS.coq.bs.llex_product.
Require Import CAS.coq.bs.add_one. 
Require Import CAS.coq.bs.add_zero.
Require Import CAS.coq.bs.cast_up. 

Open Scope nat. 

Definition infinity :=
{|
  constant_ascii := "INF"
; constant_latex := "\\infty"
|}.

Check infinity.
(*
   infinity : cas_constant
*) 

(* shortest paths algebra 
   A_min_plus is a "base algebra" (int, min, +, _, 0), 
   that is, it has no additive (min) identity. 
*) 
Check A_min_plus. 
(*
   A_min_plus : A_selective_cancellative_pre_dioid_with_one nat

   The base algebrea is a selective, cancellative, pre-dioid with a one. 

   Let's convert it to a (C)ommutative and (S)elective bi-semigroup (A_bs_CS). 
 *)
Check A_bs_CS_from_selective_cancellative_pre_dioid_with_one. 
(*
   A_bs_CS_from_selective_cancellative_pre_dioid_with_one
        : ∀ S : Type, A_selective_cancellative_pre_dioid_with_one S → A_bs_CS S

*) 
Definition A_bs_CS_min_plus := A_bs_CS_from_selective_cancellative_pre_dioid_with_one nat A_min_plus.

Check A_bs_CS_min_plus.
(*
   A_bs_CS_min_plus : A_bs_CS nat

   Now, let's add a zero 
*) 
Check A_bs_CS_add_zero.
(* 
   A_bs_CS_add_zero : ∀ S : Type, A_bs_CS S → cas_constant → A_bs_CS (with_constant S)
*) 

Definition A_shortest_paths := A_bs_CS_add_zero nat A_bs_CS_min_plus infinity.

Check A_shortest_paths.
(*
   A_shortest_paths : A_bs_CS (with_constant nat)
*) 

(* Let's inspect this algebra 

   First, what are the fields in a A_bs_CS record?
*)
Print A_bs_CS.
(*
Record A_bs_CS (S : Type) : Type := Build_A_bs_CS
  { A_bs_CS_eqv           : structures.A_eqv S;
    A_bs_CS_plus          : binary_op S;
    A_bs_CS_times         : binary_op S;
    A_bs_CS_plus_proofs   : sg_CS_proofs S (structures.A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus;
    A_bs_CS_times_proofs  : msg_proofs S (structures.A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times;
    A_bs_CS_id_ann_proofs : id_ann_proofs S (structures.A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times;
    A_bs_CS_proofs        : bs_proofs S (structures.A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times;
    A_bs_CS_ast           : ast.cas_ast }


Let's look at what's in the records for msg_proofs and id_ann_proofs. 
Note : msg stands for multiplicative semigroup. 
We do not keep track of idempotence/selectivity for such semigroups. 
 *)
Print msg_proofs. 
(*
Record msg_proofs (S : Type) (eq : brel S) (bop : binary_op S) : Type
  := Build_msg_proofs
  { A_msg_associative      : bop_associative S eq bop;
    A_msg_congruence       : bop_congruence S eq bop;
    A_msg_commutative_d    : bop_commutative_decidable S eq bop;
    A_msg_is_left_d        : bop_is_left_decidable S eq bop;
    A_msg_is_right_d       : bop_is_right_decidable S eq bop;
    A_msg_left_cancel_d    : bop_left_cancellative_decidable S eq bop;
    A_msg_right_cancel_d   : bop_right_cancellative_decidable S eq bop;
    A_msg_left_constant_d  : bop_left_constant_decidable S eq bop;
    A_msg_right_constant_d : bop_right_constant_decidable S eq bop;
    A_msg_anti_left_d      : bop_anti_left_decidable S eq bop;
    A_msg_anti_right_d     : bop_anti_right_decidable S eq bop }

    Let's look at the value of one field, bop_commutative_decidable
 *)
Print bop_commutative_decidable. 
(*
   bop_commutative_decidable = 
   λ (S : Type) (r : brel S) (b : binary_op S),
    (bop_commutative S r b + bop_not_commutative S r b)%type
     : ∀ S : Type, brel S → binary_op S → Type
 *)
Print bop_commutative. 
(*
bop_commutative = 
λ (S : Type) (r : brel S) (b : binary_op S),
  ∀ s t : S, r (b s t) (b t s) = true
     : ∀ S : Type, brel S → binary_op S → Prop
 *)
Print bop_not_commutative.
(*
   bop_not_commutative = 
  λ (S : Type) (r : brel S) (b : binary_op S),
     {z : S * S & let (s, t) := z in r (b s t) (b t s) = false}
     : ∀ S : Type, brel S → binary_op S → Type
 *)

(* Now, look at id_ann_proofs: *)
Print id_ann_proofs. 
(*
Record id_ann_proofs (S : Type) (eq : brel S) (plus times : binary_op S)
  : Type := Build_id_ann_proofs
  { A_id_ann_plus_times_d : exists_id_ann_decidable S eq plus times;
    A_id_ann_times_plus_d : exists_id_ann_decidable S eq times plus }
 *)
Print exists_id_ann_decidable. 
(*
Inductive
exists_id_ann_decidable (S : Type) (eq : brel S) (b1 b2 : binary_op S)
  : Type :=
    Id_Ann_Proof_None : bop_not_exists_id S eq b1 *
                        bop_not_exists_ann S eq b2
                        → exists_id_ann_decidable S eq b1 b2
  | Id_Ann_Proof_Id_None : bop_exists_id S eq b1 * bop_not_exists_ann S eq b2
                           → exists_id_ann_decidable S eq b1 b2
  | Id_Ann_Proof_None_Ann : bop_not_exists_id S eq b1 *
                            bop_exists_ann S eq b2
                            → exists_id_ann_decidable S eq b1 b2
  | Id_Ann_Proof_Equal : bops_exists_id_ann_equal S eq b1 b2
                         → exists_id_ann_decidable S eq b1 b2
  | Id_Ann_Proof_Not_Equal : bops_exists_id_ann_not_equal S eq b1 b2
                             → exists_id_ann_decidable S eq b1 b2
 *)


(* A_bs_CS is the fully annotated version.  We 
   can translate this to an "OCaml version that
   preserves only the computational content. 
   This is done with the function A2C_bs_CS. 
   (A2C = Annotated to Certificates) 
 *)
Check A2C_bs_CS.
(*
   A2C_bs_CS : ∀ S : Type, A_bs_CS S → bs_CS

   OK, but what do bs_CS records look like? 
 *)
Print bs_CS.
(* 
Record bs_CS (S : Type) : Type := Build_bs_CS
  { bs_CS_eqv          : structures.eqv;
    bs_CS_plus         : binary_op S;
    bs_CS_times        : binary_op S;
    bs_CS_plus_certs   : sg_CS_certificates;
    bs_CS_times_certs  : msg_certificates;
    bs_CS_id_ann_certs : id_ann_certificates;
    bs_CS_certs        : bs_certificates;
    bs_CS_ast          : ast.cas_ast }
 *)

(*Let's look at some of the value associated with  bs_CS_times_certs *)
Print msg_certificates.
(*
Record msg_certificates (S : Type) : Type := Build_msg_certificates
  { msg_associative : assert_associative;
    msg_congruence : assert_bop_congruence;
    msg_commutative_d : check_commutative;
    msg_is_left_d : check_is_left;
    msg_is_right_d : check_is_right;
    msg_left_cancel_d : check_left_cancellative;
    msg_right_cancel_d : check_right_cancellative;
    msg_left_constant_d : check_left_constant;
    msg_right_constant_d : check_right_constant;
    msg_anti_left_d : check_anti_left;
    msg_anti_right_d : check_anti_right }

Let's look again at commutativity. 
*) 
Print check_commutative.
(*
Inductive check_commutative (S : Type) : Type :=
    Certify_Commutative : check_commutative
  | Certify_Not_Commutative : S * S → check_commutative

Here's how something of type 
    bop_commutative_decidable S eq bop 
is translated to something of type 
    check_commutative. 
 *)
Print p2c_commutative_check.  
(*
p2c_commutative_check = 
λ (S : Type) 
  (eq0 : brel S) 
  (b : binary_op S) 
  (d : bop_commutative_decidable S eq0 b),
  match d with
  | inl _ => Certify_Commutative
  | inr p => Certify_Not_Commutative (projT1 p)
  end
        : ∀ (S : Type) (r : brel S) (b : binary_op S),
             bop_commutative_decidable S r b → check_commutative

*) 

(* Now, let's inspect "A2C_bs_CS _ A_shortest_paths" *)

Eval cbv in (bs_CS_plus_certs (A2C_bs_CS _ A_shortest_paths)). 
(* 
     = {|
       sg_CS_associative := Assert_Associative;
       sg_CS_congruence := Assert_Bop_Congruence;
       sg_CS_commutative := Assert_Commutative;
       sg_CS_selective := Assert_Selective |}
     : sg_CS_certificates
*) 
Eval cbv in (bs_CS_times_certs (A2C_bs_CS _ A_shortest_paths)).
(*
     = {|
       msg_associative := Assert_Associative;
       msg_congruence := Assert_Bop_Congruence;
       msg_commutative_d := Certify_Commutative;
       msg_is_left_d := Certify_Not_Is_Left
                          (inr 0,
                          inl
                            {|
                            constant_ascii := "INF";
                            constant_latex := "\\infty" |});
       msg_is_right_d := Certify_Not_Is_Right
                           (inl
                              {|
                              constant_ascii := "INF";
                              constant_latex := "\\infty" |}, 
                           inr 0);
       msg_left_cancel_d := Certify_Not_Left_Cancellative
                              (inl
                                 {|
                                 constant_ascii := "INF";
                                 constant_latex := "\\infty" |},
                              (inr 0, inr 1));
       msg_right_cancel_d := Certify_Not_Right_Cancellative
                               (inl
                                  {|
                                  constant_ascii := "INF";
                                  constant_latex := "\\infty" |},
                               (inr 0, inr 1));
       msg_left_constant_d := Certify_Not_Left_Constant
                                (inr 0,
                                (inr 0,
                                inl
                                  {|
                                  constant_ascii := "INF";
                                  constant_latex := "\\infty" |}));
       msg_right_constant_d := Certify_Not_Right_Constant
                                 (inr 0,
                                 (inr 0,
                                 inl
                                   {|
                                   constant_ascii := "INF";
                                   constant_latex := "\\infty" |}));
       msg_anti_left_d := Certify_Not_Anti_Left
                            (inl
                               {|
                               constant_ascii := "INF";
                               constant_latex := "\\infty" |}, 
                            inr 0);
       msg_anti_right_d := Certify_Not_Anti_Right
                             (inl
                                {|
                                constant_ascii := "INF";
                                constant_latex := "\\infty" |}, 
                             inr 0) |}
     : msg_certificates
*) 

Eval cbv in (bs_CS_id_ann_certs (A2C_bs_CS _ A_shortest_paths)).
(*
     = {|
       id_ann_plus_times_d := Id_Ann_Cert_Equal
                                (inl
                                   {|
                                   constant_ascii := "INF";
                                   constant_latex := "\\infty" |});
       id_ann_times_plus_d := Id_Ann_Cert_Equal (inr 0) |}
     : id_ann_certificates

 *)

Eval cbv in (bs_CS_certs (A2C_bs_CS _ A_shortest_paths)).
(*
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Right_Distributive;
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Left_Right_Absorptive;
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Right_Right_Absorptive |}
     : bs_certificates
*) 


(* widest paths algebra *)

Check A_max_min.
(*
   A_max_min : A_selective_distributive_prelattice_with_zero nat
*) 
Definition A_bs_CS_max_min := A_bs_CS_from_selective_distributive_prelattice_with_zero nat A_max_min.

Check A_bs_CS_max_min.
(*
   A_bs_CS_max_min : A_bs_CS nat
*) 

Check A_bs_CS_add_one.
(*
   A_bs_CS_add_one : ∀ S : Type, A_bs_CS S → cas_constant → A_bs_CS (with_constant S)
*) 

Definition A_widest_paths := A_bs_CS_add_one nat A_bs_CS_max_min infinity.

Eval cbv in (bs_CS_certs (A2C_bs_CS _ A_widest_paths)).
(* 
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Right_Distributive;
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Left_Right_Absorptive;
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Right_Right_Absorptive |}
     : bs_certificates
*) 

Check A_llex_product_from_CS_CS.
(*
   A_llex_product_from_CS_CS : ∀ S T : Type, A_bs_CS S → A_bs_CS T → A_bs_CS (S * T)
*) 

Definition A_widest_shortest_paths :=
  A_bs_CS_add_zero _
                (A_llex_product_from_CS_CS _ _ A_bs_CS_min_plus A_widest_paths)
                infinity. 

Eval cbv in (bs_CS_certs (A2C_bs_CS _ A_widest_shortest_paths)).
(*
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Right_Distributive;
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Left_Right_Absorptive;
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Right_Right_Absorptive |}
     : bs_certificates
*) 

(* Let's try doing the lex product in the other way (this time we will ignore identities/annihilators)
*)

Definition A_shortest_widest_paths_version_1 := A_llex_product_from_CS_CS _ _ A_bs_CS_max_min A_bs_CS_min_plus. 

Eval cbv in (bs_CS_id_ann_certs (A2C_bs_CS _ A_shortest_widest_paths_version_1)).
(*
     = {|
       id_ann_plus_times_d := Id_Ann_Cert_None;
       id_ann_times_plus_d := Id_Ann_Cert_None |}
     : id_ann_certificates
*) 
Eval cbv in (bs_CS_certs (A2C_bs_CS _ A_shortest_widest_paths_version_1)).
(* 
     = {|
       bs_left_distributive_d := Certify_Not_Left_Distributive
                                   (0, 0, (0, 0, (1, 1)));
       bs_right_distributive_d := Certify_Not_Right_Distributive
                                    (0, 0, (0, 0, (1, 1)));
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Left_Right_Absorptive;
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Right_Right_Absorptive |}
     : bs_certificates

So, we are already in trouble wrt distributivity! 
Let's test it. 
 *)
Definition a := (0,0).
Definition b := (0,0).
Definition c := (1,1).
Definition left_distrib_counter_example := (a, (b, c)). 
Eval cbv in left_distrib_counter_example.
(* 
   = (0, 0, (0, 0, (1, 1))) : nat * nat * (nat * nat * (nat * nat))
  
   Note the ugly way Coq prints this out!   Yuck! 
*) 
Definition plus  := A_bs_CS_plus _ A_shortest_widest_paths_version_1.
Definition times := A_bs_CS_times _ A_shortest_widest_paths_version_1.
Definition lhs := times a (plus b c).
Definition rhs := plus (times a b) (times a c).
Eval cbv in lhs.  (* = (0, 1) : nat * nat *)
Eval cbv in rhs.  (* = (0, 0) : nat * nat *) 

     
Definition self :=
{|
  constant_ascii := "self"
; constant_latex := "\\bot"
|}.

Definition A_shortest_widest_paths :=
   A_bs_CS_add_one _
   (A_bs_CS_add_zero _ (A_llex_product_from_CS_CS _ _ A_bs_CS_max_min A_bs_CS_min_plus) infinity)
   self.   

Eval cbv in (bs_CS_id_ann_certs (A2C_bs_CS _ A_shortest_widest_paths)).
(*
     = {|
       id_ann_plus_times_d := Id_Ann_Cert_Equal
                                (inr
                                   (inl
                                      {|
                                      constant_ascii := "INF";
                                      constant_latex := "\\infty" |}));
       id_ann_times_plus_d := Id_Ann_Cert_Equal
                                (inl
                                   {|
                                   constant_ascii := "self";
                                   constant_latex := "\\bot" |}) |}
     : id_ann_certificates
*) 

Eval cbv in (bs_CS_certs (A2C_bs_CS _ A_shortest_widest_paths)).
(* 
     = {|
       bs_left_distributive_d := Certify_Not_Left_Distributive
                                   (inr (inr (0, 0)),
                                   (inr (inr (0, 0)), inr (inr (1, 1))));
       bs_right_distributive_d := Certify_Not_Right_Distributive
                                    (inr (inr (0, 0)),
                                    (inr (inr (0, 0)), inr (inr (1, 1))));
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Left_Right_Absorptive;
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Right_Right_Absorptive |}
     : bs_certificates
*) 


(* Now, let's think about adding "next hops" to a path problem. 
   
  If (S, +) is a commutative and selective semigroup, then 
  the combinator A_bs_left_from_sg_CS will transform it to 
  a bi-semigroup (S, +, left), where "a left b = a". 
*) 

Check A_bs_left_from_sg_CS. 
(*
   A_bs_left_from_sg_CS : ∀ S : Type, A_sg_CS S → A_selective_presemiring S
*) 
Check A_sg_CS_min.
(* 
   A_sg_CS_min : A_sg_CS nat
*) 
Definition A_next_hop := A_bs_CS_from_selective_presemiring _ (A_bs_left_from_sg_CS _ A_sg_CS_min).

Eval cbv in (bs_CS_certs (A2C_bs_CS _ A_next_hop)).
(*
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Right_Distributive;
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Not_Left_Right_Absorptive (1, 0);
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Not_Right_Right_Absorptive (1, 0) |}
     : bs_certificates
*) 

Definition test1 := A_llex_product_from_CS_CS _ _ A_bs_CS_min_plus A_next_hop. 

Eval cbv in (bs_CS_id_ann_certs (A2C_bs_CS _ test1)).
(*
     = {|
       id_ann_plus_times_d := Id_Ann_Cert_None;
       id_ann_times_plus_d := Id_Ann_Cert_None_Ann (0, 0) |}
     : id_ann_certificates
*) 

Eval cbv in (bs_CS_certs (A2C_bs_CS _ test1)).
(* 
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Right_Distributive;
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Not_Left_Right_Absorptive
                                       (0, 1, (0, 0));
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Not_Right_Right_Absorptive
                                        (0, 1, (0, 0)) |}
     : bs_certificates
*) 

Definition test2 := A_llex_product_from_CS_CS _ _ A_bs_CS_max_min A_next_hop. 

Eval cbv in (bs_CS_id_ann_certs (A2C_bs_CS _ test2)).
(*
     = {|
       id_ann_plus_times_d := Id_Ann_Cert_None;
       id_ann_times_plus_d := Id_Ann_Cert_None |}
     : id_ann_certificates

 *)

Eval cbv in (bs_CS_certs (A2C_bs_CS _ test2)).
(*
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Not_Right_Distributive
                                    (0, 0, (0, 0, (1, 1)));
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Not_Left_Right_Absorptive
                                       (0, 1, (0, 0));
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Not_Right_Right_Absorptive
                                        (0, 1, (0, 0)) |}
     : bs_certificates

Interesting!  Is left distributive, but not right distributive. 
*) 

Definition test3 :=
  A_llex_product_from_CS_CS _ _
     (A_llex_product_from_CS_CS _ _ A_bs_CS_min_plus A_bs_CS_max_min)
     A_next_hop. 

Eval cbv in (bs_CS_id_ann_certs (A2C_bs_CS _ test3)).

Eval cbv in (bs_CS_certs (A2C_bs_CS _ test3)).
(*
     = {|
       bs_left_distributive_d := Certify_Left_Distributive;
       bs_right_distributive_d := Certify_Not_Right_Distributive
                                    (0, 0, 0, (0, 0, 0, (0, 1, 1)));
       bs_left_left_absorptive_d := Certify_Left_Left_Absorptive;
       bs_left_right_absorptive_d := Certify_Not_Left_Right_Absorptive
                                       (0, 0, 1, (0, 0, 0));
       bs_right_left_absorptive_d := Certify_Right_Left_Absorptive;
       bs_right_right_absorptive_d := Certify_Not_Right_Right_Absorptive
                                        (0, 0, 1, (0, 0, 0)) |}
     : bs_certificates
*) 
