Require Import Coq.Arith.Arith.     
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.cef. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.cast. 
Require Import CAS.code.check. 

Definition eqv_certs_eq_bool : eqv_certificates bool
:= {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness bool true 
     ; certify_nontrivial_negate   := Certify_Negate bool negb
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence bool 
    ; eqv_reflexive     := Assert_Reflexive bool 
    ; eqv_symmetric     := Assert_Symmetric bool 
    ; eqv_transitive    := Assert_Transitive bool 
   |}. 

Open Scope nat. 

Definition eqv_certs_eq_nat : eqv_certificates nat
:= {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness nat 0 
     ; certify_nontrivial_negate   := Certify_Negate nat S (* (λ (i : nat), S i) *) 
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence nat 
    ; eqv_reflexive     := Assert_Reflexive nat 
    ; eqv_symmetric     := Assert_Symmetric nat 
    ; eqv_transitive    := Assert_Transitive nat
   |}. 

Open Scope list_scope. 

Definition eqv_certs_add_constant : ∀ (S : Type), cas_constant -> eqv_certificates S -> eqv_certificates (with_constant S) 
:= λ S c eqvS, 
   let w := nontrivial_witness S (eqv_nontrivial S eqvS) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness (with_constant S) (inr _ w)  
     ; certify_nontrivial_negate   := 
              Certify_Negate (with_constant S) 
                   (λ (d : with_constant S), 
                        match d with | inl _ => inr _ w | inr _ => inl S c end)

     |} 
    ; eqv_congruence    := Assert_Brel_Congruence (with_constant S) 
    ; eqv_reflexive     := Assert_Reflexive (with_constant S) 
    ; eqv_symmetric     := Assert_Symmetric (with_constant S) 
    ; eqv_transitive    := Assert_Transitive (with_constant S) 
   |}. 



Definition eqv_certs_brel_list : ∀ (S : Type),  eqv_certificates S -> eqv_certificates (list S) 
:= λ S eqvS, 
   let w := nontrivial_witness S (eqv_nontrivial S eqvS) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness (list S) nil  
     ; certify_nontrivial_negate   := Certify_Negate (list S) (λ (l : list S), w :: l)
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence (list S) 
    ; eqv_reflexive     := Assert_Reflexive (list S) 
    ; eqv_symmetric     := Assert_Symmetric (list S) 
    ; eqv_transitive    := Assert_Transitive (list S) 
   |}. 

Definition eqv_certs_brel_set : ∀ (S : Type) (r : brel S),  eqv_certificates S -> eqv_certificates (finite_set S) 
:= λ S r eqvS, 
   let s := nontrivial_witness S (eqv_nontrivial S eqvS) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness (finite_set S) nil  
     ; certify_nontrivial_negate   := Certify_Negate (finite_set S) 
              (λ (l : finite_set S), if brel_set S r nil l then (s :: nil) else nil)
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence (finite_set S) 
    ; eqv_reflexive     := Assert_Reflexive (finite_set S) 
    ; eqv_symmetric     := Assert_Symmetric (finite_set S) 
    ; eqv_transitive    := Assert_Transitive (finite_set S) 
   |}. 


Definition assert_product_nontrivial : ∀ (S T : Type),  assert_nontrivial S -> assert_nontrivial T -> assert_nontrivial (S * T) 
:= λ S T ntS ntT, 
  match certify_nontrivial_negate S ntS, certify_nontrivial_negate T ntT with 
  | Certify_Negate _ f, Certify_Negate _ g => 
    {| 
       certify_nontrivial_witness  := 
          Certify_Witness (S * T) (nontrivial_witness S ntS, nontrivial_witness T ntT)
     ; certify_nontrivial_negate   := 
           Certify_Negate (S * T) (λ (p : S * T), let (x, y) := p in (f x, g y))
   |}
  end. 

Definition eqv_certs_product : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> eqv_certificates (S * T) 
:= λ S T eqvS eqvT, 
   {| 
      eqv_nontrivial := assert_product_nontrivial S T 
                           (eqv_nontrivial _ eqvS) 
                           (eqv_nontrivial _ eqvT)
    ; eqv_congruence    := Assert_Brel_Congruence (S * T) 
    ; eqv_reflexive     := Assert_Reflexive (S * T) 
    ; eqv_symmetric     := Assert_Symmetric (S * T) 
    ; eqv_transitive    := Assert_Transitive (S * T) 
   |}. 



Definition eqv_certs_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> eqv_certificates (S + T) 
:= λ S T eqvS eqvT, 
   let wS := nontrivial_witness S (eqv_nontrivial S eqvS) in 
   let wT := nontrivial_witness T (eqv_nontrivial T eqvT) in 
   {| 
     eqv_nontrivial := 
     {| 
       certify_nontrivial_witness  := Certify_Witness (S + T) (inl T wS) 
     ; certify_nontrivial_negate   := 
              Certify_Negate (S + T) 
                   (λ (d : S + T), match d with | inl _ => inr S wT | inr _ => inl T wS end)
     |} 
    ; eqv_congruence    := Assert_Brel_Congruence (S + T)
    ; eqv_reflexive     := Assert_Reflexive (S + T)
    ; eqv_symmetric     := Assert_Symmetric (S + T)
    ; eqv_transitive    := Assert_Transitive (S + T)
   |}. 



(* orders *) 

Definition po_certs_dual : ∀ (S : Type), po_certificates S -> po_certificates S 
:= λ S tpS, 
{|
  po_congruence    := Assert_Brel_Congruence S 
; po_reflexive     := Assert_Reflexive S 
; po_transitive    := Assert_Transitive S 
; po_antisymmetric := Assert_Antisymmetric S 
; po_total_d       := po_total_d S tpS
|}.


Definition po_certs_llte : ∀ (S : Type), 
               eqv_certificates S -> sg_CI_certificates S -> po_certificates S 
:= λ S eqv sgp, 
{|
  po_congruence    := Assert_Brel_Congruence S 
; po_reflexive     := Assert_Reflexive S 
; po_transitive    := Assert_Transitive S 
; po_antisymmetric := Assert_Antisymmetric S 
; po_total_d       := match sg_CI_selective_d _ sgp with 
                      | Certify_Selective _ => Certify_Total S 
                      | Certify_Not_Selective _ (a, b) => Certify_Not_Total S (a, b)
                      end 
|}.


Definition po_certs_rlte : ∀ (S : Type),
               eqv_certificates S -> sg_CI_certificates S -> po_certificates S 
               
:= λ S eqv sgp, 
{|
  po_congruence    := Assert_Brel_Congruence S 
; po_reflexive     := Assert_Reflexive S 
; po_transitive    := Assert_Transitive S 
; po_antisymmetric := Assert_Antisymmetric S 
; po_total_d       := match sg_CI_selective_d _ sgp with 
                      | Certify_Selective _ => Certify_Total S 
                      | Certify_Not_Selective _ (a, b) => Certify_Not_Total S (a, b)
                      end 
|}.

Definition to_certs_bool : to_certificates bool 
:= {|
  to_congruence    := Assert_Brel_Congruence _
; to_reflexive     := Assert_Reflexive _ 
; to_transitive    := Assert_Transitive _
; to_antisymmetric := Assert_Antisymmetric _
; to_total         := Assert_Total _ 
|}.

Definition to_certs_nat : to_certificates nat 
:= {|
  to_congruence    := Assert_Brel_Congruence _
; to_reflexive     := Assert_Reflexive _
; to_transitive    := Assert_Transitive _
; to_antisymmetric := Assert_Antisymmetric _
; to_total         := Assert_Total _ 
|}.

Definition to_certs_dual : ∀ (S : Type), to_certificates S -> to_certificates S 
               
:= λ S tpS, 
{|
  to_congruence    := Assert_Brel_Congruence S 
; to_reflexive     := Assert_Reflexive S 
; to_transitive    := Assert_Transitive S 
; to_antisymmetric := Assert_Antisymmetric S 
; to_total         := Assert_Total S 
|}.


Definition to_certs_llte : ∀ (S : Type), 
                      eqv_certificates S -> sg_CS_certificates S -> to_certificates S 
:= λ S eqv sgp, 
{|
  to_congruence    := Assert_Brel_Congruence S 
; to_reflexive     := Assert_Reflexive S 
; to_transitive    := Assert_Transitive S 
; to_antisymmetric := Assert_Antisymmetric S 
; to_total         := Assert_Total S 
|}.

Definition to_certs_rlte : ∀ (S : Type), 
                      eqv_certificates S -> sg_CS_certificates S -> to_certificates S 
:= λ S eqv sgp, 
{|
  to_congruence    := Assert_Brel_Congruence S 
; to_reflexive     := Assert_Reflexive S 
; to_transitive    := Assert_Transitive S 
; to_antisymmetric := Assert_Antisymmetric S 
; to_total         := Assert_Total S 
|}.


(* semigroups *) 

(* basics *) 

(* from Compute (P2C_sg _ brel_eq_bool bop_and (sg_proofs_and)) *) 
Definition sg_certs_and : sg_certificates bool
:= {| 
       sg_associative := Assert_Associative bool;
       sg_congruence := Assert_Bop_Congruence bool;
       sg_commutative_d := Certify_Commutative bool;
       sg_selective_d := Certify_Selective bool;
       sg_idempotent_d := Certify_Idempotent bool;
       sg_exists_id_d := Certify_Exists_Id bool true;
       sg_exists_ann_d := Certify_Exists_Ann bool false;
       sg_is_left_d := Certify_Not_Is_Left bool (true, false);
       sg_is_right_d := Certify_Not_Is_Right bool (false, true);
       sg_left_cancel_d := Certify_Not_Left_Cancellative bool
                             (false, (false, true));
       sg_right_cancel_d := Certify_Not_Right_Cancellative bool
                              (false, (false, true));
       sg_left_constant_d := Certify_Not_Left_Constant bool
                               (true, (false, true));
       sg_right_constant_d := Certify_Not_Right_Constant bool
                                (true, (false, true));
       sg_anti_left_d := Certify_Not_Anti_Left bool (true, true);
       sg_anti_right_d := Certify_Not_Anti_Right bool (true, true)
   |}. 


(* from Compute (P2C_sg _ brel_eq_bool bop_or (sg_proofs_or)) *) 
Definition sg_certs_or : sg_certificates bool
:= {| 
       sg_associative := Assert_Associative bool;
       sg_congruence := Assert_Bop_Congruence bool;
       sg_commutative_d := Certify_Commutative bool;
       sg_selective_d := Certify_Selective bool;
       sg_idempotent_d := Certify_Idempotent bool;
       sg_exists_id_d := Certify_Exists_Id bool false;
       sg_exists_ann_d := Certify_Exists_Ann bool true;
       sg_is_left_d := Certify_Not_Is_Left bool (false, true);
       sg_is_right_d := Certify_Not_Is_Right bool (true, false);
       sg_left_cancel_d := Certify_Not_Left_Cancellative bool
                             (true, (true, false));
       sg_right_cancel_d := Certify_Not_Right_Cancellative bool
                              (true, (true, false));
       sg_left_constant_d := Certify_Not_Left_Constant bool
                               (false, (true, false));
       sg_right_constant_d := Certify_Not_Right_Constant bool
                                (false, (true, false));
       sg_anti_left_d := Certify_Not_Anti_Left bool (true, true);
       sg_anti_right_d := Certify_Not_Anti_Right bool (true, true)
   |}. 


(* 
  Compute (P2C_sg _ brel_eq_nat bop_min (sg_proofs_min)). 
*) 
Definition sg_certs_min : sg_certificates nat
:= {| 
       sg_associative := Assert_Associative nat;
       sg_congruence := Assert_Bop_Congruence nat;
       sg_commutative_d := Certify_Commutative nat;
       sg_selective_d := Certify_Selective nat;
       sg_idempotent_d := Certify_Idempotent nat;
       sg_exists_id_d := Certify_Not_Exists_Id nat;
       sg_exists_ann_d := Certify_Exists_Ann nat 0;
       sg_is_left_d := Certify_Not_Is_Left nat (1, 0);
       sg_is_right_d := Certify_Not_Is_Right nat (0, 1);
       sg_left_cancel_d := Certify_Not_Left_Cancellative nat (0, (0, 1));
       sg_right_cancel_d := Certify_Not_Right_Cancellative nat (0, (0, 1));
       sg_left_constant_d := Certify_Not_Left_Constant nat (1, (0, 1));
       sg_right_constant_d := Certify_Not_Right_Constant nat (1, (0, 1));
       sg_anti_left_d := Certify_Not_Anti_Left nat (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right nat (0, 0) 
   |}. 


(* 
  Compute (P2C_sg _ brel_eq_nat bop_max (sg_proofs_max)). 
*) 
Definition sg_certs_max : sg_certificates nat
:= {| 
       sg_associative := Assert_Associative nat;
       sg_congruence := Assert_Bop_Congruence nat;
       sg_commutative_d := Certify_Commutative nat;
       sg_selective_d := Certify_Selective nat;
       sg_idempotent_d := Certify_Idempotent nat;
       sg_exists_id_d := Certify_Exists_Id nat 0;
       sg_exists_ann_d := Certify_Not_Exists_Ann nat;
       sg_is_left_d := Certify_Not_Is_Left nat (0, 1);
       sg_is_right_d := Certify_Not_Is_Right nat (1, 0);
       sg_left_cancel_d := Certify_Not_Left_Cancellative nat (1, (1, 0));
       sg_right_cancel_d := Certify_Not_Right_Cancellative nat (1, (1, 0));
       sg_left_constant_d := Certify_Not_Left_Constant nat (0, (1, 0));
       sg_right_constant_d := Certify_Not_Right_Constant nat (0, (1, 0));
       sg_anti_left_d := Certify_Not_Anti_Left nat (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right nat (0, 0) 
   |}. 


(* 
  Compute (P2C_sg _ brel_eq_nat bop_plus (sg_proofs_plus)). 
*) 
Definition sg_certs_plus : sg_certificates nat
:= {| 
       sg_associative := Assert_Associative nat;
       sg_congruence := Assert_Bop_Congruence nat;
       sg_commutative_d := Certify_Commutative nat;
       sg_selective_d := Certify_Not_Selective nat (1, 1);
       sg_idempotent_d := Certify_Not_Idempotent nat 1;
       sg_exists_id_d := Certify_Exists_Id nat 0;
       sg_exists_ann_d := Certify_Not_Exists_Ann nat;
       sg_is_left_d := Certify_Not_Is_Left nat (0, 1);
       sg_is_right_d := Certify_Not_Is_Right nat (1, 0);
       sg_left_cancel_d := Certify_Left_Cancellative nat;
       sg_right_cancel_d := Certify_Right_Cancellative nat;
       sg_left_constant_d := Certify_Not_Left_Constant nat (0, (0, 1));
       sg_right_constant_d := Certify_Not_Right_Constant nat (0, (0, 1));
       sg_anti_left_d := Certify_Not_Anti_Left nat (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right nat (0, 0)

   |}. 


(* 
  Compute (P2C_sg _ brel_eq_nat bop_times (sg_proofs_times)). 
*) 
Definition sg_certs_times : sg_certificates nat
:= {| 
       sg_associative := Assert_Associative nat;
       sg_congruence := Assert_Bop_Congruence nat;
       sg_commutative_d := Certify_Commutative nat;
       sg_selective_d := Certify_Not_Selective nat (2, 2);
       sg_idempotent_d := Certify_Not_Idempotent nat 2;
       sg_exists_id_d := Certify_Exists_Id nat 1;
       sg_exists_ann_d := Certify_Exists_Ann nat 0;
       sg_is_left_d := Certify_Not_Is_Left nat (1, 0);
       sg_is_right_d := Certify_Not_Is_Right nat (0, 1);
       sg_left_cancel_d := Certify_Not_Left_Cancellative nat (0, (0, 1));
       sg_right_cancel_d := Certify_Not_Right_Cancellative nat (0, (0, 1));
       sg_left_constant_d := Certify_Not_Left_Constant nat (1, (0, 1));
       sg_right_constant_d := Certify_Not_Right_Constant nat (1, (0, 1));
       sg_anti_left_d := Certify_Not_Anti_Left nat (0, 0);
       sg_anti_right_d := Certify_Not_Anti_Right nat (0, 0) 
   |}. 



(******************) 

Definition sg_CS_certs_and : sg_CS_certificates bool
:= {| 
     sg_CS_associative        := Assert_Associative bool 
   ; sg_CS_congruence         := Assert_Bop_Congruence bool 
   ; sg_CS_commutative        := Assert_Commutative bool 
   ; sg_CS_selective          := Assert_Selective bool 
   ; sg_CS_exists_id_d        := Certify_Exists_Id bool true 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann bool false 
   |}. 

Definition sg_CS_certs_or : sg_CS_certificates bool
:= {| 
     sg_CS_associative        := Assert_Associative bool 
   ; sg_CS_congruence         := Assert_Bop_Congruence bool 
   ; sg_CS_commutative        := Assert_Commutative bool 
   ; sg_CS_selective          := Assert_Selective bool 
   ; sg_CS_exists_id_d        := Certify_Exists_Id bool false 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann bool true
   |}. 

Definition sg_CS_certs_min : sg_CS_certificates nat 
:= {|
     sg_CS_associative        := Assert_Associative nat 
   ; sg_CS_congruence         := Assert_Bop_Congruence nat 
   ; sg_CS_commutative        := Assert_Commutative nat 
   ; sg_CS_selective          := Assert_Selective nat 
   ; sg_CS_exists_id_d        := Certify_Not_Exists_Id nat 
   ; sg_CS_exists_ann_d       := Certify_Exists_Ann nat 0
   |}. 

Definition sg_CS_certs_max : sg_CS_certificates nat 
:= {| 
     sg_CS_associative        := Assert_Associative nat 
   ; sg_CS_congruence         := Assert_Bop_Congruence nat 
   ; sg_CS_commutative        := Assert_Commutative nat 
   ; sg_CS_selective          := Assert_Selective nat 
   ; sg_CS_exists_id_d        := Certify_Exists_Id nat 0
   ; sg_CS_exists_ann_d       := Certify_Not_Exists_Ann nat 
   |}. 


Definition sg_CK_certs_plus : sg_CK_certificates nat 
:= {|
     sg_CK_associative    := Assert_Associative nat 
   ; sg_CK_congruence     := Assert_Bop_Congruence nat 
   ; sg_CK_commutative    := Assert_Commutative nat 
   ; sg_CK_left_cancel    := Assert_Left_Cancellative nat 
   ; sg_CK_exists_id_d    := Certify_Exists_Id nat 0 
   ; sg_CK_anti_left_d    := Certify_Not_Anti_Left nat (0, 0) 
   ; sg_CK_anti_right_d   := Certify_Not_Anti_Right nat (0, 0) 
   |}.


Definition sg_C_certs_times : sg_C_certificates nat 
:= {|
     sg_C_associative    := Assert_Associative nat 
   ; sg_C_congruence     := Assert_Bop_Congruence nat 
   ; sg_C_commutative    := Assert_Commutative nat 
   ; sg_C_selective_d    := Certify_Not_Selective nat (2, 2)
   ; sg_C_idempotent_d   := Certify_Not_Idempotent nat 2
   ; sg_C_exists_id_d    := Certify_Exists_Id nat 1 
   ; sg_C_exists_ann_d   := Certify_Exists_Ann nat 0
   ; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative nat (0, (0, 1))
   ; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative nat (0, (0, 1))
   ; sg_C_left_constant_d  := Certify_Not_Left_Constant  nat (1, (0, 1))
   ; sg_C_right_constant_d := Certify_Not_Right_Constant nat (1, (0, 1))
   ; sg_C_anti_left_d      := Certify_Not_Anti_Left nat (0, 0)
   ; sg_C_anti_right_d     := Certify_Not_Anti_Right nat (0, 0)
   |}.


Definition sg_certs_concat : ∀ (S : Type),  eqv_certificates S -> sg_certificates (list S) 
:= λ S eqvS,  
let (s, t) := nontrivial_pair S (eqv_nontrivial _ eqvS) in 
{|
  sg_associative      := Assert_Associative (list S) 
; sg_congruence       := Assert_Bop_Congruence (list S) 
; sg_commutative_d    := Certify_Not_Commutative (list S) (s :: nil, t :: nil)
; sg_selective_d      := Certify_Not_Selective (list S) (s :: nil, t :: nil)
; sg_is_left_d        := Certify_Not_Is_Left (list S) (nil, s :: nil)
; sg_is_right_d       := Certify_Not_Is_Right (list S) (s :: nil, nil)
; sg_idempotent_d     := Certify_Not_Idempotent (list S) (s :: nil)
; sg_exists_id_d      := Certify_Exists_Id (list S) nil 
; sg_exists_ann_d     := Certify_Not_Exists_Ann (list S) 
; sg_left_cancel_d    := Certify_Left_Cancellative (list S) 
; sg_right_cancel_d   := Certify_Right_Cancellative (list S) 
; sg_left_constant_d  := Certify_Not_Left_Constant (list S)  (nil, (nil, s :: nil))
; sg_right_constant_d := Certify_Not_Right_Constant (list S) (nil, (nil, s :: nil))
; sg_anti_left_d      := Certify_Not_Anti_Left (list S) (s :: nil, nil) 
; sg_anti_right_d     := Certify_Not_Anti_Right (list S) (s :: nil, nil)
|}. 

Definition sg_certs_left : ∀ (S : Type),  eqv_certificates S -> sg_certificates S 
:= λ S eqvS,  
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
let t := f s in 
{|
  sg_associative      := Assert_Associative S 
; sg_congruence       := Assert_Bop_Congruence S 
; sg_commutative_d    := Certify_Not_Commutative S (s, t)
; sg_selective_d      := Certify_Selective S 
; sg_is_left_d        := Certify_Is_Left S 
; sg_is_right_d       := Certify_Not_Is_Right S (s, t)
; sg_idempotent_d     := Certify_Idempotent S 
; sg_exists_id_d      := Certify_Not_Exists_Id S  
; sg_exists_ann_d     := Certify_Not_Exists_Ann S 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative S (s, (s, t)) 
; sg_right_cancel_d   := Certify_Right_Cancellative S
; sg_left_constant_d  := Certify_Left_Constant S
; sg_right_constant_d := Certify_Not_Right_Constant S (s, (s, t)) 
; sg_anti_left_d      := Certify_Not_Anti_Left S (s, s) 
; sg_anti_right_d     := Certify_Not_Anti_Right S (s, s) 
|}
end. 


Definition sg_certs_right : ∀ (S : Type),  eqv_certificates S -> sg_certificates S 
:= λ S eqvS,  
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
let t := f s in 
{|
  sg_associative   := Assert_Associative S 
; sg_congruence    := Assert_Bop_Congruence S 
; sg_commutative_d := Certify_Not_Commutative S (t, s)
; sg_selective_d   := Certify_Selective S 
; sg_is_left_d     := Certify_Not_Is_Left S (t, s)
; sg_is_right_d    := Certify_Is_Right S 
; sg_idempotent_d  := Certify_Idempotent S 
; sg_exists_id_d   := Certify_Not_Exists_Id S  
; sg_exists_ann_d  := Certify_Not_Exists_Ann S 
; sg_left_cancel_d    := Certify_Left_Cancellative S
; sg_right_cancel_d   := Certify_Not_Right_Cancellative S (s, (s, t))
; sg_left_constant_d  := Certify_Not_Left_Constant S (s, (s, t))
; sg_right_constant_d := Certify_Right_Constant S
; sg_anti_left_d      := Certify_Not_Anti_Left S (s, s) 
; sg_anti_right_d     := Certify_Not_Anti_Right S (s, s) 
|}
end. 

(* sg add_id *) 

Definition sg_certs_add_id : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_certificates S -> sg_certificates (with_constant S) 
:= λ S c eqvS sgS,  
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_associative      := Assert_Associative (with_constant S) 
; sg_congruence       := Assert_Bop_Congruence (with_constant S) 
; sg_commutative_d    := bop_add_id_commutative_check S (sg_commutative_d S sgS) 
; sg_selective_d      := bop_add_id_selective_check S (sg_selective_d S sgS) 
; sg_is_left_d        := bop_add_id_not_is_left_check S c 
                            (certify_nontrivial_witness S (eqv_nontrivial S eqvS))
; sg_is_right_d       := bop_add_id_not_is_right_check S c 
                            (certify_nontrivial_witness S (eqv_nontrivial S eqvS))
; sg_idempotent_d     := bop_add_id_idempotent_check S (sg_idempotent_d S sgS) 
; sg_exists_id_d      := Certify_Exists_Id (with_constant S) (inl S c) 
; sg_exists_ann_d     := bop_add_id_exists_ann_check S (sg_exists_ann_d S sgS) 
; sg_left_cancel_d    := bop_add_id_left_cancellative_check S c 
                            (sg_anti_left_d S sgS)
                            (sg_left_cancel_d S sgS)
; sg_right_cancel_d   := bop_add_id_right_cancellative_check S c 
                            (sg_anti_right_d S sgS)
                            (sg_right_cancel_d S sgS)
; sg_left_constant_d  := Certify_Not_Left_Constant (with_constant S) (inl c, (inr s, inr (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant (with_constant S) (inl c, (inr s, inr (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left (with_constant S) (inr s, inl c)
; sg_anti_right_d     := Certify_Not_Anti_Right (with_constant S) (inr s, inl c)
|}
end. 


Definition sg_C_certs_add_id : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_C_certificates S -> sg_C_certificates (with_constant S) 
:= λ S c eqvS sgS,  
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_C_associative   := Assert_Associative (with_constant S) 
; sg_C_congruence    := Assert_Bop_Congruence (with_constant S) 
; sg_C_commutative   := Assert_Commutative (with_constant S) 
; sg_C_selective_d   := bop_add_id_selective_check S (sg_C_selective_d S sgS) 
; sg_C_idempotent_d  := bop_add_id_idempotent_check S (sg_C_idempotent_d S sgS) 
; sg_C_exists_id_d   := Certify_Exists_Id (with_constant S) (inl S c) 
; sg_C_exists_ann_d  := bop_add_id_exists_ann_check S (sg_C_exists_ann_d S sgS) 
; sg_C_left_cancel_d    := bop_add_id_left_cancellative_check S c 
                            (sg_C_anti_left_d S sgS)
                            (sg_C_left_cancel_d S sgS)
; sg_C_right_cancel_d   := bop_add_id_right_cancellative_check S c 
                            (sg_C_anti_right_d S sgS)
                            (sg_C_right_cancel_d S sgS)
; sg_C_left_constant_d  := Certify_Not_Left_Constant (with_constant S) (inl c, (inr s, inr (f s)))
; sg_C_right_constant_d := Certify_Not_Right_Constant (with_constant S) (inl c, (inr s, inr (f s)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left (with_constant S) (inr s, inl c)
; sg_C_anti_right_d     := Certify_Not_Anti_Right (with_constant S) (inr s, inl c)
|}
end. 

Definition sg_CI_certs_add_id : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_CI_certificates S -> sg_CI_certificates (with_constant S) 
:= λ S c eqvS sgS,  
let wS := certify_nontrivial_witness S (eqv_nontrivial S eqvS) in 
match wS, certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_CI_associative        := Assert_Associative (with_constant S) 
; sg_CI_congruence         := Assert_Bop_Congruence (with_constant S) 
; sg_CI_commutative        := Assert_Commutative (with_constant S) 
; sg_CI_idempotent         := Assert_Idempotent (with_constant S) 
; sg_CI_selective_d        := bop_add_id_selective_check S (sg_CI_selective_d S sgS) 
; sg_CI_exists_id_d        := Certify_Exists_Id (with_constant S) (inl S c) 
; sg_CI_exists_ann_d       := bop_add_id_exists_ann_check S (sg_CI_exists_ann_d S sgS) 
|}
end. 


Definition sg_CS_certs_add_id : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_CS_certificates S -> sg_CS_certificates (with_constant S) 
:= λ S c eqvS sg,  
let wS := certify_nontrivial_witness S (eqv_nontrivial S eqvS) in 
match wS, certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_CS_associative   := Assert_Associative (with_constant S) 
; sg_CS_congruence    := Assert_Bop_Congruence (with_constant S) 
; sg_CS_commutative   := Assert_Commutative (with_constant S) 
; sg_CS_selective     := Assert_Selective (with_constant S) 
; sg_CS_exists_id_d   := Certify_Exists_Id (with_constant S) (inl S c) 
; sg_CS_exists_ann_d  := bop_add_id_exists_ann_check S (sg_CS_exists_ann_d S sg) 
|}
end. 



(* sg add_ann *) 

Definition sg_certs_add_ann : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_certificates S -> sg_certificates (with_constant S) 
:= λ S c eqvS sgS,  
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_associative      := Assert_Associative (with_constant S) 
; sg_congruence       := Assert_Bop_Congruence (with_constant S) 
; sg_commutative_d    := bop_add_ann_commutative_check S (sg_commutative_d S sgS) 
; sg_selective_d      := bop_add_ann_selective_check S (sg_selective_d S sgS) 
; sg_is_left_d        := bop_add_ann_not_is_left_check S c 
                            (certify_nontrivial_witness S (eqv_nontrivial S eqvS))
; sg_is_right_d       := bop_add_ann_not_is_right_check S c 
                            (certify_nontrivial_witness S (eqv_nontrivial S eqvS))
; sg_idempotent_d     := bop_add_ann_idempotent_check S (sg_idempotent_d S sgS) 
; sg_exists_id_d      := bop_add_ann_exists_id_check S (sg_exists_id_d S sgS)
; sg_exists_ann_d     := Certify_Exists_Ann (with_constant S) (inl S c) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (with_constant S) (inl c, (inr s, inr (f s))) 
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (with_constant S) (inl c, (inr s, inr (f s))) 
; sg_left_constant_d  := Certify_Not_Left_Constant (with_constant S) (inr s, (inr s, inl c))
; sg_right_constant_d := Certify_Not_Right_Constant (with_constant S) (inr s, (inr s, inl c))
; sg_anti_left_d      := Certify_Not_Anti_Left (with_constant S) (inl c, inr s) 
; sg_anti_right_d     := Certify_Not_Anti_Right (with_constant S) (inl c, inr s) 
|}
end. 

Definition sg_C_certs_add_ann : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_C_certificates S -> sg_C_certificates (with_constant S) 
:= λ S c eqvS sgS,  
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_C_associative   := Assert_Associative (with_constant S) 
; sg_C_congruence    := Assert_Bop_Congruence (with_constant S) 
; sg_C_commutative   := Assert_Commutative (with_constant S) 
; sg_C_selective_d   := bop_add_ann_selective_check S (sg_C_selective_d S sgS) 
; sg_C_idempotent_d  := bop_add_ann_idempotent_check S (sg_C_idempotent_d S sgS) 
; sg_C_exists_id_d   := bop_add_ann_exists_id_check S (sg_C_exists_id_d S sgS)
; sg_C_exists_ann_d  := Certify_Exists_Ann (with_constant S) (inl S c) 
; sg_C_left_cancel_d  := Certify_Not_Left_Cancellative (with_constant S) (inl c, (inr s, inr (f s))) 
; sg_C_right_cancel_d := Certify_Not_Right_Cancellative (with_constant S) (inl c, (inr s, inr (f s))) 
; sg_C_left_constant_d  := Certify_Not_Left_Constant (with_constant S) (inr s, (inr s, inl c))
; sg_C_right_constant_d := Certify_Not_Right_Constant (with_constant S) (inr s, (inr s, inl c))
; sg_C_anti_left_d      := Certify_Not_Anti_Left (with_constant S) (inl c, inr s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (with_constant S) (inl c, inr s) 
|}
end. 


Definition sg_CI_certs_add_ann : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_CI_certificates S -> sg_CI_certificates (with_constant S) 
:= λ S c eqvS sgS,  
let wS := certify_nontrivial_witness S (eqv_nontrivial S eqvS) in 
match wS, certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_CI_associative        := Assert_Associative (with_constant S) 
; sg_CI_congruence         := Assert_Bop_Congruence (with_constant S) 
; sg_CI_commutative        := Assert_Commutative (with_constant S) 
; sg_CI_idempotent         := Assert_Idempotent (with_constant S) 
; sg_CI_selective_d        := bop_add_ann_selective_check S (sg_CI_selective_d S sgS) 
; sg_CI_exists_id_d        := bop_add_ann_exists_id_check S (sg_CI_exists_id_d S sgS)
; sg_CI_exists_ann_d       := Certify_Exists_Ann (with_constant S) (inl S c) 
|}
end. 


Definition sg_CS_certs_add_ann : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_CS_certificates S -> sg_CS_certificates (with_constant S) 
:= λ S c eqvS sg,  
let wS := certify_nontrivial_witness S (eqv_nontrivial S eqvS) in 
match wS, certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_CS_associative   := Assert_Associative (with_constant S) 
; sg_CS_congruence    := Assert_Bop_Congruence (with_constant S) 
; sg_CS_commutative   := Assert_Commutative (with_constant S) 
; sg_CS_selective     := Assert_Selective (with_constant S) 
; sg_CS_exists_id_d   := bop_add_ann_exists_id_check S (sg_CS_exists_id_d S sg)
; sg_CS_exists_ann_d  := Certify_Exists_Ann (with_constant S) (inl S c) 
|}
end. 

(* semigroup sums *) 

Definition sg_certs_left_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_certificates S -> sg_certificates T -> sg_certificates (S + T) 
:= λ S T eS eT cS cT,  
let s := nontrivial_witness S (eqv_nontrivial S eS) in 
let f := nontrivial_negate S (eqv_nontrivial S eS) in 
let t := nontrivial_witness T (eqv_nontrivial T eT) in
let g := nontrivial_negate T (eqv_nontrivial T eT) in  
{|
  sg_associative      := Assert_Associative (S + T)  
; sg_congruence       := Assert_Bop_Congruence (S + T) 
; sg_commutative_d    := check_commutative_sum S T 
                            (sg_commutative_d S cS) 
                            (sg_commutative_d T cT)
; sg_idempotent_d     := check_idempotent_sum S T 
                            (sg_idempotent_d S cS) 
                            (sg_idempotent_d T cT)
; sg_selective_d      := check_selective_sum S T 
                            (sg_selective_d S cS) 
                            (sg_selective_d T cT)
; sg_is_left_d        := Certify_Not_Is_Left (S + T) (inr S t, inl T s) 
; sg_is_right_d       := Certify_Not_Is_Right (S + T) (inl T s, inr S t) 
; sg_exists_id_d      := check_exists_id_left_sum S T (sg_exists_id_d T cT)
; sg_exists_ann_d     := check_exists_ann_left_sum S T (sg_exists_ann_d S cS)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative _ (inl s, (inr t, inr (g t)))
; sg_right_cancel_d   := Certify_Not_Right_Cancellative _ (inl s, (inr t, inr (g t)))
; sg_left_constant_d  := Certify_Not_Left_Constant _ (inr t, (inl s, inl (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant _ (inr t, (inl s, inl (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left _ (inl s, inr t) 
; sg_anti_right_d     := Certify_Not_Anti_Right _ (inl s, inr t) 
|}.

Definition sg_certs_right_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_certificates S -> sg_certificates T -> sg_certificates (S + T) 
:= λ S T eS eT cS cT,  
let s := nontrivial_witness S (eqv_nontrivial S eS) in
let f := nontrivial_negate S (eqv_nontrivial S eS) in  
let t := nontrivial_witness T (eqv_nontrivial T eT) in 
let g := nontrivial_negate T (eqv_nontrivial T eT) in  
{|
  sg_associative   := Assert_Associative (S + T)  
; sg_congruence    := Assert_Bop_Congruence (S + T) 
; sg_commutative_d := check_commutative_sum S T 
                         (sg_commutative_d S cS) 
                         (sg_commutative_d T cT)
; sg_idempotent_d  := check_idempotent_sum S T 
                         (sg_idempotent_d S cS) 
                         (sg_idempotent_d T cT)
; sg_selective_d   := check_selective_sum S T 
                         (sg_selective_d S cS) 
                         (sg_selective_d T cT)
; sg_is_left_d     := Certify_Not_Is_Left (S + T) (inl T s, inr S t) 
; sg_is_right_d    := Certify_Not_Is_Right (S + T) (inr S t, inl T s) 
; sg_exists_id_d   := check_exists_id_right_sum S T (sg_exists_id_d S cS)
; sg_exists_ann_d  := check_exists_ann_right_sum S T (sg_exists_ann_d T cT)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative _ (inr t, (inl s, inl (f s)))
; sg_right_cancel_d   := Certify_Not_Right_Cancellative _ (inr t, (inl s, inl (f s)))
; sg_left_constant_d  := Certify_Not_Left_Constant _ (inl s, (inr t, inr (g t)))
; sg_right_constant_d := Certify_Not_Right_Constant _ (inl s, (inr t, inr (g t)))
; sg_anti_left_d      := Certify_Not_Anti_Left _ (inr t, inl s) 
; sg_anti_right_d     := Certify_Not_Anti_Right _ (inr t, inl s) 
|}.


Definition sg_C_certs_left_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_C_certificates S -> sg_C_certificates T -> sg_C_certificates (S + T) 
:= λ S T eS eT cS cT,  
let s := nontrivial_witness S (eqv_nontrivial S eS) in 
let f := nontrivial_negate S (eqv_nontrivial S eS) in 
let t := nontrivial_witness T (eqv_nontrivial T eT) in
let g := nontrivial_negate T (eqv_nontrivial T eT) in  
{|
  sg_C_associative      := Assert_Associative (S + T)  
; sg_C_congruence       := Assert_Bop_Congruence (S + T) 
; sg_C_commutative      := Assert_Commutative (S + T) 
; sg_C_idempotent_d     := check_idempotent_sum S T 
                            (sg_C_idempotent_d S cS) 
                            (sg_C_idempotent_d T cT)
; sg_C_selective_d      := check_selective_sum S T 
                            (sg_C_selective_d S cS) 
                            (sg_C_selective_d T cT)
; sg_C_exists_id_d      := check_exists_id_left_sum S T (sg_C_exists_id_d T cT)
; sg_C_exists_ann_d     := check_exists_ann_left_sum S T (sg_C_exists_ann_d S cS)
; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative _ (inl s, (inr t, inr (g t)))
; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative _ (inl s, (inr t, inr (g t)))
; sg_C_left_constant_d  := Certify_Not_Left_Constant _ (inr t, (inl s, inl (f s)))
; sg_C_right_constant_d := Certify_Not_Right_Constant _ (inr t, (inl s, inl (f s)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left _ (inl s, inr t) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right _ (inl s, inr t) 
|}.

Definition sg_C_certs_right_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_C_certificates S -> sg_C_certificates T -> sg_C_certificates (S + T) 
:= λ S T eS eT cS cT,  
let s := nontrivial_witness S (eqv_nontrivial S eS) in
let f := nontrivial_negate S (eqv_nontrivial S eS) in  
let t := nontrivial_witness T (eqv_nontrivial T eT) in 
let g := nontrivial_negate T (eqv_nontrivial T eT) in  
{|
  sg_C_associative   := Assert_Associative (S + T)  
; sg_C_congruence    := Assert_Bop_Congruence (S + T) 
; sg_C_commutative      := Assert_Commutative (S + T) 
; sg_C_idempotent_d  := check_idempotent_sum S T 
                         (sg_C_idempotent_d S cS) 
                         (sg_C_idempotent_d T cT)
; sg_C_selective_d   := check_selective_sum S T 
                         (sg_C_selective_d S cS) 
                         (sg_C_selective_d T cT)
; sg_C_exists_id_d   := check_exists_id_right_sum S T (sg_C_exists_id_d S cS)
; sg_C_exists_ann_d  := check_exists_ann_right_sum S T (sg_C_exists_ann_d T cT)
; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative _ (inr t, (inl s, inl (f s)))
; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative _ (inr t, (inl s, inl (f s)))
; sg_C_left_constant_d  := Certify_Not_Left_Constant _ (inl s, (inr t, inr (g t)))
; sg_C_right_constant_d := Certify_Not_Right_Constant _ (inl s, (inr t, inr (g t)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left _ (inr t, inl s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right _ (inr t, inl s) 
|}.

Definition sg_CI_certs_left_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_CI_certificates S -> sg_CI_certificates T -> sg_CI_certificates (S + T) 
:= λ S T eS eT cS cT,  
{|
  sg_CI_associative  := Assert_Associative (S + T)  
; sg_CI_congruence   := Assert_Bop_Congruence (S + T) 
; sg_CI_commutative  := Assert_Commutative (S + T) 
; sg_CI_idempotent   := Assert_Idempotent (S + T) 
; sg_CI_selective_d  := check_selective_sum S T (sg_CI_selective_d S cS) (sg_CI_selective_d T cT)
; sg_CI_exists_id_d  := check_exists_id_left_sum S T (sg_CI_exists_id_d T cT)
; sg_CI_exists_ann_d := check_exists_ann_left_sum S T (sg_CI_exists_ann_d S cS)
|}.

Definition sg_CI_certs_right_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_CI_certificates S -> sg_CI_certificates T -> sg_CI_certificates (S + T) 
:= λ S T eS eT cS cT,  
{|
  sg_CI_associative  := Assert_Associative (S + T)  
; sg_CI_congruence   := Assert_Bop_Congruence (S + T) 
; sg_CI_commutative  := Assert_Commutative (S + T) 
; sg_CI_idempotent   := Assert_Idempotent (S + T) 
; sg_CI_selective_d  := check_selective_sum S T (sg_CI_selective_d S cS) (sg_CI_selective_d T cT)
; sg_CI_exists_id_d  := check_exists_id_right_sum S T (sg_CI_exists_id_d S cS)
; sg_CI_exists_ann_d := check_exists_ann_right_sum S T (sg_CI_exists_ann_d T cT)
|}.


Definition sg_CS_certs_left_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_CS_certificates S -> sg_CS_certificates T -> sg_CS_certificates (S + T) 
:= λ S T eS eT cS cT,  
{|
  sg_CS_associative  := Assert_Associative (S + T)  
; sg_CS_congruence   := Assert_Bop_Congruence (S + T) 
; sg_CS_commutative  := Assert_Commutative (S + T) 
; sg_CS_selective    := Assert_Selective (S + T) 
; sg_CS_exists_id_d  := check_exists_id_left_sum S T (sg_CS_exists_id_d T cT)
; sg_CS_exists_ann_d := check_exists_ann_left_sum S T (sg_CS_exists_ann_d S cS)
|}.

Definition sg_CS_certs_right_sum : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_CS_certificates S -> sg_CS_certificates T -> sg_CS_certificates (S + T) 
:= λ S T eS eT cS cT,  
{|
  sg_CS_associative  := Assert_Associative (S + T)  
; sg_CS_congruence   := Assert_Bop_Congruence (S + T) 
; sg_CS_commutative  := Assert_Commutative (S + T) 
; sg_CS_selective    := Assert_Selective (S + T) 
; sg_CS_exists_id_d  := check_exists_id_right_sum S T (sg_CS_exists_id_d S cS)
; sg_CS_exists_ann_d := check_exists_ann_right_sum S T (sg_CS_exists_ann_d T cT)
|}.


(* semigrou products *) 

Definition sg_certs_product : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_certificates S -> sg_certificates T -> sg_certificates (S * T) 
:= λ S T eS eT cS cT,  
   let wS := eqv_nontrivial S eS in 
   let wT := eqv_nontrivial T eT in 
{|
  sg_associative   := Assert_Associative (S * T)  
; sg_congruence    := Assert_Bop_Congruence (S * T)  
; sg_commutative_d := check_commutative_product S T wS wT 
                         (sg_commutative_d S cS) 
                         (sg_commutative_d T cT)
; sg_selective_d   := check_selective_product S T wS wT 
                         (sg_is_left_d S cS) 
                         (sg_is_left_d T cT)
                         (sg_is_right_d S cS) 
                         (sg_is_right_d T cT)
; sg_is_left_d     := check_is_left_product S T wS wT 
                         (sg_is_left_d S cS) 
                         (sg_is_left_d T cT)
; sg_is_right_d    := check_is_right_product S T wS wT 
                         (sg_is_right_d S cS) 
                         (sg_is_right_d T cT)
; sg_idempotent_d  := check_idempotent_product S T wS wT 
                         (sg_idempotent_d S cS) 
                         (sg_idempotent_d T cT)
; sg_exists_id_d   := check_exists_id_product S T 
                         (sg_exists_id_d S cS) 
                         (sg_exists_id_d T cT)
; sg_exists_ann_d  := check_exists_ann_product S T 
                         (sg_exists_ann_d S cS) 
                         (sg_exists_ann_d T cT)
; sg_left_cancel_d    := check_left_cancellative_product S T wS wT 
                          (sg_left_cancel_d S cS)
                          (sg_left_cancel_d T cT)
; sg_right_cancel_d   := check_right_cancellative_product S T wS wT 
                          (sg_right_cancel_d S cS)
                          (sg_right_cancel_d T cT)
; sg_left_constant_d  := check_left_constant_product S T wS wT 
                          (sg_left_constant_d S cS)
                          (sg_left_constant_d T cT)
; sg_right_constant_d := check_right_constant_product S T wS wT 
                          (sg_right_constant_d S cS)
                          (sg_right_constant_d T cT)
; sg_anti_left_d      := check_anti_left_product S T 
                         (sg_anti_left_d S cS) 
                         (sg_anti_left_d T cT)
; sg_anti_right_d     := check_anti_right_product S T 
                         (sg_anti_right_d S cS) 
                         (sg_anti_right_d T cT)
|}.


Definition sg_CK_certs_product : ∀ (S T : Type),  eqv_certificates S -> eqv_certificates T -> sg_CK_certificates S -> sg_CK_certificates T -> sg_CK_certificates (S * T) 
:= λ S T eS eT cS cT,  
   let wS := eqv_nontrivial S eS in 
   let wT := eqv_nontrivial T eT in 
{|
  sg_CK_associative   := Assert_Associative (S * T)  
; sg_CK_congruence    := Assert_Bop_Congruence (S * T)  
; sg_CK_commutative   := Assert_Commutative (S * T)  
; sg_CK_left_cancel   := Assert_Left_Cancellative (S * T)  
; sg_CK_exists_id_d   := check_exists_id_product S T 
                         (sg_CK_exists_id_d S cS) 
                         (sg_CK_exists_id_d T cT)
; sg_CK_anti_left_d   := check_anti_left_product S T 
                         (sg_CK_anti_left_d S cS) 
                         (sg_CK_anti_left_d T cT)
; sg_CK_anti_right_d  := check_anti_right_product S T 
                         (sg_CK_anti_right_d S cS) 
                         (sg_CK_anti_right_d T cT)


|}.

Definition sg_C_certs_product : ∀ (S T : Type),  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) -> eqv_certificates S -> eqv_certificates T -> sg_C_certificates S -> sg_C_certificates T -> sg_C_certificates (S * T) 
:= λ S T rS rT bS bT eS eT cS cT,  
let wS := eqv_nontrivial S eS in 
let wT := eqv_nontrivial T eT in 
let s := nontrivial_witness S wS in
let f := nontrivial_negate S wS in  
let t := nontrivial_witness T wT in 
let g := nontrivial_negate T wT in  
{|
  sg_C_associative   := Assert_Associative (S * T)  
; sg_C_congruence    := Assert_Bop_Congruence (S * T)  
; sg_C_commutative   := Assert_Commutative (S * T)  
; sg_C_selective_d   := check_selective_product S T wS wT 
                         (Certify_Not_Is_Left S (cef_commutative_implies_not_is_left S rS bS s f))
                         (Certify_Not_Is_Left T (cef_commutative_implies_not_is_left T rT bT t g))
                         (Certify_Not_Is_Right S (cef_commutative_implies_not_is_right S rS bS s f))
                         (Certify_Not_Is_Right T (cef_commutative_implies_not_is_right T rT bT t g))
; sg_C_idempotent_d  := check_idempotent_product S T wS wT 
                         (sg_C_idempotent_d S cS) 
                         (sg_C_idempotent_d T cT)
; sg_C_exists_id_d   := check_exists_id_product S T 
                         (sg_C_exists_id_d S cS) 
                         (sg_C_exists_id_d T cT)
; sg_C_exists_ann_d  := check_exists_ann_product S T 
                         (sg_C_exists_ann_d S cS) 
                         (sg_C_exists_ann_d T cT)
; sg_C_left_cancel_d    := check_left_cancellative_product S T wS wT 
                          (sg_C_left_cancel_d S cS)
                          (sg_C_left_cancel_d T cT)
; sg_C_right_cancel_d   := check_right_cancellative_product S T wS wT 
                          (sg_C_right_cancel_d S cS)
                          (sg_C_right_cancel_d T cT)
; sg_C_left_constant_d  := check_left_constant_product S T wS wT 
                          (sg_C_left_constant_d S cS)
                          (sg_C_left_constant_d T cT)
; sg_C_right_constant_d := check_right_constant_product S T wS wT 
                          (sg_C_right_constant_d S cS)
                          (sg_C_right_constant_d T cT)
; sg_C_anti_left_d      := check_anti_left_product S T 
                         (sg_C_anti_left_d S cS) 
                         (sg_C_anti_left_d T cT)
; sg_C_anti_right_d     := check_anti_right_product S T 
                         (sg_C_anti_right_d S cS) 
                         (sg_C_anti_right_d T cT)

|}.

Definition sg_CI_certs_product : ∀ (S T : Type),  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) -> eqv_certificates S -> eqv_certificates T -> sg_CI_certificates S -> sg_CI_certificates T -> sg_CI_certificates (S * T) 
:= λ S T rS rT bS bT eS eT cS cT,  
let wS := eqv_nontrivial S eS in 
let wT := eqv_nontrivial T eT in 
let s := nontrivial_witness S wS in
let f := nontrivial_negate S wS in  
let t := nontrivial_witness T wT in 
let g := nontrivial_negate T wT in  
{|
  sg_CI_associative   := Assert_Associative (S * T)  
; sg_CI_congruence    := Assert_Bop_Congruence (S * T)  
; sg_CI_commutative   := Assert_Commutative (S * T)  
; sg_CI_idempotent  := Assert_Idempotent (S * T)  
; sg_CI_selective_d   := check_selective_product S T wS wT 
                         (Certify_Not_Is_Left S (cef_commutative_implies_not_is_left S rS bS s f))
                         (Certify_Not_Is_Left T (cef_commutative_implies_not_is_left T rT bT t g))
                         (Certify_Not_Is_Right S (cef_commutative_implies_not_is_right S rS bS s f))
                         (Certify_Not_Is_Right T (cef_commutative_implies_not_is_right T rT bT t g))
; sg_CI_exists_id_d   := check_exists_id_product S T 
                         (sg_CI_exists_id_d S cS) 
                         (sg_CI_exists_id_d T cT)
; sg_CI_exists_ann_d  := check_exists_ann_product S T 
                         (sg_CI_exists_ann_d S cS) 
                         (sg_CI_exists_ann_d T cT)
|}.

(* semigroup lexicographic *) 

Definition sg_certs_llex : ∀ (S T : Type),  
        brel S -> binary_op S -> 
        eqv_certificates S -> 
        eqv_certificates T -> 
        sg_CS_certificates S -> 
        sg_certificates T -> sg_certificates (S * T)
:= λ S T rS bS eS eT cS cT,  
let wS := eqv_nontrivial S eS in 
let wT := eqv_nontrivial T eT in 
let s := nontrivial_witness S wS in
let t := nontrivial_witness T wT in
let f := nontrivial_negate S wS in  
let g := nontrivial_negate T wT in  
{|
  sg_associative      := Assert_Associative (S * T)  
; sg_congruence       := Assert_Bop_Congruence (S * T)  
; sg_commutative_d    := check_commutative_llex S T wS (sg_commutative_d T cT)
; sg_selective_d      := check_selective_llex S T wS (sg_selective_d T cT)
; sg_idempotent_d     := check_idempotent_llex S T wS (sg_idempotent_d T cT)
; sg_exists_id_d      := check_exists_id_llex S T (sg_CS_exists_id_d S cS) (sg_exists_id_d T cT)
; sg_exists_ann_d     := check_exists_ann_llex S T (sg_CS_exists_ann_d S cS) (sg_exists_ann_d T cT)

; sg_is_left_d        := Certify_Not_Is_Left _ (cef_bop_llex_not_is_left S T rS bS s f t)
; sg_is_right_d       := Certify_Not_Is_Right _ (cef_bop_llex_not_is_right S T rS bS s f t)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative _ (cef_bop_llex_not_cancellative S T rS bS s f t g)
; sg_right_cancel_d   := Certify_Not_Right_Cancellative _ (cef_bop_llex_not_cancellative S T rS bS s f t g)
; sg_left_constant_d  := Certify_Not_Left_Constant _ (cef_bop_llex_not_constant S T rS bS s f t g)
; sg_right_constant_d := Certify_Not_Right_Constant _ (cef_bop_llex_not_constant S T rS bS s f t g)
; sg_anti_left_d      := Certify_Not_Anti_Left _ (cef_bop_llex_not_anti_left S T rS bS s f t)
; sg_anti_right_d     := Certify_Not_Anti_Right _ (cef_bop_llex_not_anti_right S T rS bS s f t)
|}. 

Definition sg_C_certs_llex : ∀ (S T : Type) (rS : brel S) (bS : binary_op S), 
        eqv_certificates S -> eqv_certificates T -> sg_CS_certificates S -> sg_C_certificates T -> sg_C_certificates (S * T) 
:= λ S T rS bS eS eT cS cT,  
let wS := eqv_nontrivial S eS in 
let wT := eqv_nontrivial T eT in 
let s := nontrivial_witness S wS in
let t := nontrivial_witness T wT in
let f := nontrivial_negate S wS in  
let g := nontrivial_negate T wT in  
{|
  sg_C_associative   := Assert_Associative (S * T)  
; sg_C_congruence    := Assert_Bop_Congruence (S * T)  
; sg_C_commutative   := Assert_Commutative (S * T)  
; sg_C_selective_d   := check_selective_llex S T wS (sg_C_selective_d T cT)
; sg_C_idempotent_d  := check_idempotent_llex S T wS (sg_C_idempotent_d T cT)
; sg_C_exists_id_d   := check_exists_id_llex S T (sg_CS_exists_id_d S cS) (sg_C_exists_id_d T cT)
; sg_C_exists_ann_d  := check_exists_ann_llex S T (sg_CS_exists_ann_d S cS) (sg_C_exists_ann_d T cT)
; sg_C_left_cancel_d    := Certify_Not_Left_Cancellative _ (cef_bop_llex_not_cancellative S T rS bS s f t g)
; sg_C_right_cancel_d   := Certify_Not_Right_Cancellative _ (cef_bop_llex_not_cancellative S T rS bS s f t g)
; sg_C_left_constant_d  := Certify_Not_Left_Constant _ (cef_bop_llex_not_constant S T rS bS s f t g)
; sg_C_right_constant_d := Certify_Not_Right_Constant _ (cef_bop_llex_not_constant S T rS bS s f t g)
; sg_C_anti_left_d      := Certify_Not_Anti_Left _ (cef_bop_llex_not_anti_left S T rS bS s f t)                            
; sg_C_anti_right_d     := Certify_Not_Anti_Right _ (cef_bop_llex_not_anti_right S T rS bS s f t)
|}.

Definition sg_CI_certs_llex : ∀ (S T : Type) (rS : brel S) (bS : binary_op S), 
        eqv_certificates S -> eqv_certificates T -> sg_CS_certificates S -> sg_CI_certificates T -> sg_CI_certificates (S * T) 
:= λ S T rS bS eS eT cS cT,  
{|
  sg_CI_associative   := Assert_Associative (S * T)  
; sg_CI_congruence    := Assert_Bop_Congruence (S * T)  
; sg_CI_commutative   := Assert_Commutative (S * T)  
; sg_CI_idempotent    := Assert_Idempotent (S * T)  
; sg_CI_selective_d   := check_selective_llex S T (eqv_nontrivial S eS) (sg_CI_selective_d T cT)
; sg_CI_exists_id_d   := check_exists_id_llex S T (sg_CS_exists_id_d S cS) (sg_CI_exists_id_d T cT)
; sg_CI_exists_ann_d  := check_exists_ann_llex S T (sg_CS_exists_ann_d S cS) (sg_CI_exists_ann_d T cT)
|}.

Definition sg_CS_certs_llex : ∀ (S T : Type) (rS : brel S) (bS : binary_op S), 
        eqv_certificates S -> eqv_certificates T -> sg_CS_certificates S -> sg_CS_certificates T -> sg_CS_certificates (S * T) 
:= λ S T rS bS eS eT cS cT,  
{|
  sg_CS_associative   := Assert_Associative (S * T)  
; sg_CS_congruence    := Assert_Bop_Congruence (S * T)  
; sg_CS_commutative   := Assert_Commutative (S * T)  
; sg_CS_selective     := Assert_Selective (S * T)  
; sg_CS_exists_id_d   := check_exists_id_llex S T (sg_CS_exists_id_d S cS) (sg_CS_exists_id_d T cT)
; sg_CS_exists_ann_d  := check_exists_ann_llex S T (sg_CS_exists_ann_d S cS) (sg_CS_exists_ann_d T cT)
|}.



Definition sg_CI_certs_union : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_CI_certificates (with_constant (finite_set S))
:= λ S c eqvS, 
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_CI_associative   := Assert_Associative (with_constant (finite_set S)) 
; sg_CI_congruence    := Assert_Bop_Congruence (with_constant (finite_set S))
; sg_CI_commutative   := Assert_Commutative (with_constant (finite_set S)) 
; sg_CI_idempotent    := Assert_Idempotent (with_constant (finite_set S)) 
; sg_CI_selective_d   := Certify_Not_Selective (with_constant (finite_set S)) 
                           (inr _ (s :: nil), inr _ ((f s) :: nil)) 
; sg_CI_exists_id_d   := Certify_Exists_Id (with_constant (finite_set S)) (inr _ nil) 
; sg_CI_exists_ann_d  := Certify_Exists_Ann (with_constant (finite_set S)) (inl _ c) 
|}
end. 



Definition sg_CI_certs_intersect : ∀ (S : Type),  cas_constant -> eqv_certificates S -> sg_CI_certificates (with_constant (finite_set S))
:= λ S c eqvS, 
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_negate S (eqv_nontrivial S eqvS) 
with 
| Certify_Witness _ s, Certify_Negate _ f =>  
{|
  sg_CI_associative   := Assert_Associative (with_constant (finite_set S)) 
; sg_CI_congruence    := Assert_Bop_Congruence (with_constant (finite_set S))
; sg_CI_commutative   := Assert_Commutative (with_constant (finite_set S)) 
; sg_CI_idempotent    := Assert_Idempotent (with_constant (finite_set S)) 
; sg_CI_selective_d   := Certify_Not_Selective (with_constant (finite_set S)) 
                           (inr _ (s :: nil), inr _ ((f s) :: nil)) 
; sg_CI_exists_id_d   := Certify_Exists_Id (with_constant (finite_set S)) (inl _ c) 
; sg_CI_exists_ann_d  := Certify_Exists_Ann (with_constant (finite_set S)) (inr _ nil) 
|}
end. 

(*********************************************** *) 












Definition bs_certs_add_zero : 
  ∀ (S : Type), eqv_certificates S -> bs_certificates S -> bs_certificates (with_constant S) 
:= λ S eqvS pS, 
match certify_nontrivial_witness S (eqv_nontrivial S eqvS) with 
| Certify_Witness _ s =>  
{|
  bs_left_distributive_d    := 
     bops_add_zero_left_distributive_check S (bs_left_distributive_d S pS) 
; bs_right_distributive_d   := 
     bops_add_zero_right_distributive_check S (bs_right_distributive_d S pS) 

; bs_left_left_absorptive_d      := 
     bops_add_zero_left_left_absorptive_check S s (bs_left_left_absorptive_d S pS)
; bs_left_right_absorptive_d      := 
     bops_add_zero_left_right_absorptive_check S s (bs_left_right_absorptive_d S pS)
; bs_right_left_absorptive_d     := 
     bops_add_zero_right_left_absorptive_check S s (bs_right_left_absorptive_d S pS)
; bs_right_right_absorptive_d     := 
     bops_add_zero_right_right_absorptive_check S s (bs_right_right_absorptive_d S pS)

; bs_plus_id_is_times_ann_d :=  Certify_Plus_Id_Equals_Times_Ann (with_constant S) 
; bs_times_id_is_plus_ann_d :=  
  match bs_times_id_is_plus_ann_d S pS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann _ => Certify_Times_Id_Equals_Plus_Ann (with_constant S) 
  | Certify_Not_Times_Id_Equals_Plus_Ann _ => Certify_Not_Times_Id_Equals_Plus_Ann (with_constant S) 
  end 
|}
end. 


Definition bs_certs_add_one : 
  ∀ (S : Type) (c : cas_constant),
     eqv_certificates S -> sg_certificates S -> bs_certificates S -> 
        bs_certificates (with_constant S) 
:= λ S c eqvS ppS pS, 
{|
  bs_left_distributive_d      :=  bops_add_one_left_distributive_check S c 
                                      (sg_idempotent_d S ppS) 
                                      (bs_left_left_absorptive_d S pS) 
                                      (bs_right_left_absorptive_d S pS) 
                                      (bs_left_distributive_d S pS) 
; bs_right_distributive_d     := bops_add_one_right_distributive_check S c 
                                      (sg_idempotent_d S ppS) 
                                      (bs_left_right_absorptive_d S pS) 
                                      (bs_right_right_absorptive_d S pS) 
                                      (bs_right_distributive_d S pS) 
; bs_left_left_absorptive_d   := bops_add_one_left_left_absorptive_check S c 
                                      (sg_idempotent_d S ppS) 
                                      (bs_left_left_absorptive_d S pS) 
; bs_left_right_absorptive_d  := bops_add_one_left_right_absorptive_check S c 
                                      (sg_idempotent_d S ppS) 
                                      (bs_left_right_absorptive_d S pS) 
; bs_right_left_absorptive_d  := bops_add_one_right_left_absorptive_check S c 
                                      (sg_idempotent_d S ppS) 
                                      (bs_right_left_absorptive_d S pS) 
; bs_right_right_absorptive_d := bops_add_one_right_right_absorptive_check S c 
                                      (sg_idempotent_d S ppS) 
                                      (bs_right_right_absorptive_d S pS) 
; bs_plus_id_is_times_ann_d := 
  match bs_plus_id_is_times_ann_d S pS with (*** NB : type coer ***) 
  | Certify_Plus_Id_Equals_Times_Ann _ => Certify_Plus_Id_Equals_Times_Ann (with_constant S) 
  | Certify_Not_Plus_Id_Equals_Times_Ann _ => Certify_Not_Plus_Id_Equals_Times_Ann (with_constant S) 
  end 
; bs_times_id_is_plus_ann_d :=  Certify_Times_Id_Equals_Plus_Ann (with_constant S) 

|}. 


Definition bs_certs_product : 
  ∀ (S T: Type), 
        eqv_certificates S -> eqv_certificates T -> bs_certificates S -> bs_certificates T -> bs_certificates (S * T) 
:= λ S T eqvS eqvT bsS bsT, 
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_witness T (eqv_nontrivial T eqvT)
with 
| Certify_Witness _ s, Certify_Witness _ t => 
{|
  bs_left_distributive_d      := bop_product_left_distributive_check S T 
                                     (eqv_nontrivial S eqvS)  
                                     (eqv_nontrivial T eqvT)  
                                     (bs_left_distributive_d S bsS)
                                     (bs_left_distributive_d T bsT)
; bs_right_distributive_d     := bop_product_right_distributive_check S T 
                                     (eqv_nontrivial S eqvS)  
                                     (eqv_nontrivial T eqvT)  
                                     (bs_right_distributive_d S bsS)
                                     (bs_right_distributive_d T bsT)
; bs_plus_id_is_times_ann_d   := bop_product_plus_id_is_times_ann_check S T 
                                     (bs_plus_id_is_times_ann_d S bsS)
                                     (bs_plus_id_is_times_ann_d T bsT)
; bs_times_id_is_plus_ann_d   := bop_product_times_id_equals_plus_ann_check S T 
                                     (bs_times_id_is_plus_ann_d S bsS)
                                     (bs_times_id_is_plus_ann_d T bsT)
; bs_left_left_absorptive_d   := bop_product_left_left_absorptive_check S T s t 
                                     (bs_left_left_absorptive_d S bsS)
                                     (bs_left_left_absorptive_d T bsT)
; bs_left_right_absorptive_d  := bop_product_left_right_absorptive_check S T s t 
                                     (bs_left_right_absorptive_d S bsS)
                                     (bs_left_right_absorptive_d T bsT)
; bs_right_left_absorptive_d  := bop_product_right_left_absorptive_check S T s t
                                     (bs_right_left_absorptive_d S bsS)
                                     (bs_right_left_absorptive_d T bsT)
; bs_right_right_absorptive_d := bop_product_right_right_absorptive_check S T s t
                                     (bs_right_right_absorptive_d S bsS)
                                     (bs_right_right_absorptive_d T bsT)

|}
end. 





Definition bs_certs_and_or : bs_certificates bool := 
  {| 
     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 


Definition bs_certs_or_and : bs_certificates bool := 
  {| 
     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 


Definition bs_certs_max_min : bs_certificates nat := 
  {| 

     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Not_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 

Definition bs_certs_min_max : bs_certificates nat := 
  {| 
     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Not_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 


Definition bs_certs_min_plus : bs_certificates nat := 
  {| 
     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Not_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 


Definition bs_certs_max_plus : bs_certificates nat := 
  {| 
     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Not_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Not_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Not_Left_Left_Absorptive _ (0, 1) 
   ; bs_left_right_absorptive_d  := Certify_Not_Left_Right_Absorptive _ (0, 1) 
   ; bs_right_left_absorptive_d  := Certify_Not_Right_Left_Absorptive _ (0, 1) 
   ; bs_right_right_absorptive_d := Certify_Not_Right_Right_Absorptive _ (0, 1) 
  |}. 



Definition bs_certs_union_intersect : ∀ (S : Type), bs_certificates S 
:= λ S, 
  {| 

     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 


Definition bs_certs_intersect_union : ∀ (S : Type), bs_certificates S 
:= λ S, 
  {| 

     bs_left_distributive_d      := Certify_Left_Distributive _ 
   ; bs_right_distributive_d     := Certify_Right_Distributive _ 
   ; bs_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann _ 
   ; bs_times_id_is_plus_ann_d   := Certify_Times_Id_Equals_Plus_Ann _ 
   ; bs_left_left_absorptive_d   := Certify_Left_Left_Absorptive _ 
   ; bs_left_right_absorptive_d  := Certify_Left_Right_Absorptive _ 
   ; bs_right_left_absorptive_d  := Certify_Right_Left_Absorptive _ 
   ; bs_right_right_absorptive_d := Certify_Right_Right_Absorptive _ 
  |}. 


Definition bs_certs_llex_product : 
  ∀ (S T: Type)
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T),
    eqv_certificates S -> 
    eqv_certificates T -> 
    sg_certificates S  → 
    sg_certificates T → 
    bs_certificates S -> 
    bs_certificates T -> bs_certificates (S * T) 
:= λ S T rS rT addS addT mulT eqvS eqvT sg_timesS sg_timesT bsS bsT, 
match certify_nontrivial_witness S (eqv_nontrivial S eqvS), 
      certify_nontrivial_witness T (eqv_nontrivial T eqvT)
with 
| Certify_Witness _ s, Certify_Witness _ t => 
{|
  bs_left_distributive_d     := bops_llex_product_left_distributive_check S T 
                                     rS rT addS addT mulT 
                                     (eqv_nontrivial S eqvS)  
                                     (eqv_nontrivial T eqvT)  
                                     (sg_left_cancel_d S sg_timesS)
                                     (sg_left_constant_d T sg_timesT) 
                                     (bs_left_distributive_d S bsS)
                                     (bs_left_distributive_d T bsT)
; bs_right_distributive_d    := bops_llex_product_right_distributive_check S T 
                                     rS rT addS addT mulT 
                                     (eqv_nontrivial S eqvS)  
                                     (eqv_nontrivial T eqvT)  
                                     (sg_right_cancel_d S sg_timesS)
                                     (sg_right_constant_d T sg_timesT) 
                                     (bs_right_distributive_d S bsS)
                                     (bs_right_distributive_d T bsT)
; bs_plus_id_is_times_ann_d := bops_llex_product_plus_id_is_times_ann_check S T 
                                     (bs_plus_id_is_times_ann_d S bsS)
                                     (bs_plus_id_is_times_ann_d T bsT)
; bs_times_id_is_plus_ann_d := bops_llex_product_times_id_equals_plus_ann_check S T 
                                     (bs_times_id_is_plus_ann_d S bsS)
                                     (bs_times_id_is_plus_ann_d T bsT)
; bs_left_left_absorptive_d := bops_llex_product_left_left_absorptive_check S T t 
                                     (bs_left_left_absorptive_d S bsS)
                                     (bs_left_left_absorptive_d T bsT) 
                                     (sg_anti_left_d S sg_timesS) 
; bs_left_right_absorptive_d := bops_llex_product_left_right_absorptive_check S T t 
                                     (bs_left_right_absorptive_d S bsS)
                                     (bs_left_right_absorptive_d T bsT) 
                                     (sg_anti_right_d S sg_timesS)
; bs_right_left_absorptive_d := bops_llex_product_right_left_absorptive_check S T t 
                                     (bs_right_left_absorptive_d S bsS)
                                     (bs_right_left_absorptive_d T bsT) 
                                     (sg_anti_left_d S sg_timesS)  
; bs_right_right_absorptive_d   := bops_llex_product_right_right_absorptive_check S T t
                                     (bs_right_right_absorptive_d S bsS)
                                     (bs_right_right_absorptive_d T bsT)
                                     (sg_anti_right_d S sg_timesS) 

|}
end. 




