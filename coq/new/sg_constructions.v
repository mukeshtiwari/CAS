Require Import Coq.Arith.Arith.
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.data.
Require Import CAS.coq.new.signatures.
Require Import CAS.coq.new.ast.

Open Scope nat.

Definition eqv_eq_nat : eqv (S := nat)
:= {| 
      eqv_eq    := brel_eq_nat 
    ; eqv_witness := 0
    ; eqv_new := S
    ; eqv_data  := λ n, DATA_nat n 
    ; eqv_rep   := λ b, b
    ; eqv_ast   := Ast_eqv_nat
   |}. 

Definition brel_constant : brel cas_constant
  := λ  x y, true. (* all constants equal! *)



Definition eqv_product : ∀ {S T : Type},  @eqv S -> @eqv T -> @eqv (S * T)
:= λ {S T} eqvS eqvT,
  let eqS := eqv_eq eqvS in
  let eqT := eqv_eq eqvT in
  let s   := eqv_witness eqvS in
  let f   := eqv_new eqvS in  
  let t   := eqv_witness eqvT in
  let g   := eqv_new eqvT in    
  let r   := brel_product eqS eqT in 
   {| 
     eqv_eq       := r
    ; eqv_witness := (s, t)
    ; eqv_new     := λ (p : S * T), let (x, y) := p in (f x, y)
    ; eqv_data          := λ p, DATA_pair (eqv_data eqvS (fst p), eqv_data eqvT (snd p))
    ; eqv_rep           := λ p, (eqv_rep eqvS (fst p), eqv_rep eqvT (snd p))
    ; eqv_ast  := Ast_eqv_product (eqv_ast eqvS, eqv_ast eqvT)
   |}. 


Definition sg_plus : @sg nat
:= {| 
     sg_eq  := eqv_eq_nat 
   ; sg_bop := bop_plus
   ; sg_id  := Some 0
   ; sg_ann := None
   ; sg_ast := Ast_sg_plus 
   |}. 


Definition sg_times : @sg nat
:= {| 
     sg_eq  := eqv_eq_nat 
   ; sg_bop := bop_times 
   ; sg_id  := Some 1
   ; sg_ann := Some 0
   ; sg_ast := Ast_sg_times
  |}.


Definition sg_min : @sg nat
:= {| 
     sg_eq  := eqv_eq_nat 
   ; sg_bop := bop_min
   ; sg_id  := None
   ; sg_ann := Some 0
   ; sg_ast := Ast_sg_min
   |}. 

Definition sg_max : @sg nat
:= {| 
     sg_eq  := eqv_eq_nat 
   ; sg_bop := bop_max
   ; sg_id  := Some 0
   ; sg_ann := None
   ; sg_ast := Ast_sg_max
   |}. 


Definition eqv_add_constant : ∀ {S : Type},  @eqv S -> cas_constant -> @eqv (cas_constant + S)
  := λ {S} eqvS c,
  let s  := eqv_witness eqvS in
  let f  := eqv_new eqvS in
   {| 
      eqv_eq       := brel_sum brel_constant (eqv_eq eqvS) 
    ; eqv_witness := inl c 
    ; eqv_new     := (λ (d : cas_constant + S), match d with | inl _ => inr (eqv_witness eqvS) | inr _ => inl c end) 
    ; eqv_data    := λ d, (match d with inl s => DATA_inl(DATA_constant s) | inr a => DATA_inr (eqv_data eqvS a) end)
    ; eqv_rep     := λ d, (match d with inl s => inl _ s  | inr s => inr _ (eqv_rep eqvS s) end )
    ; eqv_ast     := Ast_eqv_add_constant (c, eqv_ast eqvS)
   |}. 


Definition sg_add_id: ∀ {S : Type},  cas_constant -> @sg S -> @sg (with_constant S)
:= λ {S} c sgS, 
   {| 
     sg_eq     := eqv_add_constant (sg_eq sgS) c 
   ; sg_bop    := bop_add_id (sg_bop sgS) c
   ; sg_id     := Some (inl c) 
   ; sg_ann    := (match sg_ann sgS with None => None | Some ann => (Some (inr ann)) end)
   ; sg_ast    := Ast_sg_add_id (c, sg_ast sgS)
   |}. 


Definition sg_add_ann:  ∀ {S : Type},  cas_constant -> @sg S -> @sg (with_constant S)
:= λ {S} c sgS, 
   {| 
     sg_eq      := eqv_add_constant (sg_eq sgS) c 
   ; sg_bop     := bop_add_ann (sg_bop sgS) c
   ; sg_id      := (match sg_id sgS with None => None | Some id => (Some (inr id)) end)
   ; sg_ann     := Some (inl c)                                  
   ; sg_ast     := Ast_sg_add_ann (c, sg_ast sgS)
   |}. 


Definition sg_product : ∀ {S T : Type},  @sg S -> @sg T -> @sg (S * T)
:= λ {S T} sgS sgT, 
   {| 
       sg_eq     := eqv_product (sg_eq sgS) (sg_eq sgT) 
     ; sg_bop    := bop_product (sg_bop sgS) (sg_bop sgT)
     ; sg_id     := (match sg_id sgS, sg_id sgT with
                     | Some idS, Some idT => Some(idS, idT)
                     | _, _ => None                                 
                    end)
     ; sg_ann    := (match sg_ann sgS, sg_ann sgT with
                     | Some annS, Some annT => Some(annS, annT)
                     | _, _ => None                                 
                    end)
     ; sg_ast    := Ast_sg_product (sg_ast sgS, sg_ast sgT)
   |}. 



Definition sg_llex : ∀ {S T : Type},  @sg S -> @sg T -> @sg (S * T)
:= λ {S T} sgS sgT, 
   {| 
     sg_eq           := eqv_product (sg_eq sgS) (sg_eq sgT) 
   ; sg_bop          := bop_llex (eqv_eq (sg_eq sgS)) (sg_bop sgS) (sg_bop sgT) 
     ; sg_id     := (match sg_id sgS, sg_id sgT with
                     | Some idS, Some idT => Some(idS, idT)
                     | _, _ => None                                 
                    end)
     ; sg_ann    := (match sg_ann sgS, sg_ann sgT with
                     | Some annS, Some annT => Some(annS, annT)
                     | _, _ => None                                 
                    end)
   ; sg_ast   := Ast_sg_llex (sg_ast sgS, sg_ast sgT)
   |}. 
