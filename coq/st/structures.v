Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.tr.structures.

Require Import CAS.coq.st.properties.

(* SLT = Semigroup with a Left Transform 

Comparison to bi-semigroups (bs)

For bs, 0-stability means id(x) = ann(+), so there is no point in going around loops. 
Note this implies absorption: 
    a (+) (a (x) b) = a (x) (id (+) b) = a (x) id = a. 
However, this kind of argument does not work for slt. 
slt_absorptive means 
    for all l, s, s = s (+) (l |> s). 
This cannot be derived from properties of ann(+), etc. 
We do want to know if there exists ann(+). But note that it makes no
sence for this to be an id of the multiplicative component, 
   "l |> ann(+) = l" <<< this is a type error, l has type L, not S. 

We still want to know if the id(+) acts as an slt-annihilator. 
That is, if 
   for all l, l |> id(+) = id(+). 

What condition do we need to guarantee that an slt will terminate 
using the iterative algorithm? 

    A^<0> = I   (so need id(+) and ann(+) to build this matrix) 
    A^<k+1> = (A |> A^<k>) (+) I 

    where 

    (A |> B)[i,j] = (+)_q A[i, q] |> B[q, j]. 

Definition.  The left-weight lw(p) of a path p is defined as

lw([]) = ann(+) 
lw((i, j) p) = A[i,j] |> lw(p) 


Claim : A^<k>[i,j] = the best left-weight for all paths from i to j with at most k arcs. 
Proof : induction. 

Definition. p |> s. 

   [] |> s = s 
   ((i, j) p) |> s = A[i,j] |> (p |> s)

Note that lw(p1 p2) = p1 |> lw(p2). 

How can we eliminate loops?   Suppose p2 is a loop and 

    p = p1 p2 p3 

    lw(p) = lw(p1 p2 p3) = p1 |> p2 |> lw(p3) 
    
    now,  

    (p1 |> p2 |> lw(p3)) (+) (p1 |> lw(p3)) 
    = (dist) 
    p1 |> (p2 |> lw(p3) (+) lw(p3))  
    = {by absorption: for all l, s, s = s (+) (l |> s)} 
    p1 |> lw(p3)
    = lw(p1 p3)

So, we need absorption! 

 *)

Section ACAS.
  
Record slt_proofs {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_slt_distributive_d 
    : slt_distributive_decidable r add ltr
; A_slt_absorptive_d 
    : slt_absorptive_decidable r add ltr
; A_slt_strictly_absorptive_d 
  : slt_strictly_absorptive_decidable r add ltr  
}.



Record left_dioid_proofs {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_dioid_distributive : slt_distributive r add ltr
; A_left_dioid_absorptive : slt_absorptive r add ltr                                               
; A_left_dioid_strictly_absorptive_d : 
    slt_strictly_absorptive_decidable r add ltr 
}.


Record left_semiring_proofs {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_semiring_distributive  : slt_distributive r add ltr
; A_left_semiring_not_absorptive : slt_not_absorptive r add ltr                                               
}.


Record A_slt {L S : Type} :=
{
  A_slt_carrier        : A_eqv S
; A_slt_label          : A_eqv L
; A_slt_plus           : binary_op S                                               
; A_slt_trans          : ltr_type L S (* L -> (S -> S) *)
; A_slt_plus_proofs    : sg_proofs S (A_eqv_eq S A_slt_carrier) A_slt_plus                                 
; A_slt_trans_proofs   :  left_transform_proofs L S 
                            (A_eqv_eq S A_slt_carrier) 
                            (A_eqv_eq L A_slt_label)  
                            A_slt_trans
; A_slt_exists_plus_ann_d : bop_exists_ann_decidable S 
                            (A_eqv_eq S A_slt_carrier) 
                            A_slt_plus                                 
; A_slt_id_ann_proofs_d  : slt_exists_id_ann_decidable 
                            (A_eqv_eq S A_slt_carrier) 
                            A_slt_plus  
                            A_slt_trans                        
; A_slt_proofs : slt_proofs 
                  (A_eqv_eq S A_slt_carrier) 
                  A_slt_plus 
                  A_slt_trans                                  
; A_slt_ast : cas_lstr_ast
}.






Record A_selective_left_dioid {L S : Type} :=
{
  A_selective_left_dioid_carrier      : A_eqv S
; A_selective_left_dioid_label        : A_eqv L
; A_selective_left_dioid_plus         : binary_op S                                               
; A_selective_left_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
; A_selective_left_dioid_plus_proofs  : sg_CS_proofs S 
                                        (A_eqv_eq S A_selective_left_dioid_carrier) 
                                        A_selective_left_dioid_plus 
; A_selective_left_dioid_trans_proofs : left_transform_proofs L S
                                        (A_eqv_eq S A_selective_left_dioid_carrier)
                                        (A_eqv_eq L A_selective_left_dioid_label)
                                        A_selective_left_dioid_trans
; A_selective_left_dioid_exists_plus_ann : bop_exists_ann S
                                          (A_eqv_eq S A_selective_left_dioid_carrier)
                                          A_selective_left_dioid_plus                                 
; A_selective_left_dioid_id_ann_proofs  : slt_exists_id_ann_equal 
                                          (A_eqv_eq S A_selective_left_dioid_carrier)
                                          A_selective_left_dioid_plus
                                          A_selective_left_dioid_trans                        
; A_selective_left_dioid_proofs : left_dioid_proofs 
                                    (A_eqv_eq S A_selective_left_dioid_carrier)
                                    A_selective_left_dioid_plus
                                    A_selective_left_dioid_trans                                  
; A_selective_left_dioid_ast : cas_lstr_ast 
}.


Record A_left_dioid {L S : Type} :=
{
  A_left_dioid_carrier         : A_eqv S
; A_left_dioid_label           : A_eqv L
; A_left_dioid_plus            : binary_op S                                               
; A_left_dioid_trans           : ltr_type L S (* L -> (S -> S) *)
; A_left_dioid_plus_proofs     : sg_CI_proofs S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus                                 
; A_left_dioid_trans_proofs    : left_transform_proofs L S 
                                    (A_eqv_eq S A_left_dioid_carrier) 
                                    (A_eqv_eq L A_left_dioid_label) 
                                    A_left_dioid_trans
; A_left_dioid_exists_plus_ann : bop_exists_ann S 
                                  (A_eqv_eq S A_left_dioid_carrier) 
                                  A_left_dioid_plus                                 
; A_left_dioid_id_ann_proofs   : slt_exists_id_ann_equal 
                                  (A_eqv_eq S A_left_dioid_carrier) 
                                  A_left_dioid_plus  
                                  A_left_dioid_trans 
; A_left_dioid_proofs          : left_dioid_proofs 
                                  (A_eqv_eq S A_left_dioid_carrier) 
                                  A_left_dioid_plus 
                                  A_left_dioid_trans 
; A_left_dioid_ast             : cas_lstr_ast 
}.


Record A_left_pre_semiring {L S : Type} :=
  {
    A_left_pre_semiring_carrier         : A_eqv S
  ; A_left_pre_semiring_label           : A_eqv L
  ; A_left_pre_semiring_plus            : binary_op S                                               
  ; A_left_pre_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
  ; A_left_pre_semiring_plus_proofs     : sg_C_proofs S 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          A_left_pre_semiring_plus                                 
  ; A_left_pre_semiring_trans_proofs    : left_transform_proofs L S 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          (A_eqv_eq L A_left_pre_semiring_label)  
                                          A_left_pre_semiring_trans
  ; A_left_pre_semiring_exists_plus_ann_d : bop_exists_ann_decidable S 
                                            (A_eqv_eq S A_left_pre_semiring_carrier) 
                                            A_left_pre_semiring_plus                                 
  ; A_left_pre_semiring_id_ann_proofs_d   : slt_exists_id_ann_decidable 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          A_left_pre_semiring_plus  
                                          A_left_pre_semiring_trans 
  ; A_left_pre_semiring_proofs          : left_semiring_proofs 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          A_left_pre_semiring_plus 
                                          A_left_pre_semiring_trans 
  ; A_left_pre_semiring_ast             : cas_lstr_ast 
}.



Record A_left_semiring {L S : Type} :=
{
  A_left_semiring_carrier         : A_eqv S
; A_left_semiring_label           : A_eqv L
; A_left_semiring_plus            : binary_op S                                               
; A_left_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
; A_left_semiring_plus_proofs     : sg_C_proofs S 
                                    (A_eqv_eq S A_left_semiring_carrier) 
                                    A_left_semiring_plus                                 
; A_left_semiring_trans_proofs    : left_transform_proofs L S 
                                    (A_eqv_eq S A_left_semiring_carrier) 
                                    (A_eqv_eq L A_left_semiring_label)  
                                    A_left_semiring_trans
; A_left_semiring_exists_plus_ann_d : bop_exists_ann_decidable S 
                                      (A_eqv_eq S A_left_semiring_carrier) 
                                      A_left_semiring_plus                                 
; A_left_semiring_id_ann_proofs   : slt_exists_id_ann_equal 
                                    (A_eqv_eq S A_left_semiring_carrier) 
                                    A_left_semiring_plus  
                                    A_left_semiring_trans 
; A_left_semiring_proofs          : left_semiring_proofs 
                                    (A_eqv_eq S A_left_semiring_carrier) 
                                    A_left_semiring_plus 
                                    A_left_semiring_trans 
; A_left_semiring_ast             : cas_lstr_ast 
}.


End ACAS.

Section AMCAS.                                                    

Inductive A_slt_mcas {L S : Type} :=
| A_SLT_Error : list string                          -> @A_slt_mcas L S
| A_SLT : @A_slt L S                                  -> @A_slt_mcas L S
| A_SLT_Dioid : @A_left_dioid L S                     -> @A_slt_mcas L S
| A_SLT_Selective_Dioid : @A_selective_left_dioid L S -> @A_slt_mcas L S
| A_SLT_Left_Pre_Semiring : @A_left_pre_semiring L S -> @A_slt_mcas L S 
| A_SLT_Semiring : @A_left_semiring L S -> @A_slt_mcas L S. 



Inductive A_slt_mcas_proofs {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S)  :=
| A_SLT_proofs  : @slt_proofs L S r add ltr ->  @A_slt_mcas_proofs L S r add ltr
| A_SLT_dioid_proofs : @left_dioid_proofs L S r add ltr -> @A_slt_mcas_proofs L S r add ltr
| A_SLT_semiring_proofs : @left_semiring_proofs L S r add ltr -> @A_slt_mcas_proofs L S r add ltr. 

Definition A_slt_classify_proofs {L S : Type}  (r : brel S) 
  (add : binary_op S) 
  (ltr : ltr_type L S)  
  (A : @slt_proofs L S r add ltr) : @A_slt_mcas_proofs L S r add ltr :=
  match A_slt_distributive_d _ _ _ A with
  | inl ld => match A_slt_absorptive_d _ _ _ A with
    | inl la => A_SLT_dioid_proofs _ _ _ 
      {|
          A_left_dioid_distributive            := ld
        ; A_left_dioid_absorptive              := la                                               
        ; A_left_dioid_strictly_absorptive_d := A_slt_strictly_absorptive_d _ _ _ A 
      |}
    | inr nla => A_SLT_semiring_proofs _ _ _ 
      {|
          A_left_semiring_distributive            := ld
        ; A_left_semiring_not_absorptive          := nla                                              
      |}
  end
  | inr _  =>  A_SLT_proofs _ _ _ A      
  end.



Definition A_slt_classify_slt {L S : Type} (A : @A_slt L S) : A_slt_mcas :=
  let plus_proofs := A_slt_plus_proofs A in
  match A_slt_classify_proofs _ _  _  (A_slt_proofs A) with 
  | A_SLT_proofs _ _ _ _ =>  A_SLT A
  | A_SLT_semiring_proofs _ _ _ pf => 
    match  A_slt_id_ann_proofs_d A with
    | SLT_Id_Ann_Proof_Equal _ _ _ ppf => 
      match sg_proof_classify _ _ _ (A_MCAS_Proof_sg _ _ _ plus_proofs) with
      | A_MCAS_Proof_sg_C _ _ _ B   => 
            A_SLT_Semiring 
            {|
              A_left_semiring_carrier         := A_slt_carrier A
            ; A_left_semiring_label           := A_slt_label A
            ; A_left_semiring_plus            := A_slt_plus A                                              
            ; A_left_semiring_trans           := A_slt_trans A  (* L -> (S -> S) *)
            ; A_left_semiring_plus_proofs     := B                                 
            ; A_left_semiring_trans_proofs    := A_slt_trans_proofs A 
            ; A_left_semiring_exists_plus_ann_d := A_slt_exists_plus_ann_d A                               
            ; A_left_semiring_id_ann_proofs  := ppf
            ; A_left_semiring_proofs          := pf
            ; A_left_semiring_ast             := A_slt_ast A
            |}
      | _ => A_SLT A
      end
    | _ => A_SLT A
    end
  | A_SLT_dioid_proofs _ _ _ pf => 
    match A_slt_exists_plus_ann_d A with 
    | inl ann =>  
      match  A_slt_id_ann_proofs_d A with
      | SLT_Id_Ann_Proof_Equal _ _ _ ppf =>  
        match sg_proof_classify _ _ _ (A_MCAS_Proof_sg _ _ _ plus_proofs) with
        | A_MCAS_Proof_sg_CS _ _ _ B    =>
          A_SLT_Selective_Dioid 
            {|
              A_selective_left_dioid_carrier         := A_slt_carrier A
            ; A_selective_left_dioid_label           := A_slt_label A
            ; A_selective_left_dioid_plus            := A_slt_plus A                                              
            ; A_selective_left_dioid_trans           := A_slt_trans A  (* L -> (S -> S) *)
            ; A_selective_left_dioid_plus_proofs     := B                                 
            ; A_selective_left_dioid_trans_proofs    := A_slt_trans_proofs A 
            ; A_selective_left_dioid_exists_plus_ann := ann                               
            ; A_selective_left_dioid_id_ann_proofs   := ppf
            ; A_selective_left_dioid_proofs          := pf
            ; A_selective_left_dioid_ast             := A_slt_ast A
            |}
        | A_MCAS_Proof_sg_CI _ _ _ B    => 
            A_SLT_Dioid
            {|
              A_left_dioid_carrier         := A_slt_carrier A
            ; A_left_dioid_label           := A_slt_label A
            ; A_left_dioid_plus            := A_slt_plus A                                              
            ; A_left_dioid_trans           := A_slt_trans A  (* L -> (S -> S) *)
            ; A_left_dioid_plus_proofs     := B                                 
            ; A_left_dioid_trans_proofs    := A_slt_trans_proofs A 
            ; A_left_dioid_exists_plus_ann := ann                               
            ; A_left_dioid_id_ann_proofs   := ppf
            ; A_left_dioid_proofs          := pf
            ; A_left_dioid_ast             := A_slt_ast A
            |}
        | _ => A_SLT A 
        end
      | _ => A_SLT A
      end
    | inr _  => A_SLT A
    end 
  end. 
    
 


Definition A_slt_classify {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
  match A with
  | A_SLT_Error ls => A
  | A_SLT slt => A_slt_classify_slt slt
  | A_SLT_Dioid slt => A
  | A_SLT_Left_Pre_Semiring slt => A 
  | A_SLT_Semiring slt => A
  | A_SLT_Selective_Dioid slt => A 
  end.  

End AMCAS.       



Section CAS. 

  Record slt_certificates {L S : Type} :=
    {
      slt_distributive_d          : @check_slt_distributive L S
    ; slt_absorptive_d            : @check_slt_absorptive L S 
    ; slt_strictly_absorptive_d   : @check_slt_strictly_absorptive L S
    }.

  Record left_dioid_certificates {L S : Type} :=
    {
      left_dioid_distributive            : @assert_slt_distributive L S
    ; left_dioid_absorptive              : @assert_slt_absorptive L S                                              
    ; left_dioid_strictly_absorptive_d : @check_slt_strictly_absorptive L S
    }.


  Record left_semiring_certificates {L S : Type} :=
    {
      left_semiring_distributive            : @assert_slt_distributive L S
    ; left_semiring_not_absorptive          : @assert_slt_not_absorptive L S                                           
    }.


   
  Record slt {L S : Type} :=
    {
      slt_carrier        : @eqv S
    ; slt_label          : @eqv L
    ; slt_plus           : binary_op S                                               
    ; slt_trans          : ltr_type L S (* L -> (S -> S) *)
    ; slt_plus_certs    : @sg_certificates S                                
    ; slt_trans_certs   : @left_transform_certificates L S
    ; slt_exists_plus_ann_d : @check_exists_ann S                              
    ; slt_id_ann_certs_d : @check_slt_exists_id_ann L S                 
    ; slt_certs         : @slt_certificates L S                                
    ; slt_ast            : cas_lstr_ast
    }.
   
  
  Record selective_left_dioid {L S : Type} :=
    {
      selective_left_dioid_carrier      : @eqv S
    ; selective_left_dioid_label        : @eqv L
    ; selective_left_dioid_plus         : binary_op S                                               
    ; selective_left_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
    ; selective_left_dioid_plus_certs : @sg_CS_certificates S
    ; selective_left_dioid_trans_certs : @left_transform_certificates L S
    ; selective_left_dioid_exists_plus_ann : @assert_exists_ann S                              
    ; selective_left_dioid_id_ann_certs  : @assert_slt_exists_id_ann_equal L S                      
    ; selective_left_dioid_certs  : @left_dioid_certificates L S                                
    ; selective_left_dioid_ast          : cas_lstr_ast 
    }.


  Record left_dioid {L S : Type} :=
    {
      left_dioid_carrier         : @eqv S
    ; left_dioid_label           : @eqv L
    ; left_dioid_plus            : binary_op S                                               
    ; left_dioid_trans           : ltr_type L S (* L -> (S -> S) *)
    ; left_dioid_plus_certs     : @sg_CI_certificates S                                 
    ; left_dioid_trans_certs    : @left_transform_certificates L S    
    ; left_dioid_exists_plus_ann : @assert_exists_ann S                               
    ; left_dioid_id_ann_certs   : @assert_slt_exists_id_ann_equal L S
    ; left_dioid_certs          : @left_dioid_certificates L S
    ; left_dioid_ast             : cas_lstr_ast 
    }.
    
  
  Record left_pre_semiring {L S : Type} :=
    {
        left_pre_semiring_carrier         : @eqv S
      ; left_pre_semiring_label           : @eqv L
      ; left_pre_semiring_plus            : binary_op S                                               
      ; left_pre_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
      ; left_pre_semiring_plus_certs     : @sg_C_certificates S                                
      ; left_pre_semiring_trans_certs    : @left_transform_certificates L S
      ; left_pre_semiring_exists_plus_ann_d : @check_exists_ann S                                
      ; left_pre_semiring_id_ann_certs_d   : @check_slt_exists_id_ann L S 
      ; left_pre_semiring_certs          : @left_semiring_certificates L S
      ; left_pre_semiring_ast             : cas_lstr_ast 
    }.

  Record left_semiring {L S : Type} :=
    {
      left_semiring_carrier         : @eqv S
    ; left_semiring_label           : @eqv L
    ; left_semiring_plus            : binary_op S                                               
    ; left_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
    ; left_semiring_plus_certs     : @sg_C_certificates S                                
    ; left_semiring_trans_certs    : @left_transform_certificates L S
    ; left_semiring_exists_plus_ann_d : @check_exists_ann S                                
    ; left_semiring_id_ann_certs   : @assert_slt_exists_id_ann_equal L S 
    ; left_semiring_certs          : @left_semiring_certificates L S
    ; left_semiring_ast             : cas_lstr_ast 
    }.  
    
    
End CAS.


Section MCAS.

  Inductive slt_mcas {L S : Type} :=
  | SLT_Error : list string                          -> @slt_mcas L S
  | SLT : @slt L S                                  -> @slt_mcas L S
  | SLT_Dioid : @left_dioid L S                     -> @slt_mcas L S
  | SLT_Selective_Dioid : @selective_left_dioid L S -> @slt_mcas L S
  | SLT_Left_Pre_Semiring : @left_pre_semiring L S -> @slt_mcas L S
  | SLT_Semiring : @left_semiring L S -> @slt_mcas L S. 


  Inductive slt_mcas_certificates {L S : Type} :=
  | SLT_certs  : @slt_certificates L S ->  @slt_mcas_certificates L S
  | SLT_dioid_certs : @left_dioid_certificates L S -> @slt_mcas_certificates L S
  | SLT_semiring_certs : @left_semiring_certificates L S -> @slt_mcas_certificates L S.
  
  
  
  Definition slt_classify_certificates {L S : Type} 
    (A : @slt_certificates L S) : @slt_mcas_certificates L S :=
    match slt_distributive_d A with
    | Certify_Slt_Distributive =>
        match slt_absorptive_d A with
        | Certify_Slt_Absorptive => 
            SLT_dioid_certs 
            {|
                left_dioid_distributive := Assert_Slt_Distributive 
              ; left_dioid_absorptive := Assert_Slt_Absorptive
              ; left_dioid_strictly_absorptive_d := slt_strictly_absorptive_d A  
            |}
        | Certify_Slt_Not_Absorptive pf => 
            SLT_semiring_certs 
            {|
                left_semiring_distributive := Assert_Slt_Distributive
              ; left_semiring_not_absorptive := Assert_Slt_Not_Absorptive pf

            |}
        end
    | Certify_Slt_Not_Distributive _ => SLT_certs A 
    end. 


  
  Definition slt_classify_slt {L S : Type} (A : @slt L S) : @slt_mcas L S :=
    let plus_certificates := slt_plus_certs A in
    match slt_classify_certificates (slt_certs A) with 
    | SLT_certs _ => SLT A 
    | SLT_semiring_certs pf =>
        match  slt_id_ann_certs_d A with
        | Certify_SLT_Id_Ann_Proof_Equal ppf => 
            match sg_certificates_classify (MCAS_Cert_sg plus_certificates) with
            | MCAS_Cert_sg_C B => 
                SLT_Semiring 
                {|
                  left_semiring_carrier         := slt_carrier A
                ; left_semiring_label           := slt_label A
                ; left_semiring_plus            := slt_plus A                                              
                ; left_semiring_trans           := slt_trans A  (* L -> (S -> S) *)
                ; left_semiring_plus_certs     := B                                 
                ; left_semiring_trans_certs    := slt_trans_certs A 
                ; left_semiring_exists_plus_ann_d := slt_exists_plus_ann_d A                               
                ; left_semiring_id_ann_certs   := Assert_Slt_Exists_Id_Ann_Equal ppf
                ; left_semiring_certs          := pf
                ; left_semiring_ast             := slt_ast A
                |}
            | _ => SLT A
            end
        | _ => SLT A
        end
    | SLT_dioid_certs pf =>
        match slt_exists_plus_ann_d A with 
        | Certify_Exists_Ann ann => 
            match slt_id_ann_certs_d A with
            | Certify_SLT_Id_Ann_Proof_Equal ppf =>  
                match sg_certificates_classify (MCAS_Cert_sg plus_certificates) with
                | MCAS_Cert_sg_CS B => 
                    SLT_Selective_Dioid 
                    {|
                      selective_left_dioid_carrier         := slt_carrier A
                    ; selective_left_dioid_label           := slt_label A
                    ; selective_left_dioid_plus            := slt_plus A                                              
                    ; selective_left_dioid_trans           := slt_trans A  (* L -> (S -> S) *)
                    ; selective_left_dioid_plus_certs     := B                                 
                    ; selective_left_dioid_trans_certs    := slt_trans_certs A 
                    ; selective_left_dioid_exists_plus_ann := Assert_Exists_Ann ann                               
                    ; selective_left_dioid_id_ann_certs   := Assert_Slt_Exists_Id_Ann_Equal ppf
                    ; selective_left_dioid_certs          := pf
                    ; selective_left_dioid_ast             := slt_ast A
                    |}
                | MCAS_Cert_sg_CI B => 
                    SLT_Dioid
                    {|
                      left_dioid_carrier         := slt_carrier A
                    ; left_dioid_label           := slt_label A
                    ; left_dioid_plus            := slt_plus A                                              
                    ; left_dioid_trans           := slt_trans A  (* L -> (S -> S) *)
                    ; left_dioid_plus_certs     := B                                 
                    ; left_dioid_trans_certs    := slt_trans_certs A 
                    ; left_dioid_exists_plus_ann := Assert_Exists_Ann ann                               
                    ; left_dioid_id_ann_certs   := Assert_Slt_Exists_Id_Ann_Equal ppf
                    ; left_dioid_certs          := pf
                    ; left_dioid_ast             := slt_ast A
                    |}
                | _ => SLT A
                end 
            | _ => SLT A
            end
        | Certify_Not_Exists_Ann => SLT A
        end
    end. 



  Definition slt_classify {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => A
    | SLT slt => slt_classify_slt slt
    | SLT_Dioid slt => A
    | SLT_Left_Pre_Semiring slt => A
    | SLT_Semiring slt => A 
    | SLT_Selective_Dioid slt => A 
    end.  



End MCAS.


Section Translation.


  Definition P2C_slt {L S : Type}  (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @slt_proofs L S r add ltr -> @slt_certificates L S :=
    λ A,  
    {|
      slt_distributive_d          := p2c_slt_distributive_check r add ltr 
        (A_slt_distributive_d _ _ _ A)
    ; slt_absorptive_d            := p2c_slt_absorptive_check r add ltr
        (A_slt_absorptive_d _ _ _ A) 
    ; slt_strictly_absorptive_d   := p2c_slt_strictly_absorptive_check r add ltr
        (A_slt_strictly_absorptive_d _ _ _ A)
    |}.


  Definition P2C_left_dioid {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @left_dioid_proofs L S r add ltr -> @left_dioid_certificates L S :=
    λ A, 
    {|
      left_dioid_distributive            := p2c_slt_distributive_assert r add ltr 
        ( A_left_dioid_distributive _ _ _ A)
    ; left_dioid_absorptive              := p2c_slt_absorptive_assert r add ltr
        (A_left_dioid_absorptive _ _ _ A)                                          
    ; left_dioid_strictly_absorptive_d := p2c_slt_strictly_absorptive_check r add ltr
        (A_left_dioid_strictly_absorptive_d _ _ _ A)
    |}.


  Definition P2C_left_semiring {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @left_semiring_proofs L S r add ltr -> @left_semiring_certificates L S :=
    λ A,
    {|
      left_semiring_distributive            := p2c_slt_distributive_assert r add ltr
        (A_left_semiring_distributive  _ _ _ A) 
    ; left_semiring_not_absorptive          := p2c_slt_not_absorptive_assert r add ltr
        (A_left_semiring_not_absorptive _ _ _ A)                              
    |}.
      

  Definition A2C_slt {L S : Type} :
    @A_slt L S -> @slt L S :=
    λ A, 
    {|
        slt_carrier := A2C_eqv _ (A_slt_carrier A)
      ; slt_label := A2C_eqv _ (A_slt_label A)
      ; slt_plus := A_slt_plus A
      ; slt_trans := A_slt_trans A
      ; slt_plus_certs := P2C_sg _ _ _ (A_slt_plus_proofs A)
      ; slt_trans_certs := P2C_left_transform _ _ _ _ _ (A_slt_trans_proofs A) 
      ; slt_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_slt_exists_plus_ann_d A)
      ; slt_id_ann_certs_d := @p2c_slt_exists_id_ann_check L S _ _ _ (A_slt_id_ann_proofs_d A) 
      ; slt_certs := @P2C_slt L S _ _ _ (A_slt_proofs A)
      ; slt_ast := A_slt_ast  A
    |}.


  Definition A2C_selective_left_dioid {L S : Type} :
    @A_selective_left_dioid L S -> @selective_left_dioid L S :=
    λ A, 
    {|
        selective_left_dioid_carrier := A2C_eqv _ (A_selective_left_dioid_carrier A) 
      ; selective_left_dioid_label := A2C_eqv _ (A_selective_left_dioid_label A)
      ; selective_left_dioid_plus := A_selective_left_dioid_plus A
      ; selective_left_dioid_trans  := A_selective_left_dioid_trans A
      ; selective_left_dioid_plus_certs := P2C_sg_CS _ _ _ (A_selective_left_dioid_plus_proofs A)
      ; selective_left_dioid_trans_certs := P2C_left_transform _ _ _ _ _ (A_selective_left_dioid_trans_proofs A)
      ; selective_left_dioid_exists_plus_ann := p2c_exists_ann_assert _ _ _ (A_selective_left_dioid_exists_plus_ann A)
      ; selective_left_dioid_id_ann_certs := @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_selective_left_dioid_id_ann_proofs A)
      ; selective_left_dioid_certs := @P2C_left_dioid L S _ _ _ (A_selective_left_dioid_proofs A)
      ; selective_left_dioid_ast := A_selective_left_dioid_ast A   
    |}.

    
  Definition A2C_left_dioid  {L S : Type} :
    @A_left_dioid L S -> @left_dioid L S :=
    λ A, 
    {|
        left_dioid_carrier := A2C_eqv _ (A_left_dioid_carrier A)
      ; left_dioid_label := A2C_eqv _ (A_left_dioid_label A)
      ; left_dioid_plus := A_left_dioid_plus A
      ; left_dioid_trans  := A_left_dioid_trans A
      ; left_dioid_plus_certs := P2C_sg_CI _ _ _ (A_left_dioid_plus_proofs A)
      ; left_dioid_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_dioid_trans_proofs A)
      ; left_dioid_exists_plus_ann := p2c_exists_ann_assert _ _ _ (A_left_dioid_exists_plus_ann A)
      ; left_dioid_id_ann_certs := @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_left_dioid_id_ann_proofs A)
      ; left_dioid_certs := @P2C_left_dioid L S _ _ _ (A_left_dioid_proofs A)
      ; left_dioid_ast  := A_left_dioid_ast A  
    |}.

  
  Definition A2C_pre_left_semiring {L S : Type} :
    @A_left_pre_semiring L S -> @left_pre_semiring L S :=
    λ A, 
    {|
        left_pre_semiring_carrier := A2C_eqv _ (A_left_pre_semiring_carrier A)
      ; left_pre_semiring_label := A2C_eqv _ (A_left_pre_semiring_label A)
      ; left_pre_semiring_plus := A_left_pre_semiring_plus A
      ; left_pre_semiring_trans := A_left_pre_semiring_trans A
      ; left_pre_semiring_plus_certs := P2C_sg_C _ _ _ (A_left_pre_semiring_plus_proofs A)
      ; left_pre_semiring_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_pre_semiring_trans_proofs A)
      ; left_pre_semiring_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_left_pre_semiring_exists_plus_ann_d A)
      ; left_pre_semiring_id_ann_certs_d := p2c_slt_exists_id_ann_check _ _ _ (A_left_pre_semiring_id_ann_proofs_d A)
      ; left_pre_semiring_certs := P2C_left_semiring _ _ _ (A_left_pre_semiring_proofs A)
      ; left_pre_semiring_ast  := A_left_pre_semiring_ast A 
    |}.

    

  Definition A2C_left_semiring {L S : Type} :
    @A_left_semiring L S -> @left_semiring L S :=
    λ A, 
    {|
        left_semiring_carrier := A2C_eqv _ (A_left_semiring_carrier A)
      ; left_semiring_label := A2C_eqv _ (A_left_semiring_label A)
      ; left_semiring_plus := A_left_semiring_plus A
      ; left_semiring_trans := A_left_semiring_trans A
      ; left_semiring_plus_certs := P2C_sg_C _ _ _ (A_left_semiring_plus_proofs A)
      ; left_semiring_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_semiring_trans_proofs A)
      ; left_semiring_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_left_semiring_exists_plus_ann_d A)
      ; left_semiring_id_ann_certs :=  @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_left_semiring_id_ann_proofs A)
      ; left_semiring_certs := P2C_left_semiring _ _ _ (A_left_semiring_proofs A)
      ; left_semiring_ast  := A_left_semiring_ast A 
    |}.


  

  Definition A2C_mcas_slt {L S : Type} :
    @A_slt_mcas L S -> @slt_mcas L S :=
    λ A, match A with
      | A_SLT_Error err => SLT_Error err    
      | A_SLT pf => SLT (A2C_slt pf)
      | A_SLT_Dioid pf => SLT_Dioid (A2C_left_dioid pf) 
      | A_SLT_Selective_Dioid pf => SLT_Selective_Dioid (A2C_selective_left_dioid pf)
      | A_SLT_Left_Pre_Semiring pf => SLT_Left_Pre_Semiring (A2C_pre_left_semiring pf) 
      | A_SLT_Semiring pf => SLT_Semiring (A2C_left_semiring pf) 
    end. 



  Definition P2C_proofs_mcas_slt {L S : Type} 
    (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @A_slt_mcas_proofs L S r add ltr -> @slt_mcas_certificates L S :=
    λ A, match A with
    | A_SLT_proofs _ _ _ pf => SLT_certs (P2C_slt r add ltr pf)
    | A_SLT_dioid_proofs  _ _ _ pf => SLT_dioid_certs (P2C_left_dioid r add ltr pf)
    | A_SLT_semiring_proofs _ _ _ pf => SLT_semiring_certs (P2C_left_semiring r add ltr pf)
    end.



End Translation.

Section Verify.

  
  Context 
    {L S : Type}.

  
  Lemma corectness_slt_classify_certificates_proofs 
    (r : brel S) (add : binary_op S) (ltr : ltr_type L S)
    (s : slt_proofs r add ltr) :
    slt_classify_certificates (P2C_slt r add ltr s) = 
    P2C_proofs_mcas_slt r add ltr (A_slt_classify_proofs r add ltr s).
  Proof.
      unfold slt_classify_certificates, 
      A_slt_classify_proofs; compute.
      destruct s; simpl.
      destruct A_slt_distributive_d0;
      simpl.
      + destruct A_slt_absorptive_d0.
        ++ reflexivity.
        ++ reflexivity.   
      + reflexivity.
  Qed.  



  Lemma correctness_slt_classify_slt : 
    forall pf,
    slt_classify_slt (A2C_slt pf) = 
    @A2C_mcas_slt L S (A_slt_classify_slt pf).
  Proof.
    unfold slt_classify_slt,
    A_slt_classify_slt;
    destruct pf; simpl.
    rewrite corectness_slt_classify_certificates_proofs.
    destruct ((A_slt_classify_proofs 
      (A_eqv_eq S A_slt_carrier0) A_slt_plus0
      A_slt_trans0 A_slt_proofs0)); simpl.
    + reflexivity.
    + destruct A_slt_exists_plus_ann_d0; simpl.
      ++ 
        destruct A_slt_id_ann_proofs_d0; simpl.
        +++ destruct p; simpl; reflexivity.
        +++ destruct p; simpl; reflexivity.
        +++ destruct p; simpl; reflexivity.
        +++ rewrite correct_sg_certificates_classify_sg;
            destruct (A_sg_proofs_classify_sg S 
            (A_eqv_eq S A_slt_carrier0) A_slt_plus0
            A_slt_plus_proofs0);
            simpl; reflexivity.
        +++ reflexivity.
      ++ reflexivity.
    + destruct A_slt_id_ann_proofs_d0; 
      simpl.
      ++ destruct p; simpl; reflexivity.
      ++ destruct p; simpl; reflexivity.
      ++ destruct p; simpl; reflexivity.
      ++ rewrite correct_sg_certificates_classify_sg;
      destruct (A_sg_proofs_classify_sg S 
        (A_eqv_eq S A_slt_carrier0) A_slt_plus0
        A_slt_plus_proofs0);
      simpl; reflexivity.
      ++ reflexivity.
  Qed. 


  Lemma correctness_A2C_left_dioid : 
    forall pf, 
    SLT_Dioid (A2C_left_dioid pf) = 
    @SLT_Dioid L S (A2C_left_dioid pf).
  Proof.
    intros pf.
    reflexivity.
  Qed.
  

  Lemma correctness_A2C_selective_left_dioid : 
    forall pf, 
    SLT_Selective_Dioid (A2C_selective_left_dioid pf) =
    @SLT_Selective_Dioid L S (A2C_selective_left_dioid pf).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  Lemma correctness_A2C_pre_left_semiring : 
    forall pf, 
    SLT_Left_Pre_Semiring (A2C_pre_left_semiring pf) =
    @SLT_Left_Pre_Semiring L S (A2C_pre_left_semiring pf).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  Lemma correctness_A2C_left_semiring : 
    forall pf, 
    SLT_Semiring (A2C_left_semiring pf) = 
    @SLT_Semiring L S (A2C_left_semiring pf).
  Proof.
    intros ?.
    reflexivity.
  Qed.
  
 

  
  Lemma correctness_slt_classify : 
    forall pf,  
    slt_classify (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (A_slt_classify pf).
  Proof.
    destruct pf; simpl.
    + reflexivity.
    + eapply correctness_slt_classify_slt.
    + eapply correctness_A2C_left_dioid.
    + eapply correctness_A2C_selective_left_dioid.
    + eapply correctness_A2C_pre_left_semiring.
    + eapply correctness_A2C_left_semiring.
  Qed.      


End Verify.