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
  
Record slt_proofs {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_slt_distributive_d          : slt_distributive_decidable r add ltr
; A_slt_absorptive_d            : slt_absorptive_decidable r add ltr
; A_slt_strictly_absorptive_d   : slt_strictly_absorptive_decidable r add ltr  
}.



Record left_dioid_proofs {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_dioid_distributive            : slt_distributive r add ltr
; A_left_dioid_absorptive              : slt_absorptive r add ltr                                               
; A_left_dioid_strictly_absorptive_d : slt_strictly_absorptive_decidable r add ltr 
}.


Record A_slt {L S : Type} :=
{
  A_slt_carrier        : A_eqv S
; A_slt_label          : A_eqv L
; A_slt_plus           : binary_op S                                               
; A_slt_trans          : ltr_type L S (* L -> (S -> S) *)
; A_slt_plus_proofs    : sg_proofs S (A_eqv_eq S A_slt_carrier) A_slt_plus                                 
; A_slt_trans_proofs   : left_transform_proofs L S (A_eqv_eq S A_slt_carrier) (A_eqv_eq L A_slt_label)  A_slt_trans
; A_slt_exists_plus_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_slt_carrier) A_slt_plus                                 
; A_stl_id_ann_proofs  : slt_exists_id_ann_decidable (A_eqv_eq S A_slt_carrier) A_slt_plus  A_slt_trans                        
; A_slt_proofs         : slt_proofs (A_eqv_eq S A_slt_carrier) A_slt_plus A_slt_trans                                  
; A_slt_ast            : cas_lstr_ast
}.






Record A_selective_left_dioid {L S : Type} :=
{
  A_selective_left_dioid_carrier      : A_eqv S
; A_selective_left_dioid_label        : A_eqv L
; A_selective_left_dioid_plus         : binary_op S                                               
; A_selective_left_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
; A_selective_left_dioid_plus_proofs  : sg_CS_proofs S (A_eqv_eq S A_selective_left_dioid_carrier) A_selective_left_dioid_plus 
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
; A_selective_left_dioid_proofs       : left_dioid_proofs (A_eqv_eq S A_selective_left_dioid_carrier)
                                                          A_selective_left_dioid_plus
                                                          A_selective_left_dioid_trans                                  
; A_selective_left_dioid_ast          : cas_lstr_ast 
}.


Record A_left_dioid {L S : Type} :=
{
  A_left_dioid_carrier         : A_eqv S
; A_left_dioid_label           : A_eqv L
; A_left_dioid_plus            : binary_op S                                               
; A_left_dioid_trans           : ltr_type L S (* L -> (S -> S) *)
; A_left_dioid_plus_proofs     : sg_CI_proofs S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus                                 
; A_left_dioid_trans_proofs    : left_transform_proofs L S (A_eqv_eq S A_left_dioid_carrier) (A_eqv_eq L A_left_dioid_label)  A_left_dioid_trans
; A_left_dioid_exists_plus_ann : bop_exists_ann S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus                                 
; A_left_dioid_id_ann_proofs   : slt_exists_id_ann_equal (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus  A_left_dioid_trans 
; A_left_dioid_proofs          : left_dioid_proofs (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus A_left_dioid_trans 
; A_left_dioid_ast             : cas_lstr_ast 
}.

End ACAS.

Section AMCAS.                                                    

Inductive A_slt_mcas {L S : Type} :=
| A_SLT_Error : list string                          -> @A_slt_mcas L S
| A_SLT : @A_slt L S                                  -> @A_slt_mcas L S
| A_SLT_Dioid : @A_left_dioid L S                     -> @A_slt_mcas L S
| A_SLT_Selective_Dioid : @A_selective_left_dioid L S -> @A_slt_mcas L S
.

Inductive A_slt_mcas_proofs {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S)  :=
| A_SLT_proof  : @slt_proofs L S r add ltr ->  @A_slt_mcas_proofs L S r add ltr
| A_SLT_dioid_proof : @left_dioid_proofs L S r add ltr -> @A_slt_mcas_proofs L S r add ltr.

Definition A_stl_classify_proofs {L S : Type}  (r : brel S) 
  (add : binary_op S) 
  (ltr : ltr_type L S)  
  (A : @slt_proofs L S r add ltr) : @A_slt_mcas_proofs L S r add ltr :=
  match A_slt_distributive_d _ _ _ A with
  | inl ld => match A_slt_absorptive_d _ _ _ A with
    | inl la => A_SLT_dioid_proof _ _ _ 
      {|
          A_left_dioid_distributive            := ld
        ; A_left_dioid_absorptive              := la                                               
        ; A_left_dioid_strictly_absorptive_d := A_slt_strictly_absorptive_d _ _ _ A 
      |}
    | inr _ => A_SLT_proof _ _ _ A
  end
  | inr _  =>  A_SLT_proof _ _ _ A      
  end.



Definition A_stl_classify_slt {L S : Type} (A : @A_slt L S) : A_slt_mcas :=
  let plus_proofs := A_slt_plus_proofs A in
  match A_stl_classify_proofs _ _  _  (A_slt_proofs A) with 
  | A_SLT_proof _ _ _ _ =>  A_SLT A
  | A_SLT_dioid_proof _ _ _ pf => 
    match A_slt_exists_plus_ann_d A with 
    | inl ann =>  
      match  A_stl_id_ann_proofs A with
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
    
 


Definition A_stl_classify {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
  match A with
  | A_SLT_Error ls => A
  | A_SLT slt => A_stl_classify_slt slt
  | A_SLT_Dioid slt => A
  | A_SLT_Selective_Dioid slt => A 
  end.  

End AMCAS.                                                    

