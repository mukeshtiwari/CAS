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
  
Record slt_proofs (L S : Type) (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_slt_distributive_d          : slt_distributive_decidable L S r add ltr
; A_slt_absorptive_d            : slt_absorptive_decidable L S r add ltr
; A_slt_strictly_absorptive_d   : slt_strictly_absorptive_decidable L S r add ltr                                                                              }.

Record left_semiring_proofs (L S : Type) (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_semiring_distributive            : slt_distributive L S r add ltr
; A_left_semiring_not_absorptive          : slt_not_absorptive L S r add ltr                                               
}.

Record left_dioid_proofs (L S : Type) (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_dioid_distributive            : slt_distributive L S r add ltr
; A_left_dioid_absorptive              : slt_absorptive L S r add ltr                                               
; A_left_dioid_not_strictly_absorptive : slt_not_strictly_absorptive L S r add ltr 
}.

Record strictly_absorptive_left_dioid_proofs (L S : Type) (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_strictly_absorptive_left_dioid_distributive          : slt_distributive L S r add ltr
; A_strictly_absorptive_left_dioid_strictly_absorptive   : slt_strictly_absorptive L S r add ltr 
}.

Record A_slt (L S : Type) :=
{
  A_slt_carrier        : A_eqv S
; A_slt_label          : A_eqv L
; A_slt_plus           : binary_op S                                               
; A_slt_trans          : ltr_type L S (* L -> (S -> S) *)
; A_slt_plus_proofs    : sg_proofs S (A_eqv_eq S A_slt_carrier) A_slt_plus                                 
; A_slt_trans_proofs   : left_transform_proofs L S (A_eqv_eq S A_slt_carrier) (A_eqv_eq L A_slt_label)  A_slt_trans
; A_slt_exists_plus_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_slt_carrier) A_slt_plus                                 
; A_stl_id_ann_proofs  : stl_exists_id_ann_decidable L S (A_eqv_eq S A_slt_carrier) A_slt_plus  A_slt_trans                        
; A_slt_proofs         : slt_proofs L S (A_eqv_eq S A_slt_carrier) A_slt_plus A_slt_trans                                  
; A_slt_ast            : cas_lstr_ast
}.


Record A_slt_CS (L S : Type) :=
{
  A_slt_CS_carrier        : A_eqv S
; A_slt_CS_label          : A_eqv L
; A_slt_CS_plus           : binary_op S                                               
; A_slt_CS_trans          : ltr_type L S (* L -> (S -> S) *)
; A_slt_CS_plus_proofs    : sg_CS_proofs S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus                                 
; A_slt_CS_trans_proofs   : left_transform_proofs L S (A_eqv_eq S A_slt_CS_carrier) (A_eqv_eq L A_slt_CS_label)  A_slt_CS_trans
; A_slt_CS_exists_plus_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus                                 
; A_stl_CS_id_ann_proofs  : stl_exists_id_ann_decidable L S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus  A_slt_CS_trans                        
; A_slt_CS_proofs         : slt_proofs L S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus A_slt_CS_trans                                  
; A_slt_CS_ast            : cas_lstr_ast
}.

Record A_slt_CI (L S : Type) :=
{
  A_slt_CI_carrier      : A_eqv S
; A_slt_CI_label        : A_eqv L
; A_slt_CI_plus         : binary_op S                                               
; A_slt_CI_trans        : ltr_type L S (* L -> (S -> S) *)
; A_slt_CI_plus_proofs  : sg_CI_proofs S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus                                 
; A_slt_CI_trans_proofs : left_transform_proofs L S (A_eqv_eq S A_slt_CI_carrier) (A_eqv_eq L A_slt_CI_label)  A_slt_CI_trans
; A_slt_CI_exists_plus_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus                                 
; A_stl_CI_id_ann_proofs  : stl_exists_id_ann_decidable L S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus  A_slt_CI_trans                        
; A_slt_CI_proofs       : slt_proofs L S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus A_slt_CI_trans                                  
; A_slt_CI_ast          : cas_lstr_ast 
}.


Record A_selective_left_dioid (L S : Type) :=
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
; A_selective_left_dioid_id_ann_proofs  : stl_exists_id_ann_equal L S
                                                                  (A_eqv_eq S A_selective_left_dioid_carrier)
                                                                  A_selective_left_dioid_plus
                                                                  A_selective_left_dioid_trans                        
; A_selective_left_dioid_proofs       : left_dioid_proofs L S (A_eqv_eq S A_selective_left_dioid_carrier)
                                                          A_selective_left_dioid_plus
                                                          A_selective_left_dioid_trans                                  
; A_selective_left_dioid_ast          : cas_lstr_ast 
}.

Record A_left_dioid (L S : Type) :=
{
  A_left_dioid_carrier         : A_eqv S
; A_left_dioid_label           : A_eqv L
; A_left_dioid_plus            : binary_op S                                               
; A_left_dioid_trans           : ltr_type L S (* L -> (S -> S) *)
; A_left_dioid_plus_proofs     : sg_CI_proofs S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus                                 
; A_left_dioid_trans_proofs    : left_transform_proofs L S (A_eqv_eq S A_left_dioid_carrier) (A_eqv_eq L A_left_dioid_label)  A_left_dioid_trans
; A_left_dioid_exists_plus_ann : bop_exists_ann S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus                                 
; A_left_dioid_id_ann_proofs   : stl_exists_id_ann_equal L S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus  A_left_dioid_trans 
; A_left_dioid_proofs          : left_dioid_proofs L S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus A_left_dioid_trans 
; A_left_dioid_ast             : cas_lstr_ast 
}.

End ACAS.

Section AMCAS.                                                    

Inductive A_slt_mcas (L S : Type) :=
| A_SLT_Error : list string                          -> A_slt_mcas L S
| A_SLT : A_slt L S                                  -> A_slt_mcas L S
| A_SLT_CS : A_slt_CS L S                            -> A_slt_mcas L S
| A_SLT_CI : A_slt_CI L S                            -> A_slt_mcas L S
| A_SLT_Dioid : A_left_dioid L S                     -> A_slt_mcas L S
| A_SLT_Selective_Dioid : A_selective_left_dioid L S -> A_slt_mcas L S
.

End AMCAS.                                                    

