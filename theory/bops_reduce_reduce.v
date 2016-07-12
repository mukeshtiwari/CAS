Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.bop_reduction. 


Section ReduceReduce. 

Variable S       : Type.  
Variable rS      : brel S.  
Variable addS    : binary_op S. 
Variable mulS    : binary_op S. 
Variable u       : unary_op S. 

Variable transS   : brel_transitive S rS. 
Variable symS     : brel_symmetric S rS. 
Variable cong_u   : uop_congruence S rS u. 
Variable cong_add : bop_congruence S rS addS. 
Variable cong_mul : bop_congruence S rS mulS. 
Variable ass_add  : bop_associative S rS addS. 
Variable ass_mul  : bop_associative S rS mulS. 


Lemma bops_reduce_reduce_left_distributive : 
      bop_left_distributive S rS addS mulS → 
         bop_left_distributive S 
           (brel_reduce S rS u)
           (bop_then_unary S u addS) 
           (bop_then_unary S u mulS). 
Proof. intros ldS s1 s2 s3. compute. 
       admit. 
(* 
   u (u (s1 * (u (s2 + s3))))) = u (u ((u(s1 * s2)) + (u(s1 * s3))))

   u (u (s1 * (u (s2 + s3))))) 
   = idem_u 
   u (s1 * (u (s2 + s3)))
   = dist_u_plus 
   u (s1 * ((u s2) + (u s3)))
   = dist_left_plus_times 
   u ((s1 * (u s2)) + (s1 * (u s3))) 
   = reduction_plus 
   u (u (s1 * (u s2)) + u(s1 * (u s3))) 
   = reduction_right_times 
   u (u (s1 * s2) + u(s1 * s3)) 
   = reduction_plus
   u (u (u (s1 * s2) + u(s1 * s3))) 
*) 
Defined. 


Lemma bops_reduce_reduce_left_absorption  : 
      bops_left_absorption S rS addS mulS → 
         bops_left_absorption S 
           (brel_reduce S rS u)
           (bop_then_unary S u addS) 
           (bop_then_unary S u mulS). 
Proof. intros ldS s1 s2. compute. 
(*
   u s1 = u (u (s1 + u (s1 * s2)))

   u s1 
   = abs 
   u (s1 + (s1 * s2)) 
   = reduce_left 
   u (s1 + u (s1 * s2)) 
   = idem_u 
   u (u (s1 + u (s1 * s2)))  
*) 
       admit. 
Qed. 


End ReduceReduce. 




