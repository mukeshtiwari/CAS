Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 


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


Definition cef_bop_llex_not_cancellative {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T) (g : T -> T) 
  := if brel_llt rS bS s (f s) 
     then ((s, t), ((f s, t), (f s, g t))) 
     else ((f s, t), ((s, t), (s, g t))).


Definition cef_bop_llex_not_anti_left {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T)  
  := if rS (bS s (f s)) s then ((s, t), (f s, t)) else ((f s, t), (s, t)). 

Definition cef_bop_llex_not_anti_right {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T)  
  := if rS (bS s (f s)) s then ((s, t), (f s, t)) else ((f s, t), (s, t)). 


Definition cef_bop_llex_not_constant {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T) (g : T -> T) 
  := if brel_llt rS bS s (f s) 
     then ((f s, t), ((s, t), (s, g t)))
     else ((s, t), ((f s, t), (f s, g t))). 


Definition cef_bop_llex_not_is_left {S T : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (t : T) 
   := if r (b s (f s)) s then ((f s, t), (s, t)) else ((s, t), (f s, t)). 

Definition cef_bop_llex_not_is_right {S T : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (t : T) 
   := if r (b s (f s)) s then ((s, t), (f s, t)) else ((f s, t), (s, t)).
           
(*
Definition cef_llex_product_not_left_distributive 
      {S T : Type}
      (rS : brel S)
      (rT : brel T)
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
      (addS : binary_op S) 
      (addT : binary_op T)
      (mulT : binary_op T) 
:= if (rS (addS s2 s3) s2) 
   then if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
   else if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s3, t3), (s2, t2)))
        else ((s1, t1), ((s2, t3), (s3, t2))). 

*) 
Definition cef_llex_product_not_left_distributive  
      {S T : Type}
      (rS : brel S)
      (rT : brel T)
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
      (addS : binary_op S) 
      (addT : binary_op T)
      (mulT : binary_op T) 
:= if (rS (addS s2 s3) s2) 
   then if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
   else if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t2), (s3, t3)))
        else ((s1, t1), ((s2, t3), (s3, t2))). 


Definition cef_llex_product_not_right_distributive
      {S T : Type}
      (rS : brel S)
      (rT : brel T)
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
      (addS : binary_op S) 
      (addT : binary_op T)
      (mulT : binary_op T) 
:= if (rS (addS s2 s3) s2) 
   then if rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
   else if rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))
        then ((s1, t1), ((s2, t2), (s3, t3)))
        else ((s1, t1), ((s2, t3), (s3, t2))). 

