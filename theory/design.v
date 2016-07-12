Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.uop. 
Require Import CAS.theory.properties. 
Require Import CAS.theory.facts.
Require Import CAS.a_code.proof_records. 



(* 

   C  S  L  R  I  1  0
   -------------------
   T  -  F  F  -  -  - 16    
   F  -  -  -  -  -  - 64 


   -  T  -  -  T  -  - 
   -  F  -  -  T  -  - 
   -  F  -  -  F  -  - 


   T  T  F  F  T  -  -  4 comm, selective 
   T  F  F  F  T  -  -  4 comm, idem 
   T  F  F  F  F  -  -  4 comm 

   F  T  F  F  T  -  -  4 not_comm, selective 
   F  F  F  F  T  -  -  4 not_comm, idem 
   F  F  F  F  F  -  -  4 not_comm 

   F  T  T  F  T  F  F  1 Left 
   F  T  F  T  T  F  F  1 Right 
                       ---
                       26 

   -------------------
   ------------------- impossible    
   T  -  T  F  -  -  - 
   T  -  F  T  -  -  - 
   T  -  T  T  -  -  - 

   -  T  -  -  F  -  - 


 


*) 


Record sg_profile := 
{
  sg_profile_commutative   : bool (*  1  2   *) 
; sg_profile_selective     : bool (*  2  4   *)
; sg_profile_is_left       : bool (*  3  8   *) 
; sg_profile_is_right      : bool (*  4  16  *) 
; sg_profile_idempotent    : bool (*  5  32  *) 
; sg_profile_exists_id     : bool (*  6  64  *) 
; sg_profile_exists_ann    : bool (*  7  128 *) 
}. 

Definition sg_class := sg_profile → bool.  


Definition fits_sg_profile (p : sg_profile) (S: Type) (r : brel S) (b : binary_op S) := 
  (if sg_profile_commutative p then bop_commutative S r b else bop_not_commutative S r b) (*  1 *) 
* (if sg_profile_selective p   then bop_selective S r b   else bop_not_selective S r b)   (*  2 *) 
* (if sg_profile_is_left p     then bop_is_left S r b     else bop_not_is_left S r b)     (*  3 *) 
* (if sg_profile_is_right p    then bop_is_right S r b    else bop_not_is_right S r b)    (*  4 *) 
* (if sg_profile_idempotent p  then bop_idempotent S r b  else bop_not_idempotent S r b)  (*  5 *) 
* (if sg_profile_exists_id p   then bop_exists_id S r b   else bop_not_exists_id S r b)   (*  6 *) 
* (if sg_profile_exists_ann p  then bop_exists_ann S r b  else bop_not_exists_ann S r b)  (*  7 *) 
. 


Definition in_sg_class (c : sg_class) (S: Type) (r : brel S) (b : binary_op S) 
   := ∀ (p : sg_profile), c p = true ->  eqv_proofs S r -> fits_sg_profile p S r b. 


Definition sg_class_empty (c : sg_class) 
   := ∀ (p : sg_profile) (S: Type) (r : brel S) (b : binary_op S), 
              ((c p = true) * (eqv_proofs S r) * (fits_sg_profile p S r b)) -> False. 


(* classes *) 

Definition sg_class_commutative (p: sg_profile) := sg_profile_commutative p. 

Definition sg_class_commutative_left_or_right (p: sg_profile) := 
     (sg_profile_commutative p) 
  && ((sg_profile_is_left p) || (sg_profile_is_right p)). 

Definition sg_class_selective_not_idempotent (p: sg_profile) := 
     (sg_profile_selective p) && (negb (sg_profile_is_left p)). 

(* ******** *) 


Lemma sg_class_commutative_left_or_right_empty : sg_class_empty sg_class_commutative_left_or_right. 
Proof. unfold sg_class_empty, sg_class_commutative_left_or_right. 
       intros p S r b [[H E] Q]. 
       apply andb_is_true_left in H.  
       destruct H as [L R]. 
       apply orb_is_true_left in R.  unfold fits_sg_profile in Q. 
       destruct p. destruct E. 
       unfold sg_profile_commutative, sg_profile_selective,
              sg_profile_is_left, sg_profile_is_right,  
              sg_profile_idempotent, sg_profile_exists_id, 
              sg_profile_exists_ann
       in *. 
       destruct Q as [[[[[[commS _] isL] isR] _] _] _]. 
       rewrite L in commS. 
       destruct R as [R | R]. 
          rewrite R in isL. apply (bop_commutative_implies_not_is_left S r b); auto. 
          rewrite R in isR. apply (bop_commutative_implies_not_is_right S r b); auto. 
Qed. 






