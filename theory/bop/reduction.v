Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop.  
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.bop_properties. 
Require Import CAS.theory.brel.reduce. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.facts. 


(* 
Section Reduction. 


Variable S       : Type.  
Variable eq      : brel S.  
Variable u       : unary_op S. 
Variable b       : binary_op S. 
Variable transS  : brel_transitive S eq. 
Variable symS    : brel_symmetric S eq. 
Variable cong_u  : uop_congruence S eq u. 
Variable cong_b  : bop_congruence S eq b. 
Variable assoc_b : bop_associative S eq b. 

(* Definition reduce := (bop_then_unary S u b). *) 

(*  Here "reduction" refers to the combination 

    brel_reduce S eq u
    bop_then_unary S u b

Definition uop_bop_left_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b (u s) t)) = true. 

Definition uop_bop_right_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b s (u t))) = true. 

Definition uop_bop_reduction (S : Type) (eq : brel S) (u : unary_op S) (b : binary_op S)
:= ∀ s t : S, eq (u (b s t)) (u (b (u s) (u t))) = true. 

Definition uop_cancellative (S : Type) (r : brel S) (u : unary_op S)
    := ∀ s t : S, r (u s) (u t) = true -> r s t = true.

Definition uop_injective (S : Type) (r : brel S) (u : unary_op S) := 
  ∀ s t : S, r (u s) (u t) = true -> r s t = true. 

Definition uop_idempotent (S : Type) (r : brel S) (u : unary_op S) := 
   ∀ s : S, r (u (u s)) (u s) = true. 

idem : u s = u (u s) 
inj  : u s = u t -> s = t 
red  : u (s + t) = u ((u s) + (u t))
dis  : u (s + t) = (u s) + (u t)

idem & dis -> red  : u (s + t) = u ((u s) + (u t))
   u (s + t) 
   = 
   u (u (s + t)) 
   = 
   u ((u s) + (u t))

*) 

Lemma bop_reduction_intro_v1 : 
     uop_bop_left_reduction S eq u b -> uop_bop_right_reduction S eq u b -> 
        uop_bop_reduction S eq u b. 
Proof. intros lr rr s t. apply (transS _ _ _ (lr s t) (rr (u s) t)). Qed.  


Lemma bop_reduction_intro_v2 : 
       uop_bop_left_reduction S eq u b -> bop_commutative S eq b -> 
          uop_bop_reduction S eq u b. 
Proof. intros lr comm_b s t. 
       assert (fact1 := lr s t).
       assert (fact2 := lr t (u s)).
       assert (fact3 := comm_b (u s) t). 
       assert (fact4 := cong_u _ _ fact3). 
       assert (fact5 := transS _ _ _ fact1 fact4). 
       assert (fact6 := transS _ _ _ fact5 fact2). 
       assert (fact7 := comm_b (u t) (u s)). 
       assert (fact8 := cong_u _ _ fact7). 
       assert (fact9 := transS _ _ _ fact6 fact8). 
       assumption. 
Qed. 


Lemma bop_reduction_intro_v3 : 
       uop_bop_right_reduction S eq u b -> bop_commutative S eq b -> 
          uop_bop_reduction S eq u b. 
Proof. intros rr comm_b s t. 
       assert (fact1 := rr s t).
       assert (fact2 := rr (u t) s ).
       assert (fact3 := comm_b s (u t)). 
       assert (fact4 := cong_u _ _ fact3). 
       assert (fact5 := transS _ _ _ fact1 fact4). 
       assert (fact6 := transS _ _ _ fact5 fact2). 
       assert (fact7 := comm_b (u t) (u s)). 
       assert (fact8 := cong_u _ _ fact7). 
       assert (fact9 := transS _ _ _ fact6 fact8). 
       assumption. 
Qed. 

Lemma bop_reduction_congruence : 
       uop_idempotent S eq u -> 
       uop_bop_reduction S eq u b -> 
       bop_congruence S (brel_reduce S eq u) (bop_then_unary S u b). 
Proof. intros idem_u red_u. 
       unfold bop_congruence. 
       unfold bop_then_unary. unfold brel_reduce. 
       intros s1 s2 t1 t2 H1 H2. 
       assert (fact1 := cong_b _ _ _ _ H1 H2). 
       assert (fact2 := cong_u _ _ fact1). 
(* 
  H1 : eq (u s1) (u t1) = true
  H2 : eq (u s2) (u t2) = true
  fact1 : eq (b (u s1) (u s2)) (b (u t1) (u t2)) = true            [cong_b] 
  fact2 : eq (u (b (u s1) (u s2))) (u (b (u t1) (u t2))) = true    [cong_u] 

   u (u (b s1 s2)) 
   = u (b s1 s2)           [idem_u] 
   = u (b (u s1) (u s2))   [red_u] 
   = u (b (u t1) (u t2))   [fact2]
   = u (b t1 t2)           [red_u] 
   = u (u (b t1 t2))       [idem_u] 
*) 
       assert (fact3 := idem_u (b s1 s2)). 
       assert (fact4 := red_u s1 s2). 
       assert (fact5 := transS _ _ _ fact3 fact4). 
       assert (fact6 := transS _ _ _ fact5 fact2). 
       assert (fact7 := red_u t1 t2). apply symS in fact7. 
       assert (fact8 := transS _ _ _ fact6 fact7). 
       assert (fact9 := idem_u (b t1 t2)).  apply symS in fact9. 
       assert (fact10 := transS _ _ _ fact8 fact9). 
       assumption. 
Qed. 


Lemma bop_reduction_associative : 
       uop_idempotent S eq u -> 
       uop_bop_left_reduction S eq u b -> 
       uop_bop_right_reduction S eq u b -> 
       bop_associative S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u lred_u rred_u s t v. 
       unfold brel_reduce, bop_then_unary. 
       assert (fact1 := assoc_b s t v). 
       assert (fact2 := cong_u _ _ fact1). 
(*
  fact1 : eq (b (b s t) v) (b s (b t v)) = true
  fact2 : eq (u (b (b s t) v)) (u (b s (b t v))) = true

   u (u (b (u (b s t)) v))
 =    u (b (u (b s t)) v)       [idem_u] 
 =    u (b (b s t) v)           [lred_u] 
 =    u (b s (b t v))           [fact2] 
 =    u (b s (u (b t v)))       [rred_u] 
 = u (u (b s (u (b t v))))      [idem_u] 
*) 
       assert (fact3 := idem_u (b (u (b s t)) v)).
       assert (fact4 := lred_u (b s t) v). apply symS in fact4. 
       assert (fact5 := transS _ _ _ fact3 fact4). 
       assert (fact6 := transS _ _ _ fact5 fact2). 
       assert (fact7 := rred_u s (b t v)). 
       assert (fact8 := transS _ _ _ fact6 fact7). 
       assert (fact9 := idem_u (b s (u (b t v)))). apply symS in fact9.
       assert (fact10 := transS _ _ _ fact8 fact9). 
       assumption. 
Qed. 


Lemma bop_reduction_commutative : 
       uop_idempotent S eq u -> 
       bop_commutative S eq b -> 
       bop_commutative S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u comm_b s t. 
       unfold brel_reduce, bop_then_unary. 
       assert (fact1 := comm_b s t). 
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u (b s t)). 
       assert (fact4 := idem_u (b t s)). apply symS in fact4. 
       assert (fact5 := transS _ _ _ fact3 fact2). 
       assert (fact6 := transS _ _ _ fact5 fact4). 
       assumption. 
Qed. 


Lemma bop_reduction_idempotent : 
       uop_idempotent S eq u -> bop_idempotent S eq b -> 
          bop_idempotent S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u idem_b s. 
       unfold brel_reduce, bop_then_unary. 
       assert (fact1 := idem_b s). 
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u (b s s)). 
       assert (fact4 := transS _ _ _ fact3 fact2). 
       assumption. 
Qed. 

Lemma bop_reduction_left_cancellative : 
       uop_cancellative S eq u -> 
       bop_left_cancellative S eq b -> 
       bop_left_cancellative S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros cancel_u lc_b. 
       unfold brel_reduce, bop_then_unary. intros  s t v H. 
       assert (fact1 := lc_b s t v).
       assert (fact2 := cancel_u _ _ H).  
       assert (fact3 := cancel_u _ _ fact2).  
       apply fact1 in fact3. 
       assert (fact4 := cong_u _ _ fact3). 
       assumption. 
Qed. 


Lemma bop_reduction_right_cancellative : 
       uop_cancellative S eq u -> 
       bop_right_cancellative S eq b -> 
       bop_right_cancellative S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros cancel_u lc_b. 
       unfold brel_reduce, bop_then_unary. intros  s t v H. 
       assert (fact1 := lc_b s t v).
       assert (fact2 := cancel_u _ _ H).  
       assert (fact3 := cancel_u _ _ fact2).  
       apply fact1 in fact3. 
       assert (fact4 := cong_u _ _ fact3). 
       assumption. 
Qed. 

Lemma bop_reduction_left_constant :
       uop_idempotent S eq u ->  
       bop_left_constant S eq b -> 
       bop_left_constant S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u lc_b. 
       unfold brel_reduce, bop_then_unary. intros  s t v. 
       assert (fact1 := lc_b s t v).
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u (b s t)). 
       assert (fact4 := idem_u (b s v)). apply symS in fact4. 
       assert (fact5 := transS _ _ _ fact3 fact2). 
       assert (fact6 := transS _ _ _ fact5 fact4). 
       assumption. 
Qed. 

Lemma bop_reduction_right_constant : 
       uop_idempotent S eq u -> 
       bop_right_constant S eq b -> 
       bop_right_constant S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u rc_b. 
       unfold brel_reduce, bop_then_unary. intros  s t v. 
       assert (fact1 := rc_b s t v).
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u (b t s)). 
       assert (fact4 := idem_u (b v s)). apply symS in fact4. 
       assert (fact5 := transS _ _ _ fact3 fact2). 
       assert (fact6 := transS _ _ _ fact5 fact4). 
       assumption. 
Qed. 

Lemma bop_reduction_is_left : 
       uop_idempotent S eq u -> 
       bop_is_left S eq b -> 
       bop_is_left S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u il_b. 
       unfold brel_reduce, bop_then_unary. intros  s t. 
       assert (fact1 := il_b s t).
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u (b s t)). 
       assert (fact4 := transS _ _ _ fact3 fact2). 
       assumption. 
Qed. 

Lemma bop_reduction_is_right : 
       uop_idempotent S eq u -> 
       bop_is_right S eq b -> 
       bop_is_right S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u ir_b. 
       unfold brel_reduce, bop_then_unary. intros  s t. 
       assert (fact1 := ir_b s t).
       assert (fact2 := cong_u _ _ fact1). 
       assert (fact3 := idem_u (b s t)). 
       assert (fact4 := transS _ _ _ fact3 fact2). 
       assumption. 
Qed. 


Lemma bop_reduction_selective : 
       uop_idempotent S eq u -> 
       bop_selective S eq b -> 
       bop_selective S (brel_reduce S eq u) (bop_then_unary S u b).
Proof. intros idem_u sel_b s t. 
       unfold brel_reduce, bop_then_unary. 
       destruct (sel_b s t) as [fact1 | fact1]. 
          left. 
          assert (fact2 := cong_u _ _ fact1). 
          assert (fact3 := idem_u (b s t)). 
          assert (fact4 := transS _ _ _ fact3 fact2). 
          assumption. 
          right. 
          assert (fact2 := cong_u _ _ fact1). 
          assert (fact3 := idem_u (b s t)). 
          assert (fact4 := transS _ _ _ fact3 fact2). 
          assumption. 
Qed. 



(******************************
Lemma bop_reduction_is_id : ∀ (i : S), 
      bop_is_id S eq b i -> 
         bop_is_id S (brel_reduce S eq u) (bop_then_unary S u b) (u i). 
Proof. intros i isI s. compute. split. 
          admit. 
          
Qed. 


exists_id
exists_ann

*******************************) 

End Reduction.


*) 