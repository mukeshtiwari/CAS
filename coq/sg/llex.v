Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.and. 

Require Import CAS.coq.os.theory. 


Section Computation.

(* for the general case t will be the identity of T. 
   for the selective S case, t can be any element of T since that case can't be reached. 
 *)

Definition llex_p2 {S T : Type} (t : T) (eq : brel S) (b2 : binary_op T) (ac a c : S) (b d : T) : T 
  := match eq a ac, eq ac c with
     | true, true   => b2 b d 
     | true, false  => b 
     | false, true  => d               
     | false, false => t 
     end. 
  
Definition bop_lex_left : ∀ {S T : Type}, T → brel S → binary_op S → binary_op T → binary_op (S * T) 
:= λ {S T} t eq b1 b2 x y,  
   match x, y with
    | (a, b), (c, d) => let ac := b1 a c in (ac, llex_p2 t eq b2 ac a c b d) 
   end.

End Computation.


Declare Scope bop_lex_left_scope.

Notation " a 'llex' [ eqS , t ] b"  := (bop_lex_left t eqS a b) (at level 1) : bop_lex_left_scope.

Open Scope brel_product_scope.
Open Scope bop_lex_left_scope.


Section Theory.

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T. 
Variable bS : binary_op S. 
Variable bT : binary_op T.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 


Variable conS : brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.  (* needed where? *) 
Variable tranS : brel_transitive S rS.

Variable wT : T.
Variable argT : T.
Variable g : T -> T.                
Variable Pg : brel_not_trivial T rT g. 

Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.  (* needed where? *) 
Variable tranT : brel_transitive T rT.
  
Variable b_conS : bop_congruence S rS bS.
Variable assS   : bop_associative S rS bS.
Variable idemS  : bop_idempotent S rS bS. 
Variable commS  : bop_commutative S rS bS.


Variable b_conT : bop_congruence T rT bT.  
Variable assT : bop_associative T rT bT. 


Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a !=S b" := (rS a b = false) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a !=T b" := (rT a b = false) (at level 15).
Notation "a *S b"  := (bS a b) (at level 15).
Notation "a *T b"  := (bT a b) (at level 15).
Notation "a <<= b" := (brel_lte_left rS bS a b = true) (at level 15).
Notation "a !<<= b" := (brel_lte_left rS bS a b = false) (at level 15).
Notation "a << b"  := (brel_lt_left rS bS a b = true) (at level 15).
Notation "a !<< b" := (brel_lt_left rS bS a b = false) (at level 15).

(*Notation "a <*> b" := (brel_product a b) (at level 15).*) 
(* Notation "a [*] b" := (bop_lex_left argT rS a b) (at level 15). *) 

Notation "[| p1 | a | c | b | d |]" := (llex_p2 argT rS bT p1 a c b d) (at level 15).


Lemma llex_p2_congruence (s1 s2 s3 s4 : S) (t1 t2 t3 t4 : T)
  (C1 : s1 =S s3) 
  (C2 : t1 =T t3)
  (C3 : s2 =S s4)
  (C4 : t2 =T t4) : 
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T ([|s3 *S s4 | s3 | s4 | t3 | t4|]). 
Proof. unfold llex_p2.
       assert (F1 := b_conS _ _ _ _ C1 C3). 
       assert (F2 := conS _ _ _ _ C1 F1). rewrite F2. 
       assert (F3 := conS _ _ _ _ F1 C3). rewrite F3.
       case_eq(rS s3 (s3 *S s4)); intro A; case_eq(rS (s3 *S s4) s4); intro B; auto. 
Qed.


Lemma bop_lex_left_congruence : bop_congruence (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]; intros H1 H2.
       unfold brel_product in H1, H2. 
       destruct (bop_and_elim _ _ H1) as [C1 C2].
       destruct (bop_and_elim _ _ H2) as [C3 C4].
       unfold bop_lex_left. unfold brel_product. apply bop_and_intro. 
          exact (b_conS _ _ _ _ C1 C3).
          apply llex_p2_congruence; auto. 
Qed.

Lemma bop_lex_left_idempotent :bop_idempotent T rT bT → bop_idempotent (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros idemT (s, t). compute. assert (I := idemS s). rewrite I. apply symS in I. rewrite I. 
       rewrite idemT. reflexivity.
Qed.        

Lemma bop_lex_left_not_idempotent : bop_not_idempotent T rT bT →  bop_not_idempotent (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [t P]. exists (wS, t). compute.
       assert (I := idemS wS). rewrite I. apply symS in I. rewrite I. exact P.
Defined. 

Lemma bop_lex_left_not_commutative : bop_not_commutative T rT bT → bop_not_commutative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [ [t t'] P]. exists ((wS, t), (wS, t')). compute. rewrite refS. 
       assert (I := idemS wS). rewrite I. apply symS in I. rewrite I. exact P. 
Defined. 


Lemma llex_p2_commutative (commT : bop_commutative T rT bT) (s1 s2 : S) (t1 t2 : T) :
    ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T ([|s2 *S s1 | s2 | s1 | t2 | t1|]).
Proof. assert (F1 := commS s1 s2).
       assert (F2 := commT t1 t2). compute. 
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS s2 (s2 *S s1)); intro B.
       - apply symS in B. rewrite (tranS _ _ _ F1 B). 
         apply symS in A. apply symS in F1. 
         rewrite (tranS _ _ _  F1 A). apply commT. 
       - assert (F3 := tranS _ _ _ A F1). apply symS in F3. rewrite F3. 
         assert (F4 : (s1 *S s2) !=S s2).
            case_eq(rS (s1 *S s2) s2); intro F5; auto. 
               apply symS in F5. rewrite (tranS _ _ _ F5 F1) in B. discriminate B.
         rewrite F4. apply refT. 
       - apply symS in F1. assert (F3 := tranS _ _ _ B F1). 
         apply symS in F3. rewrite F3.
         assert (F4 : (s2 *S s1) !=S s1).
            case_eq(rS (s2 *S s1) s1); intro F5; auto.          
               apply symS in F5. rewrite (tranS _ _ _ F5 F1) in A. 
               discriminate A. 
         rewrite F4. apply refT. 
       - assert (F3 : (s2 *S s1) !=S s1).
            case_eq(rS (s2 *S s1) s1); intro F5; auto.          
               apply symS in F5. apply symS in F1. rewrite (tranS _ _ _ F5 F1) in A. 
               discriminate A.          
         assert (F4 : (s1 *S s2) !=S s2).
            case_eq(rS (s1 *S s2) s2); intro F5; auto.          
               apply symS in F5. rewrite (tranS _ _ _ F5 F1) in B. 
               discriminate B.          
         rewrite F3, F4. apply refT. 
Qed. 

Lemma bop_lex_left_commutative : bop_commutative T rT bT → bop_commutative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros commT (s1, t1) (s2, t2).  
       unfold brel_product. unfold bop_lex_left. 
       apply bop_and_intro. 
          apply commS.
          apply llex_p2_commutative; auto. 
Qed. 


(*Definition witness_bop_lex_left_not_is_left {S T : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (t : T) 
   := if r (b s (f s)) s then ((f s, t), (s, t)) else ((s, t), (f s, t)). 
*) 
Lemma bop_lex_left_not_is_left : bop_not_is_left (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. destruct (bop_commutative_implies_not_is_left S rS bS wS f Pf symS tranS commS) as [[s1 s2] Q]. 
       exists ((s1, wT), (s2, wT)). compute. rewrite Q. reflexivity. 
Defined.

(*Definition witness_bop_lex_left_not_is_right {S T : Type} (r : brel S) (b : binary_op S) (s : S) (f : S -> S) (t : T) 
   := if r (b s (f s)) s then ((s, t), (f s, t)) else ((f s, t), (s, t)).
*)           

Lemma bop_lex_left_not_is_right : bop_not_is_right (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. destruct (bop_commutative_implies_not_is_right S rS bS wS f Pf symS tranS commS) as [[s1 s2] Q]. 
       exists ((s1, wT), (s2, wT)). compute. rewrite Q. reflexivity. 
Defined.

Lemma bop_lex_left_selective : 
     bop_selective S rS bS → bop_selective T rT bT → bop_selective (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS selT [s1 t1] [s2 t2].
       unfold bop_lex_left.
       unfold brel_product. unfold llex_p2.
       destruct (selS s1 s2) as [A | A]; destruct (selT t1 t2) as [B | B]; rewrite A. 
       - apply symS in A. rewrite A.
         case_eq(rS (s1 *S s2) s2); intro C. 
         + left. rewrite B. compute. reflexivity. 
         + left. rewrite refT. compute. reflexivity. 
       - apply symS in A. rewrite A.
         case_eq(rS (s1 *S s2) s2); intro C. 
         + right. rewrite B. compute. reflexivity. 
         + left. rewrite refT. compute. reflexivity. 
       - case_eq(rS s1 (s1 *S s2)); intro C. 
         + apply symS in C. rewrite C. 
           left. rewrite B. compute. reflexivity. 
         + right. rewrite refT. compute. reflexivity. 
       - case_eq(rS s1 (s1 *S s2)); intro C. 
         + apply symS in C. rewrite C. 
           right. rewrite B. compute. reflexivity. 
         + right. rewrite refT. compute. reflexivity. 
Qed.

Lemma bop_lex_left_not_selective_left : 
     bop_not_selective S rS bS → bop_not_selective (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [ [s1 s2] [A B]]. exists ((s1, wT), (s2, wT)). compute.        
       rewrite A, B.  split; reflexivity. 
Defined.   


Lemma bop_lex_left_not_selective_right : 
     bop_selective S rS bS → bop_not_selective T rT bT → bop_not_selective (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS [ [t1 t2] [A B]]. exists ((wS, t1), (wS, t2)). compute. 
       assert (I := idemS wS). rewrite I. apply symS in I. rewrite I. rewrite A, B. split; reflexivity. 
Defined.



Lemma bop_lex_left_is_id (iS : S ) (iT : T )
       (pS : bop_is_id S rS bS iS) (pT : bop_is_id T rT bT iT) : 
         bop_is_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (iS, iT). 
Proof. intros [s t].  compute.
       destruct (pS s) as [A1 A2]. destruct (pT t) as [B1 B2]. 
       rewrite A1, A2. apply symS in A1. apply symS in A2. 
       case_eq(rS iS (iS *S s)); intro C. 
       - rewrite A2. assert (D := commS s iS). apply symS in C. 
         rewrite (tranS _ _ _ D C). split; assumption. 
       - rewrite A2.
         case_eq(rS (s *S iS) iS); intro D. 
         + split. apply refT. exact B2.
         + split; apply refT.
Defined.


Lemma bop_lex_left_exists_id : bop_exists_id S rS bS -> bop_exists_id T rT bT -> 
                              bop_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros [iS pS] [iT pT]. exists (iS, iT). apply bop_lex_left_is_id; auto. Defined. 

Lemma bop_lex_left_not_exists_id_left : bop_not_exists_id S rS bS -> bop_not_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. unfold bop_not_exists_ann. 
       intros pS (s, t). destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. compute. rewrite F. reflexivity. 
          exists (x, t). right. compute. rewrite F. reflexivity. 
Defined. 

Lemma bop_lex_left_not_exists_id_right: bop_not_exists_id T rT bT -> bop_not_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. unfold bop_not_exists_ann. 
       intros pT (s, t). destruct (pT t) as [x [F | F]]. 
          - exists (s, x). left. compute. assert (I := idemS s).  rewrite I. apply symS in I. rewrite I. exact F. 
          - exists (s, x). right. compute. assert (I := idemS s).  rewrite I. apply symS in I. rewrite I. exact F. 
Defined.


Lemma bop_lex_left_is_ann (aS : S ) (aT : T )
                         (pS : bop_is_ann S rS bS aS) (pT : bop_is_ann T rT bT aT) :
                             bop_is_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (aS, aT). 
Proof. intros [s t]. compute. 
       destruct (pS s) as [A1 A2]. destruct (pT t) as [B1 B2]. 
       rewrite A1, A2. apply symS in A1. apply symS in A2.
       rewrite A1. 
       case_eq(rS s (s *S aS)); intro C. 
       - apply symS in C. assert (D := commS aS s). 
         rewrite (tranS _ _ _ D C). split; assumption. 
       - case_eq(rS (aS *S s) s); intro D. 
         + split. exact B1. apply refT. 
         + split; apply refT.
Defined.


Lemma bop_lex_left_exists_ann : bop_exists_ann S rS bS -> bop_exists_ann T rT bT -> 
                              bop_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros [iS pS] [iT pT]. exists (iS, iT). apply bop_lex_left_is_ann; auto. Defined. 

Lemma bop_lex_left_not_exists_ann_left : bop_not_exists_ann S rS bS -> bop_not_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros pS (s, t). destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. compute. rewrite F. reflexivity. 
          exists (x, t). right. compute. rewrite F. reflexivity. 
Defined. 

Lemma bop_lex_left_not_exists_ann_right : bop_not_exists_ann T rT bT -> bop_not_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros pT (s, t). destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. compute. assert (I := idemS s).  rewrite I. apply symS in I. rewrite I. exact F. 
          exists (s, x). right. compute. assert (I := idemS s).  rewrite I. apply symS in I. rewrite I. exact F. 
Defined. 


(*

(* this is really just a curiosity since bS is communtative and so bop_is_right cannot hold. *) 
Lemma bop_lex_left_left_cancellative (rightS : bop_is_right S rS bS) (canT : bop_left_cancellative T rT bT) :
               bop_left_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros [s1 t1] [s2 t2] [s3 t3]. unfold brel_product. unfold bop_lex_left.   
       intros A. apply bop_and_elim in A. destruct A as [A B].
       assert (R1 : rS (s1 *S s2) s2 = true). apply rightS. 
       assert (R2 : rS (s1 *S s3) s3 = true). apply rightS. 
       apply symS in R1. assert (C := tranS _ _ _ R1 A). 
       rewrite (tranS _ _ _ C R2). 
       unfold llex_p2 in B. 
       case_eq(rS s1 (s1 *S s2)); intro D; rewrite D in B. 
       - rewrite R2 in B. rewrite (symS _ _ R1) in B. 
         assert (E := tranS _ _ _ D A). rewrite E in B. 
         rewrite (canT _ _ _ B). compute. reflexivity. 

       - rewrite R2 in B. apply symS in C. rewrite (tranS _ _ _ A C) in B. 
         case_eq(rS s1 (s1 *S s3)); intro E; rewrite E in B.
         + apply symS in A. rewrite (tranS _ _ _ E A) in D. discriminate D.
         + rewrite B. compute; reflexivity. 
Qed. 


Lemma bop_lex_not_left_cancellative_general (a b c : T):
  (bop_not_is_right S rS bS) + (bop_not_left_cancellative T rT bT) -> 
               bop_not_left_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros [[[s1 s2] A] | [[t1 [t2 t3]] [B C]]].
       - exists ((s1, a), ((s1 *S s2, b), (s2, c))). compute.
         assert (C : rS (s1 *S (s1 *S s2)) (s1 *S s2) = true). admit.
         rewrite C. rewrite A. 
         admit.
       - exists ((wS, t1), ((wS, t2), (wS, t3))). compute.
         rewrite refS. rewrite (symS _ _ (refS wS)).
         assert (I := idemS wS). rewrite I. apply symS in I. rewrite I.          
         rewrite B, C. split; reflexivity. 
Admitted. 

  (* 
   s1 <> s2 = f s1 
   t1 <> t2 = g t1 

   1) s1 < s2 :  (s1 ,t1) * (s2, t1) =  (s1 ,t1) * (s2, f t1) 
   2) s2 < s1 :  (s2 ,t1) * (s1, t1) =  (s2 ,t1) * (s1, f t1) 
   3) s2 = s1 : contradiction. 


   if s < f s 
   then ((s ,t), (f s, t), (f s, g t))
   else ((f s ,t), (s, t), (s, g t))

*) 
Lemma bop_lex_left_not_left_cancellative (s1 s2 s3 : S) (t1 t2 t3 : T) : bop_not_left_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists ((s1, t1), ((s2, t2), (s3, t3))). compute.
       assert (A : rS s2 s3 = false). admit. rewrite A. 
       assert (B : rS (s1 *S s2) (s1 *S s3) = true). admit. 
       rewrite B.
       case_eq(rS s1 (s1 *S s2)); intro C; case_eq(rS s1 (s1 *S s3)); intro D.
       - admit. 
       - admit.
       - admit.
       - admit.          
Admitted. 


(*
  intros selS commS. 
       destruct (Pf wS) as [Ls Rs]. destruct (Pg wT) as [Lt Rt]. 
       assert (fact1 := brel_lt_left_total_order_split S rS bS symS refS tranS b_conS selS wS (f wS)). 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       exists ((wS, wT), ((f wS, wT), (f wS, g wT))); simpl. 
          rewrite (refS (wS *S (f wS))). rewrite eq, lt. 
          rewrite (refS (f wS)). rewrite (refT wT). rewrite Lt. auto. 
       exists ((f wS, wT), ((wS, wT), (wS, g wT))); simpl. 
          rewrite (refS ((f wS) *S wS)). rewrite Rs. 
          rewrite (refS wS). rewrite Lt. simpl. 
          apply brel_lt_left_false_elim in lt. 
          unfold brel_lt_left, brel_conjunction, brel_complement, brel_lte_left.
          destruct lt as [lt | lt]. 
             rewrite Rs. 
             assert (fact2 := selS wS (f wS)). 
             destruct fact2 as [J | K]. 
                apply symS in J. rewrite J in lt. discriminate. 
                apply symS in K. 
                assert (fact3 := commS wS (f wS)). 
                assert (fact4 := tranS _ _ _ K fact3). 
                rewrite fact4. simpl. rewrite (refT wT). auto. 
       rewrite lt in eq. discriminate.        
Defined.
*) 

Definition cef_bop_lex_left_not_cancellative {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T) (g : T -> T) 
  := if brel_lt_left rS bS s (f s) 
     then ((s, t), ((f s, t), (f s, g t))) 
     else ((f s, t), ((s, t), (s, g t))).



Lemma bop_lex_left_not_left_cancellative_v2 : 
      bop_selective S rS bS → bop_commutative S rS bS → bop_not_left_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS commS.
       exists (cef_bop_lex_left_not_cancellative rS bS wS f wT g). 
       destruct (Pf wS) as [Ls Rs]. destruct (Pg wT) as [Lt Rt]. 
       assert (fact1 := brel_lt_left_total_order_split S rS bS symS refS tranS b_conS selS wS (f wS)). 
       unfold cef_bop_lex_left_not_cancellative. 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt. simpl. 
          rewrite (refS (wS *S (f wS))). rewrite eq, lt. 
          rewrite (refS (f wS)). rewrite (refT wT). rewrite Lt. auto. 
       rewrite lt. simpl. 
          rewrite (refS ((f wS) *S wS)). rewrite Rs. 
          rewrite (refS wS). rewrite Lt. simpl. 
          apply brel_lt_left_false_elim in lt. 
          unfold brel_lt_left, brel_conjunction, brel_complement, brel_lte_left.
          destruct lt as [lt | lt]. 
             rewrite Rs. 
             assert (fact2 := selS wS (f wS)). 
             destruct fact2 as [J | K]. 
                apply symS in J. rewrite J in lt. discriminate. 
                apply symS in K. 
                assert (fact3 := commS wS (f wS)). 
                assert (fact4 := tranS _ _ _ K fact3). 
                rewrite fact4. simpl. rewrite (refT wT). auto. 
       rewrite lt in eq. discriminate.        
Defined. 


Lemma bop_lex_left_not_right_cancellative : 
      bop_selective S rS bS → bop_commutative S rS bS → bop_not_right_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS commS .
       exists (cef_bop_lex_left_not_cancellative rS bS wS f wT g). 
       destruct (Pf wS) as [Ls Rs]. destruct (Pg wT) as [Lt Rt]. 
       assert (fact1 := brel_lt_left_total_order_split S rS bS symS refS tranS b_conS selS wS (f wS)). 
       unfold cef_bop_lex_left_not_cancellative. 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt. simpl. 
          rewrite (refS (bS (f wS) wS)). rewrite (refS (f wS)). rewrite Lt, Rs. 
          apply brel_lt_left_asymmetric in lt; auto. rewrite lt; auto. 
          rewrite (refT wT); auto. simpl.
       rewrite lt. simpl. 
          rewrite (refS (bS wS (f wS))). rewrite Ls. 
          rewrite (refS wS). rewrite lt, Lt. simpl. rewrite (refT wT); auto. 
Defined. 



(* 
   s1 <> s2 = f s1 
   t1 <> t2 = g t1 

   1) s1 < s2 :  (s2 ,t1) * (s1, t1) <>  (s2 ,t1) * (s1, g t1) 
   2) s2 < s1 :  (s1 ,t1) * (s2, t1) <>  (s1 ,t1) * (s2, g t1) 
   3) s2 = s1 : contradiction. 

 *)

Definition cef_bop_lex_left_not_constant {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T) (g : T -> T) 
  := if brel_lt_left rS bS s (f s) 
     then ((f s, t), ((s, t), (s, g t)))
     else ((s, t), ((f s, t), (f s, g t))). 


Lemma bop_lex_left_not_left_constant : 
      bop_selective S rS bS → bop_commutative S rS bS → bop_not_left_constant (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS commS.
       exists (cef_bop_lex_left_not_constant rS bS wS f wT g). 
       unfold cef_bop_lex_left_not_constant. 
       destruct (Pf wS) as [Ls Rs]. destruct (Pg wT) as [Lt Rt]. 
       assert (fact1 := brel_lt_left_total_order_split S rS bS symS refS tranS b_conS selS wS (f wS)). 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt; simpl. 
          rewrite (refS ((f wS) *S wS)). rewrite Rs. 
          apply brel_lt_left_asymmetric in lt; auto. rewrite lt, Lt. auto. 
       rewrite lt; simpl. 
          rewrite (refS (wS *S (f wS))). rewrite Ls. rewrite lt, Lt. auto. 
Defined. 
   

Lemma bop_lex_left_not_right_constant : 
      bop_selective S rS bS → bop_commutative S rS bS → bop_not_right_constant (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS commS.
       exists (cef_bop_lex_left_not_constant rS bS wS f wT g). 
       unfold cef_bop_lex_left_not_constant. 
       destruct (Pf wS) as [Ls Rs]. destruct (Pg wT) as [Lt Rt]. 
       assert (fact1 := brel_lt_left_total_order_split S rS bS symS refS tranS b_conS selS wS (f wS)). 
       destruct fact1 as [[[eq lt] | [eq lt]] | [eq lt]]. 
       rewrite eq in Ls. discriminate. 
       rewrite lt; simpl. 
          rewrite (refS (bS wS (f wS))). rewrite Ls. rewrite lt, Lt. auto. 
       rewrite lt; simpl. 
          rewrite (refS (bS (f wS) wS)). rewrite Rs. 
          apply brel_lt_left_false_elim in lt; auto. 
          destruct lt as [lt | lt].
             unfold brel_lt_left, brel_conjunction, brel_lte_left, brel_complement. rewrite Rs. 
             assert (fact1 : rS (f wS) (bS (f wS) wS) = true). 
                destruct (selS wS (f wS)) as [fact2 | fact2].
                   apply symS in fact2.  rewrite fact2 in lt. discriminate. 
                   assert (fact3 := commS wS (f wS)). apply symS in fact2. 
                   apply (tranS _ _ _ fact2 fact3). 
             rewrite fact1; auto.          
       rewrite eq in lt. discriminate. 
Defined.


Definition cef_bop_lex_left_not_anti_left {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T)  
  := if rS (bS s (f s)) s then ((s, t), (f s, t)) else ((f s, t), (s, t)). 


Lemma bop_lex_left_not_anti_left : 
      bop_selective S rS bS → bop_commutative S rS bS → bop_not_anti_left (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS commS .
       exists (cef_bop_lex_left_not_anti_left rS bS wS f wT). 
       unfold cef_bop_lex_left_not_anti_left. 
       destruct (Pf wS) as [Ls Rs]. 
       unfold bop_not_anti_left, brel_product, bop_lex_left. 
       unfold brel_lt_left. unfold brel_conjunction, brel_lte_left, brel_complement. 
       assert (fact1 := commS wS (f wS)). 
       assert (H := selS wS (f wS)). 
       destruct H as [H | H]. 
          rewrite H, Ls.  simpl. apply symS in H. rewrite H. simpl. apply refT. 
          assert (fact2 : rS (bS wS (f wS)) wS = false). 
             apply symS in H. 
             assert (fact3 := brel_transititivity_implies_dual _ _ tranS _ _ _ H Rs).              
             rewrite fact3. reflexivity. 
          rewrite fact2. apply symS in H. 
          assert (fact3 := tranS _ _ _ H fact1). rewrite fact3, Rs. simpl. apply refT. 
Defined. 

Definition cef_bop_lex_left_not_anti_right {S T : Type} (rS : brel S) (bS : binary_op S) (s : S) (f : S -> S) (t : T)  
  := if rS (bS s (f s)) s then ((s, t), (f s, t)) else ((f s, t), (s, t)). 

Lemma bop_lex_left_not_anti_right : 
      bop_selective S rS bS → bop_commutative S rS bS → bop_not_anti_right (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS commS .
       exists (cef_bop_lex_left_not_anti_right rS bS wS f wT). 
       unfold cef_bop_lex_left_not_anti_right. 
       destruct (Pf wS) as [Ls Rs]. 
       unfold bop_not_anti_right, brel_product, bop_lex_left. 
       unfold brel_lt_left. unfold brel_conjunction, brel_lte_left, brel_complement. 
       assert (fact1 := commS wS (f wS)). 
       assert (H := selS wS (f wS)). 
       destruct H as [H | H]. 
          rewrite H. apply symS in H. 
          assert (fact2 := tranS _ _ _ H fact1). 
          assert (fact3 := brel_transititivity_implies_dual _ _ tranS _ _ _ fact2 Ls). 
          apply (brel_symmetric_implies_dual _ _ symS) in fact3. 
          rewrite Rs, fact2, fact3. simpl. apply refT. 

          assert (fact2 : rS (bS wS (f wS)) wS = false).
             apply symS in H. 
             assert (fact3 := brel_transititivity_implies_dual _ _ tranS _ _ _ H Rs).              
             rewrite fact3. reflexivity. 
          rewrite fact2, Ls.  
          apply symS in H. rewrite H. simpl. 
          case_eq(rS wS (bS wS (f wS))); intro J. 
             simpl. apply refT. 
             simpl. apply refT. 
Defined. 

*)


(*================== ASSOCIATIVITY ========================

A bit tedious .... 

*) 

Lemma llex_assoc_case1_aux 
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)):
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])). 
Proof. unfold llex_p2.
       assert (D := tranS _ _ _ A2 C2). apply symS in C1. apply symS in A1. 
       assert (E := tranS _ _ _ C1 A1).
       assert (F := assS s1 s2 s3). 
       assert (G := tranS _ _ _ C1 F). apply symS in G. 
       assert (H := tranS _ _ _ A2 G). 
       assert (I := tranS _ _ _ H E). rewrite I. apply symS in D. 
       assert (J := tranS _ _ _ D H). rewrite J.
       apply symS in E. apply symS in J.
       assert (K := tranS _ _ _ E J). 
       case_eq(rS (s1 *S s2) s2); intro L; case_eq(rS s2 (s2 *S s3)); intro M. 
       - apply assT. 
       - apply symS in L. rewrite (tranS _ _ _ L K) in M. discriminate M. 
       - apply symS in M. rewrite (tranS _ _ _ K M) in L. discriminate L. 
       - apply refT. 
Qed. 

Lemma llex_assoc_case1 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)):
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case1_aux A1 C1 A2 C2). Qed. 

Lemma llex_assoc_case2_aux
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T t1. 
Proof. unfold llex_p2.
       apply symS in C1. apply symS in A1. 
       assert (E := tranS _ _ _ C1 A1).
       assert (F := assS s1 s2 s3). 
       assert (G := tranS _ _ _ C1 F). apply symS in G. 
       assert (H := tranS _ _ _ A2 G). 
       assert (I := tranS _ _ _ H E). rewrite I.
       assert (J : (s1 *S (s2 *S s3)) =S (s2 *S s3)). 
       (*
         s1 *S (s2 *S s3)
         = s1 *S ((s2 * S s2) *S s3)
         = s1 *S (s2 * S (s2 *S s3))
         = (s1 *S s2) * S (s2 *S s3)
         = s3 * S (s2 *S s3)
         = (s3 * S s2) *S s3
         = (s2 * S s3) *S s3
         = s2 * S (s3 *S s3)
         = s2 * S s3 
        *)
          assert (J1 : (s1 *S (s2 *S s3)) =S (s1 *S ((s2 *S s2) *S s3))).
             assert (J2 := b_conS _ _ _ _ (idemS s2) (refS s3)). 
             assert (J3 := b_conS _ _ _ _ (refS s1) J2).  apply symS in J3.
             exact J3.
          assert (J2 : (s1 *S (s2 *S s3)) =S (s1 *S (s2 *S (s2 *S s3)))).
             assert (J3 := assS s2 s2 s3). 
             assert (J4 := b_conS _ _ _ _ (refS s1) J3).  apply symS in J3.
             exact (tranS _ _ _ J1 J4).
          assert (J3 : (s1 *S (s2 *S s3)) =S ((s1 *S s2) *S (s2 *S s3))).  
             assert (J4 := assS s1 s2 (s2 *S s3)). apply symS in J4. 
             exact (tranS _ _ _ J2 J4).
          assert (J4 : (s1 *S (s2 *S s3)) =S (s3 *S (s2 *S s3))).
             assert (J5 := b_conS _ _ _ _ E (refS (s2 *S s3))). apply symS in J5.
             exact (tranS _ _ _ J3 J5).             
          assert (J5 : (s1 *S (s2 *S s3)) =S ((s2 *S s3) *S s3)).
             assert (J6 := commS s3 (s2 *S s3)).
             exact (tranS _ _ _ J4 J6). 
          assert (J7 : (s1 *S (s2 *S s3)) =S (s2 *S (s3 *S s3))).  
             assert (J8 := assS s2 s3 s3).  
             exact (tranS _ _ _ J5 J8). 
          assert (J8 : (s1 *S (s2 *S s3)) =S (s2 *S s3)).
             assert (J9 := b_conS _ _ _ _ (refS s2) (idemS s3)). 
             exact (tranS _ _ _ J7 J9). 
         exact J8. 
      rewrite J in C2. discriminate C2. 
Qed. 

Lemma llex_assoc_case2
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case2_aux A1 C1 A2 C2). Qed. 


Lemma llex_assoc_case3_aux_selS
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (selS : bop_selective S rS bS) 
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. unfold llex_p2.
       assert (F0 := assS s1 s2 s3).
       assert (F2 := tranS _ _ _ A1 F0). 
       assert (F3 := tranS _ _ _ F2 C2). 
       assert (F4 : s1 !=S (s1 *S s2)).
          case_eq(rS s1 (s1 *S s2)); intro F4; auto.
             rewrite (tranS _ _ _ F4 F2) in A2. discriminate A2. 
       rewrite F4.
       assert (F5 : (s2 *S s3) =S s3). apply symS in F3.
          assert (F6 := tranS _ _ _ F3 A1). 
          exact (tranS _ _ _ F6 C1). 
       rewrite F5. 
       destruct (selS s1 s2) as [A | A]; destruct (selS s2 s3) as [B | B]. 
       - apply symS in B. rewrite B.
         case_eq(rS (s1 *S s2) s2); intro F6.
         + apply refT. 
         + apply symS in B. rewrite (tranS _ _ _ F3 B) in F6.
           discriminate F6.
       - apply symS in A. rewrite A in F4. discriminate F4. 
       - rewrite A. apply symS in B. rewrite B. apply refT. 
       - rewrite A. apply symS in A. rewrite (tranS _ _ _ A F3). apply refT. 
Qed. 

Lemma llex_assoc_case3_aux_idT 
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (idT : bop_is_id T rT bT argT) 
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3).
       assert (F2 := tranS _ _ _ A1 C1).
       assert (F3 := tranS _ _ _ A1 F1). 
       assert (F4 := tranS _ _ _ F3 C2). apply symS in F4. 
       assert (F5 := tranS _ _ _ F4 F2).     
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS s2 (s2 *S s3)); intro B.
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + apply refT. 
         + rewrite F5 in D. discriminate D. 
         + assert (F6 := tranS _ _ _ B F4). apply symS in F6.
           rewrite F6 in C. discriminate C. 
         + rewrite F5 in D. discriminate D. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + assert (F6 := tranS _ _ _ F4 C). apply symS in F6.
           rewrite F6 in B. discriminate B. 
         + rewrite F5 in D. discriminate D. 
         + destruct (idT t3) as [F6 F7]. exact F6.
         + rewrite F5 in D. discriminate D. 
Qed. 
  
Lemma llex_assoc_case3 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (selS_or_idT : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) 
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       destruct selS_or_idT  as [selS | idT].
       - exact (llex_assoc_case3_aux_selS selS A1 C1 A2 C2).
       - exact (llex_assoc_case3_aux_idT idT A1 C1 A2 C2). 
Qed. 

Lemma llex_assoc_case4_aux 
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T argT.
Proof. unfold llex_p2.
       assert (A := assS s1 s2 s3). 
       assert (B := assS s1 s2 s2). 
       assert (C := assS s2 s1 s2). apply symS in C1.        
       assert (F1 : (s2 *S s3) =S (s1 *S (s2 *S s3))).
           (* s2 *S s3
              = s2 *S ((s1 *S s2) *S s3)
              = (s2 *S (s1 *S s2)) *S s3
              = ((s1 *S s2) * s2) *S s3
              = ((s1 *S (s2 * s2)) *S s3
              = ((s1 *S s2) *S s3
              = (s1 *S (s2 *S s3))
            *)
          assert (F5 := b_conS _ _ _ _ (refS s2) C1). 
          assert (F6 := assS s2 (s1 *S s2) s3). apply symS in F6. 
          assert (F7 := tranS _ _ _ F5 F6).
          assert (F8 := commS s2 (s1 *S s2)). 
          assert (F9 := b_conS _ _ _ _ F8 (refS s3)). 
          assert (F10 := tranS _ _ _ F7 F9).
          assert (F11 := assS s1 s2 s2). 
          assert (F12 := b_conS _ _ _ _ F11 (refS s3)). 
          assert (F13 := tranS _ _ _ F10 F12).
          assert (F14 := b_conS _ _ _ _ (refS s1) (idemS s2)). 
          assert (F15 := b_conS _ _ _ _ F14 (refS s3)).
          assert (F16 := tranS _ _ _ F13 F15).          
          assert (F17 := assS s1 s2 s3). 
          exact (tranS _ _ _ F16 F17). 
       apply symS in F1. rewrite F1 in C2. discriminate C2. 
Qed. 

Lemma llex_assoc_case4 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case4_aux A1 C1 A2 C2). Qed. 

Lemma llex_assoc_case5_aux
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (selS_or_idT : (bop_selective S rS bS) + (bop_is_id T rT bT argT))     
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])).
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3). 
       assert (F2 := tranS _ _ _ A1 F1). apply symS in F2. 
       assert (F3 := tranS _ _ _ A2 F2). rewrite F3.
       assert (F4 : (s1 *S s2) =S (s2 *S s3)). apply symS in F3. 
          assert (F5 := tranS _ _ _ F3 A2). 
          exact (tranS _ _ _ F5 C2).           
       assert (F5 : rS (s2 *S s3) s3 = false).
          case_eq(rS (s2 *S s3) s3); intro F6; auto. 
             assert (F7 := tranS _ _ _ F4 F6). apply symS in F7. 
             assert (F8 := tranS _ _ _ F7 A1). apply symS in F8. 
             rewrite F8 in C1. discriminate C1. 
       rewrite F5.
       destruct selS_or_idT  as [selS | idT].
       - destruct(selS s1 s2) as [A | A].
         + case_eq(rS s2 (s2 *S s3)); intro B.
           *  assert (F6 : (s1 *S s2) =S s2). 
              apply symS in B. exact (tranS _ _ _ F4 B). 
           rewrite F6. apply refT.
           * destruct (selS s2 s3) as [F6 | F6].
               apply symS in F6. rewrite F6 in B. discriminate B. 
               rewrite F6 in F5. discriminate F5. 
         + rewrite A. apply symS in A. rewrite (tranS _ _ _ A F4). 
           apply refT. 
       - case_eq(rS (s1 *S s2) s2); intro A.
         + case_eq(rS s2 (s2 *S s3)); intro B.
           * apply refT. 
           * apply symS in A. rewrite (tranS _ _ _ A F4) in B.
             discriminate B. 
         + case_eq(rS s2 (s2 *S s3)); intro B.
           * apply symS in F4.
             assert (F6 := tranS _ _ _ B F4). apply symS in F6. 
             rewrite F6 in A. discriminate A.             
           *  destruct (idT t1) as [F6 F7]. apply symT. exact F7. 
Qed. 

       
Lemma llex_assoc_case5
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (selS_or_idT : (bop_selective S rS bS) + (bop_is_id T rT bT argT))   
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]).
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case5_aux selS_or_idT A1 C1 A2 C2). Qed.

Lemma llex_assoc_case6_aux
  {s1 s2 s3 : S}
  {t1 t2    : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T t1.
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3). 
       assert (F2 := tranS _ _ _ A1 F1). apply symS in F2. 
       rewrite (tranS _ _ _ A2 F2). 
       case_eq(rS (s1 *S s2) s2); intro A. 
       - assert (F3 : (s1 *S (s2 *S s3)) =S (s2 *S s3)).
            assert (F4 := b_conS _ _ _ _ A (refS s3)). apply symS in F1. 
            exact (tranS _ _ _ F1 F4).             
         rewrite F3 in C2. discriminate C2. 
       - apply refT. 
Qed. 

Lemma llex_assoc_case6
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case6_aux A1 C1 A2 C2). Qed.   


Lemma llex_assoc_case7_aux
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. unfold llex_p2.
       assert (F0 := assS s1 s2 s3). 
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS s2 (s2 *S s3)); intro B.
       - assert (F1 := tranS _ _ _ A A1).
         rewrite (tranS _ _ _ F1 F0) in A2. discriminate A2. 
       - assert (F1 := tranS _ _ _ A A1).
         rewrite (tranS _ _ _ F1 F0) in A2. discriminate A2. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D. 
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + apply refT.
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + assert (F1 : s2 =S (s1 *S s2)). apply symS in C2. 
              assert (F2 := tranS _ _ _ B C2). apply symS in A1. apply symS in F0. 
              assert (F3 := tranS _ _ _ F0 A1). 
              exact (tranS _ _ _ F2 F3). 
           apply symS in F1. rewrite F1 in C. discriminate C.          
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D. 
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + assert (F1 : (s2 *S s3) =S s2).
              assert (F2 := tranS _ _ _ A1 F0). 
              assert (F3 := tranS _ _ _ F2 C2). apply symS in F3. 
              exact (tranS _ _ _ F3 C). 
           apply symS in F1. rewrite F1 in B. discriminate B.            
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + apply refT.
Qed. 

  
Lemma llex_assoc_case7
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case7_aux A1 C1 A2 C2). Qed.   


Lemma llex_assoc_case8_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
 ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T argT.
Proof. compute.
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS (s1 *S s2) s2); intro B.
       - assert (F1 := tranS _ _ _ A A1).  
         assert (F2 := assS s1 s2 s3). 
         rewrite (tranS _ _ _ F1 F2) in A2.
         discriminate A2.
       - assert (F1 := tranS _ _ _ A A1).  
         assert (F2 := assS s1 s2 s3). 
         rewrite (tranS _ _ _ F1 F2) in A2.
         discriminate A2.
       - assert (F1 : (s1 *S (s2 *S s3)) =S (s2 *S s3)). 
           assert (F2 := b_conS _ _ _ _ B (refS s3)). 
           assert (F3 := assS s1 s2 s3). apply symS in F3. 
           exact (tranS _ _ _ F3 F2). 
         rewrite F1 in C2. discriminate C2. 
       - apply refT.
Qed. 

Lemma llex_assoc_case8
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       exact (llex_assoc_case8_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).
Qed.   

Lemma llex_assoc_case9_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  t3 =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])).
Proof. unfold llex_p2.
       assert (F : (s1 *S s2) =S ((s1 *S s2) *S s3)).
          (* F1 : s1 = (s2 *S s3). 
             so (s1 *S s2) 
                = ((s2 *S s3) *S s2) 
                = ((s3 *S s2) *S s2) 
                = s3 *S (s2 *S s2) 
                = s3 *S s2
                = s2 *S s3
                = ((s1 *S s2) *S s3)
          *) 
          assert (F1 := tranS _ _ _ A2 C2).
          assert (F2 := b_conS _ _ _ _ F1 (refS s2)). 
          assert (F3 := commS s2 s3). 
          assert (F4 := b_conS _ _ _ _ F3 (refS s2)). 
          assert (F5 := tranS _ _ _ F2 F4).
          assert (F6 := assS s3 s2 s2). 
          assert (F7 := tranS _ _ _ F5 F6).
          assert (F8 := b_conS _ _ _ _ (refS s3) (idemS s2)). 
          assert (F9 := tranS _ _ _ F7 F8). apply symS in F3. 
          assert (F10 := tranS _ _ _ F9 F3). apply symS in C2. 
          assert (F11 := tranS _ _ _ F10 C2).
          assert (F12 := assS s1 s2 s3). apply symS in F12. 
          exact (tranS _ _ _ F11 F12).
       rewrite F in A1. discriminate A1. 
Qed. 
       
Lemma llex_assoc_case9
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       exact (llex_assoc_case9_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).       
Qed.   

Lemma llex_assoc_case10
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3))  : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       assert (F1 := assS s1 s2 s3). apply symS in C1. 
       assert (F2 := tranS _ _ _ C1 F1). apply symS in F2. 
       assert (F3 := tranS _ _ _ A2 F2). 
       assert (F4 : (s1 *S (s2 *S s3)) =S (s2 *S s3)).
          (* 
             s1 *S (s2 *S s3)
             = s3 *S (s2 *S s3)
             = (s3 *S s2) *S s3
             = (s2 *S s3) *S s3
             = s2 *S (s3 *S s3)
             = s2 *S s3 
          *) 
          assert (F5 := b_conS _ _ _ _ F3 (refS (s2 *S s3))).
          assert (F6 := commS s3 (s2 *S s3)).
          assert (F7 := tranS _ _ _ F5 F6). 
          assert (F8 := assS s2 s3 s3). 
          assert (F9 := tranS _ _ _ F7 F8). 
          assert (F10 := b_conS _ _ _ _ (refS s2) (idemS s3)).           
          exact (tranS _ _ _ F9 F10).           
       rewrite F4 in C2. discriminate C2. 
Qed. 


Lemma llex_assoc_case11_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  t3 =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]). 
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3). 
       assert (F2 := tranS _ _ _ F1 C2). apply symS in C1. 
       assert (F3 := tranS _ _ _ C1 F2). apply symS in C1. 
       case_eq(rS s2 (s2 *S s3)); intro A; case_eq(rS (s2 *S s3) s3); intro B.
       - assert (F4 := tranS _ _ _ A B).
         assert (F5 : (s1 *S s2) =S ((s1 *S s2) *S s3)). 
            assert (F6 := b_conS _ _ _ _ (refS s1) A).  apply symS in F1. 
            exact (tranS _ _ _ F6 F1).             
         rewrite F5 in A1. discriminate A1. 
       - assert (F4 : (s1 *S s2) =S ((s1 *S s2) *S s3)).
            assert (F6 := b_conS _ _ _ _ (refS s1) A).  apply symS in F1. 
            exact (tranS _ _ _ F6 F1).             
         rewrite F4 in A1. discriminate A1.            
       - apply refT. 
       - apply symS in F3. rewrite F3 in B. discriminate B. 
Qed. 
         
Lemma llex_assoc_case11
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. 
   exact (llex_assoc_case11_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).
Qed. 

Lemma llex_assoc_case12
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       assert (F1 : (s1 *S (s2 *S s3)) =S (s2 *S s3)). 
          apply symS in C1. 
          assert (F2 := b_conS _ _ _ _ (refS s2) C1). 
          assert (F3 := assS s2 (s1 *S s2) s3). apply symS in F3. 
          assert (F4 := tranS _ _ _ F2 F3).
          assert (F5 : (s2 *S (s1 *S s2)) =S (s1 *S s2)). 
             assert (F6 := commS s2 (s1 *S s2)). 
             assert (F7 := assS s1 s2 s2). 
             assert (F8 := tranS _ _ _ F6 F7).
             assert (F9 := b_conS _ _ _ _ (refS s1) (idemS s2)).              
            exact (tranS _ _ _ F8 F9).
          assert (F6 := b_conS _ _ _ _ F5 (refS s3)). 
          assert (F7 := tranS _ _ _ F4 F6).
          assert (F8 := assS s1 s2 s3). 
          assert (F9 := tranS _ _ _ F7 F8). apply symS. 
          exact F9.            
       rewrite F1 in C2. discriminate C2. 
Qed. 


Lemma llex_assoc_case13_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  argT =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])).
Proof. compute.
       assert (F1 : (s1 *S s2) =S ((s1 *S s2) *S s3)). 
          assert (F2 := b_conS _ _ _ _ A2 (refS s2)). 
          assert (F3 := assS s1 (s2 *S s3) s2). 
          assert (F4 := tranS _ _ _ F2 F3). 
          assert (F5 : ((s2 *S s3) *S s2) =S (s2 *S s3)). 
             assert (F6 := commS s2 s3). 
             assert (F7 := b_conS _ _ _ _ F6 (refS s2)). 
             assert (F8 := assS s3 s2 s2). 
             assert (F9 := tranS _ _ _ F7 F8). 
             assert (F10 := b_conS _ _ _ _ (refS s3) (idemS s2)). 
             assert (F11 := tranS _ _ _ F9 F10).
             assert (F12 := commS s3 s2). 
             exact (tranS _ _ _ F11 F12).              
          assert (F6 := b_conS _ _ _ _ (refS s1) F5). 
          assert (F7 := tranS _ _ _ F4 F6).
          assert (F8 := assS s1 s2 s3). apply symS in F8.
          exact (tranS _ _ _ F7 F8). 
       rewrite F1 in A1. discriminate A1. 
Qed. 

Lemma llex_assoc_case13
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       exact (llex_assoc_case13_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).              
Qed. 


Lemma llex_assoc_case14
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)): 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       assert (F1 : (s1 *S s2) =S ((s1 *S s2) *S s3)). 
          assert (F2 := b_conS _ _ _ _ A2 (refS s2)).
          assert (F3 := assS s1 (s2 *S s3) s2). 
          assert (F4 := tranS _ _ _ F2 F3). 
          assert (F5 : ((s2 *S s3) *S s2) =S (s2 *S s3)).
             assert (F6 := commS (s2 *S s3) s2). 
             assert (F7 := assS s2 s2 s3). apply symS in F7.
             assert (F8 := tranS _ _ _ F6 F7). 
             assert (F9 := b_conS _ _ _ _ (idemS s2) (refS s3)).
             exact (tranS _ _ _ F8 F9). 
          assert (F6 := b_conS _ _ _ _ (refS s1) F5).
          assert (F7 := tranS _ _ _ F4 F6).
          assert (F8 := assS s1 s2 s3).  apply symS in F8. 
          exact (tranS _ _ _ F7 F8). 
       rewrite F1 in A1. discriminate A1. 
Qed. 

Lemma llex_assoc_case15_aux 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  argT =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. compute.
       assert (F1 := assS s1 s2 s3).
       assert (F2 : (s2 *S s3) !=S s3).
          case_eq(rS (s2 *S s3) s3); intro D; auto.
             assert (F3 := tranS _ _ _ C2 D). 
             rewrite (tranS _ _ _ F1 F3) in C1. 
             discriminate C1. 
       rewrite F2.
       assert (F3 : s2 !=S (s2 *S s3)). 
          case_eq(rS s2 (s2 *S s3)); intro D; auto.
             assert (F4 := b_conS _ _ _ _ (refS s1) D).
             apply symS in F1. 
             rewrite (tranS _ _ _ F4 F1) in A1. 
             discriminate A1. 
       rewrite F3.       
       apply refT. 
Qed. 
       
Lemma llex_assoc_case15
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
   exact (llex_assoc_case15_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).       
Qed. 

Lemma llex_assoc_case16
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. apply refT. Qed. 

Lemma bop_lex_left_associative : 
     (bop_selective S rS bS + bop_is_id T rT bT argT) → bop_associative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. 
    intros selS_or_idT [s1 t1] [s2 t2] [s3 t3].
    unfold brel_product, bop_lex_left. 
    apply bop_and_intro.
       apply assS.
       case_eq(rS (s1 *S s2) ((s1 *S s2) *S s3)); intro A1; 
       case_eq(rS ((s1 *S s2) *S s3) s3); intro C1; 
       case_eq(rS s1 (s1 *S (s2 *S s3))); intro A2; 
       case_eq(rS (s1 *S (s2 *S s3)) (s2 *S s3)); intro C2. 
       - apply llex_assoc_case1; auto. 
       - apply llex_assoc_case2; auto. 
       - apply llex_assoc_case3; auto. (* uses selS_or_idT *)
       - apply llex_assoc_case4; auto. 
       - apply llex_assoc_case5; auto. (* uses selS_or_idT *)
       - apply llex_assoc_case6; auto. 
       - apply llex_assoc_case7; auto. 
       - apply llex_assoc_case8; auto. 
       - apply llex_assoc_case9; auto. 
       - apply llex_assoc_case10; auto. 
       - apply llex_assoc_case11; auto. 
       - apply llex_assoc_case12; auto. 
       - apply llex_assoc_case13; auto. 
       - apply llex_assoc_case14; auto. 
       - apply llex_assoc_case15; auto. 
       - apply llex_assoc_case16; auto. 
Qed. 


(* projections 

where needed? 



Lemma bop_lex_left_is_id_left : 
   ∀ (s : S ) (t : T ), (bop_is_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (s, t)) ->  bop_is_id S rS bS s.  
Proof. intros s t H s1. destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_lex_left_is_id_right : 
   ∀ (s : S ) (t : T ), (bop_is_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (s, t)) ->  bop_is_id T rT bT t.  
Proof. intros s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite (refS s) in RL. rewrite (refS s) in RR. 
       rewrite RL, RR. auto.        
Defined.                         

Lemma bop_lex_left_is_ann_left : 
   ∀ (s : S ) (t : T ), (bop_is_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (s, t)) ->  bop_is_ann S rS bS s.  
Proof. intros s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_lex_left_is_ann_right : 
   ∀ (s : S ) (t : T ), (bop_is_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (s, t)) ->  bop_is_ann T rT bT t.  
Proof. intros s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite (refS s) in RL. rewrite (refS s) in RR.        
       rewrite RL, RR. auto. 
Defined.                         

*) 

End Theory.


Section ACAS.

Variable S T : Type. 

Section Decide.
 

Variable eqvS : A_eqv S.
Variable eqvT : A_eqv T.   
Variable bS : binary_op S. 
Variable pS : sg_CI_proofs S (A_eqv_eq S eqvS) bS. 
Variable bT : binary_op T.
Variable pT : sg_proofs T (A_eqv_eq T eqvT) bT. 
Variable argT : T.

Definition bop_lex_left_commutative_decide
             (dT : bop_commutative_decidable T (A_eqv_eq T eqvT) bT) : 
               bop_commutative_decidable (S * T)
                                         (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                                         (bop_lex_left argT (A_eqv_eq S eqvS) bS bT) 
:= let   rS := A_eqv_eq S eqvS in 
   let   PS := A_eqv_proofs S eqvS in 
   let   wS := A_eqv_witness S eqvS in 
   let refS := A_eqv_reflexive S rS PS in 
   let symS := A_eqv_symmetric S rS PS in 
   let trnS := A_eqv_transitive S rS PS in 
   let   rT := A_eqv_eq T eqvT in 
   let   PT := A_eqv_proofs T eqvT in 
   let refT := A_eqv_reflexive T rT PT in 
   let commS := A_sg_CI_commutative S rS bS pS in 
   let idemS := A_sg_CI_idempotent S rS bS pS in 
    match dT with 
   | inl commT     => inl _ (bop_lex_left_commutative S T rS rT bS bT symS trnS argT refT commS commT)
   | inr not_commT => inr _ (bop_lex_left_not_commutative S T rS rT bS bT wS refS symS argT idemS not_commT)
    end.

Definition bop_lex_left_idempotent_decide (dT : bop_idempotent_decidable T (A_eqv_eq T eqvT) bT): 
  bop_idempotent_decidable (S * T)
                           (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                           (bop_lex_left argT (A_eqv_eq S eqvS) bS bT) 
:=
let   rS := A_eqv_eq S eqvS in 
   let   PS := A_eqv_proofs S eqvS in 
   let   wS := A_eqv_witness S eqvS in 
   let symS := A_eqv_symmetric S rS PS in 
   let   rT := A_eqv_eq T eqvT in 
   let idemS := A_sg_CI_idempotent S rS bS pS in 
   match dT with 
   | inl idemT     => inl _ (bop_lex_left_idempotent S T rS rT bS bT symS argT idemS idemT)
   | inr not_idemT => inr _ (bop_lex_left_not_idempotent S T rS rT bS bT wS symS argT idemS not_idemT)
   end. 

Definition bop_lex_left_selective_decide
           (dS : bop_selective_decidable S (A_eqv_eq S eqvS) bS)
           (dT : bop_selective_decidable T (A_eqv_eq T eqvT) bT) : 
             bop_selective_decidable (S * T)
                                    (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                                    (bop_lex_left argT (A_eqv_eq S eqvS) bS bT) 
:= let   rS := A_eqv_eq S eqvS in 
   let   PS := A_eqv_proofs S eqvS in 
   let   wS := A_eqv_witness S eqvS in 
   let symS := A_eqv_symmetric S rS PS in 
   let   rT := A_eqv_eq T eqvT in 
   let   PT := A_eqv_proofs T eqvT in
   let   wT := A_eqv_witness T eqvT in    
   let refT := A_eqv_reflexive T rT PT in 
   let idemS := A_sg_CI_idempotent S rS bS pS in 
   match dS with 
   | inl selS     => match dT with
                     | inl selT => inl (bop_lex_left_selective S T rS rT bS bT symS argT refT selS selT)
                     | inr not_selT => inr (bop_lex_left_not_selective_right S T rS rT bS bT wS symS argT idemS selS not_selT)
                     end
   | inr not_selS => inr _ (bop_lex_left_not_selective_left S T rS rT bS bT wT argT not_selS)
   end.



Definition bop_lex_left_exists_id_decide
           (dS : bop_exists_id_decidable S (A_eqv_eq S eqvS) bS)
           (dT : bop_exists_id_decidable T (A_eqv_eq T eqvT) bT) : 
                 bop_exists_id_decidable (S * T) 
                                         (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                                         (bop_lex_left argT (A_eqv_eq S eqvS) bS bT) 
:= let   rS := A_eqv_eq S eqvS in 
   let   PS := A_eqv_proofs S eqvS in 
   let symS := A_eqv_symmetric S rS PS in 
   let trnS := A_eqv_transitive S rS PS in 
   let   rT := A_eqv_eq T eqvT in 
   let   PT := A_eqv_proofs T eqvT in 
   let refT := A_eqv_reflexive T rT PT in 
   let commS := A_sg_CI_commutative S rS bS pS in 
   let idemS := A_sg_CI_idempotent S rS bS pS in
   match dS with 
   | inl eS => match dT with 
               | inl eT  => inl _ (bop_lex_left_exists_id S T rS rT bS bT symS trnS argT refT commS eS eT)
               | inr neT => inr _ (bop_lex_left_not_exists_id_right S T rS rT bS bT symS argT idemS neT)
               end 
   | inr neS   => inr _ (bop_lex_left_not_exists_id_left S T rS rT bS bT argT neS)
   end.


Definition bop_lex_left_exists_ann_decide 
  (dS : bop_exists_ann_decidable S (A_eqv_eq S eqvS) bS)
  (dT : bop_exists_ann_decidable T (A_eqv_eq T eqvT) bT) : 
                bop_exists_ann_decidable (S * T)
                                         (brel_product (A_eqv_eq S eqvS) (A_eqv_eq T eqvT))
                                         (bop_lex_left argT (A_eqv_eq S eqvS) bS bT) 
:= let   rS := A_eqv_eq S eqvS in 
   let   PS := A_eqv_proofs S eqvS in 
   let symS := A_eqv_symmetric S rS PS in 
   let trnS := A_eqv_transitive S rS PS in 
   let   rT := A_eqv_eq T eqvT in 
   let   PT := A_eqv_proofs T eqvT in 
   let refT := A_eqv_reflexive T rT PT in 
   let commS := A_sg_CI_commutative S rS bS pS in 
   let idemS := A_sg_CI_idempotent S rS bS pS in
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_lex_left_exists_ann S T rS rT bS bT symS trnS argT refT commS eS eT)
         | inr neT => inr _ (bop_lex_left_not_exists_ann_right S T rS rT bS bT symS argT idemS neT)
         end 
       | inr neS   => inr _ (bop_lex_left_not_exists_ann_left S T rS rT bS bT argT neS)
       end. 

Definition bop_lex_left_associative_assert
           (selS_or_idT : bop_selective S (A_eqv_eq S eqvS) bS +
                          bop_is_id T (A_eqv_eq T eqvT) bT argT) 
:= let   rS := A_eqv_eq S eqvS in 
   let   PS := A_eqv_proofs S eqvS in 
   let   wS := A_eqv_witness S eqvS in 
   let refS := A_eqv_reflexive S rS PS in 
   let symS := A_eqv_symmetric S rS PS in 
   let trnS := A_eqv_transitive S rS PS in 
   let   rT := A_eqv_eq T eqvT in 
   let   PT := A_eqv_proofs T eqvT in 
   let refT := A_eqv_reflexive T rT PT in
   let symT := A_eqv_symmetric T rT PT in    
   let conS := A_sg_CI_congruence S rS bS pS in       
   let assS := A_sg_CI_associative S rS bS pS in    
   let commS := A_sg_CI_commutative S rS bS pS in 
   let idemS := A_sg_CI_idempotent S rS bS pS in 
   let assT := A_sg_associative T rT bT pT in    
          bop_lex_left_associative S T rS rT bS bT
                                   refS symS trnS
                                   argT
                                   refT symT 
                                   conS assS idemS commS
                                   assT
                                   selS_or_idT. 

End  Decide.
End ACAS.


(*
Section Proofs. 

Definition proofs_llex
    (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S)
    (eqvS : eqv_proofs S rS) (eqvT : eqv_proofs T rT)
    (sgS : sg_CS_proofs S rS bS) 
        asg_proofs (S * T) (brel_product rS rT) (bop_lex_left rS bS bT)
:= λ S T rS rT bS bT s eqvS eqvT sgS sgT,
let congS  := A_eqv_congruence _ _ eqvS in   
let refS   := A_eqv_reflexive _ _ eqvS in
let transS := A_eqv_transitive _ _ eqvS in    
let symS   := A_eqv_symmetric _ _ eqvS in
let congT  := A_eqv_congruence _ _ eqvT in   
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in   
let symT   := A_eqv_symmetric _ _ eqvT in
let bcongS := A_sg_CS_congruence _ _ _ sgS in   
{|
  A_asg_associative   := bop_lex_left_associative S T rS rT bS bT congS refS symS transS refT bcongS
                         (A_sg_CS_associative _ _ _ sgS)
                         (A_asg_associative _ _ _ sgT)                          
                         (A_sg_CS_commutative  S rS bS sgS)
                         (A_sg_CS_selective S rS bS sgS)
; A_asg_congruence    := bop_lex_left_congruence S T rS rT bS bT congS congT 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_asg_congruence _ _ _ sgT) 
; A_asg_commutative   := bop_lex_left_commutative S T rS rT bS bT congS refS symS transS refT 
                         (A_sg_CS_selective S rS bS sgS)
                         (A_sg_CS_commutative S rS bS sgS)
                         (A_asg_commutative _ _ _ sgT) 
; A_asg_selective_d   := bop_lex_left_selective_decide S T rS rT bS bT s refS symS transS refT bcongS
                         (A_sg_CS_commutative S rS bS sgS)
                         (A_sg_CS_selective S rS bS sgS)
                         (A_asg_selective_d _ _ _ sgT)                          
; A_asg_idempotent_d  := bop_lex_left_idempotent_decide S T rS rT bS bT s refS 
                         (A_sg_CS_selective S rS bS sgS)
                         (A_asg_idempotent_d _ _ _ sgT) 
|}. 

  

Definition sg_proofs_llex : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CS_proofs S rS bS -> sg_proofs T rT bT -> 
        sg_proofs (S * T) (brel_product rS rT) (bop_lex_left rS bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let congS  := A_eqv_congruence _ _ eqvS in   
let refS   := A_eqv_reflexive _ _ eqvS in
let transS := A_eqv_transitive _ _ eqvS in    
let symS   := A_eqv_symmetric _ _ eqvS in
let congT  := A_eqv_congruence _ _ eqvT in   
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in   
let symT   := A_eqv_symmetric _ _ eqvT in
let bcongS := A_sg_CS_congruence _ _ _ sgS in   
{|
  A_sg_associative   := bop_lex_left_associative S T rS rT bS bT congS refS symS transS refT bcongS
                         (A_sg_CS_associative _ _ _ sgS)
                         (A_sg_associative _ _ _ sgT)                          
                         (A_sg_CS_commutative  S rS bS sgS)
                         (A_sg_CS_selective S rS bS sgS)
; A_sg_congruence    := bop_lex_left_congruence S T rS rT bS bT congS congT 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_congruence _ _ _ sgT) 

; A_sg_commutative_d := bop_lex_left_commutative_decide S T rS rT bS bT s congS refS symS transS refT 
                         (A_sg_CS_selective S rS bS sgS)
                         (A_sg_CS_commutative S rS bS sgS)
                         (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_lex_left_selective_decide S T rS rT bS bT s refS symS transS refT bcongS
                         (A_sg_CS_commutative S rS bS sgS)
                         (A_sg_CS_selective S rS bS sgS)
                         (A_sg_selective_d _ _ _ sgT)                          
; A_sg_idempotent_d  := bop_lex_left_idempotent_decide S T rS rT bS bT s refS 
                         (A_sg_CS_selective S rS bS sgS)
                         (A_sg_idempotent_d _ _ _ sgT) 

; A_sg_is_left_d     := inr _ (bop_lex_left_not_is_left S T rS rT bS bT s f Pf symS transS t
                                 (A_sg_CS_commutative S rS bS sgS) 
                                 (A_sg_CS_selective S rS bS sgS))
; A_sg_is_right_d    := inr _ (bop_lex_left_not_is_right S T rS rT bS bT s f Pf symS transS t
                                 (A_sg_CS_commutative S rS bS sgS)
                                 (A_sg_CS_selective S rS bS sgS) )
; A_sg_left_cancel_d    := inr _ (bop_lex_left_not_left_cancellative_v2 S T rS rT bS bT s f Pf refS symS transS t g Pg refT bcongS 
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) )
; A_sg_right_cancel_d   := inr _ (bop_lex_left_not_right_cancellative S T rS rT bS bT  s f Pf refS symS transS t g Pg refT bcongS 
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) )
; A_sg_left_constant_d  := inr _ (bop_lex_left_not_left_constant S T rS rT bS bT s f Pf refS symS transS t g Pg bcongS 
                                    (A_sg_CS_selective S rS bS sgS) 
                                    (A_sg_CS_commutative S rS bS sgS) )
; A_sg_right_constant_d := inr _ (bop_lex_left_not_right_constant S T rS rT bS bT s f Pf refS symS transS t g Pg bcongS 
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) )
; A_sg_anti_left_d      := inr _ (bop_lex_left_not_anti_left S T rS rT bS bT s f Pf symS transS t refT 
                                    (A_sg_CS_selective S rS bS sgS) 
                                    (A_sg_CS_commutative S rS bS sgS) )
; A_sg_anti_right_d     := inr _ (bop_lex_left_not_anti_right S T rS rT bS bT s f Pf symS transS t refT 
                                    (A_sg_CS_selective S rS bS sgS)
                                    (A_sg_CS_commutative S rS bS sgS) )
|}. 

Definition sg_C_proofs_llex :
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CS_proofs S rS bS -> sg_C_proofs T rT bT -> 
        sg_C_proofs (S * T) (brel_product rS rT) (bop_lex_left rS bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sg_CT,
let congS  := A_eqv_congruence _ _ eqvS in   
let refS   := A_eqv_reflexive _ _ eqvS in
let transS := A_eqv_transitive _ _ eqvS in    
let symS   := A_eqv_symmetric _ _ eqvS in
let congT  := A_eqv_congruence _ _ eqvT in   
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in   
let symT   := A_eqv_symmetric _ _ eqvT in
let bcongS := A_sg_CS_congruence _ _ _ sgS in   
{|
  A_sg_C_associative   := bop_lex_left_associative S T rS rT bS bT congS refS symS transS refT bcongS
                         (A_sg_CS_associative _ _ _ sgS)
                         (A_sg_C_associative _ _ _ sg_CT)                          
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
; A_sg_C_congruence    := bop_lex_left_congruence S T rS rT bS bT congS congT 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_C_congruence _ _ _ sg_CT) 
; A_sg_C_commutative := bop_lex_left_commutative S T rS rT bS bT congS refS symS transS refT 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_C_commutative _ _ _ sg_CT) 

; A_sg_C_selective_d   := bop_lex_left_selective_decide S T rS rT bS bT s refS symS transS refT bcongS
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_C_selective_d _ _ _ sg_CT) 
; A_sg_C_idempotent_d  := bop_lex_left_idempotent_decide S T rS rT bS bT s refS 
                         (A_sg_CS_selective _ _ _ sgS)
                         (A_sg_C_idempotent_d _ _ _ sg_CT) 
; A_sg_C_cancel_d    := inr _ (bop_lex_left_not_left_cancellative_v2 S T rS rT bS bT s f Pf refS symS transS t g Pg refT bcongS 
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS))
; A_sg_C_constant_d  := inr _ (bop_lex_left_not_left_constant S T rS rT bS bT s f Pf refS symS transS t g Pg bcongS 
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS))
; A_sg_C_anti_left_d      := inr _ (bop_lex_left_not_anti_left S T rS rT bS bT s f Pf symS transS t refT 
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS))
; A_sg_C_anti_right_d     := inr _ (bop_lex_left_not_anti_right S T rS rT bS bT s f Pf symS transS t refT 
                                    (A_sg_CS_selective _ _ _ sgS)
                                    (A_sg_CS_commutative _ _ _ sgS))

|}. 


Definition sg_CI_proofs_llex : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S), 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CS_proofs S rS bS -> sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S * T) (brel_product rS rT) (bop_lex_left rS bS bT)
:= λ S T rS rT bS bT s eqvS eqvT sgS sg_CIT,
let congS  := A_eqv_congruence _ _ eqvS in   
let refS   := A_eqv_reflexive _ _ eqvS in
let transS := A_eqv_transitive _ _ eqvS in    
let symS   := A_eqv_symmetric _ _ eqvS in
let congT  := A_eqv_congruence _ _ eqvT in   
let refT   := A_eqv_reflexive _ _ eqvT in 
let bcongS := A_sg_CS_congruence _ _ _ sgS in   
{|
  A_sg_CI_associative   := bop_lex_left_associative S T rS rT bS bT congS refS symS transS refT bcongS
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CI_associative _ _ _ sg_CIT) 
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
; A_sg_CI_congruence    := bop_lex_left_congruence S T rS rT bS bT congS congT 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CI_congruence _ _ _ sg_CIT) 
; A_sg_CI_commutative := bop_lex_left_commutative S T rS rT bS bT congS refS symS transS refT 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CI_commutative _ _ _ sg_CIT) 
; A_sg_CI_idempotent   := bop_lex_left_idempotent S T rS rT bS bT refS 
                         (bop_selective_implies_idempotent S rS bS 
                                  (A_sg_CS_selective _ _ _ sgS))                                              
                         (A_sg_CI_idempotent _ _ _ sg_CIT)                                               
; A_sg_CI_selective_d   := bop_lex_left_selective_decide S T rS rT bS bT s refS symS transS refT bcongS
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CI_selective_d _ _ _ sg_CIT) 
|}. 


Definition sg_CS_proofs_llex : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) , 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CS_proofs S rS bS -> sg_CS_proofs T rT bT -> 
        sg_CS_proofs (S * T) (brel_product rS rT) (bop_lex_left rS bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sg_CST,
let congS  := A_eqv_congruence _ _ eqvS in   
let refS   := A_eqv_reflexive _ _ eqvS in
let transS := A_eqv_transitive _ _ eqvS in    
let symS   := A_eqv_symmetric _ _ eqvS in
let congT  := A_eqv_congruence _ _ eqvT in   
let refT   := A_eqv_reflexive _ _ eqvT in 
let bcongS := A_sg_CS_congruence _ _ _ sgS in   
{|
  A_sg_CS_associative   := bop_lex_left_associative S T rS rT bS bT congS refS symS transS refT bcongS
                         (A_sg_CS_associative _ _ _ sgS) 
                         (A_sg_CS_associative _ _ _ sg_CST)                          
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
; A_sg_CS_congruence    := bop_lex_left_congruence S T rS rT bS bT congS congT 
                         (A_sg_CS_congruence _ _ _ sgS) 
                         (A_sg_CS_congruence _ _ _ sg_CST) 
; A_sg_CS_commutative := bop_lex_left_commutative S T rS rT bS bT congS refS symS transS refT 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_commutative _ _ _ sgS)
                         (A_sg_CS_commutative _ _ _ sg_CST) 
; A_sg_CS_selective   := bop_lex_left_selective S T rS rT bS bT refS symS transS refT bcongS
                         (A_sg_CS_commutative _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sgS) 
                         (A_sg_CS_selective _ _ _ sg_CST)
|}. 

End Proofs.



Definition A_sg_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg T -> A_sg (S * T)
:= λ S T sgS sgT,
let eqvS := A_sg_CS_eqv S sgS in
let eqvT := A_sg_eq T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let bS   := A_sg_CS_bop S sgS in
let bT   := A_sg_bop T sgT in 
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in
let refT := A_eqv_reflexive _ _ (A_eqv_proofs T eqvT) in
let symS := A_eqv_symmetric _ _ (A_eqv_proofs S eqvS) in
let trnS := A_eqv_transitive _ _ (A_eqv_proofs S eqvS) in
let comS := A_sg_CS_commutative S rS bS (A_sg_CS_proofs S sgS)  in 
let id1  := A_sg_CS_exists_id_d _ sgS in
let id2  := A_sg_exists_id_d _ sgT in
let an1  := A_sg_CS_exists_ann_d _ sgS in
let an2  := A_sg_exists_ann_d _ sgT in        
{| 
        A_sg_eq     := A_eqv_product S T eqvS eqvT 
      ; A_sg_bop    := bop_lex_left rS bS bT 
      ; A_sg_exists_id_d   := bop_lex_left_exists_id_decide S T rS rT bS bT refS symS trnS refT comS id1 id2 
      ; A_sg_exists_ann_d  := bop_lex_left_exists_ann_decide S T rS rT bS bT refS symS trnS refT comS an1 an2 
      ; A_sg_proofs := sg_proofs_llex S T rS rT bS bT 
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT)
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_proofs T sgT)
     
      ; A_sg_ast     := Ast_sg_llex (A_sg_CS_ast S sgS, A_sg_ast T sgT)  
|}. 


Definition A_sg_C_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_C T -> A_sg_C (S * T)
:= λ S T sgS sgT,
let eqvS := A_sg_CS_eqv S sgS in
let eqvT := A_sg_C_eqv T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let bS   := A_sg_CS_bop S sgS in
let bT   := A_sg_C_bop T sgT in 
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in
let refT := A_eqv_reflexive _ _ (A_eqv_proofs T eqvT) in
let symS := A_eqv_symmetric _ _ (A_eqv_proofs S eqvS) in
let trnS := A_eqv_transitive _ _ (A_eqv_proofs S eqvS) in
let comS := A_sg_CS_commutative S rS bS (A_sg_CS_proofs S sgS)  in 
let id1  := A_sg_CS_exists_id_d _ sgS in
let id2  := A_sg_C_exists_id_d _ sgT in
let an1  := A_sg_CS_exists_ann_d _ sgS in
let an2  := A_sg_C_exists_ann_d _ sgT in        
{| 
        A_sg_C_eqv    := A_eqv_product S T eqvS eqvT 
      ; A_sg_C_bop    := bop_lex_left rS bS bT 
      ; A_sg_C_exists_id_d   := bop_lex_left_exists_id_decide S T rS rT bS bT refS symS trnS refT comS id1 id2 
      ; A_sg_C_exists_ann_d  := bop_lex_left_exists_ann_decide S T rS rT bS bT refS symS trnS refT comS an1 an2 
      ; A_sg_C_proofs := sg_C_proofs_llex S T rS rT bS bT 
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)                           
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_C_proofs T sgT)
      
      ; A_sg_C_ast     := Ast_sg_llex (A_sg_CS_ast S sgS, A_sg_C_ast T sgT)  
|}. 


Definition A_sg_CI_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CI T -> A_sg_CI (S * T)
:= λ S T sgS sgT,
let eqvS := A_sg_CS_eqv S sgS in
let eqvT := A_sg_CI_eqv T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let bS   := A_sg_CS_bop S sgS in
let bT   := A_sg_CI_bop T sgT in 
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in
let refT := A_eqv_reflexive _ _ (A_eqv_proofs T eqvT) in
let symS := A_eqv_symmetric _ _ (A_eqv_proofs S eqvS) in
let trnS := A_eqv_transitive _ _ (A_eqv_proofs S eqvS) in
let comS := A_sg_CS_commutative S rS bS (A_sg_CS_proofs S sgS)  in 
let id1  := A_sg_CS_exists_id_d _ sgS in
let id2  := A_sg_CI_exists_id_d _ sgT in
let an1  := A_sg_CS_exists_ann_d _ sgS in
let an2  := A_sg_CI_exists_ann_d _ sgT in        
{| 
        A_sg_CI_eqv     := A_eqv_product S T eqvS eqvT 
      ; A_sg_CI_bop    := bop_lex_left rS bS bT 
      ; A_sg_CI_exists_id_d   := bop_lex_left_exists_id_decide S T rS rT bS bT refS symS trnS refT comS id1 id2 
      ; A_sg_CI_exists_ann_d  := bop_lex_left_exists_ann_decide S T rS rT bS bT refS symS trnS refT comS an1 an2 
      ; A_sg_CI_proofs := sg_CI_proofs_llex S T rS rT bS bT 
                           (A_eqv_witness S eqvS) 
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)                           
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_CI_proofs T sgT)
      
      ; A_sg_CI_ast     := Ast_sg_llex (A_sg_CS_ast S sgS, A_sg_CI_ast T sgT)  
 |}. 


Definition A_sg_CS_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S * T)
:= λ S T sgS sgT,
let eqvS := A_sg_CS_eqv S sgS in
let eqvT := A_sg_CS_eqv T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let bS   := A_sg_CS_bop S sgS in
let bT   := A_sg_CS_bop T sgT in 
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in
let refT := A_eqv_reflexive _ _ (A_eqv_proofs T eqvT) in
let symS := A_eqv_symmetric _ _ (A_eqv_proofs S eqvS) in
let trnS := A_eqv_transitive _ _ (A_eqv_proofs S eqvS) in
let comS := A_sg_CS_commutative S rS bS (A_sg_CS_proofs S sgS)  in 
let id1  := A_sg_CS_exists_id_d _ sgS in
let id2  := A_sg_CS_exists_id_d _ sgT in
let an1  := A_sg_CS_exists_ann_d _ sgS in
let an2  := A_sg_CS_exists_ann_d _ sgT in        
{| 
        A_sg_CS_eqv    := A_eqv_product S T eqvS eqvT 
      ; A_sg_CS_bop    := bop_lex_left rS bS bT 
      ; A_sg_CS_exists_id_d   := bop_lex_left_exists_id_decide S T rS rT bS bT refS symS trnS refT comS id1 id2 
      ; A_sg_CS_exists_ann_d  := bop_lex_left_exists_ann_decide S T rS rT bS bT refS symS trnS refT comS an1 an2 
      ; A_sg_CS_proofs := sg_CS_proofs_llex S T rS rT bS bT 
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)                           
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT)
      
      ; A_sg_CS_ast    := Ast_sg_llex (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)  
|}. 
End ACAS.
*)

(*
Section CAS.

Definition check_commutative_llex : ∀ {S T : Type},  S -> @check_commutative T -> @check_commutative (S * T)
:= λ {S T} s cT,  
      match cT with 
      | Certify_Commutative              => Certify_Commutative 
      | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative ((s, t1), (s, t2))
      end. 


Definition check_idempotent_llex : ∀ {S T : Type}, S -> @check_idempotent T -> @check_idempotent (S * T)
:= λ {S T} s cT,  
      match cT with 
      | Certify_Idempotent        => Certify_Idempotent 
      | Certify_Not_Idempotent t1 => Certify_Not_Idempotent (s, t1) 
      end.

Definition check_selective_llex : ∀ {S T : Type}, S -> @check_selective T -> @check_selective (S * T)
:= λ {S T} s dT,  
     match dT with 
     | Certify_Selective              => Certify_Selective 
     | Certify_Not_Selective (t1, t2) => Certify_Not_Selective ((s, t1), (s, t2)) 
     end.


Definition check_exists_id_llex : ∀ {S T : Type}, 
             (check_exists_id (S := S)) -> (check_exists_id (S := T)) -> (check_exists_id (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t => Certify_Exists_Id  (s, t) 
      | Certify_Not_Exists_Id, _                 => Certify_Not_Exists_Id 
      | _, Certify_Not_Exists_Id                 => Certify_Not_Exists_Id 
      end. 

Definition check_exists_ann_llex : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := T)) -> (check_exists_ann (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann  (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann 
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann 
      end. 

Definition asg_certs_llex : ∀ {S T : Type},  
        brel S -> binary_op S -> 
        S -> 
        sg_CS_certificates (S := S) -> 
        asg_certificates (S := T) -> asg_certificates (S := (S * T))
:= λ {S T} rS bS s cS cT,  
{|
  asg_associative      := Assert_Associative   
; asg_congruence       := Assert_Bop_Congruence   
; asg_commutative      := Assert_Commutative
; asg_selective_d      := check_selective_llex s (asg_selective_d cT)
; asg_idempotent_d     := check_idempotent_llex s (asg_idempotent_d cT)
|}. 

Definition sg_certs_llex : ∀ {S T : Type},  
        brel S -> binary_op S -> 
        S -> (S -> S) -> 
        T -> (T -> T) -> 
        sg_CS_certificates (S := S) -> 
        sg_certificates (S := T) -> sg_certificates (S := (S * T))
:= λ {S T} rS bS s f t g cS cT,  
{|
  sg_associative      := Assert_Associative   
; sg_congruence       := Assert_Bop_Congruence   
; sg_commutative_d    := check_commutative_llex s (sg_commutative_d cT)
; sg_selective_d      := check_selective_llex s (sg_selective_d cT)
; sg_idempotent_d     := check_idempotent_llex s (sg_idempotent_d cT)

; sg_is_left_d        := Certify_Not_Is_Left (cef_bop_lex_left_not_is_left rS bS s f t)
; sg_is_right_d       := Certify_Not_Is_Right (cef_bop_lex_left_not_is_right rS bS s f t)
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (cef_bop_lex_left_not_cancellative rS bS s f t g)
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (cef_bop_lex_left_not_cancellative rS bS s f t g)
; sg_left_constant_d  := Certify_Not_Left_Constant (cef_bop_lex_left_not_constant rS bS s f t g)
; sg_right_constant_d := Certify_Not_Right_Constant (cef_bop_lex_left_not_constant rS bS s f t g)
; sg_anti_left_d      := Certify_Not_Anti_Left (cef_bop_lex_left_not_anti_left rS bS s f t)
; sg_anti_right_d     := Certify_Not_Anti_Right (cef_bop_lex_left_not_anti_right rS bS s f t)
|}. 

Definition sg_C_certs_llex : ∀ {S T : Type} (rS : brel S) (bS : binary_op S), 
        S -> (S -> S) -> T -> (T -> T) -> sg_CS_certificates (S := S) -> sg_C_certificates (S := T) -> sg_C_certificates (S := (S * T)) 
:= λ {S T} rS bS s f t g cS cT,  
{|
  sg_C_associative   := Assert_Associative 
; sg_C_congruence    := Assert_Bop_Congruence   
; sg_C_commutative   := Assert_Commutative   
; sg_C_selective_d   := check_selective_llex s (sg_C_selective_d cT)
; sg_C_idempotent_d  := check_idempotent_llex s (sg_C_idempotent_d cT)
; sg_C_cancel_d    := Certify_Not_Left_Cancellative (cef_bop_lex_left_not_cancellative rS bS s f t g)
; sg_C_constant_d  := Certify_Not_Left_Constant (cef_bop_lex_left_not_constant rS bS s f t g)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_bop_lex_left_not_anti_left rS bS s f t)                            
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_bop_lex_left_not_anti_right rS bS s f t)
|}.

Definition sg_CI_certs_llex : ∀ {S T : Type} (rS : brel S) (bS : binary_op S), 
        S -> sg_CS_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S * T)) 
:= λ {S T} rS bS s cS cT,  
{|
  sg_CI_associative   := Assert_Associative   
; sg_CI_congruence    := Assert_Bop_Congruence   
; sg_CI_commutative   := Assert_Commutative   
; sg_CI_idempotent    := Assert_Idempotent   
; sg_CI_selective_d   := check_selective_llex s (sg_CI_selective_d cT)
|}.

Definition sg_CS_certs_llex : ∀ {S T : Type} (rS : brel S) (bS : binary_op S), 
        sg_CS_certificates (S := S) -> sg_CS_certificates (S := T) -> sg_CS_certificates (S := (S * T)) 
:= λ {S T} rS bS cS cT,  
{|
  sg_CS_associative   := Assert_Associative   
; sg_CS_congruence    := Assert_Bop_Congruence   
; sg_CS_commutative   := Assert_Commutative   
; sg_CS_selective     := Assert_Selective   
|}.

Definition sg_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg (S := T) -> sg (S := (S * T))
:= λ {S T} sgS sgT, 
   {| 
     sg_eq           := eqv_product (sg_CS_eqv sgS) (sg_eq sgT) 
   ; sg_bop          := bop_lex_left (eqv_eq (sg_CS_eqv sgS)) (sg_CS_bop sgS) (sg_bop sgT) 
   ; sg_exists_id_d  := check_exists_id_llex (sg_CS_exists_id_d sgS) (sg_exists_id_d sgT)
   ; sg_exists_ann_d := check_exists_ann_llex (sg_CS_exists_ann_d sgS) (sg_exists_ann_d sgT)
   ; sg_certs := sg_certs_llex 
                   (eqv_eq (sg_CS_eqv sgS)) 
                   (sg_CS_bop sgS) 
                   (eqv_witness (sg_CS_eqv sgS)) (eqv_new (sg_CS_eqv sgS)) 
                   (eqv_witness (sg_eq sgT)) (eqv_new (sg_eq sgT)) 
                   (sg_CS_certs sgS) 
                   (sg_certs sgT)
   
   ; sg_ast   := Ast_sg_llex (sg_CS_ast sgS, sg_ast sgT)
   |}. 

Definition sg_C_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg_C (S := T) -> sg_C (S := (S * T))
:= λ {S T} sgS sgT, 
      {| 
        sg_C_eqv     := eqv_product (sg_CS_eqv sgS) (sg_C_eqv sgT) 
      ; sg_C_bop    := bop_lex_left 
                          (eqv_eq (sg_CS_eqv sgS)) 
                          (sg_CS_bop sgS) 
                          (sg_C_bop sgT)
      ; sg_C_exists_id_d  := check_exists_id_llex (sg_CS_exists_id_d sgS) (sg_C_exists_id_d sgT)
      ; sg_C_exists_ann_d := check_exists_ann_llex (sg_CS_exists_ann_d sgS) (sg_C_exists_ann_d sgT)
      ; sg_C_certs := sg_C_certs_llex 
                          (eqv_eq (sg_CS_eqv sgS))
                          (sg_CS_bop sgS) 
                          (eqv_witness (sg_CS_eqv sgS)) (eqv_new (sg_CS_eqv sgS)) 
                          (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT))
                          (sg_CS_certs sgS) 
                          (sg_C_certs sgT)
      
      ; sg_C_ast    := Ast_sg_llex (sg_CS_ast sgS, sg_C_ast sgT)  
      |}. 

Definition sg_CI_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg_CI (S := T) -> sg_CI (S := (S * T))
:= λ {S T} sgS sgT, 
      {| 
        sg_CI_eqv     := eqv_product (sg_CS_eqv sgS) (sg_CI_eqv sgT) 
      ; sg_CI_bop    := bop_lex_left 
                          (eqv_eq (sg_CS_eqv sgS)) 
                          (sg_CS_bop sgS) 
                          (sg_CI_bop sgT) 
      ; sg_CI_exists_id_d  := check_exists_id_llex (sg_CS_exists_id_d sgS) (sg_CI_exists_id_d sgT)
      ; sg_CI_exists_ann_d := check_exists_ann_llex (sg_CS_exists_ann_d sgS) (sg_CI_exists_ann_d sgT)
      ; sg_CI_certs := sg_CI_certs_llex 
                          (eqv_eq (sg_CS_eqv sgS))
                          (sg_CS_bop sgS)
                          (eqv_witness (sg_CS_eqv sgS)) 
                          (sg_CS_certs sgS) 
                          (sg_CI_certs sgT)
      
      ; sg_CI_ast    := Ast_sg_llex (sg_CS_ast sgS, sg_CI_ast sgT)  
      |}. 

Definition sg_CS_llex : ∀ {S T : Type},  sg_CS (S := S) -> sg_CS (S := T) -> sg_CS (S := (S * T))
:= λ {S T} sgS sgT, 
      {| 
        sg_CS_eqv    := eqv_product (sg_CS_eqv sgS) (sg_CS_eqv sgT) 
      ; sg_CS_bop    := bop_lex_left 
                          (eqv_eq (sg_CS_eqv sgS)) 
                          (sg_CS_bop sgS) 
                          (sg_CS_bop sgT) 
      ; sg_CS_exists_id_d  := check_exists_id_llex (sg_CS_exists_id_d sgS) (sg_CS_exists_id_d sgT)
      ; sg_CS_exists_ann_d := check_exists_ann_llex (sg_CS_exists_ann_d sgS) (sg_CS_exists_ann_d sgT)
      ; sg_CS_certs := sg_CS_certs_llex 
                          (eqv_eq (sg_CS_eqv sgS))
                          (sg_CS_bop sgS) 
                          (sg_CS_certs sgS) 
                          (sg_CS_certs sgT)
      
      ; sg_CS_ast    := Ast_sg_llex (sg_CS_ast sgS, sg_CS_ast sgT)  
      |}. 

End CAS.

Section Verify.

Section ChecksCorrect.
  
  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.
  Variable congS : brel_congruence S rS rS.
  
  Variable commS : bop_commutative S rS bS.
  Variable selS : bop_selective S rS bS.
  Variable b_congS : bop_congruence S rS bS.  

  Lemma correct_check_commutative_llex : ∀ (dT : bop_commutative_decidable T rT bT),
      
         p2c_commutative_check (S * T) 
            (brel_product rS rT) 
            (bop_lex_left rS bS bT)
            (bop_lex_left_commutative_decide S T rS rT bS bT wS congS refS symS transS refT selS commS dT)
         = 
         check_commutative_llex wS (p2c_commutative_check T rT bT dT). 
Proof. intros [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_llex : ∀ (dT : bop_idempotent_decidable T rT bT),

       p2c_idempotent_check (S * T) 
            (brel_product rS rT) 
            (bop_lex_left rS bS bT) 
            (bop_lex_left_idempotent_decide S T rS rT bS bT wS refS selS dT)
         = 
         check_idempotent_llex wS (p2c_idempotent_check T rT bT dT).
Proof. intros [cT | [t3 niT]]; compute; reflexivity. Defined. 

Lemma correct_check_exists_id_llex : 
      ∀ (dS : bop_exists_id_decidable S rS bS) (dT : bop_exists_id_decidable T rT bT),
         
         p2c_exists_id_check (S * T) 
            (brel_product rS rT)
            (bop_lex_left rS bS bT)
            (bop_lex_left_exists_id_decide S T rS rT bS bT refS symS transS refT commS dS dT)
         =
         check_exists_id_llex 
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT). 
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_exists_ann_llex : ∀ (dS : bop_exists_ann_decidable S rS bS) (dT : bop_exists_ann_decidable T rT bT),

         p2c_exists_ann_check (S * T) 
            (brel_product rS rT)
            (bop_lex_left rS bS bT)
            (bop_lex_left_exists_ann_decide S T rS rT bS bT refS symS transS refT commS dS dT)
         =
         check_exists_ann_llex 
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT). 
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_selective_llex : ∀ (dT : bop_selective_decidable T rT bT),

         p2c_selective_check (S * T) 
            (brel_product rS rT) 
            (bop_lex_left rS bS bT)
            (bop_lex_left_selective_decide S T rS rT bS bT wS
              refS symS transS refT b_congS commS selS dT)
         = 
         check_selective_llex wS (p2c_selective_check T rT bT dT). 
Proof.  intros [selT | [ [t1 t2] P]]; compute; reflexivity. Defined. 

End ChecksCorrect.


Section ProofsCorrect.
  
  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable eS : eqv_proofs S rS.
  Variable eT : eqv_proofs T rT.


Lemma correct_sg_CI_certs_llex : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_llex rS bS wS  
                           (P2C_sg_CS S rS bS pS) 
                           (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S * T) (brel_product rS rT) 
                     (bop_lex_left rS bS bT) 
                     (sg_CI_proofs_llex S T rS rT bS bT wS eS eT pS pT).
Proof. intros pS pT. 
       unfold sg_CI_proofs_llex, sg_CI_certs_llex, P2C_sg_CI, P2C_sg_CS; simpl. 
       rewrite correct_check_selective_llex. 
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_llex : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CS_proofs T rT bT),
      sg_CS_certs_llex rS bS (P2C_sg_CS S rS bS pS) (P2C_sg_CS T rT bT pT) 
      = 
      P2C_sg_CS (S * T) (brel_product rS rT) 
                     (bop_lex_left rS bS bT) 
                     (sg_CS_proofs_llex S T rS rT bS bT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CS_proofs_llex, sg_CS_certs_llex, P2C_sg_CS; simpl. 
       reflexivity. 
Defined. 


Lemma correct_sg_C_certs_llex :  ∀(pS : sg_CS_proofs S rS bS)  (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_llex rS bS wS f wT g (P2C_sg_CS S rS bS pS) (P2C_sg_C T rT bT pT) 
      = 
      P2C_sg_C (S * T) (brel_product rS rT) 
                       (bop_lex_left rS bS bT) 
                       (sg_C_proofs_llex S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_llex, sg_C_certs_llex, P2C_sg_C, P2C_sg_CS; simpl. 
       rewrite correct_check_selective_llex.
       rewrite correct_check_idempotent_llex.        
       reflexivity. 
Defined. 


Lemma correct_asg_certs_llex :  ∀(pS : sg_CS_proofs S rS bS)  (pT : asg_proofs T rT bT),
        
      asg_certs_llex rS bS wS (P2C_sg_CS S rS bS pS) (P2C_asg T rT bT pT) 
      = 
      P2C_asg (S * T) (brel_product rS rT) 
                      (bop_lex_left rS bS bT) 
                      (asg_proofs_llex S T rS rT bS bT wS eS eT pS pT). 
Proof. intros pS pT. 
       unfold asg_proofs_llex, asg_certs_llex, P2C_asg, P2C_sg_CS; simpl. 
       rewrite correct_check_selective_llex.
       rewrite correct_check_idempotent_llex.        
       reflexivity. 
Defined. 



Lemma correct_sg_certs_llex : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_proofs T rT bT),

      sg_certs_llex rS bS wS f wT g (P2C_sg_CS S rS bS pS) (P2C_sg T rT bT pT) 
      = 
      P2C_sg (S * T) (brel_product rS rT) 
                     (bop_lex_left rS bS bT) 
                     (sg_proofs_llex S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT.
       unfold sg_certs_llex, sg_proofs_llex, P2C_sg; simpl. 
       rewrite correct_check_selective_llex.
       rewrite correct_check_idempotent_llex.                      
       rewrite correct_check_commutative_llex.
       reflexivity. 
Defined. 

End ProofsCorrect.   


Theorem correct_sg_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg T), 
         sg_llex (A2C_sg_CS S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_llex S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_llex, A2C_sg, A2C_sg_CS; simpl. 
       rewrite <- correct_sg_certs_llex. 
       rewrite correct_eqv_product.
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_C T), 
         sg_C_llex (A2C_sg_CS S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_llex S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_llex, A2C_sg_C, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_C_certs_llex.
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex.        
       reflexivity. 
Qed. 

Theorem correct_sg_CS_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_llex (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S * T) (A_sg_CS_llex S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_llex, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CS_certs_llex.
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex.        
       reflexivity. 
Qed. 

Theorem correct_sg_CI_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CI T), 
         sg_CI_llex (A2C_sg_CS S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CI_llex, A2C_sg_CI, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CI_certs_llex.
       rewrite correct_check_exists_id_llex.  
       rewrite correct_check_exists_ann_llex. 
       reflexivity. 
Qed. 

 
End Verify.   
  
***************************************)
Close Scope brel_product_scope.
Close Scope bop_lex_left_scope.
