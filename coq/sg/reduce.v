Require Export CAS.coq.common.ast.
Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.product. 
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.product. 
(* First, the "classic" theory of reductions. 
   This will be our "ground truth" even though it 
   is not directly implementable in OCaml. 

   let (S, =, (x)) be a semigroup. 
   A function r : S -> S is a reduction for (x) if 
   (1) r(r(s)) = r(s)  
   (2) r(a (x) b) = r(r(a) (x) b) 
   (3) r(a (x) b) = r(a (x) r(b))  

   We can then define the reduced semigroup 

      (S_r, =, (x)_r) 

   where S_r = {a in S | r(a) = a}, and 
   equality on S_r is just 
   equality on S restricted to S_r, and 

      a (x)_r b = r(a (x) b). 

   The problem CAPP has with this classic picture is 
   that {a in S | r(a) = a} is not directly 
   representable as an OCaml datatype. 

   Our solution is the represent the reduced 
   semigroup as 

     (S, =_r, [x]_r) 
 
   where 

        a =_r b <-> r(a) = r(b) 

      a [x]_r b = r(r(a) (x) r(b)). 

   This works, but the 
   Big question is : do we really have to 
   do those extra reductions? That is, 
   would 
    
     (S, =_r, (x)_r) 

   still be correct? 

 *)

(* move this? *)

Definition uop_is_bop_reduction {S : Type} (eqS : brel S) (b : binary_op S) (r : unary_op S) 
  := ∀ (s1 s2 : S), eqS (r (b s1 s2)) (r (b (r s1) (r s2))) = true. 


Section Computation.

Definition bop_reduce {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  r (b x y).

Definition bop_reduce_args {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  b (r x) (r y).   

Definition bop_full_reduce {S : Type} (r : unary_op S) (b : binary_op S) : binary_op S
  := λ x y,  r(b (r x) (r y)).   

End Computation.

Section Congruence.

  (* results that depend only on congruence *) 

  
  Variables (S : Type) 
           (b : binary_op S)
           (r : unary_op S)
           (eqS    : brel S)
           (symS : brel_symmetric S eqS) 
           (trnS : brel_transitive S eqS) 
           (b_cong : bop_congruence S eqS b) 
           (r_cong  : uop_congruence S eqS r). 

  Lemma bop_full_reduce_congruence : 
    bop_congruence S (brel_reduce eqS r) (bop_full_reduce r b).
  Proof. intros x y u v H1 H2.
         compute. apply r_cong.
         unfold brel_reduce in H1, H2.
         assert (H3 := b_cong _ _ _ _ H1 H2).
         apply r_cong in H3.
         exact H3. 
  Qed.
  
  Lemma bop_reduce_congruence
    (r_is_b_reduction : uop_is_bop_reduction eqS b r) :  
    bop_congruence S (brel_reduce eqS r) (bop_reduce r b).
  Proof.  intros x y u v H1 H2.
          compute. apply r_cong.
          unfold brel_reduce in H1, H2.
          assert (H0 := b_cong _ _ _ _ H1 H2).
          apply r_cong in H0. 
          assert (H3 := r_is_b_reduction x y). 
          assert (H4 := r_is_b_reduction u v). 
          assert (H5 := trnS _ _ _ H3 H0).
          apply symS in H4.
          exact (trnS _ _ _ H5 H4). 
  Qed.

End Congruence.


Section ReductionClassical.

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r : unary_op S.
  Variable eqS    : brel S.    

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable trnS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.
  
  Variable b_cong : bop_congruence S eqS b. 
  Variable b_ass  : bop_associative S eqS b.

(* classical axioms of Semirings and path spaces by Ahnont Wongseelashote, 1979 

    r(r(a)) = r(a) 
    r(a + b) = r(r(a) + b) 
    r(a + b) = r(a + r(b)) 

*)
  Variable r_cong  : uop_congruence S eqS r. 
  Variable r_idem  : uop_idempotent S eqS r.
  Variable r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r.  (* eqS (r (b (r s1) s2)) (r (b s1 s2))  = true. *) 
  Variable r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r. (* eqS (r (b s1 (r s2))) (r (b s1 s2))  = true. *)

  Lemma is_a_fixed_point_bop_reduce :
    ∀ (p1 p2 : reduced_type _ eqS r), is_a_fixed_point _ eqS r (bop_reduce r b (projT1 p1) (projT1 p2)).
  Proof. intros [s1 p1] [s2 p2]. compute. apply r_idem. Defined.
  
  Definition reduced_bop : binary_op (reduced_type _ eqS r) :=
    λ p1 p2,  existT (is_a_fixed_point _ eqS r)
                     (bop_reduce r b (projT1 p1) (projT1 p2))
                     (is_a_fixed_point_bop_reduce p1 p2).

  Lemma reduced_bop_congruence : bop_congruence (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute.
         unfold is_a_fixed_point in *.  intros H1 H2.
         apply r_cong.
         apply b_cong; auto.
  Qed.

Lemma r_is_b_reduction : uop_is_bop_reduction eqS b r. 
Proof. intros s1 s2. 
           assert (H1 := r_left s1 s2). compute in H1. 
           assert (H2 := r_right (r s1) s2). compute in H2.            
           assert (H3 := trnS _ _ _ H2 H1). apply symS. 
           exact H3.            
    Qed. 

Lemma reduced_bop_ass : bop_associative (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop. 
Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := r_left (b s1 s2) s3).
         assert (H2 := r_right s1 (b s2 s3)).
         assert (H3 := r_cong _ _ (b_ass s1 s2 s3)).
         apply symS in H2. 
         assert (H4 := trnS _ _ _ H3 H2).
         assert (H5 := trnS _ _ _ H1 H4).
         exact H5. 
Qed.

Lemma reduced_bop_id :
  uop_preserves_id S eqS b r
  -> bop_exists_id S eqS b
  -> bop_exists_id (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop. 
Proof. intros H [id p]. exists (inject_into_reduced_type _ eqS r r_idem id).
       unfold bop_is_id in p. unfold bop_is_id.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H id p).
          assert (H4 := r_left  id t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := trnS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := trnS _ _ _ H6 pt).
          exact H7.
          assert (H3 := H id p).
          assert (H4 := r_right  t id). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := trnS _ _ _ H4 H5).
          compute in pt.
          assert (H7 := trnS _ _ _ H6 pt).
          exact H7.
Qed.

(*
Lemma reduced_bop_not_exists_id_v1 :
  bop_not_exists_id S eqS b ->
  bop_not_exists_id (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. intros nid [s P]. destruct (nid s) as [x W]. 
       assert (Q' : is_a_fixed_point S eqS r x). admit. 
       exists (existT (is_a_fixed_point S eqS r) x Q').
       compute. 
Defined. 
*) 
Lemma reduced_bop_not_exists_id_v2 :
  bop_not_exists_id S eqS b ->
  (∀ s x, ((eqS (b s x) x = false) + (eqS (b x s) x = false)) -> 
        ((eqS (r (b s (r x))) (r x) = false) + (eqS (r (b (r x) s)) (r x) = false))) ->  
  bop_not_exists_id (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. intros nid H [s P]. destruct (nid s) as [x W]. 
       assert (Q' : is_a_fixed_point S eqS r (r x)). apply r_idem.
       exists (existT (is_a_fixed_point S eqS r) (r x) Q').
       compute. apply H; auto. 
Defined. 

Lemma reduced_bop_ann :
  uop_preserves_ann S eqS b r
  -> bop_exists_ann S eqS b
  -> bop_exists_ann (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop. 
Proof. intros H [ann p]. exists (inject_into_reduced_type _ eqS r r_idem ann).
       unfold bop_is_ann in p. unfold bop_is_ann.
         intros [t pt]. compute.
         destruct (p t) as [H1  H2]. split. 
         assert (H3 := H ann p).
          assert (H4 := r_left  ann t). compute in H4.
          assert (H5 := r_cong _ _ H1).
          assert (H6 := trnS _ _ _ H4 H5).
          exact H6.
          assert (H3 := H ann p).
          assert (H4 := r_right  t ann). compute in H4.
          assert (H5 := r_cong _ _ H2).
          assert (H6 := trnS _ _ _ H4 H5).
          exact H6.
Qed.

Lemma reduced_bop_commutative
  (comm : bop_commutative _ eqS b) : 
  bop_commutative (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. intros [s P] [t Q]. compute.
       assert (A := comm s t). unfold is_a_fixed_point in P, Q.
       assert (B := r_cong _ _  A). 
       exact B.
Qed.


Lemma reduced_bop_idempotent
  (idem : bop_idempotent _ eqS b) : 
  bop_idempotent (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. intros [s P]. compute.
       assert (A := idem s). unfold is_a_fixed_point in P. 
       assert (B := r_cong _ _  A). 
       exact (trnS _ _ _ B P).
Qed.

Lemma reduced_bop_not_idempotent
      (nidem : bop_not_idempotent _ eqS b)
      (Q : let s := projT1 nidem in eqS (r s) s = true)
      (P : let s := projT1 nidem in eqS (r (b s s)) s = false) : 
  bop_not_idempotent (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. destruct nidem as [s A]. simpl in P, Q. 
       unfold bop_not_idempotent, reduced_type. 
       assert (B : is_a_fixed_point S eqS r s). exact Q. 
       exists (existT (fun x => is_a_fixed_point S eqS r x) s B).
       unfold reduced_equality, reduced_bop; simpl.
       unfold bop_reduce. 
       exact P. 
Defined.

Lemma reduced_bop_selective
  (sel : bop_selective _ eqS b) : 
  bop_selective (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. intros [s P] [s' P']. compute.
       compute in P, P'. 
       destruct (sel s s') as [A | A].
       - left. assert (B := r_cong _ _  A). 
         exact (trnS _ _ _ B P).
       - right. assert (B := r_cong _ _  A). 
         exact (trnS _ _ _ B P').
Qed.

Lemma reduced_bop_not_selective
      (nsel : bop_not_selective _ eqS b)
      (Q1 : let (s, _) := projT1 nsel in eqS (r s) s = true)
      (Q2 : let (_, s) := projT1 nsel in eqS (r s) s = true)      
      (P : let (s, t) := projT1 nsel in (eqS (r (b s t)) s = false) * (eqS (r (b s t)) t = false)): 
  bop_not_selective (reduced_type _ eqS r) (reduced_equality _ eqS r) reduced_bop.
Proof. destruct nsel as [[s t] [A B]]. simpl in P, Q1, Q2. 
       unfold bop_not_selective, reduced_type. 
       assert (C : is_a_fixed_point S eqS r s). exact Q1.
       assert (D : is_a_fixed_point S eqS r t). exact Q2.        
       exists ((existT (fun x => is_a_fixed_point S eqS r x) s C),
               (existT (fun x => is_a_fixed_point S eqS r x) t D)).
       unfold reduced_equality, reduced_bop; simpl.
       unfold bop_reduce. 
       exact P. 
Defined.

End ReductionClassical.





  
Section JustIdempotence.

(* this Section explores how far we can get with only idempotence of the reduction r *) 
  
  Variables (S : Type) 
           (b : binary_op S)
           (r : unary_op S)
           (eqS    : brel S)    
           (refS   : brel_reflexive S eqS) 
           (symS   : brel_symmetric S eqS) 
           (trnS   : brel_transitive S eqS)
           (eqS_cong : brel_congruence S eqS eqS)
           (b_cong : bop_congruence S eqS b) 
           (b_ass  : bop_associative S eqS b)
           (r_cong  : uop_congruence S eqS r) 
           (r_idem  : uop_idempotent S eqS r). 

  Local Notation "[inj]" := (inject_into_reduced_type _ eqS r r_idem).
  Local Notation "[RT]" := (reduced_type _ eqS r).
  Local Notation "[REQ]" := (reduced_equality _ eqS r).
  Local Notation "[RBOP]" := (reduced_bop _ b r eqS r_idem).
  (*
   f is a homomorphism for b and b' if 
    f(b(x, y)) = b'(f(x), f(y))

   The following show that 
    1) [inj] is a homomorphism for (bop_full_reduce r b) and reduced_bop. 
    2) projT1 is a homomorphism for reduced_bop and (bop_full_reduce r b). 
    3) ([inj] o projT1) is id on reduced_type
    4) (projT1 o [inj]) is id on r(S), the image of r 

    so we have an isomorphism between (r(S), (bop_full_reduce r b) and (reduced_type, reduced_bop) 
*)

  (* r(b (r s1) (r s2)) =_r b_r (inj s1) (inj s2) *) 
  Lemma inj_homomorphism : ∀ (s1 s2 : S),
      [REQ] ([inj] (bop_full_reduce r b s1 s2))
            ([RBOP] ([inj] s1) ([inj] s2)) = true. 
  Proof. intros s1 s2. compute. apply r_idem. Qed.

  (* fst (b_r s1 s2) = r(b (r (fst s1)) (fst s2)) *)
  Lemma proj1_homomorphism : ∀ (p1 p2 : [RT]),  eqS (projT1 ([RBOP] p1 p2)) (bop_full_reduce r b (projT1 p1) (projT1 p2)) = true. 
  Proof. intros [s1 P1] [s2 P2]. compute. compute in P1. compute in P2.
         apply r_cong.
         assert (K := b_cong _ _ _ _ P1 P2).  apply symS.
         exact K. 
  Qed. 

  (* (s, P) =_r (inj s) *)
  Lemma inj_proj1_is_id : ∀ p : [RT],  [REQ] p ([inj] (projT1 p)) = true.
  Proof. intros [s P]. compute. compute in P. apply symS. exact P. Qed. 

  (* (r s) = fst (inj s) *) 
  Lemma proj1_inj_is_id_on_image_of_r : ∀ s : S,  eqS (r s) (projT1 ([inj] s)) = true.
  Proof. intro s. compute. apply refS. Qed.

  (* s1 = s2 <-> (s1, P1) =_r (s2, P2) *) 
  Lemma equality_lemma_1 : ∀ (p1 p2 : [RT]),  eqS (projT1 p1) (projT1 p2) = [REQ] p1 p2.
  Proof. intros [s1 P1] [s2 P2]. compute. reflexivity. Qed.

  (* r s1 = r s2 <-> inj s1 =_r inj s2 *) 
  Lemma equality_lemma_2 : ∀ (s1 s2 : S),  eqS (r s1) (r s2) = [REQ] ([inj] s1) ([inj] s2).
  Proof. intros s1 s2. compute. reflexivity. Qed. 


  (*****************************************************************************************
      Now show that 
      (reduced_type, reduced_equality, reduced_bop) is "isomorphic" to our "OCaml" implementation: 

      (S, brel_reduce r eqS, bop_full_reduce r b)

      or (S, brel_reduce r eqS, bop_reduce r b)???

  *******************************************************************************************) 

  
Lemma observation1 : (bop_left_uop_invariant S (brel_reduce eqS r) b r) <-> (bop_left_uop_invariant S eqS (bop_reduce r b) r).
Proof. compute. split; auto.   Qed. 

Lemma observation2 : (bop_right_uop_invariant S eqS (bop_reduce r b) r) <-> (bop_right_uop_invariant S (brel_reduce eqS r) b r).
Proof. split; auto.   Qed.

  
  
Lemma reduced_bop_congruence_iff: 
  bop_congruence [RT] [REQ] [RBOP]
  <->
  bop_congruence S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. split.
       (* -> *) 
       intros H s1 s2 s3 s4. compute. intros H1 H2. 
       assert (K := H ([inj] s1) ([inj] s2) ([inj] s3) ([inj] s4)).  compute in K.
       apply r_cong.        
       apply K; auto.
       (* <- *) 
       intros H [s1 p1] [s2 p2] [s3 p3] [s4 p4]. compute. intros H1 H2. 
       unfold is_a_fixed_point in p1, p2, p3, p4. 
       compute in H.
       assert (J1 := r_cong _ _ H1).
       assert (J2 := r_cong _ _ H2).
       assert (J3 := H _ _ _ _ J1 J2).
       assert (J4 := r_idem (b (r s1) (r s2))).
       assert (J5 := r_idem (b (r s3) (r s4))).
       assert (J6 := trnS _ _ _ J3 J5).
       apply symS in J4.
       assert (J7 := trnS _ _ _ J4 J6).
       assert (J8 := b_cong _ _ _ _ p1 p2). apply r_cong in J8.
       assert (J9 := b_cong _ _ _ _ p3 p4). apply r_cong in J9.
       assert (J10 := trnS _ _ _ J7 J9).
       apply symS in J8.
       assert (J11 := trnS _ _ _ J8 J10).
       exact J11.
Qed.


Lemma reduced_bop_associative_iff :
  bop_associative [RT] [REQ] [RBOP]
  <->
  bop_associative S (brel_reduce eqS r) (bop_full_reduce r b). 
Proof. split; intro H.
         intros s1 s2 s3. compute. 
         assert (H1 := H ([inj] s1) ([inj] s2) ([inj] s3)). compute in H1.
         apply r_cong.
         assert (H2 := r_idem (b (r s1) (r s2))).
         assert (H3 := r_idem (b (r s2) (r s3))).
         assert (H4 := b_cong _ _ _ _ H2 (refS (r s3))).
         assert (H5 := b_cong _ _ _ _ (refS (r s1)) H3).
         apply r_cong in H4. apply r_cong in H5.
         assert (H6 := trnS _ _ _ H4 H1). apply symS in H5. 
         assert (H7 := trnS _ _ _ H6 H5).          
         exact H7.
         intros [s1 p1] [s2 p2] [s3 p3]. compute.
         assert (H1 := H s1 s2 s3). compute in H1. unfold is_a_fixed_point in p1, p2, p3.
         assert (H2 := b_cong _ _ _ _ p1 p2). apply r_cong in H2.
         assert (K2 := r_idem (b (r s1) (r s2))). 
         assert (K3 := trnS _ _ _ K2 H2). 
         assert (H3 := b_cong _ _ _ _ K3 p3). apply r_cong in H3.
         assert (K4 := r_idem (b (r (r (b (r s1) (r s2)))) (r s3))). 
         assert (K5 := trnS _ _ _ K4 H3).

         assert (H4 := b_cong _ _ _ _ p2 p3). apply r_cong in H4. 
         assert (K6 := r_idem (b (r s2) (r s3))). 
         assert (K7 := trnS _ _ _ K6 H4).
         assert (H5 := b_cong _ _ _ _ p1 K7). apply r_cong in H5.
         assert (K8 := r_idem (b (r s1) (r (r (b (r s2) (r s3)))))). 
         assert (K9 := trnS _ _ _ K8 H5).
         apply symS in K5.
         assert (H6 := trnS _ _ _ K5 H1).
         assert (H7 := trnS _ _ _ H6 K9).         
         exact H7.
Qed.


Lemma reduced_bop_commutative_iff :
  bop_commutative [RT] [REQ] [RBOP]
  <->
  bop_commutative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. split.
         intros H s1 s2. compute.
         assert (K := H ([inj] s1) ([inj] s2)). compute in K.
         apply r_cong.
         exact K. 
         intros H1 [s1 p1] [s2 p2]. compute.
         assert (K := H1 s1 s2). compute in K. 
         unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2.
         assert (J1 := r_idem (b (r s1) (r s2))).
         assert (J2 := r_idem (b (r s2) (r s1))).
         apply symS in J1.
         assert (J3 := trnS _ _ _ J1 K).
         assert (J4 := trnS _ _ _ J3 J2).
         assert (J5 := b_cong _ _ _ _ p1 p2). apply r_cong in J5. 
         assert (J6 := b_cong _ _ _ _ p2 p1). apply r_cong in J6. 
         assert (J7 := trnS _ _ _ J4 J6).         
         apply symS in J5. 
         assert (J8 := trnS _ _ _ J5 J7).
         exact J8.
Qed.

Lemma reduced_bop_not_commutative_iff_left :
  bop_not_commutative [RT] [REQ] [RBOP]
  ->
  bop_not_commutative S (brel_reduce eqS r) (bop_full_reduce r b).
Proof.   intros [[[s1 p1] [s2 p2]]  p3]. compute in p3.  unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2. 
         exists (s1, s2). compute.
         case_eq(eqS (r (r (b (r s1) (r s2)))) (r (r (b (r s2) (r s1))))); intro J1.
         assert (K : eqS (r (b s1 s2)) (r (b s2 s1)) = true).
            assert (J2 := b_cong _ _ _ _ p1 p2). apply r_cong in J2. apply symS in J2. 
            assert (J3 := r_idem (b (r s1) (r s2))).  apply symS in J3.
            assert (J4 := trnS _ _ _ J2 J3).            
            assert (J5 := trnS _ _ _ J4 J1).            
            assert (J6 := r_idem (b (r s2) (r s1))). 
            assert (J7 := trnS _ _ _ J5 J6).            
            assert (J8 := b_cong _ _ _ _ p2 p1). apply r_cong in J8.
            assert (J9 := trnS _ _ _ J7 J8).
            exact J9.
         rewrite K in p3.  discriminate p3. 
         reflexivity. 
Qed. 


Lemma reduced_bop_not_commutative_iff_right :
  bop_not_commutative S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_commutative [RT] [REQ] [RBOP].
Proof.  intros [[s1 s2]  p]. exists ([inj] s1, [inj] s2). compute.  
        compute in p. 
        case_eq(eqS (r (b (r s1) (r s2))) (r (b (r s2) (r s1)))); intro J1.
           apply r_cong in J1.
           rewrite J1 in p. discriminate p. 
        reflexivity. 
Qed. 

Lemma reduced_bop_selective_iff_left :
  bop_selective [RT] [REQ] [RBOP]
  ->
  bop_selective S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof. intros H s1 s2. compute.
  assert (K := H ([inj] s1) ([inj] s2)). compute in K.
  destruct K as [K | K]. left. 
  assert (A := r_idem (b (r s1) (r s2)) ).
  exact (trnS _ _ _ A K).
  right. assert (A := r_idem (b (r s1) (r s2)) ).
  exact (trnS _ _ _ A K).
 Qed.

 Lemma reduced_bop_selective_iff_right :
   bop_selective S (brel_reduce eqS r) (bop_full_reduce r b)
   ->
   bop_selective [RT] [REQ] [RBOP].
 Proof. intros H1 [s1 p1] [s2 p2]. compute.
  assert (K := H1 s1 s2). compute in K. 
  unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2.
  destruct K as [K | K]. left. 
  assert (A := r_idem (b (r s1) (r s2)) ). apply symS in A.
  assert (B := trnS _ _ _ A K).
  assert (C := b_cong (r s1) (r s2) s1 s2 p1 p2). apply r_cong in C. apply symS in C.
  assert (D := trnS _ _ _ C B).
  exact (trnS _ _ _ D p1).
  right.
  assert (A := r_idem (b (r s1) (r s2)) ). apply symS in A.
  assert (B := trnS _ _ _ A K).
  assert (C := b_cong (r s1) (r s2) s1 s2 p1 p2). apply r_cong in C. apply symS in C.
  assert (D := trnS _ _ _ C B).
  exact (trnS _ _ _ D p2).
 Qed.


 Lemma reduced_bop_not_selective_iff_left :
  bop_not_selective [RT] [REQ] [RBOP]
  ->
  bop_not_selective S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof.   intros [[[s1 p1] [s2 p2]]  [p3 p4]].
          compute in p3, p4.  unfold is_a_fixed_point in p1, p2. 
          exists (s1, s2). compute. split. 
          - case_eq(eqS (r (r (b (r s1) (r s2)))) (r s1)); intro J1; auto. 
            assert (K : eqS (r (b s1 s2)) s1 = true).
            {
              assert (J2 := b_cong _ _ _ _ p1 p2). apply r_cong in J2.
              assert (J3 := r_idem (b (r s1) (r s2))).  
              assert (J4 := trnS _ _ _ J3 J2). apply symS in J4. 
              assert (J5 := trnS _ _ _ J4 J1).            
              exact (trnS _ _ _ J5 p1).
            } 
            rewrite K in p3.  discriminate p3. 
          - case_eq(eqS (r (r (b (r s1) (r s2)))) (r s2)); intro J1; auto. 
            assert (K : eqS (r (b s1 s2)) s2 = true).
            {
              assert (J2 := b_cong _ _ _ _ p1 p2). apply r_cong in J2.
              assert (J3 := r_idem (b (r s1) (r s2))).  
              assert (J4 := trnS _ _ _ J3 J2). apply symS in J4. 
              assert (J5 := trnS _ _ _ J4 J1).            
              exact (trnS _ _ _ J5 p2).
            } 
            rewrite K in p4.  discriminate p4. 
Qed. 

Lemma reduced_bop_not_selective_iff_right :
  bop_not_selective S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_selective [RT] [REQ] [RBOP].
Proof.  intros [[s1 s2]  p]. exists ([inj] s1, [inj] s2). compute.  
        compute in p. destruct p as [p1 p2].
        split.
        - case_eq(eqS (r (b (r s1) (r s2))) (r s1)); intro J1; auto.
          apply r_cong in J1. assert (J2 := r_idem s1). 
          rewrite (trnS _ _ _ J1 J2) in p1. discriminate p1. 
        - case_eq(eqS (r (b (r s1) (r s2))) (r s2)); intro J1; auto.
          apply r_cong in J1. assert (J2 := r_idem s2). 
          rewrite (trnS _ _ _ J1 J2) in p2. discriminate p2. 
 Qed. 

 Lemma reduced_bop_idempotent_iff_left :
   bop_idempotent [RT] [REQ] [RBOP]
   ->
   bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof. intros H s . compute.
  assert (K := H ([inj] s)). compute in K.
  assert (A := r_idem (b (r s) (r s)) ).
  exact (trnS _ _ _ A K).
 Qed.

 Lemma reduced_bop_idempotent_iff_right :
   bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r b)
   ->
   bop_idempotent [RT] [REQ] [RBOP]. 
 Proof. intros H1 [s p]. compute.
  assert (K := H1 s). compute in K. 
  unfold is_a_fixed_point in p. 
  assert (A := r_idem (b (r s) (r s)) ). apply symS in A.
  assert (B := trnS _ _ _ A K).
  assert (C := b_cong (r s) (r s) s s p p). apply r_cong in C. apply symS in C.
  assert (D := trnS _ _ _ C B).
  exact (trnS _ _ _ D p).
 Qed.


 Lemma reduced_bop_not_idempotent_iff_left :
  bop_not_idempotent [RT] [REQ] [RBOP]
  ->
  bop_not_idempotent S (brel_reduce eqS r) (bop_full_reduce r b).
 Proof.   intros [[s1 p1] p2]. compute in p1, p2.  
          exists s1. compute. 
          case_eq(eqS (r (r (b (r s1) (r s1)))) (r s1)); intro J1; auto. 
          assert (K : eqS (r (b s1 s1)) s1 = true).
          {
            assert (J2 := b_cong _ _ _ _ p1 p1). apply r_cong in J2.
            assert (J3 := r_idem (b (r s1) (r s1))).  
            assert (J4 := trnS _ _ _ J3 J2). apply symS in J4. 
            assert (J5 := trnS _ _ _ J4 J1).            
            exact (trnS _ _ _ J5 p1).
          } 
          rewrite K in p2.  discriminate p2. 
Qed. 

Lemma reduced_bop_not_idempotent_iff_right :
  bop_not_idempotent S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_idempotent [RT] [REQ] [RBOP].
Proof.  intros [s1  p]. exists ([inj] s1). compute.  
        compute in p. 
        case_eq(eqS (r (b (r s1) (r s1))) (r s1)); intro J1; auto.
        apply r_cong in J1. assert (J2 := r_idem s1). 
        rewrite (trnS _ _ _ J1 J2) in p. discriminate p. 
 Qed. 

 Lemma red_exists_id_left :
   bop_exists_id [RT] [REQ] [RBOP]
   ->
   bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros [[id P] Q].
       exists id. intro s; compute. compute in Q.
       destruct (Q ([inj] s)) as [L R]. compute in L, R. unfold is_a_fixed_point in P.
       split.
       assert (J1 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J1.
       assert (J2 := trnS _ _ _ J1 L). apply r_cong in J2.
       assert (J3 := r_idem s).
       assert (J4 := trnS _ _ _ J2 J3).
       exact J4.
       assert (J1 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J1.
       assert (J2 := trnS _ _ _ J1 R). apply r_cong in J2.
       assert (J3 := r_idem s).
       assert (J4 := trnS _ _ _ J2 J3).
       exact J4. 
Qed. 

Lemma red_exists_id_right :
  bop_exists_id S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_exists_id [RT] [REQ] [RBOP].
Proof. intros [id Q].
       exists ([inj] id). intros [s P]; compute. compute in Q.
       destruct (Q s) as [L R].  unfold is_a_fixed_point in P.
       split.
       assert (J1 := b_cong _ _ _ _(refS (r id)) P). apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
       assert (J2 := trnS _ _ _ J1 L). 
       assert (J3 := r_idem (b (r id) s)). apply symS in J3. 
       assert (J4 := trnS _ _ _ J3 J2).
       assert (J5 := trnS _ _ _ J4 P).       
       exact J5.
       assert (J1 := b_cong _ _ _ _ P (refS (r id))). apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
       assert (J2 := trnS _ _ _ J1 R). 
       assert (J3 := r_idem (b s (r id))). apply symS in J3. 
       assert (J4 := trnS _ _ _ J3 J2).
       assert (J5 := trnS _ _ _ J4 P).       
       exact J5.
Qed. 


Lemma red_not_exists_id_left :
  bop_not_exists_id [RT] [REQ] [RBOP]
  ->
  bop_not_exists_id S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros H s. compute.
       destruct (H ([inj] s)) as [[s' P] Q]. compute in Q. unfold is_a_fixed_point in P.
       exists s'.
       destruct Q as [Q | Q].
       left.
       case_eq(eqS (r (r (b (r s) (r s')))) (r s')); intro J1.
       assert (K : eqS (r (b (r s) s')) s' = true).
          assert (J2 := trnS _ _ _ J1 P).
          assert (J3 := r_idem (b (r s) (r s'))). apply symS in J3.
          assert (J4 := trnS _ _ _ J3 J2).
          assert (J5 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J5. apply symS in J5.
          assert (J6 := trnS _ _ _ J5 J4).
          exact J6. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
       right. 
       case_eq(eqS (r (r (b (r s') (r s)))) (r s')); intro J1.
       assert (K : eqS (r (b s' (r s))) s' = true).
          assert (J2 := trnS _ _ _ J1 P).
          assert (J3 := r_idem (b (r s') (r s))). apply symS in J3.
          assert (J4 := trnS _ _ _ J3 J2).
          assert (J5 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J5. apply symS in J5.
          assert (J6 := trnS _ _ _ J5 J4).
          exact J6. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
Qed.

Lemma red_not_exists_id_right :
  bop_not_exists_id S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_exists_id [RT] [REQ] [RBOP].
Proof. intros H [s P]. compute. unfold is_a_fixed_point in P. 
       destruct (H s) as [s' Q]. compute in Q.
       exists ([inj] s'). compute. 
       destruct Q as [Q | Q].
       left.
       case_eq(eqS (r (b s (r s'))) (r s')); intro J1.
       assert (K : eqS (r (r (b (r s) (r s')))) (r s') = true).
          assert (J2 := b_cong _ _ _ _ P (refS (r s'))). apply r_cong in J2. 
          assert (J3 := trnS _ _ _ J2 J1). apply r_cong in J3. 
          assert (J4 := r_idem s'). 
          assert (J5 := trnS _ _ _ J3 J4).
          exact J5. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
       right. 
       case_eq(eqS (r (b (r s') s)) (r s')); intro J1.
       assert (K : eqS (r (r (b (r s') (r s)))) (r s') = true).
          assert (J2 := b_cong _ _ _ _ (refS (r s')) P). apply r_cong in J2. 
          assert (J3 := trnS _ _ _ J2 J1). apply r_cong in J3. 
          assert (J4 := r_idem s'). 
          assert (J5 := trnS _ _ _ J3 J4).
          exact J5. 
       rewrite K in Q.
       discriminate Q. 
       reflexivity.
Qed.


 Lemma red_exists_ann_left :
   bop_exists_ann [RT] [REQ] [RBOP]
   ->
   bop_exists_ann S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros [[ann P] Q].
       exists ann. intro s; compute. compute in Q.
       destruct (Q ([inj] s)) as [L R]. compute in L, R. unfold is_a_fixed_point in P.
       split.
       - assert (J1 := b_cong _ _ _ _ P (refS (r s))). apply r_cong in J1.
         assert (J2 := trnS _ _ _ J1 L). apply r_cong in J2.
         exact J2.
       - assert (J1 := b_cong _ _ _ _ (refS (r s)) P). apply r_cong in J1.
         assert (J2 := trnS _ _ _ J1 R). apply r_cong in J2.
         exact J2. 
Qed. 

Lemma red_exists_ann_right :
  bop_exists_ann S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_exists_ann [RT] [REQ] [RBOP].
Proof. intros [ann Q].
       exists ([inj] ann). intros [s P]; compute. compute in Q.
       destruct (Q s) as [L R].  unfold is_a_fixed_point in P.
       split.
       - assert (J1 := b_cong _ _ _ _(refS (r ann)) P). 
         apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
         assert (J2 := trnS _ _ _ J1 L). 
         assert (J3 := r_idem (b (r ann) s)). apply symS in J3. 
         exact (trnS _ _ _ J3 J2).
       - assert (J1 := b_cong _ _ _ _ P (refS (r ann))).
         apply r_cong in J1. apply r_cong in J1. apply symS in J1. 
         assert (J2 := trnS _ _ _ J1 R). 
         assert (J3 := r_idem (b s (r ann))). apply symS in J3. 
         exact (trnS _ _ _ J3 J2).
Qed. 


Lemma red_not_exists_ann_left :
  bop_not_exists_ann [RT] [REQ] [RBOP]
  ->
  bop_not_exists_ann S (brel_reduce eqS r) (bop_full_reduce r b).
Proof. intros H s. compute.
       destruct (H ([inj] s)) as [[s' P] Q]. compute in Q, P. 
       exists s'. destruct Q as [Q | Q].
       - left.
         case_eq(eqS (r (r (b (r s) (r s')))) (r s)); intro J1; auto. 
         assert (K : eqS (r (b (r s) s')) (r s) = true).
         {
           assert (J0 := b_cong _ _ _ _ (refS (r s)) P). 
           apply r_cong in J0. apply symS in J0. 
           assert (J2 := r_idem (b (r s) (r s'))). apply symS in J2. 
           assert (J4 := trnS _ _ _ J0 J2).
           exact (trnS _ _ _ J4 J1).
         } 
         rewrite K in Q. discriminate Q. 
       - right.
         case_eq(eqS (r (r (b (r s') (r s)))) (r s)); intro J1; auto. 
         assert (K : eqS (r (b s' (r s))) (r s) = true).
         {
           assert (J0 := b_cong _ _ _ _ P (refS (r s))). 
           apply r_cong in J0. apply symS in J0. 
           assert (J2 := r_idem (b (r s') (r s))). apply symS in J2. 
           assert (J4 := trnS _ _ _ J0 J2).
           exact (trnS _ _ _ J4 J1).
         } 
         rewrite K in Q. discriminate Q. 
Qed.

Lemma red_not_exists_ann_right :
  bop_not_exists_ann S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_exists_ann [RT] [REQ] [RBOP].
Proof. intros H [s P]. compute. unfold is_a_fixed_point in P. 
       destruct (H s) as [s' Q]. compute in Q.
       exists ([inj] s'). compute. 
       destruct Q as [Q | Q].
       - left.
         case_eq(eqS (r (b s (r s'))) s); intro J1; auto. 
         assert (K : eqS (r (r (b (r s) (r s')))) (r s) = true).
         {
           assert (J2 := b_cong _ _ _ _ P (refS (r s'))). apply r_cong in J2. 
           assert (J3 := trnS _ _ _ J2 J1). apply r_cong in J3. 
           exact J3.
         }
         rewrite K in Q. discriminate Q. 
       - right. 
         case_eq(eqS (r (b (r s') s)) s); intro J1; auto. 
         assert (K : eqS (r (r (b (r s') (r s)))) (r s) = true).
         {
           assert (J2 := b_cong _ _ _ _ (refS (r s')) P). apply r_cong in J2. 
           assert (J3 := trnS _ _ _ J2 J1). apply r_cong in J3. 
           exact J3.
         }
         rewrite K in Q. discriminate Q. 
Qed.

End JustIdempotence.   

Section Theory.
  Variables (S : Type) 
           (b : binary_op S)
           (r : unary_op S)
           (eqS    : brel S)    
           (refS   : brel_reflexive S eqS) 
           (symS   : brel_symmetric S eqS) 
           (trnS   : brel_transitive S eqS)
           (eqS_cong : brel_congruence S eqS eqS)
           (b_cong : bop_congruence S eqS b) 
           (b_ass  : bop_associative S eqS b)
           (r_cong  : uop_congruence S eqS r) 
           (r_idem  : uop_idempotent S eqS r)
           (r_is_b_reduction : uop_is_bop_reduction eqS b r). 

  Local Notation "x =_r y" := (brel_reduce eqS r x y = true) (at level 70) .
  Local Notation "x [FR] y" := (bop_full_reduce r b x y) (at level 70). 
  Local Notation "x [R] y" := (bop_reduce r b x y) (at level 70).
  
  Lemma bop_reduce_is_bop_full_reduce :
    ∀ x y u v, (x =_r u) -> (y =_r v) -> (x [R] y) =_r (u [FR] v).
  Proof. intros x y u v Hxu Hyv.
         unfold bop_reduce, bop_full_reduce, brel_reduce.
         assert (H0 := b_cong _ _ _ _ Hxu Hyv). 
         assert (H2 := r_is_b_reduction x y). 
         apply r_cong in H0, H2. 
         apply r_cong in H0. 
         assert (H3 := trnS _ _ _ H2 H0). 
         exact H3. 
Qed.

Lemma bop_full_reduce_congruence_iff_bop_reduce_congruence : 
  bop_congruence S (brel_reduce eqS r) (bop_full_reduce r b)
  <->
  bop_congruence S (brel_reduce eqS r) (bop_reduce r b).
Proof. assert (sym := brel_reduce_symmetric _ eqS r symS). 
       assert (trn := brel_reduce_transitive _ eqS r trnS). 
       split; intros H1 x y u v H2 H3. 
       - assert (H4 := H1 x y u v H2 H3). 
         assert (H5 := bop_reduce_is_bop_full_reduce x y u v H2 H3).
         apply sym in H4.
         assert (H6 := trn _ _ _ H5 H4). 
         apply sym in H2, H3. 
         assert (H7 := bop_reduce_is_bop_full_reduce _ _ _ _  H2 H3). 
         apply sym in H7.         
         exact (trn _ _ _ H6 H7).
       - assert (H4 := H1 x y u v H2 H3). 
         assert (H5 := bop_reduce_is_bop_full_reduce x y u v H2 H3).
         apply sym in H4.
         assert (H6 := trn _ _ _ H4 H5). 
         apply sym in H2, H3. 
         assert (H7 := bop_reduce_is_bop_full_reduce _ _ _ _  H2 H3). 
         apply sym in H7.         
         exact (trn _ _ _ H7 H6).
Qed.          


Lemma bop_full_reduce_associative_iff_bop_reduce_associative : 
  bop_associative S (brel_reduce eqS r) (bop_full_reduce r b)
  <->
    bop_associative S (brel_reduce eqS r) (bop_reduce r b).
Proof. assert (ref := brel_reduce_reflexive _ eqS r refS).
       assert (sym := brel_reduce_symmetric _ eqS r symS). 
       assert (trn := brel_reduce_transitive _ eqS r trnS).
       split; intros H1 x y u. 
       - assert (H4 := H1 x y u).
         assert (H5 : ((x [R] y) [R] u) =_r ((x [FR] y) [FR] u)).
         {
           assert (H6 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref y)). 
           assert (H7 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref (x [R] y)) (ref u)).
           assert (H8 := bop_full_reduce_congruence S b r eqS b_cong r_cong _ _ _ _ H6 (ref u)).
           exact (trn _ _ _ H7 H8).
         } 
         assert (H6 : (x [FR] (y [FR] u)) =_r (x [R] (y [R] u))).
         {
           assert (H6 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref y) (ref u)). 
           assert (H7 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref (y [R] u))).
           assert (H8 := bop_full_reduce_congruence S b r eqS b_cong r_cong _ _ _ _ (ref x) H6).
           apply sym in H8, H7.
           exact (trn _ _ _ H8 H7).
         } 
         assert (H7 := brel_reduce_transitive _ eqS r trnS _ _ _ H5 H4). 
         exact (brel_reduce_transitive _ eqS r trnS _ _ _ H7 H6).
       - assert (H4 := H1 x y u).
         assert (H5 : ((x [FR] y) [FR] u) =_r ((x [R] y) [R] u)).
         {
           assert (H6 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref y)). 
           assert (H7 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref (x [R] y)) (ref u)).
           assert (H8 := bop_full_reduce_congruence S b r eqS b_cong r_cong  _ _ _ _ H6 (ref u)).
           apply sym in H7, H8. 
           exact (trn _ _ _ H8 H7).
         } 
         assert (H6 : (x [R] (y [R] u)) =_r (x [FR] (y [FR] u))).
         {
           assert (H6 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref y) (ref u)). 
           assert (H7 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref (y [R] u))).
           assert (H8 := bop_full_reduce_congruence S b r eqS b_cong r_cong _ _ _ _ (ref x) H6).
           exact (trn _ _ _ H7 H8).
         } 
         assert (H7 := trn _ _ _ H5 H4). 
         exact (trn _ _ _ H7 H6).
Qed.          


Lemma bop_full_reduce_commutative_iff_bop_reduce_commutative : 
  bop_commutative S (brel_reduce eqS r) (bop_full_reduce r b)
  <->
  bop_commutative S (brel_reduce eqS r) (bop_reduce r b).
Proof. assert (ref := brel_reduce_reflexive _ eqS r refS).
       assert (sym := brel_reduce_symmetric _ eqS r symS). 
       assert (trn := brel_reduce_transitive _ eqS r trnS).
       split; intros H1 x y. 
       - assert (H4 := H1 x y).
         assert (H5 : (x [R] y) =_r (x [FR] y)).
         {
           exact (bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref y)). 
         }
         assert (H7 := brel_reduce_transitive _ eqS r trnS _ _ _ H5 H4). 
         assert (H6 : (y [FR] x) =_r (y [R] x)).
         {
           assert (H8 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref y) (ref x)).
           exact (sym _ _ H8). 
         } 
         exact (brel_reduce_transitive _ eqS r trnS _ _ _ H7 H6).
       - assert (H4 := H1 x y).
         assert (H5 : (x [FR] y) =_r (x [R] y)).
         {
           assert (H6 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref y)).
           exact (sym _ _ H6). 
         } 
         assert (H6 : (y [R] x) =_r (y [FR] x)).
         {
           exact (bop_reduce_is_bop_full_reduce _ _ _ _ (ref y) (ref x)). 
         } 
         assert (H7 := trn _ _ _ H5 H4). 
         exact (trn _ _ _ H7 H6).
Qed.          


Lemma bop_full_reduce_idempotent_iff_bop_reduce_idempotent : 
  bop_idempotent S (brel_reduce eqS r) (bop_full_reduce r b)
  <->
  bop_idempotent S (brel_reduce eqS r) (bop_reduce r b).
Proof. assert (ref := brel_reduce_reflexive _ eqS r refS).
       assert (sym := brel_reduce_symmetric _ eqS r symS). 
       assert (trn := brel_reduce_transitive _ eqS r trnS).
       split; intros H1 x. 
       - assert (H4 := H1 x).
         assert (H5 : (x [R] x) =_r (x [FR] x)).
         {
           exact (bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref x)). 
         }
         exact (brel_reduce_transitive _ eqS r trnS _ _ _ H5 H4). 
       - assert (H4 := H1 x).
         assert (H5 : (x [FR] x) =_r (x [R] x)).
         {
           assert (H6 := bop_reduce_is_bop_full_reduce _ _ _ _ (ref x) (ref x)).
           exact (sym _ _ H6). 
         } 
         exact (trn _ _ _ H5 H4).
Qed.

Lemma bop_full_reduce_not_selective_implies_bop_reduce_not_selective : 
  bop_not_selective S (brel_reduce eqS r) (bop_full_reduce r b)
  ->
  bop_not_selective S (brel_reduce eqS r) (bop_reduce r b).
Proof. intros [[s t] [P Q]]. 
       exists (r s, r t). unfold bop_full_reduce in P, Q.
       unfold bop_reduce. split.
       - case_eq(brel_reduce eqS r (r (b (r s) (r t))) (r s)); intro H0; auto.
         unfold brel_reduce in P, H0.
         assert (H1 := r_idem s).
         rewrite (trnS _ _ _ H0 H1) in P.
         discriminate P.
       - case_eq(brel_reduce eqS r (r (b (r s) (r t))) (r t)); intro H0; auto.
         unfold brel_reduce in Q, H0.
         assert (H1 := r_idem t).
         rewrite (trnS _ _ _ H0 H1) in Q.
         discriminate Q.          
Defined. 
       
End Theory.


Section ACAS.

  Section Proofs.

      Variables (S : Type) 
           (b : binary_op S)
           (r : unary_op S)
           (eqS    : brel S)    
           (refS   : brel_reflexive S eqS) 
           (symS   : brel_symmetric S eqS) 
           (trnS   : brel_transitive S eqS)
           (eqS_cong : brel_congruence S eqS eqS)
           (b_cong : bop_congruence S eqS b) 
           (b_ass  : bop_associative S eqS b)
           (r_cong  : uop_congruence S eqS r) 
           (r_idem  : uop_idempotent S eqS r)
           (r_left : bop_left_uop_invariant S eqS (bop_reduce r b) r)
           (r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r).

      Definition is_reduction := r_is_b_reduction S b r eqS symS trnS r_left r_right.
             
      Lemma r_is_assoc : bop_associative S (brel_reduce eqS r) (bop_reduce r b).
      Proof. apply bop_full_reduce_associative_iff_bop_reduce_associative; auto. exact is_reduction. 
             destruct (reduced_bop_associative_iff _ b r eqS refS symS trnS b_cong r_cong r_idem) as [L _].
             apply L.
             apply reduced_bop_ass; auto. 
      Qed.

      Lemma r_is_comm (b_comm : bop_commutative S eqS b) :
        bop_commutative S (brel_reduce eqS r) (bop_reduce r b).
      Proof. apply bop_full_reduce_commutative_iff_bop_reduce_commutative; auto. exact is_reduction. 
             destruct (reduced_bop_commutative_iff _ b r eqS symS trnS b_cong r_cong r_idem) as [L _].
             apply L.
             apply reduced_bop_commutative; auto. 
      Qed.

      Lemma r_is_idem (idem : bop_idempotent S eqS b) :
        bop_idempotent S (brel_reduce eqS r) (bop_reduce r b).
      Proof. apply bop_full_reduce_idempotent_iff_bop_reduce_idempotent; auto. exact is_reduction. 
             apply (reduced_bop_idempotent_iff_left _ b r eqS trnS r_idem).
             apply reduced_bop_idempotent; auto. 
      Qed.


      Lemma r_is_not_sel
        (nsel : bop_not_selective S eqS b)
        (Q1 : let (s, _) := projT1 nsel in eqS (r s) s = true)
        (Q2 : let (_, s) := projT1 nsel in eqS (r s) s = true)      
        (P0 : let (s, t) := projT1 nsel in (eqS (r (b s t)) s = false) * (eqS (r (b s t)) t = false)): 
           bop_not_selective S (brel_reduce eqS r) (bop_reduce r b).
      Proof. apply bop_full_reduce_not_selective_implies_bop_reduce_not_selective; auto. 
             apply (reduced_bop_not_selective_iff_left _ b r eqS symS trnS b_cong r_cong r_idem).
             assert (H0 := reduced_bop_not_selective S b r eqS r_idem nsel).
             destruct nsel as [[s t] [P Q]].
             simpl in H0.
             apply H0; auto.
      Defined.

      
      Definition bop_reduce_sg_CI_proofs
        (b_comm : bop_commutative S eqS b)
        (b_idem : bop_idempotent S eqS b)
        (nsel : bop_not_selective S eqS b)
        (Q1 : let (s, _) := projT1 nsel in eqS (r s) s = true)
        (Q2 : let (_, s) := projT1 nsel in eqS (r s) s = true)      
        (P0 : let (s, t) := projT1 nsel in (eqS (r (b s t)) s = false) * (eqS (r (b s t)) t = false)): 
        sg_CI_proofs S (brel_reduce eqS r) (bop_reduce r b) := 
        {|
          A_sg_CI_associative   := r_is_assoc 
        ; A_sg_CI_congruence    := bop_reduce_congruence S b r eqS symS trnS b_cong r_cong is_reduction
        ; A_sg_CI_commutative   := r_is_comm b_comm 
        ; A_sg_CI_idempotent    := r_is_idem b_idem 
        ; A_sg_CI_not_selective := r_is_not_sel nsel Q1 Q2 P0
        |}.
    
  End Proofs.

  Section Combinators.


  Definition bop_reduce_A_sg_CI
      (S : Type )
      (sg : A_sg_CI S)
      (r : unary_op S) :=
      let eqvS := A_sg_CI_eqv _ sg in
      let eqS  := A_eqv_eq _ eqvS in
      let b := A_sg_CI_bop _ sg in
      let sgP := A_sg_CI_proofs _ sg in 
      let nsel := A_sg_CI_not_selective _ _ _ sgP in
      fun
      (* for building the eqv relation *)
      (f : S -> S)   
      (nt  : brel_not_trivial S (brel_reduce eqS r) f)
      (ex2 : brel_exactly_two_decidable S (brel_reduce eqS r))
      (fin : carrier_is_finite_decidable S (brel_reduce eqS r))
      (eqv_ast : cas_eqv_ast)
      (* for building the semigroup *)       
      (r_cong  : uop_congruence S eqS r) 
      (r_idem  : uop_idempotent S eqS r)
      (r_left  : bop_left_uop_invariant S eqS (bop_reduce r b) r)
      (r_right : bop_right_uop_invariant S eqS (bop_reduce r b) r)
      (Q1 : let (s, _) := projT1 nsel in eqS (r s) s = true)
      (Q2 : let (_, s) := projT1 nsel in eqS (r s) s = true)      
      (P0 : let (s, t) := projT1 nsel in (eqS (r (b s t)) s = false) * (eqS (r (b s t)) t = false))
      (no_id  : bop_not_exists_id S (A_eqv_eq S (A_eqv_reduce S eqvS r f nt ex2 fin eqv_ast)) (bop_reduce r b))
      (no_ann : bop_not_exists_ann S (A_eqv_eq S (A_eqv_reduce S eqvS r f nt ex2 fin eqv_ast)) (bop_reduce r b))
      (sg_ast : cas_sg_ast) => 
        let eqvP := A_eqv_proofs _ eqvS in
        let cngS := A_eqv_congruence _ _ eqvP in
        let refS := A_eqv_reflexive _ _ eqvP in
        let symS := A_eqv_symmetric _ _ eqvP in
        let trnS := A_eqv_transitive _ _ eqvP in
        let b_cong := A_sg_CI_congruence _ _ _ sgP in
        let b_assoc := A_sg_CI_associative _ _ _ sgP in
        let b_comm := A_sg_CI_commutative _ _ _ sgP in
        let b_idem := A_sg_CI_idempotent _ _ _ sgP in
        {|
          A_sg_CI_eqv            := A_eqv_reduce S eqvS r f nt ex2 fin eqv_ast 
        ; A_sg_CI_bop            := bop_reduce r b 
        ; A_sg_CI_not_exists_id  := no_id
        ; A_sg_CI_not_exists_ann := no_ann 
        ; A_sg_CI_proofs         := bop_reduce_sg_CI_proofs S b r eqS refS symS trnS b_cong b_assoc r_cong r_idem r_left r_right b_comm b_idem nsel Q1 Q2 P0
        ; A_sg_CI_ast            := sg_ast 
        |}.


  End Combinators.


End ACAS. 
