From Coq Require Import
     List
     Utf8
     FunctionalExtensionality BinNatDef 
     Lia
     Even.
From CAS Require Import
     coq.common.compute
     coq.eqv.properties
     coq.eqv.structures
     coq.eqv.theory
     coq.sg.properties
     coq.tr.properties     
     coq.bs.properties     
     coq.algorithm.matrix_definition
     coq.algorithm.matrix_algorithms
     coq.algorithm.matrix_addition
     coq.algorithm.matrix_multiplication          
     coq.algorithm.weighted_path.
Import ListNotations.

Section Matrix_proofs.

    (* where does this belong? *) 
    Fixpoint no_dup {A : Type} (eqA : brel A) (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t => negb (in_list eqA t h) && no_dup eqA t
    end.

  (* carrier set and the operators *)
  Variables
    (R : Type)
    (zero one : R) (* 0 and 1 *)
    (plus mul : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).

  Definition is_eqR a b          := eqR a b = true.
  Definition is_eqN a b          := brel_eq_nat a b = true.
  Definition not_eqN a b         := brel_eq_nat a b = false.

  Local Infix "=r="  := is_eqR (at level 70).
  Local Infix "=n="  := is_eqN (at level 70).
  Local Infix "<n>"  := not_eqN (at level 70).    
  Local Infix "=n?=" := brel_eq_nat (at level 70).
  Local Infix "=r?=" := eqR (at level 70).
  Local Infix "+" := plus.
  Local Infix "*" := mul.
  Local Infix "=M=" := (eq_functional_matrix_prop R eqR) (at level 70).  
  Local Infix "+M" := (matrix_add plus) (at level 70).
  Local Notation "a *[ n ] b" := (matrix_mul zero plus mul n a b) (at level 70).    
  Local Notation "a *[ n ]>  b" := (left_matrix_mul zero plus mul n a b) (at level 70).
  Local Notation "m ^( k , n )" := (left_matrix_exponentiation zero one plus mul n m k) (at level 70).
  Local Notation "0" := zero.
  Local Notation "1" := one.
  Local Notation "Pk[ m , n ]^ k"  := (matrix_of_k_length_paths R m n k) (at level 70).
  Local Notation "LW[ X ]" := (sum_fn zero plus (lw R R one mul) X) (at level 70). 
  Local Notation "LWP[ X ]" := (fun i j => LW[ X i j]) (at level 100).
  Local Notation "[I]" := (matrix_mul_identity 0 1) (at level 70). 
  

  Local Definition domain dim := list_enum dim.

  Variables 
    (congrP : bop_congruence R eqR plus)
    (congrM : bop_congruence R eqR mul)
    (congrR : brel_congruence R eqR eqR).
  Variables 
    (plus_commutative  : bop_commutative R eqR plus)
    (plus_associative : bop_associative R eqR plus)
    (mul_associative : bop_associative R eqR mul)
    (left_distributive_mul_over_plus : bop_left_distributive R eqR plus mul) 
    (right_distributive_mul_over_plus : bop_right_distributive R eqR plus mul)
    (plusID : bop_is_id R eqR plus 0)
    (mulID : bop_is_id R eqR mul 1)    
    (mulANN : bop_is_ann R eqR mul 0).

  (*
    Lemma matrix_exp_congruence : ∀ e,  Cong e → ∀ n k, Cong (e ^(k, n)).
    Proof. intros e cong n k. induction k; unfold matrix_exp.
           + apply (matrix_mul_identity_congruence R eqR refR symR trnR zero one plus mul congr congrM congrR).
           + simpl. fold (matrix_exp zero one plus mul n e k). 
             (* apply matrix_mul_preserves_congruence; auto. *) 
    Admitted. 
*) 


  (*  let A be an adjacency matrix. 
      A^(k) := A^0 + A^1 + A^2 + ... + A^k. 

      Inductively: 
      A^(0) = I 
      A^(k+1) = A^(k) + A^{k+1}. 

      We want to show that 

     A^(k)(i,j) = Sum_{p in paths(i, j), |p| <= k} w(p)       

     Standard proof: 

     base case.  Show A^(0)(i,j)  = I(i,j) = Sum_{p in paths(i, j), |p| <= 0} w(p)       
     The right-hand sum is over paths that have no length, so we must define 
     
     w(trivial path frim i to i) = 1 
     w(null path) = 0 

     induction:  A^(k+1) = A^(k) + A^{k+1} 
                         = Sum_{p in paths(i, j), |p| <= k} w(p)       
                           + 
                           Sum_{p in paths(i, j), |p| = k} w(p)       
                         = Sum_{p in paths(i, j), |p| <= k + 1} w(p)       
   *)

  (* feels like module instantiation *)

  (* move this *) 
  Lemma bop_congruence_imlies_ltr_congruence : ltr_congruence R R eqR eqR mul. 
  Proof. intros a b c d. apply congrM. Qed. 

  Lemma matrix_path_equation (m : functional_matrix R) (*cong : Cong m *) :
    ∀n k,  m^(k, n) =M= LWP[ Pk[ m , n ]^k ].
  Proof. intros n k.
         induction k.
         + simpl. apply identity_is_weight_of_matrix_of_paths_of_length_zero; auto. 
         + simpl.
           assert (A := fundamental_theorem_on_paths_of_length_k R R 0 1 plus mul eqR eqR congrR refR symR trnR congrR refR symR trnR congrP plus_associative plus_commutative plusID bop_congruence_imlies_ltr_congruence m n k).
           assert (B : (m *[ n ]> (m ^( k, n))) =M= (m *[ n ]> (LWP[ Pk[ m, n ]^ k])) ). admit.
           apply eq_functional_matrix_prop_symmetric in A; auto.
           assert (C := eq_functional_matrix_prop_transitive _ _ trnR _ _ _ B A). 
           assert (D : S k = (k + 1)%nat). (* Ugh! *)
              admit. 
           rewrite D. exact C. 
  Admitted. 
  
(* orignal proof. 

    Lemma matrix_path_equation (n k : nat) (m : functional_matrix R) (cong : Cong m) :
      ∀ m,  (m ^(k, n)) c d
             =r= 
             sum_all_rvalues R 0 plusR (get_all_rvalues nat R 1 mulR (construct_all_paths nat eqN R 1 finN m n c d)).

    
    Proof.
      intros ? ? ? ? Hm.
      unfold sum_all_rvalues, get_all_rvalues, construct_all_paths;
      rewrite map_map.
      revert n c d.
      induction n.
      + simpl; intros ? ?; unfold I.
        destruct (c =n?= d) eqn:Ht.
        - simpl. apply symR.
          assert (Htw: 1 * 1 + 0 =r= 1 + 0).
          apply congrP.
          apply one_left_identity_mul.
          apply refR.
          rewrite <- Htw; clear Htw.
          apply congrR.
          apply refR.
          apply symR. unfold matrix_mul_identity.  rewrite Ht. 
          apply zero_right_identity_plus.
        - simpl. unfold matrix_mul_identity.  rewrite Ht. apply refR.
      + simpl; intros ? ?.
        unfold matrix_mul, matrix_mul_gen.
        assert (Ht : 
        (sum_fn nat R 0 plusR 
          (λ y : nat, m c y * (m ^ n) y d) finN =r?=
        fold_right (λ b a : R, b + a) 0
          (map (λ x : list (nat * nat * R), measure_of_path nat R 1 mulR x)
             (append_node_in_paths nat R m c
                (flat_map (λ x : nat, all_paths_klength nat eqN R 1 finN m n x d) finN))))
        =
        (sum_fn_fold nat R 0 plusR  
          (λ y : nat, m c y * (m ^ n) y d) finN =r?=
        fold_right (λ b a : R, b + a) 0
          (map (λ x : list (nat * nat * R), measure_of_path nat R 1 mulR x)
             (append_node_in_paths nat R m c
                                   (flat_map (λ x : nat, all_paths_klength nat eqN R 1 finN m n x d) finN))))).
        apply congrR.
        apply sum_fn_sum_fn_fold.
        apply refR.
        rewrite Ht; clear Ht.
        unfold sum_fn_fold.
        apply symR.
        rewrite <-(fold_map_rel nat eqN refN symN trnN finN R 0 1 plusR mulR eqR refR 
          symR trnR zero_left_identity_plus plus_associative left_distributive_mul_over_plus
          zero_right_anhilator_mul congrP 
          congrM congrR finN m n c d).
        apply congrR.
        apply refR.
        apply fold_right_cong;
        try assumption.
        intros.
        apply congrP.
        apply congrM.
        apply refR.
        apply IHn.
        exact H.
        exact Hm.
    Qed.

*) 
End Matrix_proofs.




      

      
      
  
    
    




  



    
    


  
