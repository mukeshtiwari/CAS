  (*  


      let A be an adjacency matrix. 
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


Section Computation.

  Fixpoint left_sum_of_matrix_powers_general
           {L S : Type} 
           (n : nat)
           (zeroS oneS : S)
           (plusS : binary_op S)
           (ltr : ltr_type L S) 
           (m : functional_matrix L)
           (k : nat) : functional_matrix S :=
    match k with
    | O => matrix_mul_identity zeroS oneS  
    | S k' => matrix_add plusS
                         (left_sum_of_matrix_powers_general n zeroS oneS plusS ltr m k')
                         (left_matrix_exponentiation zeroS oneS plusS ltr n m k)
    end.

  (*
  Fixpoint left_sum_of_matrix_powers (n : nat) (m : functional_matrix R) (k : nat) : functional_matrix R :=
    match k with
    | O => [I]
    | S k' => (left_sum_of_matrix_powers n m k') +M (m ^( k , n ))
    end.
   *)

  Definition left_sum_of_matrix_powers
             (S : Type)
             (n : nat)
             (zeroS oneS : S)
             (plusS mulS : binary_op S)
             (m : functional_matrix S)
             (k : nat) : functional_matrix S :=
    left_sum_of_matrix_powers_general n zeroS oneS plusS mulS m k.

  Definition left_sum_of_path_powers (R : Type) (n : nat) (m : functional_matrix R)  :=
       left_sum_of_matrix_powers_general n (zeroP R) (oneP R) (plusP R) (ltr_extend_paths R) (path_adjacency_arcs R m). 
                                      
End Computation.   

Section Matrix_proofs.


  Variables
    (R : Type)
    (zero one : R) 
    (plus mul : binary_op R)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (congrP : bop_congruence R eqR plus)
    (congrM : bop_congruence R eqR mul)
    (congrR : brel_congruence R eqR eqR).


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
  Local Notation "0" := zero.
  Local Notation "1" := one.  
  Local Infix "=M="               := (eq_functional_matrix_prop R eqR) (at level 70).  
  Local Infix "+M"                := (matrix_add plus) (at level 70).
  Local Infix "=PM="              := (eq_functional_matrix_prop (weighted_path_set R) (eq_weighted_path_set R eqR)) (at level 70).    
  Local Infix "+PM"               := (matrix_add (plusP R)) (at level 70).  
  Local Notation "a *[ n ] b"     := (matrix_mul zero plus mul n a b) (at level 70).    
  Local Notation "a *[ n ]>  b"   := (left_matrix_mul zero plus mul n a b) (at level 70).

  Local Notation "Mk[ m , k , n ]"   := (left_matrix_exponentiation zero one plus mul n m k) (at level 70).
  Local Notation "Mk{ m , k , n }"   := (left_sum_of_matrix_powers R n zero one plus mul m k) (at level 70).  
  Local Notation "Mk<| m , k , n |>" := (left_matrix_iteration zero one plus mul n m k) (at level 70).


  Local Notation "Pk[ m , k , n ]"   := (matrix_of_k_length_paths R m n k) (at level 70).  
  Local Notation "Pk{ m , k , n }"   := (left_sum_of_path_powers _ n m k) (at level 70).
  Local Notation "Pk<| m , k , n |>" := (left_matrix_iteration (zeroP R) (oneP R) (plusP R) (ltr_extend_paths R) n m k) (at level 70).


  Local Notation "LW[ X ]"         := (sum_fn zero plus (lw R R one mul) X) (at level 70). 
  Local Notation "LWP[ X ]"        := (fun i j => LW[ X i j]) (at level 100).
  Local Notation "[I]"             := (matrix_mul_identity 0 1) (at level 70). 
  
  Local Definition domain dim := list_enum dim.
  Local Definition Cong := functional_matrix_congruence R eqR.

(*  
  Variables 
    (plus_commutative  : bop_commutative R eqR plus)
    (plus_associative : bop_associative R eqR plus)
    (mul_associative : bop_associative R eqR mul)
    (left_distributive_mul_over_plus : bop_left_distributive R eqR plus mul) 
    (right_distributive_mul_over_plus : bop_right_distributive R eqR plus mul)
    (plusID : bop_is_id R eqR plus 0)
    (mulID : bop_is_id R eqR mul 1)    
    (mulANN : bop_is_ann R eqR mul 0).
*) 
    Lemma matrix_exp_congruence : ∀ m,  Cong m → ∀ n k, Cong (Mk[ m, k, n]).
    Proof. intros m cong n k. 
           induction k; simpl. 
           + admit. (*apply (matrix_mul_identity_congruence R eqR refR symR trnR zero one plus mul congrP congrM congrR).*)
           + intros i j i' j' A B. simpl.
             unfold left_matrix_mul. (* No! should preserve this abstraction and use higher-level congruence....Fix me... *) 
             apply sum_fn_congruence; auto.
             intros i0 j0 C. 
             unfold left_row_i_dot_col_j.
             apply congrM.
             apply cong; auto.
             apply IHk; auto. 
Admitted. 

  (* move this *) 
  Lemma bop_congruence_implies_ltr_congruence : ltr_congruence R R eqR eqR mul. 
  Proof. intros a b c d. apply congrM. Qed. 

  Lemma matrix_path_equation
        (plus_commutative  : bop_commutative R eqR plus)
        (plus_associative : bop_associative R eqR plus)
        (plusID : bop_is_id R eqR plus 0)
        (m : functional_matrix R) (cong : Cong m) :
    ∀n k,  Mk[m, k, n] =M= LWP[ Pk[ m , k, n ] ].
  Proof. intros n k. induction k; simpl. 
         + apply identity_is_weight_of_matrix_of_paths_of_length_zero; auto.
         + (* ugly : *) 
           assert (A := fundamental_theorem_on_paths_of_length_k R R 0 1 plus mul eqR eqR congrR refR symR trnR congrR refR symR trnR congrP bop_congruence_implies_ltr_congruence plus_associative plus_commutative plusID m cong n k).
           assert (B : (m *[ n ]> (Mk[m, k, n])) =M= (m *[ n ]> (LWP[ Pk[ m, k, n ] ])) ).
              apply (left_matrix_mul_congruence _ _ eqR eqR); auto.
              apply bop_congruence_implies_ltr_congruence. 
              apply matrix_exp_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto. 
           apply eq_functional_matrix_prop_symmetric in A; auto.
           assert (C := eq_functional_matrix_prop_transitive _ _ trnR _ _ _ B A). 
           assert (D : S k = (k + 1)%nat). (* Ugh!!! *) 
              assert (E := plus_n_Sm k 0).
              rewrite PeanoNat.Nat.add_0_r in E.
              exact E. 
           rewrite D. exact C. 
  Qed. 
  
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



  Lemma unfold_left_sum_of_matrix_powers (n : nat) (m : functional_matrix R) :
    ∀ k, Mk{ m, S k, n} =M= Mk{ m, k, n} +M Mk[m, S k, n].
  Proof. intro k. unfold left_sum_of_matrix_powers.
         unfold left_sum_of_matrix_powers_general. simpl.
         apply eq_functional_matrix_prop_reflexive; auto.
  Qed.

  Lemma unfold_left_sum_of_path_powers (n : nat) (m : functional_matrix R) :
    ∀ k, Pk{ m, S k, n} =PM= (Pk{ m, k, n} +PM Pk[m, S k, n]).
  Proof. intro k. unfold left_sum_of_path_powers.
         unfold left_sum_of_matrix_powers_general. simpl.
         apply eq_functional_matrix_prop_reflexive; auto.
         apply eq_weighted_path_set_reflexive; auto. 
  Qed.

  
  Lemma claim1 (n : nat) (m : functional_matrix R) :
    ∀ k, (Mk<| m, k , n |> +M Mk[ m, k , n ]) =M= (m *[ n ]> Mk<| m, k , n |> +M [I]). 
  Proof. induction k.
         + simpl. 
           (* (([I]) +M ([I])) =M= ((m *[ n ]> ([I])) +M ([I])) *)
           admit.
         + admit. 
  Admitted.
  
  Lemma claim2 (n : nat) (m : functional_matrix R) :
    ∀ k, (Mk{ m, k , n } +M Mk[ m, k , n ]) =M= (m *[ n ]> Mk{ m, k, n } +M [I]). 
  Proof. induction k.
         + simpl.
           (* ((m ^{ 0, n}) +M ([I])) =M= ((m *[ n ]> (m ^{ 0, n})) +M ([I])) *)
           admit.
         + admit.
  Admitted.            
  
  Lemma left_sum_of_matrix_powers_is_equal_to_left_matrix_iteration
        (n : nat) (m : functional_matrix R) :
           ∀ k, Mk{ m, k , n } =M= Mk<| m, k , n |>. 
  Proof. induction k.     
         + simpl. apply eq_functional_matrix_prop_reflexive; auto.
         + (* Show : 
              IHk : (m ^{ k, n}) =M= (m ^<| k, n |>)
              ============================
              (m ^{ S k, n}) =M= (m ^<| S k, n |>)



              Proof: 
              ((m ^{ k, n}) +M (m *[ n ]> (m ^( k, n)))) 
              =M= {IHk, congruences} 
              ((m ^<| k, n |>) +M (m *[ n ]> (m ^( k, n)))) 

              =M= ((m *[ n ]> (m ^<| k, n |>)) +M ([I]))
            *)

           (* Need unfold lemma for (m ^{ S k, n}) *)
           
           assert (A : (Mk{m, k, n} +M Mk[m, S k, n])
                       =M=
                       (Mk<| m, k, n |> +M Mk[m, S k, n])). admit.
           assert (B := claim1 n m (S k)).
           (* assert (C := eq_functional_matrix_prop_transitive _ eqR trnR _ _ _ A B). *) 
           
  Admitted.

  Lemma claim3 (plusIdempotent : bop_idempotent R eqR plus)
        (n : nat) (m : functional_matrix R) :
        ∀ k, Mk{ m, k, n} +M (m *[n] Mk{ m, k, n})
              =M=
              Mk{ m, k, n} +M Mk[m, S k, n].
  Proof. induction k. 
         + unfold left_sum_of_matrix_powers, left_matrix_exponentiation; simpl. 
           admit. (* need I is +M ann *)
         + (* IHk : Mk{ m, k, n} +M m *[ n] Mk{ m, k, n}
                    =M=
                    Mk{ m, k, n} +M Mk[ m, S k, n]
               ============================
               Mk{ m, S k, n} +M m *[ n] Mk{ m, S k, n}
               =M=
               Mk{ m, S k, n}) +M Mk[ m, S (S k), n]

              Proof: 
              Mk{ m, S k, n} +M m *[ n] Mk{ m, S k, n}
              =M={unfold} 
              Mk{ m, S k, n} +M m *[ n] (Mk{ m, k, n} +M Mk[m, S k, n]) 
              =M={left_distrib}  
              Mk{ m, S k, n} +M m *[ n] Mk{ m, k, n} +M m *[ n] Mk[m, S k, n]  
              =M= {unfold} 
              Mk{ m, S k, n} +M m *[ n] Mk{ m, k, n} +M Mk[m, S (S k), n]  
              =M={unfold} 
              Mk{m, k, n} +M Mk[m, S k, n] +M m *[ n] Mk{ m, k, n} +M Mk[m, S (S k), n]  
              =M={assoc, comm} 
              Mk{m, k, n} +M m *[ n] Mk{ m, k, n} +M Mk[m, S k, n] +M Mk[m, S (S k), n]  
              =M={IHk} 
              Mk{ m, k, n} +M Mk[ m, S k, n] +M Mk[m, S k, n] +M Mk[m, S (S k), n]  
              =M={matrix_add_idempotent} 
              Mk{ m, k, n} +M Mk[ m, S k, n] +M Mk[m, S (S k), n]  
              =M= 
              Mk{ m, S k, n}) +M Mk[ m, S (S k), n]
           *) 
Admitted. 

  Lemma powers (n : nat) (m : functional_matrix R) :
    ∀ k, Mk[ m +M [I], k , n ] =M= Mk{ m, k, n}.
  Proof. induction k.
         + simpl. apply eq_functional_matrix_prop_reflexive; auto. 
         + (* IHk : Mk[ m +M [I], k, n] =M= Mk{ m, k, n}
              ============================
              Mk[ m +M [I], S k, n] =M= Mk{ m, S k, n}
    
              Proof: 
              Mk[ m +M ([I]), S k, n]
              =M={unfold} 
              (m +M [I]) *M Mk[ m +M ([I]), k, n]
              =M={IHk, congruence} 
              (m +M [I]) *M Mk{ m, k, n} 
              =M= {right_distrib} 
              (m *M Mk{ m, k, n}) +M ([I] *M Mk{ m, k, n}) 
              =M={identity} 
              (m *M Mk{ m, k, n}) +M Mk{ m, k, n}
              =M={commutative} 
              Mk{ m, k, n} +M (m *M Mk{ m, k, n})
              =M={claim3} 
              Mk{ m, k, n} +M Mk[m, S k, n].
              =M={unfold} 
              Mk{ m, S k, n}
            *)
           assert (A : Mk[ m +M [I], S k, n]
                       =M=
                       ((m +M [I]) *[n] Mk[ m +M [I], k, n])).
              admit.
           assert (B : ((m +M [I]) *[n] Mk[ m +M [I], k, n])
                       =M=
                       ((m +M [I]) *[n] Mk{ m, k, n})).
                  admit. 
                  (*apply matrix_mul_congruence. *)
           
  Admitted.

  Lemma  base_case (plusID : bop_is_id R eqR plus 0) (n : nat) (m : functional_matrix R) :
    Mk{ m, 0, n} =M= LWP[ Pk{ m, 0, n}]. 
  Proof. unfold left_sum_of_path_powers, left_sum_of_matrix_powers.
         apply eq_functional_matrix_prop_symmetric; auto.
         apply LWP_of_path_identity_is_identity; auto. 
  Qed.          
  
  Definition trnM := eq_functional_matrix_prop_transitive R eqR trnR.
  
  Lemma left_sum_of_matrix_powers_to_k_is_equal_to_weight_of_paths_of_length_at_most_k
        (plus_associative : bop_associative R eqR plus)
        (plus_commutative  : bop_commutative R eqR plus)
        (plusID : bop_is_id R eqR plus 0)
        (n : nat) (m : functional_matrix R) (cong : Cong m):
           ∀ k, Mk{ m, k , n } =M= LWP[ Pk{ m , k , n } ].
  Proof. induction k; simpl.
         + (* Mk{ m, 0, n} =M= LWP[ Pk{ m, 0, n}] *) 
           apply base_case; auto. 
         + (*
            IHk : (Mk{ m, k, n}) =M= (LWP[ Pk{ m, k, n}])
            ============================
            (Mk{ m, S k, n}) =M= (LWP[ Pk{ m, S k, n}])

            Proof: 
            Mk{ m, S k, n}
            =M= {unfold_left_sum_of_matrix_powers} 
            Mk{ m, k, n} +M Mk[ m, S k, n]
            =M= {IHk, congruence} 
            LWP[ Pk{ m, k, n} ] +M Mk[ m, S k, n]
            =M={matrix_path_equation, congruence} 
            LWP[ Pk{ m, k, n} ] +M LWP[ Pk[ m, S k, n] ] 
            =M={LWP_distributes_over_matrix_add} 
            LWP[ Pk{ m, k, n} +PM Pk[ m, S k, n] ] 
            =M= {unfold_left_sum_of_path_powers, congruence}
            LWP[ Pk{ m, S k, n}]
           *)
           assert (A := unfold_left_sum_of_matrix_powers n m k).
           assert (B : (Mk{ m, k, n} +M Mk[ m, S k, n])
                       =M= 
                       (LWP[ Pk{ m, k, n}] +M Mk[ m, S k, n])). 
              apply matrix_add_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto. 
           assert (C : (LWP[ Pk{ m, k, n}] +M Mk[ m, S k, n])
                       =M=
                       (LWP[ Pk{ m, k, n} ] +M LWP[ Pk[ m, S k, n] ])).
              apply matrix_add_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto.
              apply matrix_path_equation; auto.
           assert (D : (LWP[ Pk{ m, k, n} ] +M LWP[ Pk[ m, S k, n] ])
                       =M=                 
                       (LWP[ Pk{ m, k, n} +PM Pk[ m, S k, n] ])).
             apply eq_functional_matrix_prop_symmetric; auto.
             apply LWP_distributes_over_matrix_add; auto.  
           assert (E := unfold_left_sum_of_path_powers n m k).
           assert (F : (LWP[ Pk{ m, k, n} +PM Pk[ m, S k, n] ])
                       =M=
                       LWP[ Pk{ m, S k, n} ]).
              apply (LWP_congruence R R 0 1 plus mul eqR eqR); auto.
              apply bop_congruence_implies_ltr_congruence; auto. 
           exact (trnM _ _ _ (trnM _ _ _ (trnM _ _ _ (trnM _ _ _ A B) C) D) F).
  Qed. 
  
End Matrix_proofs.




      

      
      
  
    
    




  



    
    


  
