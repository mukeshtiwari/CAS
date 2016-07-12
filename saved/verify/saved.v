
(*
Theorem correct_sg_CI_product :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_product S T (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_product S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CI_product, A_sg_CI_product, A2C_sg_CI; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CI_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_product :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_product S T (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_product S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_C_product, A_sg_C_product, A2C_sg_C; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_C_certs_product. 
       reflexivity. 
Qed. 
*) 

(* do this cleanly *) 

(* 
Lemma correct_sg_CI_union_HACK  :
 ∀ (S : Type) (c : cas_constant) (r : brel S) (eqvS : eqv_proofs S r), 
   eqv_certs_add_constant (finite_set S) c
      (eqv_certs_brel_set S r (P2C_eqv S r eqvS))
   =                          
   P2C_eqv (with_constant (finite_set S))
      (brel_add_constant (finite_set S) (brel_set S r) c)
      (eqv_proofs_add_constant (finite_set S)
         (brel_set S r) c
         (eqv_proofs_brel_set S r eqvS)). 
Proof. intros S c r eqvS. destruct eqvS. 
       unfold eqv_certs_add_constant, eqv_certs_brel_set, 
              eqv_proofs_add_constant, eqv_proofs_brel_set, P2C_eqv. simpl. 
       reflexivity. 
Qed. 




*) 

(* bsg 

Theorem correct_bsg_min_plus : bsg_min_plus = A2C_bsg nat A_bsg_min_plus. 
Proof. compute. reflexivity. Qed. 
*) 



(*

Theorem correct_pa_union_intersect  :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         pa_union_intersect S c (A2C_eqv S eqvS) 
         = 
         A2C_pa (with_constant (finite_set S)) (A_pa_union_intersect S c eqvS). 
Proof. intros S c eqvS. destruct eqvS. 
       unfold pa_union_intersect, A_pa_union_intersect, A2C_eqv, A2C_pa. simpl. 
       rewrite correct_sg_CI_certs_union_with_ann. 
       rewrite correct_sg_CI_union_HACK. 
       rewrite correct_sg_CI_certs_intersect_with_id. 
       rewrite correct_csr_certs_union_intersect. 
(*       rewrite correct_sg_CI_union_HACK. *) 
       reflexivity. 
Qed. 

Theorem correct_pa_intersect_union  :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         pa_intersect_union S c (A2C_eqv S eqvS) 
         = 
         A2C_pa (with_constant (finite_set S)) (A_pa_intersect_union S c eqvS). 
Proof. intros S c eqvS. destruct eqvS. 
       unfold pa_intersect_union, A_pa_intersect_union, A2C_eqv, A2C_pa. simpl. 
       rewrite correct_sg_CI_certs_union_with_ann. 
       rewrite correct_sg_CI_union_HACK. 
       rewrite correct_sg_CI_certs_intersect_with_id. 
       rewrite correct_csr_certs_union_intersect. 
       reflexivity. 
Qed. 
*) 


(* order 
Theorem correct_po_llte_from_sg_CI :
      ∀ (S : Type) (sg_CIS : A_sg_CI S), 
         po_llte_from_sg_CI S (A2C_sg_CI S sg_CIS)
         = 
         A2C_po S (A_po_llte_from_sg_CI S sg_CIS). 
Proof. intros S sg_CIS. destruct sg_CIS. 
       unfold po_llte_from_sg_CI, A_po_llte_from_sg_CI, A2C_po; simpl. 
       rewrite <- correct_certs_llte_from_sg_CI. 
       reflexivity. 
Qed. 
*) 

(* 

Theorem correct_po_product :
      ∀ (S T : Type) (poS : A_po S) (poT : A_po T), 
         po_product S T (A2C_po S poS) (A2C_po T poT) 
         = 
         A2C_po (S * T) (A_po_product S T poS poT). 
Proof. intros S T poS poT. destruct poS; destruct poT. 
       unfold A_po_product. simpl. 
       unfold A2C_po. simpl. 
       unfold po_product. simpl. 
       rewrite correct_eqv_certs_product. 
       rewrite <- correct_po_certs_product. 
       reflexivity. 
Qed. 
*) 



(* 
Lemma correct_assert_not_is_left_csg_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (eS : eqv_proofs S rS)
         (eT : eqv_proofs T rT)
         (pS : sg_CS_proofs S rS bS) 
         (pT : sg_C_proofs T rT bT),  
         p2c_not_is_left (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_not_is_left S T rS rT bS bT 
                      (A_eqv_nontrivial S rS eS)
                      (brel_nontrivial_witness T rT
                        (A_eqv_nontrivial T rT eT))
                      (A_eqv_transitive S rS eS)
                      (A_eqv_symmetric S rS eS)
                      (A_sg_CS_commutative S rS bS pS)
                      (A_sg_CS_selective S rS bS pS))
         = 
         assert_not_is_left_llex S T rS bS
            (eqv_nontrivial S (P2C_eqv S rS eS))
            (eqv_nontrivial T (P2C_eqv T rT eT)). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct eS, eT, pS. 
       compute. 
       destruct A_eqv_nontrivial as [[s sP] [f fP]]; 
       destruct A_eqv_nontrivial0 as [[t tP] [g gP]];  
       destruct (fP s) as [fL fR]; destruct (gP t) as [tL gR];  
       destruct (A_sg_CS_selective s (f s)) as [H | H];  
       compute. 
          rewrite H. reflexivity. 
          case_eq(rS (bS s (f s)) s); intro J. 
          apply A_eqv_symmetric in J. 
          assert (fact := A_eqv_transitive _ _ _ J H). 
          rewrite fact in fL. 
          discriminate.           
          reflexivity. 
Defined. 

Lemma correct_assert_not_is_right_csg_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (eS : eqv_proofs S rS)
         (eT : eqv_proofs T rT)
         (pS : sg_CS_proofs S rS bS) 
         (pT : sg_C_proofs T rT bT),  
         p2c_not_is_right (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_not_is_right S T rS rT bS bT 
                      (A_eqv_nontrivial S rS eS)
                      (brel_nontrivial_witness T rT
                        (A_eqv_nontrivial T rT eT))
                      (A_eqv_transitive S rS eS)
                      (A_eqv_symmetric S rS eS)
                      (A_sg_CS_commutative S rS bS pS)
                      (A_sg_CS_selective S rS bS pS))
         = 
         assert_not_is_right_llex S T rS bS
            (eqv_nontrivial S (P2C_eqv S rS eS))
            (eqv_nontrivial T (P2C_eqv T rT eT)).
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct eS, eT, pS. 
       compute. 
       destruct A_eqv_nontrivial as [[s sP] [f fP]]; 
       destruct A_eqv_nontrivial0 as [[t tP] [g gP]];  
       destruct (fP s) as [fL fR]; destruct (gP t) as [tL gR];  
       destruct (A_sg_CS_selective s (f s)) as [H | H];  
       compute. 
          rewrite H. reflexivity. 
          case_eq(rS (bS s (f s)) s); intro J. 
          apply A_eqv_symmetric in J. 
          assert (fact := A_eqv_transitive _ _ _ J H). 
          rewrite fact in fL. 
          discriminate.           
          reflexivity. 
Defined. 


Lemma correct_assert_not_is_left_cisg_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (eS : eqv_proofs S rS)
         (eT : eqv_proofs T rT)
         (pS : sg_CS_proofs S rS bS) 
         (pT : sg_CI_proofs T rT bT),  
         p2c_not_is_left (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_not_is_left S T rS rT bS bT 
                      (A_eqv_nontrivial S rS eS)
                      (brel_nontrivial_witness T rT
                        (A_eqv_nontrivial T rT eT))
                      (A_eqv_transitive S rS eS)
                      (A_eqv_symmetric S rS eS)
                      (A_sg_CS_commutative S rS bS pS)
                      (A_sg_CS_selective S rS bS pS))
         = 
         assert_not_is_left_llex S T rS bS
            (eqv_nontrivial S (P2C_eqv S rS eS))
            (eqv_nontrivial T (P2C_eqv T rT eT)).
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct eS, eT, pS. 
       compute. 
       destruct A_eqv_nontrivial as [[s sP] [f fP]]; 
       destruct A_eqv_nontrivial0 as [[t tP] [g gP]];  
       destruct (fP s) as [fL fR]; destruct (gP t) as [tL gR];  
       destruct (A_sg_CS_selective s (f s)) as [H | H];  
       compute. 
          rewrite H. reflexivity. 
          case_eq(rS (bS s (f s)) s); intro J. 
          apply A_eqv_symmetric in J. 
          assert (fact := A_eqv_transitive _ _ _ J H). 
          rewrite fact in fL. 
          discriminate.           
          reflexivity. 
Defined. 

Lemma correct_assert_not_is_right_cisg_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (eS : eqv_proofs S rS)
         (eT : eqv_proofs T rT)
         (pS : sg_CS_proofs S rS bS) 
         (pT : sg_CI_proofs T rT bT),  
         p2c_not_is_right (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_not_is_right S T rS rT bS bT 
                      (A_eqv_nontrivial S rS eS)
                      (brel_nontrivial_witness T rT
                        (A_eqv_nontrivial T rT eT))
                      (A_eqv_transitive S rS eS)
                      (A_eqv_symmetric S rS eS)
                      (A_sg_CS_commutative S rS bS pS)
                      (A_sg_CS_selective S rS bS pS))
         = 
         assert_not_is_right_llex S T rS bS
            (eqv_nontrivial S (P2C_eqv S rS eS))
            (eqv_nontrivial T (P2C_eqv T rT eT)). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct eS, eT, pS. 
       compute. 
       destruct A_eqv_nontrivial as [[s sP] [f fP]]; 
       destruct A_eqv_nontrivial0 as [[t tP] [g gP]];  
       destruct (fP s) as [fL fR]; destruct (gP t) as [tL gR];  
       destruct (A_sg_CS_selective s (f s)) as [H | H];  
       compute. 
          rewrite H. reflexivity. 
          case_eq(rS (bS s (f s)) s); intro J. 
          apply A_eqv_symmetric in J. 
          assert (fact := A_eqv_transitive _ _ _ J H). 
          rewrite fact in fL. 
          discriminate.           
          reflexivity. 
Defined. 


Lemma correct_assert_not_is_left_cssg_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (eS : eqv_proofs S rS)
         (eT : eqv_proofs T rT)
         (pS : sg_CS_proofs S rS bS) 
         (pT : sg_CS_proofs T rT bT),  
         p2c_not_is_left (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_not_is_left S T rS rT bS bT 
                      (A_eqv_nontrivial S rS eS)
                      (brel_nontrivial_witness T rT
                        (A_eqv_nontrivial T rT eT))
                      (A_eqv_transitive S rS eS)
                      (A_eqv_symmetric S rS eS)
                      (A_sg_CS_commutative S rS bS pS)
                      (A_sg_CS_selective S rS bS pS))
         = 
         assert_not_is_left_llex S T rS bS
            (eqv_nontrivial S (P2C_eqv S rS eS))
            (eqv_nontrivial T (P2C_eqv T rT eT)). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct eS, eT, pS. 
       compute. 
       destruct A_eqv_nontrivial as [[s sP] [f fP]]; 
       destruct A_eqv_nontrivial0 as [[t tP] [g gP]];  
       destruct (fP s) as [fL fR]; destruct (gP t) as [tL gR];  
       destruct (A_sg_CS_selective s (f s)) as [H | H];  
       compute. 
          rewrite H. reflexivity. 
          case_eq(rS (bS s (f s)) s); intro J. 
          apply A_eqv_symmetric in J. 
          assert (fact := A_eqv_transitive _ _ _ J H). 
          rewrite fact in fL. 
          discriminate.           
          reflexivity. 
Defined. 

Lemma correct_assert_not_is_right_cssg_llex : 
      ∀ (S T : Type) 
         (rS : brel S) 
         (rT : brel T) 
         (bS : binary_op S) 
         (bT : binary_op T) 
         (eS : eqv_proofs S rS)
         (eT : eqv_proofs T rT)
         (pS : sg_CS_proofs S rS bS) 
         (pT : sg_CS_proofs T rT bT),  
         p2c_not_is_right (S * T) 
            (brel_product S T rS rT) 
            (bop_llex S T rS bS bT)
            (bop_llex_not_is_right S T rS rT bS bT 
                      (A_eqv_nontrivial S rS eS)
                      (brel_nontrivial_witness T rT
                        (A_eqv_nontrivial T rT eT))
                      (A_eqv_transitive S rS eS)
                      (A_eqv_symmetric S rS eS)
                      (A_sg_CS_commutative S rS bS pS)
                      (A_sg_CS_selective S rS bS pS))
         = 
         assert_not_is_right_llex S T rS bS
            (eqv_nontrivial S (P2C_eqv S rS eS))
            (eqv_nontrivial T (P2C_eqv T rT eT)). 
Proof. intros S T rS rT bS bT eS eT pS pT. 
       destruct eS, eT, pS. 
       compute. 
       destruct A_eqv_nontrivial as [[s sP] [f fP]]; 
       destruct A_eqv_nontrivial0 as [[t tP] [g gP]];  
       destruct (fP s) as [fL fR]; destruct (gP t) as [tL gR];  
       destruct (A_sg_CS_selective s (f s)) as [H | H];  
       compute. 
          rewrite H. reflexivity. 
          case_eq(rS (bS s (f s)) s); intro J. 
          apply A_eqv_symmetric in J. 
          assert (fact := A_eqv_transitive _ _ _ J H). 
          rewrite fact in fL. 
          discriminate.           
          reflexivity. 
Defined. 





*)

(* 

Lemma correct_csr_certs_union_intersect : 
  ∀ (S : Type) 
    (rS : brel S) 
    (c : cas_constant) 
    (eqvS : eqv_proofs S rS), 
    csr_certs_union_intersect S c (P2C_eqv S rS eqvS) 
    = 
    P2C_csr (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S rS) c)
            (bop_add_ann (finite_set S) (bop_union S rS) c)
            (bop_add_id (finite_set S) (bop_intersect S rS) c)
            (csr_proofs_union_intersect S rS c eqvS).
Proof. compute. reflexivity. Defined. 


Lemma correct_csr_certs_intersect_union : 
  ∀ (S : Type) 
    (rS : brel S) 
    (c : cas_constant) 
    (eqvS : eqv_proofs S rS), 
    csr_certs_intersect_union S c (P2C_eqv S rS eqvS) 
    = 
    P2C_csr (with_constant (finite_set S)) 
            (brel_add_constant (finite_set S) (brel_set S rS) c)
            (bop_add_id (finite_set S) (bop_intersect S rS) c)
            (bop_add_ann (finite_set S) (bop_union S rS) c)
            (csr_proofs_intersect_union S rS c eqvS).
Proof. compute. reflexivity. Defined. 
*) 


(* 







Lemma correct_certs_llte_from_sg_CI : 
      ∀ (S : Type) 
        (rS : brel S) 
        (bS : binary_op S) 
        (eS : eqv_proofs S rS) 
        (pS : sg_CI_proofs S rS bS),  
      po_certs_llte S (P2C_eqv S rS eS) (P2C_sg_CI S rS bS pS) 
      = 
      P2C_po S rS (brel_llte S rS bS) (po_proofs_llte S rS bS eS pS). 
Proof. intros S rS bS eS pS . destruct pS. destruct eS. 
       unfold po_certs_llte, po_proofs_llte, P2C_po, P2C_eqv, P2C_sg_CI; simpl.
       (* ugly *) 
       case(A_sg_CI_selective_d); simpl. 
          reflexivity. 
          intros [s1 [s2 [P1 P2]]]. simpl. reflexivity. 
Defined. 


Lemma correct_bsg_certs_min_plus : 
    bsg_certs_min_plus 
    = 
    P2C_bsg nat brel_eq_nat bop_min bop_plus bsg_proofs_min_plus. 
Proof. compute. reflexivity. Defined. 
*) 

