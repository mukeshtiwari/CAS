Require Import CAS.code.basic_types. 
Require Import CAS.code.cas.
Require Import CAS.a_code.a_cas_records.   
Require Import CAS.a_code.a_cas.           
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.construct_correct. (* break up *)
Require Import CAS.verify.eqv_correct.  


Theorem correct_bs_and_or : bs_and_or = A2C_bs bool A_bs_and_or.
Proof. compute. reflexivity.  Qed. 

Theorem correct_bs_or_and : bs_or_and = A2C_bs bool A_bs_or_and.
Proof. compute. reflexivity.  Qed. 

Theorem correct_bs_max_min : bs_max_min = A2C_bs nat A_bs_max_min. 
Proof. compute. reflexivity.  Qed. 

Theorem correct_bs_min_max : bs_min_max = A2C_bs nat A_bs_min_max. 
Proof. compute. reflexivity.  Qed. 

Theorem correct_bs_min_plus : bs_min_plus = A2C_bs nat A_bs_min_plus. 
Proof. compute. reflexivity.  Qed. 

Theorem correct_bs_max_plus : bs_max_plus = A2C_bs nat A_bs_max_plus. 
Proof. compute. reflexivity.  Qed. 

(*
Theorem correct_bs_min_times : bs_min_times = A2C_bs nat A_bs_min_times. 
Proof. compute. reflexivity.  Qed. 

Theorem correct_bs_max_plus : bs_max_times = A2C_bs nat A_bs_max_times. 
Proof. compute. reflexivity.  Qed. 
   
*)    
   

Theorem correct_bs_add_one : ∀ (S : Type) (bsS: A_bs S) (c : cas_constant), 
   bs_add_one S (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_one S bsS c). 
Proof. intros S bsS c. 
       unfold bs_add_one, A_bs_add_one, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_ann. 
       rewrite correct_sg_certs_add_id. 
       rewrite correct_bs_certs_add_one. 
       reflexivity. 
Qed. 


Theorem correct_bs_add_zero: ∀ (S : Type) (bsS: A_bs S) (c : cas_constant), 
   bs_add_zero S (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_zero S bsS c). 
Proof. intros S bsS c. 
       unfold bs_add_zero, A_bs_add_zero, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_ann. 
       rewrite correct_sg_certs_add_id. 
       rewrite correct_bs_certs_add_zero. 
       reflexivity. 
Qed. 



Theorem correct_bs_product : ∀ (S T : Type) (bsS: A_bs S) (bsT : A_bs T), 
   bs_product S T (A2C_bs S bsS) (A2C_bs T bsT)
   =
   A2C_bs (S * T) (A_bs_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_product, A_bs_product, A2C_bs; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_certs_product. 
       rewrite correct_sg_certs_product. 
       rewrite correct_bs_certs_product. 
       reflexivity. 
Qed. 



Theorem correct_bs_C_llex_product : 
      ∀ (S T : Type) 
        (bsS : A_bs_CS S) 
        (bsT : A_bs_C T), 

   bs_C_llex_product S T (A2C_bs_CS S bsS) (A2C_bs_C T bsT)
   =
   A2C_bs_C (S * T) (A_bs_C_llex_product S T bsS bsT). 

Proof. intros S T sg_sgS sg_sgT. 
       unfold bs_C_llex_product, A_bs_C_llex_product, A2C_bs_CS, A2C_bs_C; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_C_certs_llex. 
       rewrite correct_sg_certs_product. 
       rewrite correct_bs_certs_llex_product. 
       reflexivity. 
Qed. 


Theorem correct_bs_CS_llex_product : 
      ∀ (S T : Type) 
        (bsS : A_bs_CS S) 
        (bsT : A_bs_CS T), 

   bs_CS_llex_product S T (A2C_bs_CS S bsS) (A2C_bs_CS T bsT)
   =
   A2C_bs_CS (S * T) (A_bs_CS_llex_product S T bsS bsT). 

Proof. intros S T sg_sgS sg_sgT. 
       unfold bs_CS_llex_product, A_bs_CS_llex_product, A2C_bs_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_CS_certs_llex. 
       rewrite correct_sg_certs_product. 
       rewrite correct_bs_certs_llex_product. 
       reflexivity. 
Qed. 




(* imports should not be needed here 

*) 
Require Import CAS.code.construct_certs.
Require Import CAS.code.certificates.
Require Import CAS.code.combined.
Require Import CAS.code.cert_records.
Require Import CAS.code.cas_records.
Require Import CAS.theory.brel_properties.
Require Import CAS.a_code.proof_records.
Require Import CAS.verify.sg_correct. 

Theorem correct_bs_union_intersect :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         bs_union_intersect S c (A2C_eqv S eqvS) 
         = 
         A2C_bs _ (A_bs_union_intersect S c eqvS). 
Proof. intros S c eqvS. 
       unfold bs_union_intersect, A_bs_union_intersect. 
       unfold A2C_bs; simpl. 
       unfold P2C_bs; simpl. 
       unfold bs_certs_union_intersect. 
       rewrite <- correct_eqv_add_constant.
       rewrite <- correct_eqv_set.

       (* UGLY *) 
       assert (K1 : get_witness S (
                 certify_nontrivial_witness S (eqv_nontrivial S (eqv_certs S (A2C_eqv S eqvS))))
                 = 
                 projT1 (brel_nontrivial_witness S (A_eqv_eq S eqvS)                    
                            (A_eqv_nontrivial S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)))
              ). compute. reflexivity. 
      assert (K2: get_negate S
                   (certify_nontrivial_negate S (eqv_nontrivial S (eqv_certs S (A2C_eqv S eqvS))))
                  = 
                  projT1
                    (brel_nontrivial_negate S (A_eqv_eq S eqvS)
                       (A_eqv_nontrivial S (A_eqv_eq S eqvS)
                          (A_eqv_proofs S eqvS)))
             ). compute. reflexivity. 
      rewrite <- K1, <- K2. 
      rewrite <- (correct_sg_certs_union S c eqvS).
      rewrite <- (correct_sg_certs_intersect S c eqvS).
      reflexivity.     
Qed. 




Theorem correct_bs_intersect_union :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         bs_intersect_union S c (A2C_eqv S eqvS) 
         = 
         A2C_bs _ (A_bs_intersect_union S c eqvS). 
Proof. intros S c eqvS. 
       unfold bs_intersect_union, A_bs_intersect_union. 
       unfold A2C_bs; simpl. 
       unfold P2C_bs; simpl. 
       unfold bs_certs_intersect_union. 
       rewrite <- correct_eqv_add_constant.
       rewrite <- correct_eqv_set.

       (* UGLY *) 
       assert (K1 : get_witness S (
                 certify_nontrivial_witness S (eqv_nontrivial S (eqv_certs S (A2C_eqv S eqvS))))
                 = 
                 projT1 (brel_nontrivial_witness S (A_eqv_eq S eqvS)                    
                            (A_eqv_nontrivial S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)))
              ). compute. reflexivity. 
      assert (K2: get_negate S
                   (certify_nontrivial_negate S (eqv_nontrivial S (eqv_certs S (A2C_eqv S eqvS))))
                  = 
                  projT1
                    (brel_nontrivial_negate S (A_eqv_eq S eqvS)
                       (A_eqv_nontrivial S (A_eqv_eq S eqvS)
                          (A_eqv_proofs S eqvS)))
             ). compute. reflexivity. 
      rewrite <- K1, <- K2. 
      rewrite <- (correct_sg_certs_union S c eqvS).
      rewrite <- (correct_sg_certs_intersect S c eqvS).
      reflexivity.     
Qed. 





