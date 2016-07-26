Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.cast.
Require Import CAS.code.construct_certs.
Require Import CAS.code.cas_records.
Require Import CAS.code.cas.
Require Import CAS.a_code.a_cast.
Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.construct_proofs.  (* ~~ construct_certs *)
Require Import CAS.a_code.a_cas_records.     (* ~~ cas_records  *) 
Require Import CAS.a_code.a_cas.             (* ~~ cas          *) 
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.construct_correct. (* ~~ construct_certs <-> construct_proofs *)


(* eqv *) 

Theorem correct_eqv_eq_bool : eqv_eq_bool = A2C_eqv bool (A_eqv_eq_bool). 
Proof. compute. reflexivity. Qed. 

Theorem correct_eqv_eq_nat : eqv_eq_nat = A2C_eqv nat (A_eqv_eq_nat). 
Proof. compute. reflexivity. Qed. 

Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
         eqv_add_constant S (A2C_eqv S E) c = A2C_eqv (with_constant S) (A_eqv_add_constant S E c). 
Proof. intros S c E. destruct E. destruct A_eqv_proofs. 
       destruct A_eqv_nontrivial. destruct brel_nontrivial_witness. 
       compute. reflexivity. 
Qed. 

Theorem correct_eqv_list : ∀ (S : Type) (E : A_eqv S),  
         eqv_list S (A2C_eqv S E) = A2C_eqv (list S) (A_eqv_list S E). 
Proof. intros S E. 
       destruct E. unfold eqv_list, A_eqv_list, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_brel_list. reflexivity. 
Qed. 

Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S),  
         eqv_set S (A2C_eqv S E) = A2C_eqv (finite_set S) (A_eqv_set S E). 
Proof. intros S E. 
       destruct E. unfold eqv_set, A_eqv_set, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_brel_set. reflexivity. 
Qed. 


Theorem correct_eqv_product :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_product S T (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S * T) (A_eqv_product S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. 
       unfold eqv_product, A_eqv_product, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_product. reflexivity. 
Qed. 

Theorem correct_eqv_sum :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_sum S T (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S + T) (A_eqv_sum S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. 
       unfold eqv_sum, A_eqv_sum, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_sum. reflexivity. 
Qed. 


(* semigroups *) 

(* basics *) 


Theorem correct_sg_times : sg_times = A2C_sg nat (A_sg_times). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_plus : sg_plus = A2C_sg nat (A_sg_plus). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_min : sg_min = A2C_sg nat (A_sg_min). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_max : sg_max = A2C_sg nat (A_sg_max). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_and : sg_and = A2C_sg bool (A_sg_and). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_or : sg_or = A2C_sg bool (A_sg_or). 
Proof. compute. reflexivity. Qed. 





Theorem correct_sg_C_times : sg_C_times = A2C_sg_C nat (A_sg_C_times). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CK_plus : sg_CK_plus = A2C_sg_CK nat (A_sg_CK_plus). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_and : sg_CS_and = A2C_sg_CS bool (A_sg_CS_and). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_or : sg_CS_or = A2C_sg_CS bool (A_sg_CS_or). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_min : sg_CS_min = A2C_sg_CS nat (A_sg_CS_min). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_max : sg_CS_max = A2C_sg_CS nat (A_sg_CS_max). 
Proof. compute. reflexivity. Qed. 


Theorem correct_sg_concat :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_concat S (A2C_eqv S eS) 
         = 
         A2C_sg (list S) (A_sg_concat S eS). 
Proof. intros S eS. 
       unfold sg_concat, A_sg_concat, A2C_sg. simpl. 
       rewrite correct_eqv_list. 
       rewrite correct_sg_certs_concat. 
       reflexivity. 
Qed. 

Theorem correct_sg_left :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_left S (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_left S eS). 
Proof. intros S eS. 
       unfold sg_left, A_sg_left, A2C_sg; simpl. 
       rewrite correct_sg_certs_left.  
       reflexivity. 
Qed. 

Theorem correct_sg_right :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_right S (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_right S eS). 
Proof. intros S eS. 
       unfold sg_right, A_sg_right, A2C_sg; simpl. 
       rewrite correct_sg_certs_right. 
       reflexivity. 
Qed. 


(* semigroup add_id *) 

Theorem correct_sg_add_id  :
      ∀ (S : Type) (c : cas_constant) (sgS : A_sg S), 
         sg_add_id S c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_id S c sgS). 
Proof. intros S c sgS. 
       unfold sg_add_id, A_sg_add_id, A2C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_id. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_add_id  :
      ∀ (S : Type) (c : cas_constant) (sg_CS : A_sg_C S), 
         sg_C_add_id S c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_id S c sg_CS). 
Proof. intros S c sg_CS. destruct sg_CS. 
       unfold sg_C_add_id, A_sg_C_add_id, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_C_certs_add_id. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_id  :
      ∀ (S : Type) (c : cas_constant) (sg_CIS : A_sg_CI S), 
         sg_CI_add_id S c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_id S c sg_CIS). 
Proof. intros S c sg_CIS. destruct sg_CIS. 
       unfold sg_CI_add_id, A_sg_CI_add_id, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CI_certs_add_id. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_id  :
      ∀ (S : Type) (c : cas_constant) (sg_CSS : A_sg_CS S), 
         sg_CS_add_id S c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_id S c sg_CSS). 
Proof. intros S c sg_CSS. destruct sg_CSS. 
       unfold sg_CS_add_id, A_sg_CS_add_id, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CS_certs_add_id. 
       reflexivity. 
Qed. 


(* semigroup add_ann *) 

Theorem correct_sg_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sgS : A_sg S), 
         sg_add_ann S c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_ann S c sgS). 
Proof. intros S c sgS. 
       unfold sg_add_ann, A_sg_add_ann, A2C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_ann. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sg_CS : A_sg_C S), 
         sg_C_add_ann S c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_ann S c sg_CS). 
Proof. intros S c sg_CS. destruct sg_CS. 
       unfold sg_C_add_ann, A_sg_C_add_ann, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_C_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sg_CIS : A_sg_CI S), 
         sg_CI_add_ann S c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_ann S c sg_CIS). 
Proof. intros S c sg_CIS. destruct sg_CIS. 
       unfold sg_CI_add_ann, A_sg_CI_add_ann, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CI_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sg_CSS : A_sg_CS S), 
         sg_CS_add_ann S c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_ann S c sg_CSS). 
Proof. intros S c sg_CSS. destruct sg_CSS. 
       unfold sg_CS_add_ann, A_sg_CS_add_ann, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CS_certs_add_ann. 
       reflexivity. 
Qed. 



(* semigroup products *) 

Theorem correct_sg_product :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_product S T (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_product, A_sg_product, A2C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_certs_product. 
       reflexivity. 
Qed. 


(*

Theorem correct_sg_product_new :
      ∀ (S T : Type) (sgS : A_sg_new S) (sgT : A_sg_new T), 
         sg_product_new S T (A2C_sg_new S sgS) (A2C_sg_new T sgT) 
         = 
         A2C_sg_new (S * T) (A_sg_product_new S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_product_new, A_sg_product_new, A2C_sg_new; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_certs_product_new. 
       reflexivity. 
Qed. 
*) 

Theorem correct_sg_CK_product :
      ∀ (S T : Type) (sgS : A_sg_CK S) (sgT : A_sg_CK T), 
         sg_CK_product S T (A2C_sg_CK S sgS) (A2C_sg_CK T sgT) 
         = 
         A2C_sg_CK (S * T) (A_sg_CK_product S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CK_product, A_sg_CK_product, A2C_sg_CK; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CK_certs_product. 
       reflexivity. 
Qed. 



(* semigroup sums *) 

Theorem correct_sg_left_sum :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_left_sum S T (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S + T) (A_sg_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_left_sum, A_sg_left_sum, A2C_sg. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_right_sum :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_right_sum S T (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S + T) (A_sg_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_right_sum, A_sg_right_sum, A2C_sg; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_certs_right_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_left_sum :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_left_sum S T (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_left_sum, A_sg_C_left_sum, A2C_sg_C. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_C_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_right_sum :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_right_sum S T (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_right_sum, A_sg_C_right_sum, A2C_sg_C; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_C_certs_right_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CS_left_sum :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_left_sum S T (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_left_sum, A_sg_CS_left_sum, A2C_sg_CS. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_CS_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CS_right_sum :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_right_sum S T (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_right_sum, A_sg_CS_right_sum, A2C_sg_CS; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_CS_certs_right_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_left_sum :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_left_sum S T (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_left_sum, A_sg_CI_left_sum, A2C_sg_CI. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_CI_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CI_right_sum :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_right_sum S T (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_right_sum, A_sg_CI_right_sum, A2C_sg_CI; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_CI_certs_right_sum. 
       reflexivity. 
Qed. 


(* semigroup lexicographic *) 

Theorem correct_sg_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg T), 
         sg_llex S T (A2C_sg_CS S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_llex, A_sg_llex, A2C_sg, A2C_sg_CS; simpl. 
       rewrite correct_sg_certs_llex. 
       rewrite correct_eqv_product. 
       reflexivity. 
Qed. 




Theorem correct_sg_C_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_C T), 
         sg_C_llex S T (A2C_sg_CS S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_C_llex, A_sg_C_llex, A2C_sg_C, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_C_certs_llex. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_llex S T (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S * T) (A_sg_CS_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CS_llex, A_sg_CS_llex, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_CS_certs_llex. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CI T), 
         sg_CI_llex S T (A2C_sg_CS S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CI_llex, A_sg_CI_llex, A2C_sg_CI, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_CI_certs_llex. 
       reflexivity. 
Qed. 

(* SETS *) 

Lemma  correct_sg_certs_union : 
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
       sg_certs_union S (get_witness _ (certify_nontrivial_witness _ 
                           (eqv_nontrivial _ (eqv_certs _ (A2C_eqv S eqvS)))))   (* UGLY *) 
                        (get_negate _ (certify_nontrivial_negate _ 
                           (eqv_nontrivial _ (eqv_certs _ (A2C_eqv S eqvS)))))   (* UGLY *) 
                         c
          (eqv_add_constant (finite_set S) (eqv_set S (A2C_eqv S eqvS)) c)
          (bop_add_ann (finite_set S) (bop_union S (eqv_eq S (A2C_eqv S eqvS))) c)
                    
       =
      P2C_sg (with_constant (finite_set S))
             (brel_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c)
             (bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c)
             (sg_proofs_union S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)). 
Proof. intros S c eqvS. 
       destruct eqvS. destruct A_eqv_proofs. destruct A_eqv_nontrivial. 
       destruct  brel_nontrivial_witness. destruct brel_nontrivial_negate. 
       compute. 
       reflexivity.        
Qed. 


Theorem correct_sg_union  :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         sg_union S c (A2C_eqv S eqvS) 
         = 
         A2C_sg (with_constant (finite_set S)) (A_sg_union S c eqvS). 
Proof. intros S c eqvS. 
       assert (H := correct_sg_certs_union S c eqvS). 
       unfold sg_union, A_sg_union, A2C_sg ; simpl.
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
      rewrite <- K1, <- K2. rewrite <- H. reflexivity. 
Qed. 



Lemma  correct_sg_certs_intersect : 
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
       sg_certs_intersect S (get_witness _ (certify_nontrivial_witness _ 
                           (eqv_nontrivial _ (eqv_certs _ (A2C_eqv S eqvS)))))   (* UGLY *) 
                        (get_negate _ (certify_nontrivial_negate _ 
                           (eqv_nontrivial _ (eqv_certs _ (A2C_eqv S eqvS)))))   (* UGLY *) 
                         c
          (eqv_add_constant (finite_set S) (eqv_set S (A2C_eqv S eqvS)) c)
          (bop_add_id (finite_set S) (bop_intersect S (eqv_eq S (A2C_eqv S eqvS))) c)
                    
       =
      P2C_sg (with_constant (finite_set S))
             (brel_add_constant (finite_set S) (brel_set S (A_eqv_eq S eqvS)) c)
             (bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c)
             (sg_proofs_intersect S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)). 
Proof. intros S c eqvS. 
       destruct eqvS. destruct A_eqv_proofs. destruct A_eqv_nontrivial. 
       destruct  brel_nontrivial_witness. destruct brel_nontrivial_negate. 

       unfold P2C_sg; simpl. 
       unfold bop.intersect.bop_intersect_not_selective. 
       unfold bop.add_id.bop_add_id_not_selective; simpl. 
       unfold bop.intersect.bop_intersect_not_selective_raw; simpl. 
       compute. 
       reflexivity.        
Qed. 


Theorem correct_sg_intersect  :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         sg_intersect S c (A2C_eqv S eqvS) 
         = 
         A2C_sg (with_constant (finite_set S)) (A_sg_intersect S c eqvS). 
Proof. intros S c eqvS. 
       assert (H := correct_sg_certs_intersect S c eqvS). 
       unfold sg_intersect, A_sg_intersect, A2C_sg ; simpl.
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
      rewrite <- K1, <- K2. rewrite <- H. reflexivity. 
Qed. 


(* ************************* bs ************************* *) 


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



(* 


Theorem correct_sg_C_sg_llex : ∀ (S T : Type) (sg_sgS: A_sg_CS_sg S) (sg_sgT : A_sg_C_sg T), 
   sg_C_sg_llex S T (A2C_sg_CS_sg S sg_sgS) (A2C_sg_C_sg T sg_sgT)
   =
   A2C_sg_C_sg (S * T) (A_sg_C_sg_llex S T sg_sgS sg_sgT). 
Proof. intros S T sg_sgS sg_sgT. 
       unfold sg_C_sg_llex, A_sg_C_sg_llex, A2C_sg_CS_sg, A2C_sg_C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_C_certs_llex. 
       rewrite correct_sg_certs_product. 
       rewrite correct_sg_sg_certs_llex_product. 
       reflexivity. 
Qed. 


*) 


