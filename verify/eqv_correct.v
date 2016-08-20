Require Import CAS.code.basic_types. 
Require Import CAS.code.cas.
Require Import CAS.a_code.a_cas_records.   
Require Import CAS.a_code.a_cas.           
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.construct_correct. (* break up *)

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


