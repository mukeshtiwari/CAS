Require Import CAS.code.basic_types. 
Require Import CAS.code.cef. 
Require Import CAS.code.certificates.

(* 

C = Constructor 
P = Property 

  1) C_P_check 
  2) C_P_assert 
  3) C_not_P_assert 

*) 

(* add_ann *) 

Definition bop_add_ann_commutative_check : 
   ∀ (S : Type),  check_commutative S → check_commutative (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Commutative            => Certify_Commutative (with_constant S) 
   | Certify_Not_Commutative (s, t) => 
        Certify_Not_Commutative (with_constant S) (inr _ s, inr _ t)
   end. 

Definition bop_add_ann_selective_check : 
   ∀ (S : Type),  check_selective S → check_selective (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Selective            => Certify_Selective(with_constant S) 
   | Certify_Not_Selective (s, t) => 
        Certify_Not_Selective (with_constant S) (inr _ s, inr _ t)
   end. 

Definition bop_add_ann_idempotent_check : 
   ∀ (S : Type),  check_idempotent S → check_idempotent (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Idempotent       => Certify_Idempotent (with_constant S) 
   | Certify_Not_Idempotent s => Certify_Not_Idempotent (with_constant S) (inr _ s) 
   end. 

Definition bop_add_ann_exists_id_check : 
   ∀ (S : Type),  check_exists_id S → check_exists_id (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Exists_Id i   => Certify_Exists_Id (with_constant S) (inr _ i)
   | Certify_Not_Exists_Id => Certify_Not_Exists_Id (with_constant S) 
   end. 

Definition bop_add_ann_not_is_left_check : 
   ∀ (S : Type),  cas_constant -> certify_witness S → check_is_left (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Left (with_constant S) (inr _ s, inl _ c) 
   end. 

Definition bop_add_ann_not_is_left_assert : 
   ∀ (S : Type),  cas_constant -> certify_witness S → assert_not_is_left (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Left (with_constant S) (inr _ s, inl _ c) 
   end. 

Definition bop_add_ann_not_is_right_check : 
   ∀ (S : Type),  cas_constant -> certify_witness S → check_is_right (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Right (with_constant S) (inl _ c, inr _ s) 
   end. 

Definition bop_add_ann_not_is_right_assert : 
   ∀ (S : Type),  cas_constant -> certify_witness S → assert_not_is_right (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Right (with_constant S) (inl _ c, inr _ s) 
   end. 


(* add_id *) 

Definition bop_add_id_commutative_check : 
   ∀ (S : Type),  check_commutative S → check_commutative (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Commutative            => Certify_Commutative (with_constant S) 
   | Certify_Not_Commutative (s, t) => 
        Certify_Not_Commutative (with_constant S) (inr _ s, inr _ t)
   end. 

Definition bop_add_id_selective_check : 
   ∀ (S : Type),  check_selective S → check_selective (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Selective            => Certify_Selective(with_constant S) 
   | Certify_Not_Selective (s, t) => 
        Certify_Not_Selective (with_constant S) (inr _ s, inr _ t)
   end. 

Definition bop_add_id_idempotent_check : 
   ∀ (S : Type),  check_idempotent S → check_idempotent (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Idempotent       => Certify_Idempotent (with_constant S) 
   | Certify_Not_Idempotent s => Certify_Not_Idempotent (with_constant S) (inr _ s) 
   end. 


Definition bop_add_id_exists_ann_check : 
   ∀ (S : Type),  check_exists_ann S → check_exists_ann (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Exists_Ann a   => Certify_Exists_Ann (with_constant S) (inr _ a)
   | Certify_Not_Exists_Ann => Certify_Not_Exists_Ann (with_constant S) 
   end. 

Definition bop_add_id_not_is_left_check : 
   ∀ (S : Type),  cas_constant -> certify_witness S → check_is_left (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Left (with_constant S) (inl _ c, inr _ s)
   end. 

Definition bop_add_id_not_is_left_assert : 
   ∀ (S : Type),  cas_constant -> certify_witness S → assert_not_is_left (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Left (with_constant S) (inl _ c, inr _ s)
   end. 


Definition bop_add_id_not_is_right_check : 
   ∀ (S : Type),  cas_constant -> certify_witness S → check_is_right (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Certify_Not_Is_Right (with_constant S) (inr _ s, inl _ c) 
   end. 

Definition bop_add_id_not_is_right_assert : 
   ∀ (S : Type),  cas_constant -> certify_witness S → assert_not_is_right (with_constant S) 
:= λ S c dS,  
   match dS with 
   | Certify_Witness s => Assert_Not_Is_Right (with_constant S) (inr _ s, inl _ c) 
   end. 


Definition bop_add_id_left_cancellative_check : 
   ∀ (S : Type) (c : cas_constant),
     check_anti_left S -> 
     check_left_cancellative S -> 
        check_left_cancellative (with_constant S) 
:= λ S c ad lcd,  
   match ad with 
   | Certify_Anti_Left => 
        match lcd with 
        | Certify_Left_Cancellative      => Certify_Left_Cancellative (with_constant S) 
        | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
             Certify_Not_Left_Cancellative (with_constant S) (inr s1, (inr s2, inr s3))
        end 
   | Certify_Not_Anti_Left (s1, s2) => 
        Certify_Not_Left_Cancellative (with_constant S) (inr s1, (inr s2, inl c)) 
   end. 


Definition bop_add_id_right_cancellative_check : 
   ∀ (S : Type) (c : cas_constant),
     check_anti_right S -> 
     check_right_cancellative S -> 
        check_right_cancellative (with_constant S) 
:= λ S c ad lcd,  
   match ad with 
   | Certify_Anti_Right => 
        match lcd with 
        | Certify_Right_Cancellative      => Certify_Right_Cancellative (with_constant S) 
        | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
             Certify_Not_Right_Cancellative (with_constant S) (inr s1, (inr s2, inr s3)) 
        end 
   | Certify_Not_Anti_Right (s1, s2) => 
        Certify_Not_Right_Cancellative (with_constant S) (inr s1, (inr s2, inl c))
   end. 


(* product *) 

Definition check_commutative_product : ∀ (S T : Type) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_commutative S) -> 
             (check_commutative T) -> 
                (check_commutative (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative _ 
      | Certify_Not_Commutative (s1, s2), _       => Certify_Not_Commutative _ ((s1, t), (s2, t))
      | _, Certify_Not_Commutative (t1, t2)       => Certify_Not_Commutative _ ((s, t1), (s, t2))
      end 
   end. 



Definition check_commutative_product_new : ∀ (S T : Type) (s : S) (t : T), 
             (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T)))
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr (s1, s2), _       => inr _ ((s1, t), (s2, t))
      | _, inr (t1, t2)       => inr _ ((s, t1), (s, t2))
      end. 


Definition check_left_cancellative_product : ∀ (S T : Type) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_left_cancellative S) -> 
             (check_left_cancellative T) -> 
                (check_left_cancellative (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Left_Cancellative, Certify_Left_Cancellative => Certify_Left_Cancellative _
      | Certify_Not_Left_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Left_Cancellative _ ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Left_Cancellative _ ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_left_cancellative_product_new : ∀ (S T : Type) (s : S) (t : T), 
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))
      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end. 


Definition check_right_cancellative_product : ∀ (S T : Type) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_right_cancellative S) -> 
             (check_right_cancellative T) -> 
                (check_right_cancellative (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Right_Cancellative, Certify_Right_Cancellative => Certify_Right_Cancellative _
      | Certify_Not_Right_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Right_Cancellative _ ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Right_Cancellative _ ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_right_cancellative_product_new : ∀ (S T : Type) (s : S) (t : T), 
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))
      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end. 



Definition check_left_constant_product : ∀ (S T : Type) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_left_constant S) -> 
             (check_left_constant T) -> 
                (check_left_constant (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Left_Constant, Certify_Left_Constant => Certify_Left_Constant _
      | Certify_Not_Left_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Left_Constant _ ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Constant (t1, (t2, t3))  => 
           Certify_Not_Left_Constant _ ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_left_constant_product_new : ∀ (S T : Type) (s : S) (t : T),  
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))

      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end.  


Definition check_right_constant_product : ∀ (S T : Type) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_right_constant S) -> 
             (check_right_constant T) -> 
                (check_right_constant (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Right_Constant, Certify_Right_Constant => Certify_Right_Constant _
      | Certify_Not_Right_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Right_Constant _ ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Constant (t1, (t2, t3))  => 
           Certify_Not_Right_Constant _ ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_right_constant_product_new : ∀ (S T : Type) (s : S) (t : T),  
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))

      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end.  


Definition check_anti_left_product : 
   ∀ (S T : Type),  check_anti_left S -> check_anti_left T -> check_anti_left (S * T) 
:= λ S T dS dT,  
   match dS with 
   | Certify_Anti_Left => Certify_Anti_Left _ 
   | Certify_Not_Anti_Left (s1, s2)  => 
     match dT with 
     | Certify_Anti_Left => Certify_Anti_Left _ 
     | Certify_Not_Anti_Left(t1, t2)  => Certify_Not_Anti_Left _ ((s1, t1), (s2, t2))
     end 
   end. 


Definition check_anti_left_product_new : 
   ∀ (S T : Type),  (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ S T dS dT,  
   match dS with 
   | inl _ => inl _ tt 
   | inr (s1, s2)  => 
     match dT with 
     | inl _ => inl _ tt 
     | inr (t1, t2)  => inr _ ((s1, t1), (s2, t2))
     end 
   end. 


Definition check_anti_right_product : 
   ∀ (S T : Type),  check_anti_right S -> check_anti_right T -> check_anti_right (S * T) 
:= λ S T dS dT,  
   match dS with 
   | Certify_Anti_Right => Certify_Anti_Right _ 
   | Certify_Not_Anti_Right (s1, s2)  => 
     match dT with 
     | Certify_Anti_Right => Certify_Anti_Right _ 
     | Certify_Not_Anti_Right (t1, t2)  => Certify_Not_Anti_Right _ ((s1, t1), (s2, t2))
     end 
   end. 

Definition check_anti_right_product_new : 
   ∀ (S T : Type),  (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ S T dS dT,  
   match dS with 
   | inl _ => inl _ tt 
   | inr (s1, s2)  => 
     match dT with 
     | inl _ => inl _ tt 
     | inr (t1, t2)  => inr _ ((s1, t1), (s2, t2))
     end 
   end. 


Definition check_idempotent_product : ∀ (S T : Type)
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_idempotent S) -> 
             (check_idempotent T) -> 
                (check_idempotent (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent _ 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent _ (s1, t) 
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent _ (s, t1) 
      end
   end.


Definition check_idempotent_product_new : ∀ (S T : Type) (s : S) (t : T), 
             (unit + S) -> 
             (unit + T) -> 
                (unit + (S * T))
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr s1 , _   => inr _ (s1, t) 
      | _, inr t1    => inr _ (s, t1) 
      end.

Definition check_is_left_product : ∀ (S T : Type)
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_is_left S) -> 
             (check_is_left T) -> 
                (check_is_left (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Is_Left, Certify_Is_Left => Certify_Is_Left _ 
      | Certify_Not_Is_Left (s1, s2), _  => Certify_Not_Is_Left _ ((s1, t), (s2, t))
      | _, Certify_Not_Is_Left (t1, t2)  => Certify_Not_Is_Left _ ((s, t1), (s, t2))
      end 
   end. 

Definition check_is_left_product_new : ∀ (S T : Type) (s : S) (t : T), 
             (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr (s1, s2), _  => inr _ ((s1, t), (s2, t))
      | _, inr (t1, t2)  => inr _ ((s, t1), (s, t2))
      end. 

Definition assert_product_not_is_left_left  : ∀ (S T : Type),  
       assert_nontrivial T -> assert_not_is_left S -> assert_not_is_left (S * T) 
:= λ S T ntT nlS,  
   match certify_nontrivial_witness _ ntT, nlS with 
   | Certify_Witness t, Assert_Not_Is_Left (s1, s2) => Assert_Not_Is_Left _ ((s1, t), (s2, t))
   end. 


Definition check_is_right_product : ∀ (S T : Type) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_is_right S) -> 
             (check_is_right T) -> 
                (check_is_right (S * T))
:= λ S T ntS ntT cS cT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Is_Right, Certify_Is_Right => Certify_Is_Right _ 
      | Certify_Not_Is_Right (s1, s2), _   => Certify_Not_Is_Right _ ((s1, t), (s2, t))
      | _, Certify_Not_Is_Right (t1, t2)   => Certify_Not_Is_Right _ ((s, t1), (s, t2))
      end
   end. 


Definition check_is_right_product_new : ∀ (S T : Type) (s : S) (t : T), 
             (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ S T s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr (s1, s2), _  => inr _ ((s1, t), (s2, t))
      | _, inr (t1, t2)  => inr _ ((s, t1), (s, t2))
      end. 


Definition assert_product_not_is_right_right  : ∀ (S T : Type),  
       assert_nontrivial S -> assert_not_is_right T -> assert_not_is_right (S * T) 
:= λ S T ntS nrT,  
   match certify_nontrivial_witness _ ntS, nrT with 
   | Certify_Witness s, Assert_Not_Is_Right (t1, t2) => Assert_Not_Is_Right _ ((s, t1), (s, t2))
   end.

Definition check_not_selective_product : ∀ (S T : Type),
             (assert_not_is_left S) -> 
             (assert_not_is_right T) -> (check_selective (S * T))
:= λ S T nlS nrT,  
     match nlS, nrT with 
     | Assert_Not_Is_Left (s1, s2), Assert_Not_Is_Right (t1, t2) => 
          Certify_Not_Selective _ ((s1, t1), (s2, t2))  
     end. 


Definition check_selective_product : ∀ (S T : Type)
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
             (check_is_left S) -> 
             (check_is_left T) -> 
             (check_is_right S) -> 
             (check_is_right T) -> 
                (check_selective (S * T))
:= λ S T ntS ntT clS clT crS crT,  
   match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
   | Certify_Witness s, Certify_Witness t => 
     match clS with 
     | Certify_Not_Is_Left (s1, s2) => 
       (* NOT LEFT S *) 
       match crS with 
       | Certify_Is_Right =>  
         (* RIGHT S *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *)   Certify_Selective _ 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *) Certify_Not_Selective _ ((s1, t1), (s2, t2)) 
           end 
       | Certify_Not_Is_Right (s3, s4) =>  
          (* NOT RIGHT S *)   (* extra case *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) (* MUST BE NOT LEFT T *) 
              match clT with 
              | Certify_Is_Left => (* NOT POSSIBLE *) Certify_Selective _ 
              | Certify_Not_Is_Left (t1, t2) => Certify_Not_Selective _ ((s3, t1), (s4, t2))
              end 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *)  
             match clT with  (* why needed ??  to match proof!  clean up! *) 
             | Certify_Is_Left => Certify_Not_Selective _ ((s1, t1), (s2, t2))  
             | Certify_Not_Is_Left (t3, t4) => Certify_Not_Selective _ ((s1, t1), (s2, t2))
             end 
           end 
       end 
     | Certify_Is_Left => 
       (* LEFT S *) 
       match clT with 
       | Certify_Is_Left =>  
         (* LEFT T *) Certify_Selective _
       | Certify_Not_Is_Left (t1, t2) =>  
         (* NOT LEFT T *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) 
                match crS with 
                | Certify_Is_Right =>   (* CAN'T HAPPEN with not-trivial S *) 
                  (* RIGHT S *)  Certify_Selective _ 
                | Certify_Not_Is_Right (s1, s2) => 
                  (* NOT RIGHT S *) Certify_Not_Selective _ ((s1, t1), (s2, t2))  
                end 
           | Certify_Not_Is_Right (t3, t4) => 
             (* NOT RIGHT T *) (* extra case *) 
             match crS with 
             | Certify_Is_Right => 
               (* RIGHT S *) (* MUST BE NOT LEFT S *) 
                match clS with 
                | Certify_Is_Left => (* NOT POSSIBLE *) Certify_Selective _ 
                | Certify_Not_Is_Left (s1, s2) => Certify_Not_Selective _ ((s1, t3), (s2, t4))
                end 
             | Certify_Not_Is_Right (s1, s2) => 
               (* NOT RIGHT S *)  Certify_Not_Selective _ ((s1, t1), (s2, t2))  
             end 
          end 
       end 
     end
  end. 


Definition check_selective_product_new : ∀ (S T : Type) (s : S) (t : T), 
            (* is left S?  *) (unit + (S * S)) -> 
            (* is left T?  *) (unit + (T * T)) -> 
            (* is right S? *) (unit + (S * S)) -> 
            (* is right T? *) (unit + (T * T)) -> 
                (unit + ((S * T) * (S * T)))
:= λ S T s t clS clT crS crT,  
     match clS with 
     | inr (s1, s2) => (* NOT LEFT S *) 
       match crS with 
       | inl _ => (* RIGHT S *) 
           match crT with 
           | inl _        => (* RIGHT T     *) inl  _ tt 
           | inr (t1, t2) => (* NOT RIGHT T *) inr _ ((s1, t1), (s2, t2)) 
             
           end 
       | inr (s3, s4) =>  (* NOT RIGHT S *)   (* extra case *) 
           match crT with 
           | inl _ => (* RIGHT T *) (* MUST BE NOT LEFT T *) 
              match clT with 
              | inl _        => (* NOT POSSIBLE *) inl  _ tt 
              | inr (t1, t2) => inr _ ((s3, t1), (s4, t2))
              end 
           | inr (t1, t2) => (* NOT RIGHT T *)  inr _ ((s1, t1), (s2, t2))  
           end 
       end 
     | inl _ => (* LEFT S *) 
       match clT with 
       | inl _        => (* LEFT T     *) inl  _ tt 
       | inr (t1, t2) => (* NOT LEFT T *) 
           match crT with 
           | inl _ => (* RIGHT T *) 
                match crS with 
                | inl _        => (* NOT POSSIBLE *) inl  _ tt 
                | inr (s1, s2) => (* NOT RIGHT S  *) inr _ ((s1, t1), (s2, t2))  
                end 
           | inr (t3, t4) => (* NOT RIGHT T *) (* extra case *) 
             match crS with 
             | inl _ => (* RIGHT S *) (* MUST BE NOT LEFT S *) 
                match clS with 
                | inl _        => (* NOT POSSIBLE *) inl _ tt 
                | inr (s1, s2) => inr _ ((s1, t3), (s2, t4))
                end 
             | inr (s1, s2) => (* NOT RIGHT S *) inr _ ((s1, t1), (s2, t2))  
             end 
          end 
       end 
     end.

Definition check_selective_product_commutative_case : ∀ (S T : Type)
             (rS : brel S) 
             (rT : brel T) 
             (bS : binary_op S) 
             (bT : binary_op T) 
             (ntS : assert_nontrivial S) 
             (ntT : assert_nontrivial T), 
                (check_selective (S * T))
:= λ S T rS rT bS bT ntS ntT,  
   let s := nontrivial_witness S ntS in
   let f := nontrivial_negate S ntS in  
   let t := nontrivial_witness T ntT in 
   let g := nontrivial_negate T ntT in  
     check_selective_product S T ntS ntT 
        (Certify_Not_Is_Left S (cef_commutative_implies_not_is_left S rS bS s f))
        (Certify_Not_Is_Left T (cef_commutative_implies_not_is_left T rT bT t g))
        (Certify_Not_Is_Right S (cef_commutative_implies_not_is_right S rS bS s f))
        (Certify_Not_Is_Right T (cef_commutative_implies_not_is_right T rT bT t g)). 


Definition check_exists_id_product : ∀ (S T : Type), 
             (check_exists_id S) -> (check_exists_id T) -> (check_exists_id (S * T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t => Certify_Exists_Id (S * T) (s, t) 
      | Certify_Not_Exists_Id, _                 => Certify_Not_Exists_Id (S * T)
      | _, Certify_Not_Exists_Id                 => Certify_Not_Exists_Id (S * T)
      end. 


Definition check_exists_id_product_new : ∀ (S T : Type), 
             (S + unit) -> (T + unit) -> ((S * T) + unit)
:= λ S T cS cT,  
      match cS, cT with 
      | inl s, inl t => inl _ (s, t) 
      | inr _, _     => inr _ tt 
      | _, inr _     => inr _ tt 
      end. 

Definition check_exists_ann_product : ∀ (S T : Type), 
             (check_exists_ann S) -> (check_exists_ann T) -> (check_exists_ann (S * T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann (S * T) (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann (S * T)
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann (S * T)
      end. 

Definition check_exists_ann_product_new : ∀ (S T : Type), 
             (S + unit) -> (T + unit) -> ((S * T) + unit)
:= λ S T cS cT,  
      match cS, cT with 
      | inl s, inl t => inl _ (s, t) 
      | inr _, _     => inr _ tt 
      | _, inr _     => inr _ tt 
      end. 




Definition bop_product_left_distributive_check : 
   ∀ (S T : Type),  
     assert_nontrivial S -> 
     assert_nontrivial T -> 
     check_left_distributive S -> 
     check_left_distributive T -> 
     check_left_distributive (S * T) 
:= λ S T ntS ntT dS dT,  
match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
| Certify_Witness s, Certify_Witness t => 
   match dS with 
   | Certify_Left_Distributive => 
     match dT with 
     | Certify_Left_Distributive => Certify_Left_Distributive (S * T) 
     | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive (S * T) ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (S * T) ((s1, t), ((s2, t), (s3, t)))
   end
end. 

Definition bop_product_right_distributive_check : 
   ∀ (S T : Type),  
     assert_nontrivial S -> 
     assert_nontrivial T -> 
     check_right_distributive S -> 
     check_right_distributive T -> 
     check_right_distributive (S * T) 
:= λ S T ntS ntT dS dT,  
match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
| Certify_Witness s, Certify_Witness t => 
   match dS with 
   | Certify_Right_Distributive => 
     match dT with 
     | Certify_Right_Distributive => Certify_Right_Distributive (S * T) 
     | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive (S * T) ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (S * T) ((s1, t), ((s2, t), (s3, t)))
   end
end. 

Definition bop_product_plus_id_is_times_ann_check : 
   ∀ (S T : Type),  
     check_plus_id_equals_times_ann S -> 
     check_plus_id_equals_times_ann T -> 
     check_plus_id_equals_times_ann (S * T) 
:= λ S T dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann (S * T) 
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann (S * T) 
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann(S * T) 
   end. 

Definition bop_product_times_id_equals_plus_ann_check : 
   ∀ (S T : Type),  
     check_times_id_equals_plus_ann S -> 
     check_times_id_equals_plus_ann T -> 
     check_times_id_equals_plus_ann (S * T) 
:= λ S T dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann (S * T) 
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann (S * T) 
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann(S * T) 
   end. 



Definition bop_product_left_left_absorptive_check : 
   ∀ (S T : Type) (s : S) (t : T),  
     check_left_left_absorptive S -> 
     check_left_left_absorptive T -> 
     check_left_left_absorptive (S * T) 
:= λ S T s t dS dT,  
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive (S * T) 
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
          Certify_Not_Left_Left_Absorptive (S * T) ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive (S * T) ((s1, t), (s2, t))
end. 

Definition bop_product_left_right_absorptive_check : 
   ∀ (S T : Type) (s : S) (t : T),  
     check_left_right_absorptive S -> 
     check_left_right_absorptive T -> 
     check_left_right_absorptive (S * T) 
:= λ S T s t dS dT,  
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive (S * T) 
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
          Certify_Not_Left_Right_Absorptive (S * T) ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive (S * T) ((s1, t), (s2, t))
end. 

Definition bop_product_right_left_absorptive_check : 
   ∀ (S T : Type) (s : S) (t : T),  
     check_right_left_absorptive S -> 
     check_right_left_absorptive T -> 
     check_right_left_absorptive (S * T) 
:= λ S T s t dS dT,  
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive (S * T) 
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
          Certify_Not_Right_Left_Absorptive (S * T) ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive (S * T) ((s1, t), (s2, t))
end. 

Definition bop_product_right_right_absorptive_check : 
   ∀ (S T : Type) (s : S) (t : T),  
     check_right_right_absorptive S -> 
     check_right_right_absorptive T -> 
     check_right_right_absorptive (S * T) 
:= λ S T s t dS dT,  
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive (S * T) 
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
          Certify_Not_Right_Right_Absorptive (S * T) ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive (S * T) ((s1, t), (s2, t))
end. 




(* llex *)

Definition check_commutative_llex : ∀ (S T : Type) 
             (ntS : assert_nontrivial S),  
             (check_commutative T) -> 
                (check_commutative (S * T))
:= λ S T ntS cT,  
   match certify_nontrivial_witness S ntS with 
   | Certify_Witness s => 
      match cT with 
      | Certify_Commutative => Certify_Commutative (S * T)
      | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative _ ((s, t1), (s, t2))
      end 
   end. 

Definition check_idempotent_llex : ∀ (S T : Type)
             (ntS : assert_nontrivial S), 
             (check_idempotent T) -> 
                (check_idempotent (S * T))
:= λ S T ntS cT,  
   match certify_nontrivial_witness S ntS with 
   | Certify_Witness s => 
      match cT with 
      | Certify_Idempotent        => Certify_Idempotent _ 
      | Certify_Not_Idempotent t1 => Certify_Not_Idempotent _ (s, t1) 
      end
   end.

Definition check_selective_llex : ∀ (S T : Type), 
           assert_nontrivial S -> check_selective T -> check_selective (S * T)
:= λ S T ntS dT,  
   match certify_nontrivial_witness S ntS with 
   | Certify_Witness s => 
     match dT with 
     | Certify_Selective              => Certify_Selective _ 
     | Certify_Not_Selective (t1, t2) => Certify_Not_Selective _ ((s, t1), (s, t2)) 
     end
  end. 


Definition check_exists_id_llex : ∀ (S T : Type), 
             (check_exists_id S) -> (check_exists_id T) -> (check_exists_id (S * T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t => Certify_Exists_Id (S * T) (s, t) 
      | Certify_Not_Exists_Id, _                 => Certify_Not_Exists_Id (S * T)
      | _, Certify_Not_Exists_Id                 => Certify_Not_Exists_Id (S * T)
      end. 

Definition check_exists_ann_llex : ∀ (S T : Type), 
             (check_exists_ann S) -> (check_exists_ann T) -> (check_exists_ann (S * T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann (S * T) (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann (S * T)
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann (S * T)
      end. 


Definition bops_llex_product_left_distributive_check 
     (S T : Type)
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (ntS : assert_nontrivial S) 
     (ntT : assert_nontrivial T) 
     (lcS_d : check_left_cancellative S) 
     (lkT_d : check_left_constant T) 
     (ldS_d : check_left_distributive S) 
     (ldT_d : check_left_distributive T) : 
     check_left_distributive (S * T) 
:= 
match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
| Certify_Witness s, Certify_Witness t => 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive (S * T) 
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive (S * T) 
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive (S * T) 
                     (cef_llex_product_not_left_distributive S T rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive (S * T) ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (S * T) ((s1, t), ((s2, t), (s3, t))) 
end
end. 

Definition bops_llex_product_right_distributive_check 
     (S T : Type)
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (ntS : assert_nontrivial S) 
     (ntT : assert_nontrivial T) 
     (lcS_d : check_right_cancellative S) 
     (lkT_d : check_right_constant T) 
     (ldS_d : check_right_distributive S) 
     (ldT_d : check_right_distributive T) : 
     check_right_distributive (S * T) 
:= 
match certify_nontrivial_witness S ntS, certify_nontrivial_witness T ntT with 
| Certify_Witness s, Certify_Witness t => 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive (S * T) 
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive (S * T) 
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive (S * T) 
                     (cef_llex_product_not_right_distributive S T rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive (S * T) ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (S * T) ((s1, t), ((s2, t), (s3, t))) 
end
end. 




(* these are the same as for product *) 
Definition bops_llex_product_plus_id_is_times_ann_check : 
   ∀ (S T : Type),  
     check_plus_id_equals_times_ann S -> 
     check_plus_id_equals_times_ann T -> 
     check_plus_id_equals_times_ann (S * T) 
:= λ S T dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann (S * T) 
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann (S * T) 
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann(S * T) 
   end. 

Definition bops_llex_product_times_id_equals_plus_ann_check : 
   ∀ (S T : Type),  
     check_times_id_equals_plus_ann S -> 
     check_times_id_equals_plus_ann T -> 
     check_times_id_equals_plus_ann (S * T) 
:= λ S T dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann (S * T) 
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann (S * T) 
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann(S * T) 
   end. 



Definition bops_llex_product_left_left_absorptive_check : 
   ∀ (S T : Type) (t : T),  
     check_left_left_absorptive S -> 
     check_left_left_absorptive T -> 
     check_anti_left S -> 
     check_left_left_absorptive (S * T) 
:= λ S T t dS dT alS,  
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive (S * T) 
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Left_Left_Absorptive (S * T) 
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Left_Left_Absorptive (S * T) ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive (S * T) ((s1, t), (s2, t))
end. 


Definition bops_llex_product_left_right_absorptive_check : 
   ∀ (S T : Type) (t : T),  
     check_left_right_absorptive S -> 
     check_left_right_absorptive T -> 
     check_anti_right S -> 
     check_left_right_absorptive (S * T) 
:= λ S T t dS dT alS,  
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive (S * T) 
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Left_Right_Absorptive (S * T) 
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Left_Right_Absorptive (S * T) ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive (S * T) ((s1, t), (s2, t))
end. 



Definition bops_llex_product_right_left_absorptive_check : 
   ∀ (S T : Type) (t : T),  
     check_right_left_absorptive S -> 
     check_right_left_absorptive T -> 
     check_anti_left S -> 
     check_right_left_absorptive (S * T) 
:= λ S T t dS dT alS,  
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive (S * T) 
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Right_Left_Absorptive (S * T) 
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Right_Left_Absorptive (S * T) ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive (S * T) ((s1, t), (s2, t))
end. 


Definition bops_llex_product_right_right_absorptive_check : 
   ∀ (S T : Type) (t : T),  
     check_right_right_absorptive S -> 
     check_right_right_absorptive T -> 
     check_anti_right S -> 
     check_right_right_absorptive (S * T) 
:= λ S T t dS dT alS,  
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive (S * T) 
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Right_Right_Absorptive (S * T) 
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Right_Right_Absorptive (S * T) ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive (S * T) ((s1, t), (s2, t))
end. 


(* add zero *) 


Definition bops_add_zero_left_distributive_check : 
   ∀ (S : Type),  
     check_left_distributive S -> 
     check_left_distributive (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Left_Distributive => Certify_Left_Distributive (with_constant S) 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (with_constant S) (inr _ s1, (inr _ s2, inr _ s3))
   end. 

Definition bops_add_zero_right_distributive_check : 
   ∀ (S : Type),  
     check_right_distributive S -> 
     check_right_distributive (with_constant S) 
:= λ S dS,  
   match dS with 
   | Certify_Right_Distributive => Certify_Right_Distributive (with_constant S) 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (with_constant S) (inr _ s1, (inr _ s2, inr _ s3))
   end. 

Definition bops_add_zero_left_left_absorptive_check : 
   ∀ (S : Type) (s : S), 
     check_left_left_absorptive S -> 
     check_left_left_absorptive (with_constant S)
:= λ S s dS ,  
match dS with 
| Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive (with_constant S)
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
     Certify_Not_Left_Left_Absorptive (with_constant S) (inr _ s1, inr _ s2)
end. 


Definition bops_add_zero_left_right_absorptive_check : 
   ∀ (S : Type) (s : S), 
     check_left_right_absorptive S -> 
     check_left_right_absorptive (with_constant S)
:= λ S s dS ,  
match dS with 
| Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive (with_constant S)
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
     Certify_Not_Left_Right_Absorptive (with_constant S) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_left_absorptive_check : 
   ∀ (S : Type) (s : S), 
     check_right_left_absorptive S -> 
     check_right_left_absorptive (with_constant S)
:= λ S s dS ,  
match dS with 
| Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive (with_constant S)
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
     Certify_Not_Right_Left_Absorptive (with_constant S) (inr _ s1, inr _ s2)
end. 

Definition bops_add_zero_right_right_absorptive_check : 
   ∀ (S : Type) (s : S), 
     check_right_right_absorptive S -> 
     check_right_right_absorptive (with_constant S)
:= λ S s dS ,  
match dS with 
| Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive (with_constant S)
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
     Certify_Not_Right_Right_Absorptive (with_constant S) (inr _ s1, inr _ s2)
end. 

(* add one *) 

Definition bops_add_one_left_distributive_check : 
   ∀ (S : Type) 
     (c : cas_constant),
     check_idempotent S -> 
     check_left_left_absorptive S -> 
     check_right_left_absorptive S -> 
     check_left_distributive S ->  check_left_distributive (with_constant S)
:= λ S c idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | Certify_Left_Distributive  => 
    match llaS_d with 
    | Certify_Left_Left_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Left_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent       => Certify_Left_Distributive _ 
         | Certify_Not_Idempotent s => Certify_Not_Left_Distributive _ (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Left_Absorptive (s1, s2) => 
            Certify_Not_Left_Distributive _ (inr _ s1, (inr _ s2, inl _ c))
      end 
    | Certify_Not_Left_Left_Absorptive (s1, s2) => 
         Certify_Not_Left_Distributive _ (inr _ s1, (inl _ c, inr _ s2))
    end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive _ (inr _ s1, (inr _ s2, inr _ s3))
   end. 


Definition bops_add_one_right_distributive_check : 
   ∀ (S : Type) 
     (c : cas_constant),
     check_idempotent S -> 
     check_left_right_absorptive S -> 
     check_right_right_absorptive S -> 
     check_right_distributive S ->  check_right_distributive (with_constant S)
:= λ S c idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | Certify_Right_Distributive  => 
    match llaS_d with 
    | Certify_Left_Right_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Right_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent       => Certify_Right_Distributive _ 
         | Certify_Not_Idempotent s => Certify_Not_Right_Distributive _ (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Right_Absorptive (s1, s2) => 
            Certify_Not_Right_Distributive _ (inr _ s1, (inr _ s2, inl _ c))
      end 
    | Certify_Not_Left_Right_Absorptive (s1, s2) => 
         Certify_Not_Right_Distributive _ (inr _ s1, (inl _ c, inr _ s2))
    end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive _ (inr _ s1, (inr _ s2, inr _ s3))
   end. 


Definition bops_add_one_left_left_absorptive_check : 
   ∀ (S : Type) 
     (c : cas_constant),
     check_idempotent S -> 
     check_left_left_absorptive S -> check_left_left_absorptive (with_constant S)
:= λ S c idemS_d laS_d, 
   match laS_d with 
   | Certify_Left_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Left_Absorptive _ 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Left_Absorptive _ (inr s, inl c) 
     end 
   | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Left_Left_Absorptive _ (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_left_right_absorptive_check : 
   ∀ (S : Type) 
     (c : cas_constant),
     check_idempotent S -> 
     check_left_right_absorptive S -> check_left_right_absorptive (with_constant S)
:= λ S c idemS_d laS_d, 
   match laS_d with 
   | Certify_Left_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Right_Absorptive _ 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Right_Absorptive _ (inr s, inl c) 
     end 
   | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Left_Right_Absorptive _ (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_left_absorptive_check : 
   ∀ (S : Type) 
     (c : cas_constant),
     check_idempotent S -> 
     check_right_left_absorptive S -> check_right_left_absorptive (with_constant S)
:= λ S c idemS_d laS_d, 
   match laS_d with 
   | Certify_Right_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Left_Absorptive _ 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Left_Absorptive _ (inr s, inl c) 
     end 
   | Certify_Not_Right_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive _ (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_right_absorptive_check : 
   ∀ (S : Type) 
     (c : cas_constant),
     check_idempotent S -> 
     check_right_right_absorptive S -> check_right_right_absorptive (with_constant S)
:= λ S c idemS_d laS_d, 
   match laS_d with 
   | Certify_Right_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Right_Absorptive _ 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Right_Absorptive _ (inr s, inl c) 
     end 
   | Certify_Not_Right_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive _ (inr _ s1, inr _ s2)
   end. 



(* sums *) 

Definition check_commutative_sum : ∀ (S T : Type), 
             (check_commutative S) -> 
             (check_commutative T) -> 
                (check_commutative (S + T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative _ 
      | Certify_Not_Commutative (s1, s2), _  => Certify_Not_Commutative _ ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Commutative (t1, t2)  => Certify_Not_Commutative _ ((inr _ t1), (inr _ t2))
      end. 

Definition check_idempotent_sum : ∀ (S T : Type), 
             (check_idempotent S) -> 
             (check_idempotent T) -> 
                (check_idempotent (S + T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent _ 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent _ (inl _ s1)
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent _ (inr _ t1)
      end. 


Definition check_selective_sum : ∀ (S T : Type), 
             (check_selective S) -> 
             (check_selective T) -> 
                (check_selective (S + T))
:= λ S T cS cT,  
      match cS, cT with 
      | Certify_Selective, Certify_Selective => Certify_Selective _ 
      | Certify_Not_Selective (s1, s2), _    => Certify_Not_Selective _ ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Selective (t1, t2)    => Certify_Not_Selective _ ((inr _ t1), (inr _ t2))
      end. 


Definition check_exists_id_left_sum : ∀ (S T : Type), 
             (check_exists_id T) -> (check_exists_id (S + T))
:= λ S T cT,  
      match cT with 
      | Certify_Exists_Id t    => Certify_Exists_Id (S + T) (inr S t) 
      | Certify_Not_Exists_Id  => Certify_Not_Exists_Id (S + T)
      end. 

Definition check_exists_id_right_sum : ∀ (S T : Type), 
             (check_exists_id S) -> (check_exists_id (S + T))
:= λ S T cS,  
      match cS with 
      | Certify_Exists_Id s    => Certify_Exists_Id (S + T) (inl T s) 
      | Certify_Not_Exists_Id  => Certify_Not_Exists_Id (S + T)
      end. 


Definition check_exists_ann_left_sum : ∀ (S T : Type), 
             (check_exists_ann S) -> (check_exists_ann (S + T))
:= λ S T cS,  
      match cS with 
      | Certify_Exists_Ann s    => Certify_Exists_Ann (S + T) (inl T s)
      | Certify_Not_Exists_Ann  => Certify_Not_Exists_Ann (S + T)
      end. 

Definition check_exists_ann_right_sum : ∀ (S T : Type), 
             (check_exists_ann T) -> (check_exists_ann (S + T))
:= λ S T cT,  
      match cT with 
      | Certify_Exists_Ann t    => Certify_Exists_Ann (S + T) (inr S t)
      | Certify_Not_Exists_Ann  => Certify_Not_Exists_Ann (S + T)
      end. 

