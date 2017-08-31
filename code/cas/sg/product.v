Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.

Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records.
Require Import CAS.code.ast.
Require Import CAS.code.eqv_records.

Require Import CAS.code.sg_certificates.
Require Import CAS.code.sg_cert_records.
Require Import CAS.code.sg_records.

Require Import CAS.code.cas.eqv.product.
Require Import CAS.code.cef. 

Definition check_commutative_product : ∀ {S T : Type} 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_commutative (S := S)) -> 
             (check_commutative (S := T)) -> 
                (check_commutative (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative 
      | Certify_Not_Commutative (s1, s2), _      => Certify_Not_Commutative ((s1, t), (s2, t))
      | _, Certify_Not_Commutative (t1, t2)       => Certify_Not_Commutative ((s, t1), (s, t2))
      end 
   end. 

Definition check_commutative_product_new : ∀ {S T : Type} (s : S) (t : T), 
             (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr (s1, s2), _       => inr _ ((s1, t), (s2, t))
      | _, inr (t1, t2)       => inr _ ((s, t1), (s, t2))
      end. 


Definition check_left_cancellative_product : ∀ {S T : Type} 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_left_cancellative (S := S)) -> 
             (check_left_cancellative (S := T)) -> 
                (check_left_cancellative (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Left_Cancellative, Certify_Left_Cancellative => Certify_Left_Cancellative
      | Certify_Not_Left_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Left_Cancellative ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Left_Cancellative ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_left_cancellative_product_new : ∀ {S T : Type} (s : S) (t : T), 
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))
      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end. 


Definition check_right_cancellative_product : ∀ {S T : Type} 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_right_cancellative (S := S)) -> 
             (check_right_cancellative (S := T)) -> 
                (check_right_cancellative (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Right_Cancellative , Certify_Right_Cancellative => Certify_Right_Cancellative
      | Certify_Not_Right_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Right_Cancellative ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Right_Cancellative ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_right_cancellative_product_new : ∀ {S T : Type} (s : S) (t : T), 
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))
      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end. 



Definition check_left_constant_product : ∀ {S T : Type} 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_left_constant (S := S)) -> 
             (check_left_constant (S := T)) -> 
                (check_left_constant (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Left_Constant, Certify_Left_Constant => Certify_Left_Constant
      | Certify_Not_Left_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Left_Constant ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Constant (t1, (t2, t3))  => 
           Certify_Not_Left_Constant ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_left_constant_product_new : ∀ {S T : Type} (s : S) (t : T),  
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))

      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end.  


Definition check_right_constant_product : ∀ {S T : Type} 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_right_constant (S := S)) -> 
             (check_right_constant (S := T)) -> 
                (check_right_constant (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Right_Constant, Certify_Right_Constant => Certify_Right_Constant
      | Certify_Not_Right_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Right_Constant ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Constant (t1, (t2, t3))  => 
           Certify_Not_Right_Constant ((s, t1), ((s, t2), (s, t3)))
      end 
   end. 

Definition check_right_constant_product_new : ∀ {S T : Type} (s : S) (t : T),  
             (unit + (S * (S * S))) -> 
             (unit + (T * (T * T))) -> 
                (unit + ((S * T) * ((S * T) * (S * T))))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _          => inl _ tt
      | inr (s1, (s2, s3)), _ => inr _ ((s1, t), ((s2, t), (s3, t)))

      | _, inr (t1, (t2, t3)) => inr _ ((s, t1), ((s, t2), (s, t3)))
      end.  


Definition check_anti_left_product : 
   ∀ {S T : Type},  check_anti_left (S := S) -> check_anti_left (S := T) -> check_anti_left (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Anti_Left => Certify_Anti_Left 
   | Certify_Not_Anti_Left (s1, s2)  => 
     match dT with 
     | Certify_Anti_Left => Certify_Anti_Left 
     | Certify_Not_Anti_Left (t1, t2)  => Certify_Not_Anti_Left ((s1, t1), (s2, t2))
     end 
   end. 


Definition check_anti_left_product_new : 
   ∀ {S T : Type},  (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ {S T} dS dT,  
   match dS with 
   | inl _ => inl _ tt 
   | inr (s1, s2)  => 
     match dT with 
     | inl _ => inl _ tt 
     | inr (t1, t2)  => inr _ ((s1, t1), (s2, t2))
     end 
   end. 


Definition check_anti_right_product : 
   ∀ {S T : Type},  check_anti_right (S := S) -> check_anti_right (S := T) -> check_anti_right (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Anti_Right  => Certify_Anti_Right 
   | Certify_Not_Anti_Right (s1, s2)  => 
     match dT with 
     | Certify_Anti_Right => Certify_Anti_Right 
     | Certify_Not_Anti_Right (t1, t2)  => Certify_Not_Anti_Right ((s1, t1), (s2, t2))
     end 
   end. 

Definition check_anti_right_product_new : 
   ∀ {S T : Type},  (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ {S T} dS dT,  
   match dS with 
   | inl _ => inl _ tt 
   | inr (s1, s2)  => 
     match dT with 
     | inl _ => inl _ tt 
     | inr (t1, t2)  => inr _ ((s1, t1), (s2, t2))
     end 
   end. 


Definition check_idempotent_product : ∀ {S T : Type}
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_idempotent (S := S)) -> 
             (check_idempotent (S := T)) -> 
                (check_idempotent (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent (s1, t) 
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent (s, t1) 
      end
   end.


Definition check_idempotent_product_new : ∀ {S T : Type} (s : S) (t : T), 
             (unit + S) -> 
             (unit + T) -> 
                (unit + (S * T))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr s1 , _   => inr _ (s1, t) 
      | _, inr t1    => inr _ (s, t1) 
      end.

Definition check_is_left_product : ∀ {S T : Type}
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_is_left (S := S)) -> 
             (check_is_left (S := T)) -> 
                (check_is_left (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Is_Left, Certify_Is_Left => Certify_Is_Left 
      | Certify_Not_Is_Left (s1, s2), _  => Certify_Not_Is_Left ((s1, t), (s2, t))
      | _, Certify_Not_Is_Left (t1, t2)  => Certify_Not_Is_Left ((s, t1), (s, t2))
      end 
   end. 

Definition check_is_left_product_new : ∀ {S T : Type} (s : S) (t : T), 
             (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr (s1, s2), _  => inr _ ((s1, t), (s2, t))
      | _, inr (t1, t2)  => inr _ ((s, t1), (s, t2))
      end. 

Definition assert_product_not_is_left_left  : ∀ {S T : Type},  
       assert_nontrivial (S := T) -> assert_not_is_left (S := S) -> assert_not_is_left (S := (S * T)) 
:= λ {S T} ntT nlS,  
   match certify_nontrivial_witness ntT, nlS with 
   | Certify_Witness t, Assert_Not_Is_Left (s1, s2) => Assert_Not_Is_Left ((s1, t), (s2, t))
   end. 


Definition check_is_right_product : ∀ {S T : Type} 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_is_right (S := S)) -> 
             (check_is_right (S := T)) -> 
                (check_is_right (S := (S * T)))
:= λ {S T} ntS ntT cS cT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
      match cS, cT with 
      | Certify_Is_Right, Certify_Is_Right => Certify_Is_Right 
      | Certify_Not_Is_Right (s1, s2), _   => Certify_Not_Is_Right ((s1, t), (s2, t))
      | _, Certify_Not_Is_Right (t1, t2)   => Certify_Not_Is_Right ((s, t1), (s, t2))
      end
   end. 


Definition check_is_right_product_new : ∀ {S T : Type} (s : S) (t : T), 
             (unit + (S * S)) -> (unit + (T * T)) -> (unit + ((S * T) * (S * T))) 
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | inl _, inl _ => inl _ tt 
      | inr (s1, s2), _  => inr _ ((s1, t), (s2, t))
      | _, inr (t1, t2)  => inr _ ((s, t1), (s, t2))
      end. 


Definition assert_product_not_is_right_right  : ∀ {S T : Type},  
       assert_nontrivial (S := S) -> assert_not_is_right (S := T) -> assert_not_is_right (S := (S * T)) 
:= λ {S T} ntS nrT,  
   match certify_nontrivial_witness ntS, nrT with 
   | Certify_Witness s, Assert_Not_Is_Right (t1, t2) => Assert_Not_Is_Right ((s, t1), (s, t2))
   end.

Definition check_not_selective_product : ∀ {S T : Type},
             (assert_not_is_left (S := S)) -> 
             (assert_not_is_right (S := T)) -> (check_selective (S := (S * T)))
:= λ {S T} nlS nrT,  
     match nlS, nrT with 
     | Assert_Not_Is_Left (s1, s2), Assert_Not_Is_Right (t1, t2) => 
          Certify_Not_Selective ((s1, t1), (s2, t2))  
     end. 


Definition check_selective_product : ∀ {S T : Type}
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
             (check_is_left (S := S)) -> 
             (check_is_left (S := T)) -> 
             (check_is_right (S := S)) -> 
             (check_is_right (S := T)) -> 
                (check_selective (S := (S * T)))
:= λ {S T} ntS ntT clS clT crS crT,  
   match certify_nontrivial_witness ntS, certify_nontrivial_witness ntT with 
   | Certify_Witness s, Certify_Witness t => 
     match clS with 
     | Certify_Not_Is_Left (s1, s2) => 
       (* NOT LEFT S *) 
       match crS with 
       | Certify_Is_Right =>  
         (* RIGHT S *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *)   Certify_Selective 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *) Certify_Not_Selective ((s1, t1), (s2, t2)) 
           end 
       | Certify_Not_Is_Right (s3, s4) =>  
          (* NOT RIGHT S *)   (* extra case *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) (* MUST BE NOT LEFT T *) 
              match clT with 
              | Certify_Is_Left => (* NOT POSSIBLE *) Certify_Selective 
              | Certify_Not_Is_Left (t1, t2) => Certify_Not_Selective ((s3, t1), (s4, t2))
              end 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *)  
             match clT with  (* why needed ??  to match proof!  clean up! *) 
             | Certify_Is_Left => Certify_Not_Selective ((s1, t1), (s2, t2))  
             | Certify_Not_Is_Left (t3, t4) => Certify_Not_Selective ((s1, t1), (s2, t2))
             end 
           end 
       end 
     | Certify_Is_Left => 
       (* LEFT S *) 
       match clT with 
       | Certify_Is_Left =>  
         (* LEFT T *) Certify_Selective
       | Certify_Not_Is_Left (t1, t2) =>  
         (* NOT LEFT T *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) 
                match crS with 
                | Certify_Is_Right =>   (* CAN'T HAPPEN with not-trivial S *) 
                  (* RIGHT S *)  Certify_Selective 
                | Certify_Not_Is_Right (s1, s2) => 
                  (* NOT RIGHT S *) Certify_Not_Selective ((s1, t1), (s2, t2))  
                end 
           | Certify_Not_Is_Right (t3, t4) => 
             (* NOT RIGHT T *) (* extra case *) 
             match crS with 
             | Certify_Is_Right => 
               (* RIGHT S *) (* MUST BE NOT LEFT S *) 
                match clS with 
                | Certify_Is_Left  => (* NOT POSSIBLE *) Certify_Selective 
                | Certify_Not_Is_Left  (s1, s2) => Certify_Not_Selective ((s1, t3), (s2, t4))
                end 
             | Certify_Not_Is_Right (s1, s2) => 
               (* NOT RIGHT S *)  Certify_Not_Selective ((s1, t1), (s2, t2))  
             end 
          end 
       end 
     end
  end. 


Definition check_selective_product_new : ∀ {S T : Type} (s : S) (t : T), 
            (* is left S?  *) (unit + (S * S)) -> 
            (* is left T?  *) (unit + (T * T)) -> 
            (* is right S? *) (unit + (S * S)) -> 
            (* is right T? *) (unit + (T * T)) -> 
                (unit + ((S * T) * (S * T)))
:= λ {S T} s t clS clT crS crT,  
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

Definition check_selective_product_commutative_case : ∀ {S T : Type}
             (rS : brel S) 
             (rT : brel T) 
             (bS : binary_op S) 
             (bT : binary_op T) 
             (ntS : assert_nontrivial (S := S)) 
             (ntT : assert_nontrivial (S := T)), 
                (check_selective (S := (S * T)))
:= λ {S T} rS rT bS bT ntS ntT,  
   let s := nontrivial_witness ntS in
   let f := nontrivial_negate ntS in  
   let t := nontrivial_witness ntT in 
   let g := nontrivial_negate ntT in  
     check_selective_product ntS ntT 
        (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS s f))
        (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT t g))
        (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS s f))
        (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT t g)). 

Definition check_exists_id_product : ∀ {S T : Type}, 
             (check_exists_id (S := S)) -> (check_exists_id (S := T)) -> (check_exists_id (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t => Certify_Exists_Id (s, t) 
      | Certify_Not_Exists_Id , _                 => Certify_Not_Exists_Id
      | _, Certify_Not_Exists_Id                => Certify_Not_Exists_Id
      end. 


Definition check_exists_id_product_new : ∀ {S T : Type}, 
             (S + unit) -> (T + unit) -> ((S * T) + unit)
:= λ {S T} cS cT,  
      match cS, cT with 
      | inl s, inl t => inl _ (s, t) 
      | inr _, _     => inr _ tt 
      | _, inr _     => inr _ tt 
      end. 

Definition check_exists_ann_product : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := T)) -> (check_exists_ann (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann 
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann 
      end. 

Definition check_exists_ann_product_new : ∀ {S T : Type}, 
             (S + unit) -> (T + unit) -> ((S * T) + unit)
:= λ {S T} cS cT,  
      match cS, cT with 
      | inl s, inl t => inl _ (s, t) 
      | inr _, _     => inr _ tt 
      | _, inr _     => inr _ tt 
      end. 





Definition sg_certs_product : ∀ {S T : Type},  eqv_certificates (S := S) -> eqv_certificates (S := T) -> sg_certificates (S := S) -> sg_certificates (S := T) -> sg_certificates (S := (S * T)) 
:= λ {S T} eS eT cS cT,  
   let wS := eqv_nontrivial eS in 
   let wT := eqv_nontrivial eT in 
{|
  sg_associative   := Assert_Associative   
; sg_congruence    := Assert_Bop_Congruence   
; sg_commutative_d := check_commutative_product wS wT 
                         (sg_commutative_d cS) 
                         (sg_commutative_d cT)
; sg_selective_d   := check_selective_product wS wT 
                         (sg_is_left_d cS) 
                         (sg_is_left_d cT)
                         (sg_is_right_d cS) 
                         (sg_is_right_d cT)
; sg_is_left_d     := check_is_left_product wS wT 
                         (sg_is_left_d cS) 
                         (sg_is_left_d cT)
; sg_is_right_d    := check_is_right_product wS wT 
                         (sg_is_right_d cS) 
                         (sg_is_right_d cT)
; sg_idempotent_d  := check_idempotent_product wS wT 
                         (sg_idempotent_d cS) 
                         (sg_idempotent_d cT)
; sg_exists_id_d   := check_exists_id_product 
                         (sg_exists_id_d cS) 
                         (sg_exists_id_d cT)
; sg_exists_ann_d  := check_exists_ann_product 
                         (sg_exists_ann_d cS) 
                         (sg_exists_ann_d cT)
; sg_left_cancel_d    := check_left_cancellative_product wS wT 
                          (sg_left_cancel_d cS)
                          (sg_left_cancel_d cT)
; sg_right_cancel_d   := check_right_cancellative_product wS wT 
                          (sg_right_cancel_d cS)
                          (sg_right_cancel_d cT)
; sg_left_constant_d  := check_left_constant_product wS wT 
                          (sg_left_constant_d cS)
                          (sg_left_constant_d cT)
; sg_right_constant_d := check_right_constant_product wS wT 
                          (sg_right_constant_d cS)
                          (sg_right_constant_d cT)
; sg_anti_left_d      := check_anti_left_product 
                         (sg_anti_left_d cS) 
                         (sg_anti_left_d cT)
; sg_anti_right_d     := check_anti_right_product 
                         (sg_anti_right_d cS) 
                         (sg_anti_right_d cT)
|}.


Definition sg_CK_certs_product : ∀ {S T : Type},  eqv_certificates (S := S) -> eqv_certificates (S := T) -> sg_CK_certificates (S := S) -> sg_CK_certificates (S := T) -> sg_CK_certificates (S := (S * T)) 
:= λ {S T} eS eT cS cT,  
   let wS := eqv_nontrivial eS in 
   let wT := eqv_nontrivial eT in 
{|
  sg_CK_associative   := Assert_Associative   
; sg_CK_congruence    := Assert_Bop_Congruence   
; sg_CK_commutative   := Assert_Commutative   
; sg_CK_left_cancel   := Assert_Left_Cancellative   
; sg_CK_exists_id_d   := check_exists_id_product 
                         (sg_CK_exists_id_d cS) 
                         (sg_CK_exists_id_d cT)
; sg_CK_anti_left_d   := check_anti_left_product 
                         (sg_CK_anti_left_d cS) 
                         (sg_CK_anti_left_d cT)
; sg_CK_anti_right_d  := check_anti_right_product 
                         (sg_CK_anti_right_d cS) 
                         (sg_CK_anti_right_d cT)


|}.

Definition sg_C_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) -> eqv_certificates (S := S) -> eqv_certificates (S := T) -> sg_C_certificates (S := S) -> sg_C_certificates (S := T) -> sg_C_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT eS eT cS cT,  
let wS := eqv_nontrivial eS in 
let wT := eqv_nontrivial eT in 
let s := nontrivial_witness wS in
let f := nontrivial_negate wS in  
let t := nontrivial_witness wT in 
let g := nontrivial_negate wT in  
{|
  sg_C_associative   := Assert_Associative   
; sg_C_congruence    := Assert_Bop_Congruence   
; sg_C_commutative   := Assert_Commutative   
; sg_C_selective_d   := check_selective_product wS wT 
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS s f))
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT t g))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS s f))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT t g))
; sg_C_idempotent_d  := check_idempotent_product wS wT 
                         (sg_C_idempotent_d cS) 
                         (sg_C_idempotent_d cT)
; sg_C_exists_id_d   := check_exists_id_product 
                         (sg_C_exists_id_d cS) 
                         (sg_C_exists_id_d cT)
; sg_C_exists_ann_d  := check_exists_ann_product 
                         (sg_C_exists_ann_d cS) 
                         (sg_C_exists_ann_d cT)
; sg_C_left_cancel_d    := check_left_cancellative_product wS wT 
                          (sg_C_left_cancel_d cS)
                          (sg_C_left_cancel_d cT)
; sg_C_right_cancel_d   := check_right_cancellative_product wS wT 
                          (sg_C_right_cancel_d cS)
                          (sg_C_right_cancel_d cT)
; sg_C_left_constant_d  := check_left_constant_product wS wT 
                          (sg_C_left_constant_d cS)
                          (sg_C_left_constant_d cT)
; sg_C_right_constant_d := check_right_constant_product wS wT 
                          (sg_C_right_constant_d cS)
                          (sg_C_right_constant_d cT)
; sg_C_anti_left_d      := check_anti_left_product 
                         (sg_C_anti_left_d cS) 
                         (sg_C_anti_left_d cT)
; sg_C_anti_right_d     := check_anti_right_product 
                         (sg_C_anti_right_d cS) 
                         (sg_C_anti_right_d cT)

|}.

Definition sg_CI_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) -> eqv_certificates (S := S) -> eqv_certificates (S := T) -> sg_CI_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT eS eT cS cT,  
let wS := eqv_nontrivial eS in 
let wT := eqv_nontrivial eT in 
let s := nontrivial_witness wS in
let f := nontrivial_negate wS in  
let t := nontrivial_witness wT in 
let g := nontrivial_negate wT in  
{|
  sg_CI_associative   := Assert_Associative   
; sg_CI_congruence    := Assert_Bop_Congruence   
; sg_CI_commutative   := Assert_Commutative   
; sg_CI_idempotent  := Assert_Idempotent   
; sg_CI_selective_d   := check_selective_product wS wT 
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rS bS s f))
                         (Certify_Not_Is_Left (cef_commutative_implies_not_is_left rT bT t g))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rS bS s f))
                         (Certify_Not_Is_Right (cef_commutative_implies_not_is_right rT bT t g))
; sg_CI_exists_id_d   := check_exists_id_product 
                         (sg_CI_exists_id_d cS) 
                         (sg_CI_exists_id_d cT)
; sg_CI_exists_ann_d  := check_exists_ann_product 
                         (sg_CI_exists_ann_d cS) 
                         (sg_CI_exists_ann_d cT)
|}.


Definition sg_CK_product : ∀ {S T : Type},  sg_CK (S := S) -> sg_CK (S := T) -> sg_CK (S := (S * T)) 
:= λ {S T} sgS sgT, 
   {| 
     sg_CK_eqv   := eqv_product (sg_CK_eqv sgS) (sg_CK_eqv sgT) 
   ; sg_CK_bop   := bop_product (sg_CK_bop sgS) (sg_CK_bop sgT) 
   ; sg_CK_certs := sg_CK_certs_product (eqv_certs (sg_CK_eqv sgS)) (eqv_certs (sg_CK_eqv sgT)) 
                                        (sg_CK_certs sgS) (sg_CK_certs sgT) 
   ; sg_CK_ast       := Ast_sg_CK_product (sg_CK_ast sgS, sg_CK_ast sgT)
   |}. 

(*!!*) 
Definition sg_C_product : ∀ {S T : Type},  sg_C (S := S) -> sg_C -> sg_C (S := (S * T)) 
:= λ {S T} sgS sgT, 
   {| 
     sg_C_eqv    := eqv_product  (sg_C_eqv sgS) (sg_C_eqv sgT) 
   ; sg_C_bop    := bop_product (sg_C_bop sgS) (sg_C_bop sgT)                            
   ; sg_C_certs := sg_C_certs_product (eqv_eq (sg_C_eqv sgS)) (eqv_eq (sg_C_eqv sgT))
                           (sg_C_bop sgS) (sg_C_bop sgT) 
                           (eqv_certs (sg_C_eqv sgS)) (eqv_certs (sg_C_eqv sgT)) 
                           (sg_C_certs sgS) (sg_C_certs sgT) 
   ; sg_C_ast       := Ast_sg_C_product (sg_C_ast sgS, sg_C_ast sgT)
   |}. 

(*!!*) 
Definition sg_CI_product : ∀ {S T : Type},  sg_CI (S := S) -> sg_CI (S := T) -> sg_CI (S := (S * T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CI_eqv    := eqv_product 
                           (sg_CI_eqv sgS) 
                           (sg_CI_eqv sgT) 
   ; sg_CI_bop       := bop_product 
                           (sg_CI_bop sgS) 
                           (sg_CI_bop sgT) 
   ; sg_CI_certs := sg_CI_certs_product 
                           (eqv_eq (sg_CI_eqv sgS)) 
                           (eqv_eq (sg_CI_eqv sgT))
                           (sg_CI_bop sgS) 
                           (sg_CI_bop sgT) 
                           (eqv_certs (sg_CI_eqv sgS)) 
                           (eqv_certs (sg_CI_eqv sgT)) 
                           (sg_CI_certs sgS) 
                           (sg_CI_certs sgT) 
   ; sg_CI_ast       := Ast_sg_CI_product (sg_CI_ast sgS, sg_CI_ast sgT)
   |}. 



