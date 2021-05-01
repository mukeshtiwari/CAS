Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.


Definition ltr_product :
   ∀ {LS S LT T: Type}, left_transform LS S → left_transform LT T → left_transform (LS * LT) (S * T)
   := λ {LS S LT T} ltrS ltrT x y,  
     match x, y with
     | (x1, x2), (y1, y2) => (ltrS x1 y1, ltrT x2 y2) 
     end.

Section Theory.
  
Variable LS S : Type.  
Variable LT T : Type.
Variable eqS : brel S.
Variable eqLS : brel LS.
Variable wS : S.
Variable wLS : LS.
Variable ltrS : left_transform LS S.
Variable eqT : brel T.
Variable eqLT : brel LT.
Variable wT : T.
Variable wLT : LT.
Variable ltrT : left_transform LT T.

Variable refS : brel_reflexive S eqS.
Variable refT : brel_reflexive T eqT. 

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (ltr_product a b) (at level 15).


Lemma ltr_product_congruence
      (CS : ltr_congruence LS S eqLS eqS ltrS)      
      (CT : ltr_congruence LT T eqLT eqT ltrT) : 
   ltr_congruence (LS * LT) (S * T) (eqLS <*> eqLT) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]. compute.
       case_eq(eqLS s1 s2); intro A; case_eq(eqLT t1 t2); intro B; intro C. 
         case_eq(eqS s3 s4); intro D; case_eq(eqT t3 t4); intro E; intro F. 
            rewrite (CS _ _ _ _ A D). rewrite (CT _ _ _ _ B E). reflexivity. 
            discriminate F. discriminate F. discriminate F. 
         discriminate C. discriminate C. discriminate C. 
Qed. 

Lemma ltr_product_is_right
      (RS : ltr_is_right LS S eqS ltrS)      
      (RT : ltr_is_right LT T eqT ltrT) : 
   ltr_is_right (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s t]. compute. rewrite RS, RT; auto. Qed. 

Lemma ltr_product_not_is_right_left
      (NRS : ltr_not_is_right LS S eqS ltrS) :
   ltr_not_is_right (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l s] A]. exists ((l, wLT), (s, wT)). compute. rewrite A; auto. Defined. 

Lemma ltr_product_not_is_right_right
      (NRT : ltr_not_is_right LT T eqT ltrT) :
   ltr_not_is_right (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l t] A]. exists ((wLS, l), (wS, t)). compute. rewrite A; auto.
       case_eq(eqS (ltrS wLS wS) wS); intro B; auto. 
Defined. 

Definition ltr_product_is_right_decidable 
      (DS : ltr_is_right_decidable LS S eqS ltrS)      
      (DT : ltr_is_right_decidable LT T eqT ltrT) : 
   ltr_is_right_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_is_right RS RT)
            | inr NRT => inr (ltr_product_not_is_right_right NRT)
            end 
| inr NRS => inr (ltr_product_not_is_right_left NRS)
end. 

  

Lemma ltr_product_left_cancellative
      (RS : ltr_left_cancellative LS S eqS ltrS)      
      (RT : ltr_left_cancellative LT T eqT ltrT) : 
   ltr_left_cancellative (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s1 t1] [s2 t2]. compute.
       case_eq(eqS (ltrS lS s1) (ltrS lS s2)); intro A; 
       case_eq(eqT (ltrT lT t1) (ltrT lT t2)); intro B; intro C.
          apply RS in A. apply RT in B. rewrite A, B; auto. 
          discriminate C. discriminate C. discriminate C. 
Qed.        

Lemma ltr_product_not_left_cancellative_left
      (NRS : ltr_not_left_cancellative LS S eqS ltrS) :
   ltr_not_left_cancellative (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l [s1 s2]] [A B]]. exists ((l, wLT), ((s1, wT), (s2, wT))). compute. 
       rewrite A, B. rewrite (refT (ltrT wLT wT)); auto.
Defined.        

Lemma ltr_product_not_left_cancellative_right
      (NRT : ltr_not_left_cancellative LT T eqT ltrT) :
   ltr_not_left_cancellative (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l [t1 t2]] [A B]]. exists ((wLS, l), ((wS, t1), (wS, t2))). compute. 
       rewrite A, B. rewrite (refS (ltrS wLS wS)); rewrite (refS wS); auto. 
Defined.        



Definition ltr_product_left_cancellative_decidable 
      (DS : ltr_left_cancellative_decidable LS S eqS ltrS)      
      (DT : ltr_left_cancellative_decidable LT T eqT ltrT) : 
   ltr_left_cancellative_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_left_cancellative RS RT)
            | inr NRT => inr (ltr_product_not_left_cancellative_right NRT)
            end 
| inr NRS => inr (ltr_product_not_left_cancellative_left NRS)
end. 


End Theory.

Section ACAS.


Definition ltr_product_proofs (LS S LT T: Type)
      (eqS : brel S) (eqLS : brel LS) (wS : S) (wLS : LS) (ltrS : left_transform LS S) (refS : brel_reflexive S eqS) (PS : ltr_proofs LS S eqS eqLS ltrS)
      (eqT : brel T) (eqLT : brel LT) (wT : T) (wLT : LT) (ltrT : left_transform LT T) (refT : brel_reflexive T eqT) (PT : ltr_proofs LT T eqT eqLT ltrT) :
              ltr_proofs (LS * LT) (S * T) (brel_product eqS eqT) (brel_product eqLS eqLT) (ltr_product ltrS ltrT) :=
{|
  A_ltr_congruence          := ltr_product_congruence LS S LT T eqS eqLS ltrS eqT eqLT ltrT
                                  (A_ltr_congruence LS S eqS eqLS ltrS PS)
                                  (A_ltr_congruence LT T eqT eqLT ltrT PT)                                                      
; A_ltr_is_right_d          := ltr_product_is_right_decidable LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT
                                  (A_ltr_is_right_d LS S eqS eqLS ltrS PS)
                                  (A_ltr_is_right_d LT T eqT eqLT ltrT PT)                                                      
; A_ltr_left_cancellative_d := ltr_product_left_cancellative_decidable LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT refS refT
                                  (A_ltr_left_cancellative_d LS S eqS eqLS ltrS PS)
                                  (A_ltr_left_cancellative_d LT T eqT eqLT ltrT PT)                                                        
|}.



End ACAS.

Section CAS.


Definition ltr_product_is_right_check {LS S LT T: Type} (wS : S) (wLS : LS) (wT : T) (wLT : LT) 
      (DS : @check_ltr_is_right LS S)      
      (DT : @check_ltr_is_right LT T) : 
            @check_ltr_is_right (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Is_Right =>
            match DT with
            | Certify_Ltr_Is_Right => Certify_Ltr_Is_Right
            | Certify_Ltr_Not_Is_Right (l, t)  => Certify_Ltr_Not_Is_Right ((wLS, l), (wS, t))
            end 
| Certify_Ltr_Not_Is_Right (l, s)  => Certify_Ltr_Not_Is_Right ((l, wLT), (s, wT))
end. 


Definition ltr_product_left_cancellative_check {LS S LT T: Type} (wS : S) (wLS : LS) (wT : T) (wLT : LT) 
      (DS : @check_ltr_left_cancellative LS S)      
      (DT : @check_ltr_left_cancellative LT T) : 
            @check_ltr_left_cancellative (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Left_Cancellative =>
            match DT with
            | Certify_Ltr_Left_Cancellative => Certify_Ltr_Left_Cancellative
            | Certify_Ltr_Not_Left_Cancellative (l, (t1, t2))  => Certify_Ltr_Not_Left_Cancellative ((wLS, l), ((wS, t1), (wS, t2)))
            end 
| Certify_Ltr_Not_Left_Cancellative (l, (s1, s2))  => Certify_Ltr_Not_Left_Cancellative ((l, wLT), ((s1, wT), (s2, wT)))
end. 



Definition ltr_product_certs {LS S LT T: Type}
      (wS : S) (wLS : LS) (PS : @ltr_certificates LS S)
      (wT : T) (wLT : LT) (PT : @ltr_certificates LT T) :
              @ltr_certificates (LS * LT) (S * T) :=
{|
  ltr_congruence_a          := Assert_Ltr_Congruence                                                       
; ltr_is_right_d := ltr_product_is_right_check wS wLS wT wLT 
                                  (ltr_is_right_d PS)
                                  (ltr_is_right_d PT)                                                      
; ltr_left_cancellative_d := ltr_product_left_cancellative_check wS wLS wT wLT 
                                  (ltr_left_cancellative_d PS)
                                  (ltr_left_cancellative_d PT)                                                        
|}.

  

End CAS.

Section Verify.

Lemma correct_ltr_product_certs (LS S LT T: Type)
      (eqS : brel S) (eqLS : brel LS) (wS : S) (wLS : LS) (ltrS : left_transform LS S) (refS : brel_reflexive S eqS) (PS : ltr_proofs LS S eqS eqLS ltrS)
      (eqT : brel T) (eqLT : brel LT) (wT : T) (wLT : LT) (ltrT : left_transform LT T) (refT : brel_reflexive T eqT) (PT : ltr_proofs LT T eqT eqLT ltrT) :
   ltr_product_certs wS wLS (P2C_ltr _ _ _ _ _ PS) wT wLT (P2C_ltr _ _ _ _ _ PT) 
   =
   P2C_ltr _ _ _ _ _ (ltr_product_proofs LS S LT T eqS eqLS wS wLS ltrS refS PS eqT eqLT wT wLT ltrT refT PT).
Proof. destruct PS. destruct PT. unfold ltr_product_certs, ltr_product_proofs, P2C_ltr; simpl. 
       destruct A_ltr_is_right_d as [IRS | [[lS s] A]];
       destruct A_ltr_is_right_d0 as [IRT | [[lT t] B]];
       destruct A_ltr_left_cancellative_d as [ILCS | [[l1 [s1 s2]] [C D]]];
       destruct A_ltr_left_cancellative_d0 as [ILCT | [[l2 [t1 t2]] [E F]]]; simpl; auto.          
Qed. 
End Verify.   
  