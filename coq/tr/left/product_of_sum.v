Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.product.
(*
  f : X -> Y
  g : W -> Z 
 
  +(f, g) : (X + W) -> (Y + Z) 

  +(f, g)(inl x) = inl(f x)
  +(f, g)(inr w) = inr(g x)

  f : X -> Y
  g : W -> Z 

  x(f, g) : (X * W) ->  (Y * Z) 
  x(f, g))(a, b) = (f a, g b) 
  
  f : A -> B -> B 
  g : C -> D -> D 

  C == x o +    (o is function composition) 

  C(f, g) : (A + C) -> (B * D) -> (B * D) 

  C(f, g)(inl b)(a,c) = (f a b, c) 
  C(f, g)(inr d)(a,c) = (a, g d c) 

*) 

Definition ltr_product_of_sum :
   ∀ {S LS T LT: Type}, left_transform LS S → left_transform LT T → left_transform (LS + LT) (S * T)
   := λ {S LS T LT} ltrS ltrT l p,  
     match l, p with
     | inl lS, (s, t) => (ltrS lS s, t)
     | inr lT, (s, t) => (s, ltrT lT t)
     end.

Section Theory.

  Variable S LS T LT : Type.
  Variable eqS  : brel S.
  Variable eqT  : brel T.
  Variable refS : brel_reflexive S eqS.
  Variable refT : brel_reflexive T eqT. 
  Variable ltrS : left_transform LS S.
  Variable ltrT : left_transform LT T.
  Variable congS : ltr_partial_congruence LS S eqS ltrS.     
  Variable congT : ltr_partial_congruence LT T eqT ltrT.   

  Notation "a <*> b" := (brel_product a b) (at level 15).
  Notation "a |*> b" := (ltr_product_of_sum a b) (at level 15). 
  


(* Lemma ltr_product_of_sum_congruence : ltr_congruence S S eqS eqS (ltr_product_of_sum bS).
 Proof. unfold ltr_congruence. unfold ltr_product_of_sum. intros. apply bS_cong; auto. Qed.

 Lemma ltr_product_of_sum_partial_congruence : ltr_partial_congruence S S eqS (ltr_product_of_sum bS). 
 Proof. unfold ltr_congruence. intros s s1 s2 H.
        unfold ltr_product_of_sum. apply bS_cong; auto. 
 Qed.
 *)

  
 Lemma ltr_product_of_sum_is_right : ltr_is_right LS S eqS ltrS -> ltr_is_right LT T eqT ltrT -> ltr_is_right (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
 Proof. intros HS HT. unfold ltr_is_right. intros [lS | lT] [s t]; compute; auto.
        rewrite HS. apply refT.
        rewrite refS. apply HT. 
 Qed. 
 
 Lemma ltr_product_of_sum_not_is_right_left (t : T) : ltr_not_is_right LS S eqS ltrS -> ltr_not_is_right (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
 Proof. intros [[lS s] P]. exists (inl lS, (s, t)). compute; auto. rewrite P. auto. Defined. 

 Lemma ltr_product_of_sum_not_is_right_right (s : S) : ltr_not_is_right LT T eqT ltrT -> ltr_not_is_right (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
 Proof. intros [[lT t] P]. exists (inr lT, (s, t)). compute; auto. rewrite refS. exact P. Defined. 
 
 
 Lemma ltr_product_of_sum_cancellative :
   ltr_left_cancellative LS S eqS ltrS -> ltr_left_cancellative LT T eqT ltrT -> ltr_left_cancellative (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
 Proof. intros HS HT [lS | lT] [s1 t1] [s2 t2]; compute; auto.
        case_eq(eqS (ltrS lS s1) (ltrS lS s2)); intro J.
        apply HS in J. rewrite J. auto.
        case_eq(eqS s1 s2); intro K; auto.
        assert(F := congS lS s1 s2 K). 
        rewrite J in F. discriminate F. 
        case_eq(eqT (ltrT lT t1) (ltrT lT t2)); intro J.
        apply HT in J. rewrite J. auto.
        case_eq(eqS s1 s2); intro K; auto.
        intro F. discriminate F. 
Qed. 


Lemma ltr_product_of_sum_not_cancellative_left (t : T) :
          ltr_not_left_cancellative LS S eqS ltrS -> ltr_not_left_cancellative (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
Proof. intros [[lS [s1 s2]] [P Q]]. exists (inl lS, ((s1, t), (s2, t))). compute; auto. rewrite P. split; auto. rewrite Q. auto. Defined.
 
Lemma ltr_product_of_sum_not_cancellative_right (s : S) :
          ltr_not_left_cancellative LT T eqT ltrT -> ltr_not_left_cancellative (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
Proof. intros [[lT [t1 t2]] [P Q]]. exists (inr lT, ((s, t1), (s, t2))). compute; auto. rewrite refS. split; auto. Defined. 

(* Note: this "left id" is not always unique *) 
 Lemma ltr_product_of_sum_exists_id : ((ltr_exists_id LS S eqS ltrS) + (ltr_exists_id LT T eqT ltrT)) -> ltr_exists_id (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
 Proof. intros [[lS PS] | [lT PT]].
        exists (inl lS). intros [s t]; compute. rewrite PS. apply refT. 
        exists (inr lT). intros [s t]; compute. rewrite refS. apply PT. 
 Defined. 

 Lemma ltr_product_of_sum_not_exists_id_left (wS : S) (wT : T) :
   (ltr_not_exists_id LS S eqS ltrS) * (ltr_not_exists_id LT T eqT ltrT) -> ltr_not_exists_id (LS + LT) (S * T) (eqS <*> eqT) (ltrS |*> ltrT).
 Proof. intros [PS PT]. intros [lS | lT].
        destruct (PS lS) as [s QS]. exists (s, wT). compute. rewrite QS. auto.
        destruct (PT lT) as [t QT]. exists (wS, t). compute. rewrite refS. auto.        
 Defined. 


End Theory.

Section ACAS.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  