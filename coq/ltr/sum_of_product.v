Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.sum.


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

  C == + o x    (o is function composition) 

  C(f, g) : (A * C) -> (B + D) -> (B + D) 

  C(f, g)(a,c)(inl b) = inl(f a b) 
  C(f, g)(a,c)(inr d) = inr(g c d) 

*) 

Definition ltr_sum_of_product :
   ∀ {S LS T LT: Type}, left_transform LS S → left_transform LT T → left_transform (LS * LT) (S + T)
   := λ {S LS T LT} ltrS ltrT l d,  
     match l, d with
     | (l1, l2), inl s => inl (ltrS l1 s)
     | (l1, l2), inr t => inr (ltrT l2 t) 
     end.

Section Theory.

  Variable S LS T LT : Type.
  Variable eqS  : brel S.
  Variable eqT  : brel T.
  Variable ltrS : left_transform LS S.
  Variable ltrT : left_transform LT T.
  Variable bS_cong : ltr_partial_congruence LS S eqS ltrS.
  Variable bT_cong : ltr_partial_congruence LT T eqT ltrT.   
  
  Notation "a <+> b" := (brel_sum a b) (at level 15).
  Notation "a |*> b" := (ltr_sum_of_product a b) (at level 15). 

 Lemma ltr_sum_of_product_partial_congruence : ltr_partial_congruence (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. unfold ltr_congruence. intros [lS lT] [s1 | t1] [s2 | t2] K; compute in K; compute; auto. Qed.
  
 Lemma ltr_sum_of_product_is_right : ltr_is_right LS S eqS ltrS -> ltr_is_right LT T eqT ltrT -> ltr_is_right (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. intros HS HT. unfold ltr_is_right. intros [lS lT] [s | t]; compute; auto. Qed. 
 
 Lemma ltr_sum_of_product_not_is_right_left (lT : LT) : ltr_not_is_right LS S eqS ltrS -> ltr_not_is_right (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. unfold ltr_not_is_right. intros [[lS s] P]. exists ((lS, lT), inl (s)). compute; auto. Defined. 

 Lemma ltr_sum_of_product_not_is_right_right (lS : LS) : ltr_not_is_right LT T eqT ltrT -> ltr_not_is_right (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. unfold ltr_not_is_right. intros [[lT t] P]. exists ((lS, lT), inr (t)). compute; auto. Defined. 
 
 Lemma ltr_sum_of_product_cancellative : ltr_left_cancellative LS S eqS ltrS -> ltr_left_cancellative LT T eqT ltrT -> ltr_left_cancellative (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. intros HS HT. unfold ltr_left_cancellative. intros [lS lT] [s1 | t1] [s2 | t2]; compute; auto. apply HS. apply HT. Qed. 

 Lemma ltr_sum_of_product_not_cancellative_left (lT : LT) :
          ltr_not_left_cancellative LS S eqS ltrS -> ltr_not_left_cancellative (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. intros [[lS [s1 s2]] [P Q]]. exists ((lS, lT), (inl s1, inl s2)). compute; auto. Defined. 

  Lemma ltr_sum_of_product_not_cancellative_right (lS : LS) :
          ltr_not_left_cancellative LT T eqT ltrT -> ltr_not_left_cancellative (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. intros [[lT [t1 t2]] [P Q]]. exists ((lS, lT), (inr t1, inr t2)). compute; auto. Defined. 

 Lemma ltr_sum_of_product_exists_id : ltr_exists_id LS S eqS ltrS -> ltr_exists_id LT T eqT ltrT -> ltr_exists_id (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. intros [lS PS] [lT PT]. exists (lS, lT). intros [s | t]; compute; auto. Defined. 

 Lemma ltr_sum_of_product_not_exists_id_left : ltr_not_exists_id LS S eqS ltrS -> ltr_not_exists_id (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. unfold ltr_not_exists_id. intros H [lS lT]. destruct (H lS) as [s P]. exists (inl s). compute. auto.  Defined. 

 Lemma ltr_sum_of_product_not_exists_id_right : ltr_not_exists_id LT T eqT ltrT -> ltr_not_exists_id (LS * LT) (S + T) (eqS <+> eqT) (ltrS |*> ltrT).
 Proof. unfold ltr_not_exists_id. intros H [lS lT]. destruct (H lT) as [t P]. exists (inr t). compute. auto.  Defined. 

End Theory.

Section ACAS.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   

