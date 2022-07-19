Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.product.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 



Section Theory. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.
Variable wS : S.
Variable wT : T.
Variable addS  mulS : binary_op S. 
Variable addT mulT : binary_op T. 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).



(* note : should be able to abstract away and universally quantfied predicate .... *) 

Lemma bop_product_left_distributive : 
      bop_left_distributive S rS addS mulS → 
      bop_left_distributive T rT addT mulT → 
         bop_left_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2] [s3 t3]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma bop_product_right_distributive : 
      bop_right_distributive S rS addS mulS → 
      bop_right_distributive T rT addT mulT → 
         bop_right_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros lrS lrT [s1 t1] [s2 t2] [s3 t3]. simpl. rewrite lrS, lrT.  simpl. reflexivity. Defined. 

Lemma bop_product_not_left_distributive_left : 
      bop_not_left_distributive S rS addS mulS → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl.        
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_distributive_right : 
      bop_not_left_distributive T rT addT mulT → 
         bop_not_left_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 

Lemma bop_product_not_right_distributive_left : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_distributive_right : 
      bop_not_right_distributive T rT addT mulT → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 

(* *******************


**************** *)






(* left left *) 
Lemma bop_product_left_left_absorptive : 
      bops_left_left_absorptive S rS addS mulS → 
      bops_left_left_absorptive T rT addT mulT → 
         bops_left_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma bop_product_not_left_left_absorptive_left : 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_left_left_absorptive_right : 
      bops_not_left_left_absorptive T rT addT mulT → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


(* left right *) 
Lemma bop_product_left_right_absorptive : 
      bops_left_right_absorptive S rS addS mulS → 
      bops_left_right_absorptive T rT addT mulT → 
         bops_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 

Lemma bop_product_not_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_left_right_absorptive_right : 
      bops_not_left_right_absorptive T rT addT mulT → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


(* strict absorption *)



Lemma bops_product_left_strictly_absorptive_v1 :
  bops_left_strictly_absorptive S rS addS mulS *
  bops_left_strictly_absorptive T rT addT mulT ->
  bops_left_strictly_absorptive (S * T) 
  (rS <*> rT) (addS [*] addT) (mulS [*] mulT).
Proof.
  intros (Ha, Hb) (sa, ta) (sb, tb).
  compute.
  destruct (Ha sa sb) as [Hc Hd]; compute.
  rewrite Hc, Hd; split.
  + apply Hb.
  + reflexivity. 
Defined.

Lemma bops_product_left_strictly_absorptive_v2 :
  bops_left_strictly_absorptive S rS addS mulS *
  bops_left_left_absorptive T rT addT mulT ->
  bops_left_strictly_absorptive (S * T) 
  (rS <*> rT) (addS [*] addT) (mulS [*] mulT).
Proof.
  intros (Ha, Hb) (sa, ta) (sb, tb).
  compute.
  destruct (Ha sa sb) as [Hc Hd]; compute.
  rewrite Hc, Hd; split.
  + apply Hb.
  + reflexivity. 
Defined.

Lemma bops_product_left_strictly_absorptive_v3 :
  bops_left_left_absorptive S rS addS mulS *
  bops_left_strictly_absorptive T rT addT mulT ->
  bops_left_strictly_absorptive (S * T) 
  (rS <*> rT) (addS [*] addT) (mulS [*] mulT).
Proof.
  intros (Ha, Hb) (sa, ta) (sb, tb).
  compute; split.
  + rewrite Ha. apply Hb.
  + destruct (rS (sa *S sb) (sa +S (sa *S sb)));
    [apply Hb | reflexivity].
Defined.



Lemma bops_product_not_left_strictly_absorptive :
  (bops_not_left_strictly_absorptive S rS addS mulS + 
  bops_not_left_strictly_absorptive T rT addT mulT) ->
  (bops_not_left_left_absorptive S rS addS mulS + 
  bops_not_left_strictly_absorptive T rT addT mulT) ->
  (bops_not_left_strictly_absorptive S rS addS mulS + 
  bops_not_left_left_absorptive T rT addT mulT) ->
  bops_not_left_strictly_absorptive (S * T) 
  (rS <*> rT) (addS [*] addT) (mulS [*] mulT).
Proof.
  intros [((s1, s2) & [Ha | Ha]) | ((t1, t2) & [Hb | Hb])]
  [((s3, s4) & Hc) | ((t3, t4) & [Hc | Hc])]
  [((s5, s6) & [Hd | Hd]) | ((t5, t6) & He)].
  +
    exists (s1, wT, (s2, wT));
    compute.
    left.
    rewrite Ha;
    reflexivity.
  + unfold bops_not_left_strictly_absorptive.
    exists (s1, wT, (s2, wT)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + unfold bops_not_left_strictly_absorptive.
    exists (s1, t5, (s2, t6)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s1, t3, (s2, t4)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s1, t3, (s2, t4)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s1, t3, (s2, t4)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s1, t3, (s2, t4)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s1, t3, (s2, t4)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s1, t3, (s2, t4)).
    compute.
    left.
    rewrite Ha.
    reflexivity.
  + exists (s3, wT, (s4, wT)).
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s3, wT, (s4, wT)).
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s3, wT, (s4, wT)).
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s5, wT, (s6, wT)).
    compute.
    left.
    rewrite Hd.
    reflexivity.
  + exists (wS, t3, (wS, t4)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS))); 
    [exact Hc | reflexivity].
  + exists (wS, t3, (wS, t4)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS))); 
    [exact Hc | reflexivity].
  + exists (s1, t3, (s2, t4)).
    compute.
    right.
    rewrite Ha.
    exact Hc.
  + exists (s1, t3, (s2, t4)).
    compute.
    right.
    rewrite Ha.
    exact Hc.
  + exists (s1, t3, (s2, t4)).
    compute.
    right.
    rewrite Ha.
    exact Hc.
  + exists (s3, t1, (s4, t2)).
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s3, t1, (s4, t2)).
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s3, t1, (s4, t2)).
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s5, t1, (s6, t2)).
    compute.
    left.
    rewrite Hd.
    reflexivity.  
  + exists (wS, t1, (wS, t2)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hb | reflexivity].
  + exists (wS, t1, (wS, t2)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hb | reflexivity].
  + exists (wS, t1, (wS, t2)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hb | reflexivity].
  + exists (wS, t1, (wS, t2)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hb | reflexivity].
  + exists (wS, t1, (wS, t2)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hb | reflexivity].
  + exists (s3, t1, (s4, t2));
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s3, t1, (s4, t2));
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s3, t1, (s4, t2));
    compute.
    left.
    rewrite Hc.
    reflexivity.
  + exists (s5, t1, (s6, t2));
    compute.
    left.
    rewrite Hd.
    reflexivity.
  + exists (s5, t1, (s6, t2));
    compute.
    right.
    rewrite Hd.
    exact Hb.
  + exists (wS, t3, (wS, t4));
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hc | reflexivity].
  + exists (s5, t3, (s6, t4));
    compute.
    left.
    rewrite Hd.
    reflexivity.
  + exists (s5, t3, (s6, t4));
    compute.
    right.
    rewrite Hd.
    exact Hc.
  + exists (wS, t5, (wS, t6)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact He | reflexivity].
  Qed. 


Lemma bops_product_not_left_strictly_absorptive :
  bops_not_left_left_absorptive S rS addS mulS + 
  bops_not_left_left_absorptive T rT addT mulT -> 
  bops_not_left_strictly_absorptive (S * T) 
  (rS <*> rT) (addS [*] addT) (mulS [*] mulT).
Proof.
  intros [((sa, sb) & Ha) | ((ta, tb) & Hb)].
  + exists (sa, wT, (sb, wT));
    compute.
    left.
    rewrite Ha;
    reflexivity.
  + exists (wS, ta, (wS, tb)).
    compute.
    left.
    case (rS wS (wS +S (wS *S wS)));
    [exact Hb | reflexivity].
Qed.







(* Strictly left right 

Lemma bop_product_strictly_left_right_absorptive : 
      bops_strictly_left_right_absorptive S rS addS mulS → 
      bops_strictly_left_right_absorptive T rT addT mulT → 
         bops_strictly_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. compute. 
       destruct (ldT t1 t2) as [A B].  rewrite A. rewrite B.
       destruct (ldS s1 s2) as [C D].  rewrite C. rewrite D. auto.        
Qed.

Lemma bop_product_strictly_left_right_absorptive_left : 
      bops_strictly_left_right_absorptive S rS addS mulS → 
      bops_left_right_absorptive T rT addT mulT → 
         bops_strictly_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldT.
       destruct (ldS s1 s2) as [A B].  rewrite A. rewrite B. compute. auto. 
Qed.

Lemma bop_product_strictly_left_right_absorptive_right : 
      bops_left_right_absorptive S rS addS mulS → 
      bops_strictly_left_right_absorptive T rT addT mulT → 
         bops_strictly_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS.
       destruct (ldT t1 t2) as [A B].  rewrite A. rewrite B. compute.
       case_eq(rS (s2 *S s1) (s1 +S (s2 *S s1))); intro C; auto. 
Qed.

Lemma bop_product_not_strictly_left_right_absorptive : 
      bops_not_strictly_left_right_absorptive S rS addS mulS →
      bops_not_strictly_left_right_absorptive T rT addT mulT →   
         bops_not_strictly_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ] [ [t1 t2] Q ].
       exists ((s1, t1), (s2, t2)). compute.
       destruct P as [P | P]; destruct Q as [Q | Q].
       + rewrite P. left; auto. 
       + rewrite P. left; auto. 
       + rewrite P. rewrite Q.
         case_eq(rS s1 (s1 +S (s2 *S s1))); intro H; left; auto. 
       + rewrite P, Q. right. auto. 
Defined. 




Lemma bop_product_not_strictly_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS →
         bops_not_strictly_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ].
       exists ((s1, wT), (s2, wT)). compute.
       rewrite P. left; auto. 
Defined. 

Lemma bop_product_not_strictly_left_right_absorptive_right : 
      bops_not_left_right_absorptive T rT addT mulT →
         bops_not_strictly_left_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ].
       exists ((wS, t1), (wS, t2)). compute.
       rewrite P.
       case_eq(rS wS (wS +S (wS *S wS))); intro Q; left; auto. 
Defined. 
*)

(* right left *) 
Lemma bop_product_right_left_absorptive : 
      bops_right_left_absorptive S rS addS mulS → 
      bops_right_left_absorptive T rT addT mulT → 
         bops_right_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 

Lemma bop_product_not_right_left_absorptive_left : 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_right_left_absorptive_right : 
      bops_not_right_left_absorptive T rT addT mulT → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ].  exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


(* right right *) 
Lemma bop_product_right_right_absorptive : 
      bops_right_right_absorptive S rS addS mulS → 
      bops_right_right_absorptive T rT addT mulT → 
         bops_right_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma bop_product_not_right_right_absorptive_left : 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_right_right_absorptive_right : 
      bops_not_right_right_absorptive T rT addT mulT → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined.


Definition bop_product_left_distributive_decide : 
     bop_left_distributive_decidable S rS addS mulS -> bop_left_distributive_decidable T rT addT mulT -> 
        bop_left_distributive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (bop_product_left_distributive ldS ldT)
     | inr nldT => inr _ (bop_product_not_left_distributive_right nldT)
     end 
   | inr nldS   => inr _ (bop_product_not_left_distributive_left nldS)
   end. 

Definition bop_product_right_distributive_decide : 
     bop_right_distributive_decidable S rS addS mulS -> bop_right_distributive_decidable T rT addT mulT -> 
       bop_right_distributive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (bop_product_right_distributive ldS ldT)
     | inr nldT => inr _ (bop_product_not_right_distributive_right nldT)
     end 
   | inr nldS   => inr _ (bop_product_not_right_distributive_left nldS)
   end. 
(*       
*) 

Definition bops_product_left_left_absorptive_decide : 
      bops_left_left_absorptive_decidable S rS addS mulS → bops_left_left_absorptive_decidable T rT addT mulT → 
         bops_left_left_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     => inl _ (bop_product_left_left_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_left_left_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_left_left_absorptive_left not_laS ) 
end. 


Definition bops_product_left_right_absorptive_decide : 
      bops_left_right_absorptive_decidable S rS addS mulS → bops_left_right_absorptive_decidable T rT addT mulT → 
         bops_left_right_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     => inl _ (bop_product_left_right_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_left_right_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_left_right_absorptive_left not_laS ) 
end. 

Definition bops_product_right_left_absorptive_decide : 
      bops_right_left_absorptive_decidable S rS addS mulS → bops_right_left_absorptive_decidable T rT addT mulT → 
         bops_right_left_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  inl _ (bop_product_right_left_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_right_left_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_right_left_absorptive_left not_laS ) 
end. 


Definition bops_product_right_right_absorptive_decide : 
      bops_right_right_absorptive_decidable S rS addS mulS → bops_right_right_absorptive_decidable T rT addT mulT → 
         bops_right_right_absorptive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  inl _ (bop_product_right_right_absorptive laS laT)
   |inr not_laT => inr _ (bop_product_not_right_right_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (bop_product_not_right_right_absorptive_left not_laS ) 
end.

End Theory.

Section ACAS.

Lemma bops_product_exists_id_ann_equal
        (S T : Type) (eqS : brel S) (eqT : brel T)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_product bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT). split.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
Defined. 


Lemma bops_product_exists_id_ann_not_equal_v1
        (S T : Type) (eqS : brel S) (eqT : brel T)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_not_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_product bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)). split. split. 
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_product_exists_id_ann_not_equal_v2
        (S T : Type) (eqS : brel S) (eqT : brel T)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_not_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_product bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)). split. split. 
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iT_not_aT.
       case_eq(eqS iS iS); intro A; reflexivity. 
Defined. 

Lemma bops_product_exists_id_ann_not_equal_v3
        (S T : Type) (eqS : brel S) (eqT : brel T)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_not_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_not_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_product bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)). split. split. 
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 



(*
*) 



Definition bops_product_exists_id_ann_decide
           (S T : Type) (eqS : brel S) (eqT : brel T)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T)           
           (PS : exists_id_ann_decidable S eqS bS1 bS2)
           (PT : exists_id_ann_decidable T eqT bT1 bT2) :
           exists_id_ann_decidable (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS1 bT1)
                                   (bop_product bS2 bT2) :=
let F0 := bop_product_exists_id S T eqS eqT bS1 bT1      in
let F1 := bop_product_not_exists_id S T eqS eqT bS1 bT1  in  

let F3 := bop_product_exists_ann S T eqS eqT bS2 bT2     in 
let F2 := bop_product_not_exists_ann S T eqS eqT bS2 bT2 in

let F4 := bops_product_exists_id_ann_equal S T eqS eqT bS1 bS2 bT1 bT2 in 
let F5 := bops_product_exists_id_ann_not_equal_v2 S T eqS eqT bS1 bS2 bT1 bT2 in 
let F6 := bops_product_exists_id_ann_not_equal_v1 S T eqS eqT bS1 bS2 bT1 bT2 in
let F7 := bops_product_exists_id_ann_not_equal_v3 S T eqS eqT bS1 bS2 bT1 bT2 in 

let E5 := extract_exist_id_from_exists_id_ann_equal S eqS bS1 bS2 in
let E1 := extract_exist_id_from_exists_id_ann_equal T eqT bT1 bT2 in 

let E6 := extract_exist_ann_from_exists_id_ann_equal S eqS bS1 bS2 in
let E3 := extract_exist_ann_from_exists_id_ann_equal T eqT bT1 bT2 in

let E7 := extract_exist_id_from_exists_id_ann_not_equal S eqS bS1 bS2 in
let E2 := extract_exist_id_from_exists_id_ann_not_equal T eqT bT1 bT2 in 

let E8 := extract_exist_ann_from_exists_id_ann_not_equal S eqS bS1 bS2 in 
let E4 := extract_exist_ann_from_exists_id_ann_not_equal T eqT bT1 bT2 in

match PS with 
| Id_Ann_Proof_None _ _ _ _ (nidS, nannS)               =>
     Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS), F2 (inl nannS))
| Id_Ann_Proof_Id_None _ _ _ _ (idS, nannS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inl nannS))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS idT, F2 (inl nannS))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inl nannS))                     
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS (E1 idT_annT_equal), F2 (inl nannS))              
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS (E2 idT_annT_not_equal), F2 (inl nannS))              
  end   
| Id_Ann_Proof_None_Ann _ _ _ _ (nidS, annS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS),F2 (inr nannT))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS), F2 (inr nannT))                         
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS annT)                      
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS (E3 idT_annT_equal))  
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS (E4 idT_annT_not_equal))   
  end   
| Id_Ann_Proof_Equal _ _ _ _ (idS_annS_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inr nannT))                      
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 (E5 idS_annS_equal) idT, F2 (inr nannT))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inr nidT), F3 (E6 idS_annS_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Equal _ _ _ _ (F4 idS_annS_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F5 idS_annS_equal idT_annT_not_equal)
  end   
| Id_Ann_Proof_Not_Equal _ _ _ _ (idS_annS_not_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inr nannT))             
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
    Id_Ann_Proof_Id_None _ _ _ _ (F0 (E7 idS_annS_not_equal) idT, F2 (inr nannT))                    
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inr nidT), F3 (E8 idS_annS_not_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F6 idS_annS_not_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F7 idS_annS_not_equal idT_annT_not_equal)
  end   
end. 





  
(* pay attention to order of arguement!  ;-) *) 
Definition id_ann_proofs_product
 (S T: Type) 
 (rS : brel S) 
 (rT : brel T) 
 (plusS timesS : binary_op S) 
 (plusT timesT : binary_op T)
 (pS : id_ann_proofs S rS plusS timesS)
 (pT : id_ann_proofs T rT plusT timesT) : 
        id_ann_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT) := 
let pS_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ _ pS in 
let pS_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ pS in 
let pT_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ _ pT in 
let pT_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ pT in 
{|
  A_id_ann_plus_times_d := bops_product_exists_id_ann_decide S T rS rT plusS timesS plusT timesT pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; A_id_ann_times_plus_d := bops_product_exists_id_ann_decide S T rS rT timesS plusS timesT plusT pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.



Definition dually_bounded_proofs_product
 (S T: Type) 
 (rS : brel S) 
 (rT : brel T) 
 (plusS timesS : binary_op S) 
 (plusT timesT : binary_op T)
 (pS : dually_bounded_proofs S rS plusS timesS)
 (pT : dually_bounded_proofs T rT plusT timesT) : 
        dually_bounded_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT) := 
let pS_id_ann_plus_times := A_bounded_plus_id_is_times_ann _ _ _ _ pS in 
let pS_id_ann_times_plus := A_bounded_times_id_is_plus_ann _ _ _ _ pS in 
let pT_id_ann_plus_times := A_bounded_plus_id_is_times_ann _ _ _ _ pT in 
let pT_id_ann_times_plus := A_bounded_times_id_is_plus_ann _ _ _ _ pT in 
{|
  A_bounded_plus_id_is_times_ann := bops_product_exists_id_ann_equal S T rS rT plusS timesS plusT timesT pS_id_ann_plus_times pT_id_ann_plus_times 
; A_bounded_times_id_is_plus_ann := bops_product_exists_id_ann_equal S T rS rT timesS plusS timesT plusT pS_id_ann_times_plus pT_id_ann_times_plus
|}.



Definition pid_is_tann_proofs_product
 (S T: Type) 
 (rS : brel S) 
 (rT : brel T) 
 (plusS timesS : binary_op S) 
 (plusT timesT : binary_op T)
 (pS : pid_is_tann_proofs S rS plusS timesS)
 (pT : pid_is_tann_proofs T rT plusT timesT) : 
        pid_is_tann_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT) := 
let pS_id_ann_plus_times := A_pid_is_tann_plus_times _ _ _ _ pS in 
let pS_id_ann_times_plus_d := A_pid_is_tann_times_plus_d _ _ _ _ pS in 
let pT_id_ann_plus_times := A_pid_is_tann_plus_times _ _ _ _ pT in 
let pT_id_ann_times_plus_d := A_pid_is_tann_times_plus_d _ _ _ _ pT in 
{|
  A_pid_is_tann_plus_times   := bops_product_exists_id_ann_equal S T rS rT plusS timesS plusT timesT pS_id_ann_plus_times pT_id_ann_plus_times 
; A_pid_is_tann_times_plus_d := bops_product_exists_id_ann_decide S T rS rT timesS plusS timesT plusT pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.


Definition pann_is_tid_proofs_product
 (S T: Type) 
 (rS : brel S) 
 (rT : brel T) 
 (plusS timesS : binary_op S) 
 (plusT timesT : binary_op T)
 (pS : pann_is_tid_proofs S rS plusS timesS)
 (pT : pann_is_tid_proofs T rT plusT timesT) : 
        pann_is_tid_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT) := 
let pS_id_ann_plus_times_d := A_pann_is_tid_plus_times_d _ _ _ _ pS in 
let pS_id_ann_times_plus := A_pann_is_tid_times_plus _ _ _ _ pS in 
let pT_id_ann_plus_times_d := A_pann_is_tid_plus_times_d _ _ _ _ pT in 
let pT_id_ann_times_plus := A_pann_is_tid_times_plus _ _ _ _ pT in 
{|
  A_pann_is_tid_plus_times_d := bops_product_exists_id_ann_decide S T rS rT plusS timesS plusT timesT pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; A_pann_is_tid_times_plus   := bops_product_exists_id_ann_equal S T rS rT timesS plusS timesT plusT pS_id_ann_times_plus pT_id_ann_times_plus
|}.


Definition bs_proofs_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T) (s : S) (t : T), 
     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 
        bs_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT s t pS pT, 
{|
  A_bs_left_distributive_d := 
     bop_product_left_distributive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_distributive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d := 
     bop_product_right_distributive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_right_distributive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d T rT plusT timesT pT)

; A_bs_left_left_absorptive_d := 
     bops_product_left_left_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_left_absorptive_d T rT plusT timesT pT)
; A_bs_left_right_absorptive_d := 
     bops_product_left_right_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_left_right_absorptive_d T rT plusT timesT pT)
; A_bs_right_left_absorptive_d := 
     bops_product_right_left_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d T rT plusT timesT pT)
; A_bs_right_right_absorptive_d := 
     bops_product_right_right_absorptive_decide S T rS rT s t plusS timesS plusT timesT
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d T rT plusT timesT pT)
|}. 




Definition dioid_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    dioid_proofs S rS addS mulS ->
    dioid_proofs T rT addT mulT ->     
        dioid_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT srS srT, 
{|
  A_dioid_left_distributive        :=
    bop_product_left_distributive S T rS rT addS mulS addT mulT  
        (A_dioid_left_distributive S rS addS mulS srS)
        (A_dioid_left_distributive T rT addT mulT srT)                                  
    
; A_dioid_right_distributive       :=
    bop_product_right_distributive S T rS rT addS mulS addT mulT  
        (A_dioid_right_distributive S rS addS mulS srS)
        (A_dioid_right_distributive T rT addT mulT srT)                                  

                                                                     
; A_dioid_left_left_absorptive   :=
    bop_product_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_dioid_left_left_absorptive S rS addS mulS srS)
        (A_dioid_left_left_absorptive T rT addT mulT srT)                                  

; A_dioid_left_right_absorptive  :=
    bop_product_left_right_absorptive S T rS rT addS mulS addT mulT
        (A_dioid_left_right_absorptive S rS addS mulS srS)
        (A_dioid_left_right_absorptive T rT addT mulT srT)                                  
|}.






Definition A_bs_product : ∀ (S T : Type),  A_bs S -> A_bs T -> A_bs (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_bs_eqv S bsS   in
let eqvT   := A_bs_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_bs_plus S bsS  in 
let plusT  := A_bs_plus T bsT  in
let timesS := A_bs_times S bsS in 
let timesT := A_bs_times T bsT in 
{| 
     A_bs_eqv        := A_eqv_product S T eqvS eqvT 
   ; A_bs_plus       := bop_product plusS plusT 
   ; A_bs_times      := bop_product timesS timesT 
   ; A_bs_plus_proofs := sg_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_proofs S bsS) 
                           (A_bs_plus_proofs T bsT) 
   ; A_bs_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_proofs S bsS) 
                           (A_bs_times_proofs T bsT)
   ; A_bs_id_ann_proofs := id_ann_proofs_product S T rS rT plusS timesS plusT timesT
                           (A_bs_id_ann_proofs S bsS) 
                           (A_bs_id_ann_proofs T bsT)                           
   ; A_bs_proofs    := bs_proofs_product S T rS rT plusS timesS plusT timesT s t 
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT)
   ; A_bs_ast        := Ast_bs_product(A_bs_ast S bsS, A_bs_ast T bsT)
|}.


Definition A_dioid_product : ∀ (S T : Type),  A_dioid S -> A_dioid T -> A_dioid (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_dioid_eqv S bsS   in
let eqvT   := A_dioid_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_dioid_plus S bsS  in 
let plusT  := A_dioid_plus T bsT  in
let timesS := A_dioid_times S bsS in 
let timesT := A_dioid_times T bsT in 
{| 
     A_dioid_eqv        := A_eqv_product S T eqvS eqvT 
   ; A_dioid_plus       := bop_product plusS plusT 
   ; A_dioid_times      := bop_product timesS timesT 
   ; A_dioid_plus_proofs := sg_CI_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_dioid_plus_proofs S bsS) 
                           (A_dioid_plus_proofs T bsT) 
   ; A_dioid_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_dioid_times_proofs S bsS) 
                           (A_dioid_times_proofs T bsT)
   ; A_dioid_id_ann_proofs := dually_bounded_proofs_product S T rS rT plusS timesS plusT timesT
                           (A_dioid_id_ann_proofs S bsS) 
                           (A_dioid_id_ann_proofs T bsT)                           
   ; A_dioid_proofs    := dioid_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT
                           (A_dioid_proofs S bsS) 
                           (A_dioid_proofs T bsT)
   ; A_dioid_ast        := Ast_bs_product (A_dioid_ast S bsS, A_dioid_ast T bsT)
|}. 



Definition A_dioid_product_from_selective_dioids : ∀ (S T : Type),  A_selective_dioid S -> A_selective_dioid T -> A_dioid (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_selective_dioid_eqv S bsS   in
let eqvT   := A_selective_dioid_eqv T bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_selective_dioid_plus S bsS  in 
let plusT  := A_selective_dioid_plus T bsT  in
let timesS := A_selective_dioid_times S bsS in 
let timesT := A_selective_dioid_times T bsT in 
{| 
     A_dioid_eqv        := A_eqv_product S T eqvS eqvT 
   ; A_dioid_plus       := bop_product plusS plusT 
   ; A_dioid_times      := bop_product timesS timesT 
   ; A_dioid_plus_proofs := sg_CI_proofs_product_from_sg_CS_proofs S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_selective_dioid_plus_proofs S bsS) 
                           (A_selective_dioid_plus_proofs T bsT) 
   ; A_dioid_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_selective_dioid_times_proofs S bsS) 
                           (A_selective_dioid_times_proofs T bsT)
   ; A_dioid_id_ann_proofs := dually_bounded_proofs_product S T rS rT plusS timesS plusT timesT
                           (A_selective_dioid_id_ann_proofs S bsS) 
                           (A_selective_dioid_id_ann_proofs T bsT)                           
   ; A_dioid_proofs    := dioid_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT
                           (A_selective_dioid_proofs S bsS) 
                           (A_selective_dioid_proofs T bsT)
   ; A_dioid_ast        := Ast_bs_product (A_selective_dioid_ast S bsS, A_selective_dioid_ast T bsT)
|}. 


Definition semiring_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    semiring_proofs S rS addS mulS ->
    semiring_proofs T rT addT mulT ->     
        semiring_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT srS srT, 
{|
  A_semiring_left_distributive        :=
    bop_product_left_distributive S T rS rT addS mulS addT mulT  
        (A_semiring_left_distributive S rS addS mulS srS)
        (A_semiring_left_distributive T rT addT mulT srT)                                  
    
; A_semiring_right_distributive       :=
    bop_product_right_distributive S T rS rT addS mulS addT mulT  
        (A_semiring_right_distributive S rS addS mulS srS)
        (A_semiring_right_distributive T rT addT mulT srT)                                  

                                                                     
; A_semiring_left_left_absorptive_d   :=
    bops_product_left_left_absorptive_decide S T rS rT s t addS mulS addT mulT
        (A_semiring_left_left_absorptive_d S rS addS mulS srS)
        (A_semiring_left_left_absorptive_d T rT addT mulT srT)                                  

; A_semiring_left_right_absorptive_d  :=
    bops_product_left_right_absorptive_decide S T rS rT s t addS mulS addT mulT
        (A_semiring_left_right_absorptive_d S rS addS mulS srS)
        (A_semiring_left_right_absorptive_d T rT addT mulT srT)                                  

|}.

Definition A_presemiring_product : ∀ (S T : Type),  A_presemiring S ->  A_presemiring T -> A_presemiring (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_presemiring_eqv S sr1   in
let eqvT   := A_presemiring_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_presemiring_plus S sr1  in 
let plusT  := A_presemiring_plus T sr2  in
let timesS := A_presemiring_times S sr1 in 
let timesT := A_presemiring_times T sr2 in 
{| 
     A_presemiring_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_presemiring_plus         := bop_product plusS plusT 
   ; A_presemiring_times        := bop_product timesS timesT 
   ; A_presemiring_plus_proofs  := sg_C_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                                (A_presemiring_plus_proofs S sr1)
                                (A_presemiring_plus_proofs T sr2)                                 
   ; A_presemiring_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                                (A_presemiring_times_proofs S sr1)
                                (A_presemiring_times_proofs T sr2)
   ; A_presemiring_id_ann_proofs := id_ann_proofs_product S T rS rT plusS timesS plusT timesT
                                   (A_presemiring_id_ann_proofs S sr1) 
                                   (A_presemiring_id_ann_proofs T sr2)                           
   ; A_presemiring_proofs       := semiring_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                                   (A_presemiring_proofs S sr1)
                                   (A_presemiring_proofs T sr2)
   ; A_presemiring_ast       := Ast_bs_product (A_presemiring_ast S sr1, A_presemiring_ast T sr2)
|}.


Definition A_semiring_product : ∀ (S T : Type),  A_semiring S ->  A_semiring T -> A_semiring (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_semiring_eqv S sr1   in
let eqvT   := A_semiring_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_semiring_plus S sr1  in 
let plusT  := A_semiring_plus T sr2  in
let timesS := A_semiring_times S sr1 in 
let timesT := A_semiring_times T sr2 in 
{| 
     A_semiring_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_semiring_plus         := bop_product plusS plusT 
   ; A_semiring_times        := bop_product timesS timesT 
   ; A_semiring_plus_proofs  := sg_C_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                                (A_semiring_plus_proofs S sr1)
                                (A_semiring_plus_proofs T sr2)                                 
   ; A_semiring_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                                (A_semiring_times_proofs S sr1)
                                (A_semiring_times_proofs T sr2)
   ; A_semiring_id_ann_proofs := pid_is_tann_proofs_product S T rS rT plusS timesS plusT timesT
                                   (A_semiring_id_ann_proofs S sr1) 
                                   (A_semiring_id_ann_proofs T sr2)                           
   ; A_semiring_proofs       := semiring_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                                   (A_semiring_proofs S sr1)
                                   (A_semiring_proofs T sr2)
   ; A_semiring_ast       := Ast_bs_product (A_semiring_ast S sr1, A_semiring_ast T sr2)
|}.


Definition distributive_lattice_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    distributive_lattice_proofs S rS addS mulS ->
    distributive_lattice_proofs T rT addT mulT ->     
        distributive_lattice_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT eqvS eqvT srS srT, 
{|
  A_distributive_lattice_absorptive        := 
    bop_product_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_distributive_lattice_absorptive S rS addS mulS srS)
        (A_distributive_lattice_absorptive T rT addT mulT srT)                                  
                                     
; A_distributive_lattice_absorptive_dual   :=
    bop_product_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_distributive_lattice_absorptive_dual S rS addS mulS srS)
        (A_distributive_lattice_absorptive_dual T rT addT mulT srT)                                  

    
; A_distributive_lattice_distributive        :=
    bop_product_left_distributive S T rS rT addS mulS addT mulT  
        (A_distributive_lattice_distributive S rS addS mulS srS)
        (A_distributive_lattice_distributive T rT addT mulT srT)                                  
    
|}.

Definition A_distributive_lattice_product : ∀ (S T : Type),  A_distributive_lattice S ->  A_distributive_lattice T -> A_distributive_lattice (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_distributive_lattice_eqv S sr1   in
let eqvT   := A_distributive_lattice_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let joinS  := A_distributive_lattice_join S sr1  in 
let joinT  := A_distributive_lattice_join T sr2  in
let meetS  := A_distributive_lattice_meet S sr1 in 
let meetT  := A_distributive_lattice_meet T sr2 in 
{| 
     A_distributive_lattice_eqv   := A_eqv_product S T eqvS eqvT 
   ; A_distributive_lattice_join  := bop_product joinS joinT 
   ; A_distributive_lattice_meet  := bop_product meetS meetT 
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_product S T rS rT joinS joinT s f t g Pf Pg peqvS peqvT  
                                (A_distributive_lattice_join_proofs S sr1)
                                (A_distributive_lattice_join_proofs T sr2)                                 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_product S T rS rT meetS meetT s f t g Pf Pg peqvS peqvT  
                                (A_distributive_lattice_meet_proofs S sr1)
                                (A_distributive_lattice_meet_proofs T sr2)
   ; A_distributive_lattice_id_ann_proofs := dually_bounded_proofs_product S T rS rT joinS meetS joinT meetT 
                                   (A_distributive_lattice_id_ann_proofs S sr1) 
                                   (A_distributive_lattice_id_ann_proofs T sr2)                           
   ; A_distributive_lattice_proofs  := distributive_lattice_proofs_product S T rS rT joinS meetS joinT meetT peqvS peqvT  
                                   (A_distributive_lattice_proofs S sr1)
                                   (A_distributive_lattice_proofs T sr2)
   ; A_distributive_lattice_ast  := Ast_bs_product (A_distributive_lattice_ast S sr1, A_distributive_lattice_ast T sr2)
|}.


Definition lattice_proofs_product : 
  ∀ (S T : Type) (rS : brel S) (rT : brel T) (addS mulS : binary_op S) (addT mulT : binary_op T) (s : S) (t : T), 
    eqv_proofs S rS ->
    eqv_proofs T rT -> 
    lattice_proofs S rS addS mulS ->
    lattice_proofs T rT addT mulT ->     
        lattice_proofs (S * T) (brel_product rS rT) (bop_product addS addT) (bop_product mulS mulT)
:= λ S T rS rT addS mulS addT mulT s t eqvS eqvT srS srT, 
{|
  A_lattice_absorptive        := 
    bop_product_left_left_absorptive S T rS rT addS mulS addT mulT
        (A_lattice_absorptive S rS addS mulS srS)
        (A_lattice_absorptive T rT addT mulT srT)                                  
                                     
; A_lattice_absorptive_dual   :=
    bop_product_left_left_absorptive S T rS rT mulS addS mulT addT
        (A_lattice_absorptive_dual S rS addS mulS srS)
        (A_lattice_absorptive_dual T rT addT mulT srT)                                  

    
; A_lattice_distributive_d        :=
     bop_product_left_distributive_decide S T rS rT s t addS mulS addT mulT 
        (A_lattice_distributive_d S rS addS mulS srS)
        (A_lattice_distributive_d T rT addT mulT  srT)

; A_lattice_distributive_dual_d        :=
     bop_product_left_distributive_decide S T rS rT s t mulS addS mulT addT 
        (A_lattice_distributive_dual_d S rS addS mulS srS)
        (A_lattice_distributive_dual_d T rT addT mulT  srT)
        
|}.


Definition A_lattice_product : ∀ (S T : Type),  A_lattice S ->  A_lattice T -> A_lattice (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_lattice_eqv S sr1   in
let eqvT   := A_lattice_eqv T sr2   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let joinS  := A_lattice_join S sr1  in 
let joinT  := A_lattice_join T sr2  in
let meetS  := A_lattice_meet S sr1 in 
let meetT  := A_lattice_meet T sr2 in 
{| 
     A_lattice_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_lattice_join         := bop_product joinS joinT 
   ; A_lattice_meet         := bop_product meetS meetT 
   ; A_lattice_join_proofs  := sg_CI_proofs_product S T rS rT joinS joinT s f t g Pf Pg peqvS peqvT  
                                (A_lattice_join_proofs S sr1)
                                (A_lattice_join_proofs T sr2)                                 
   ; A_lattice_meet_proofs := sg_CI_proofs_product S T rS rT meetS meetT s f t g Pf Pg peqvS peqvT  
                                (A_lattice_meet_proofs S sr1)
                                (A_lattice_meet_proofs T sr2)
   ; A_lattice_id_ann_proofs := dually_bounded_proofs_product S T rS rT joinS meetS joinT meetT 
                                   (A_lattice_id_ann_proofs S sr1) 
                                   (A_lattice_id_ann_proofs T sr2)                           
   ; A_lattice_proofs  := lattice_proofs_product S T rS rT joinS meetS joinT meetT s t peqvS peqvT  
                                   (A_lattice_proofs S sr1)
                                   (A_lattice_proofs T sr2)
   ; A_lattice_ast  := Ast_bs_product (A_lattice_ast S sr1, A_lattice_ast T sr2)
|}.

End ACAS.

Section AMCAS.

Open Scope list_scope.
Open Scope string_scope.     

Definition A_mcas_bs_product (S T : Type) (A : A_bs_mcas S) (B : A_bs_mcas T) : A_bs_mcas (S * T)  := 
  match A_bs_mcas_cast_up _ A, A_bs_mcas_cast_up _ B  with
  | A_BS_bs _ C, A_BS_bs _ D            => A_bs_classify _ (A_BS_bs _ (A_bs_product _ _ C D))
  | A_BS_Error _ sl1,  A_BS_Error _ sl2 => A_BS_Error _ (sl1 ++ sl2) 
  | _,  A_BS_Error _ sl2                => A_BS_Error _ sl2
  | A_BS_Error _ sl1, _                 => A_BS_Error _ sl1                                       
  | _, _ => A_BS_Error _ ("internal error : A_bs_mcas_product" :: nil) 
  end.
    
End AMCAS.   



Section CAS.

Definition bop_product_left_distributive_check : 
   ∀ {S T : Type},  
     S -> 
     T -> 
     @check_left_distributive S -> 
     @check_left_distributive T -> 
     @check_left_distributive (S * T) 
:= λ {S T} s t dS dT,  
   match dS with 
   | Certify_Left_Distributive => 
     match dT with 
     | Certify_Left_Distributive => Certify_Left_Distributive 
     | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive ((s1, t), ((s2, t), (s3, t)))
   end.

Definition bop_product_right_distributive_check : 
   ∀ {S T : Type},  
     S -> 
     T -> 
     @check_right_distributive S -> 
     @check_right_distributive T -> 
     @check_right_distributive (S * T) 
:= λ {S T} s t dS dT,  
   match dS with 
   | Certify_Right_Distributive => 
     match dT with 
     | Certify_Right_Distributive => Certify_Right_Distributive  
     | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((s, t1), ((s, t2), (s, t3))) 
     end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, t), ((s2, t), (s3, t)))
   end.



Definition bop_product_left_left_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_left_left_absorptive S -> 
     @check_left_left_absorptive T -> 
     @check_left_left_absorptive (S * T) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive  
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
          Certify_Not_Left_Left_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_left_right_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_left_right_absorptive S -> 
     @check_left_right_absorptive T -> 
     @check_left_right_absorptive (S * T)
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive  
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
          Certify_Not_Left_Right_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_right_left_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_right_left_absorptive S -> 
     @check_right_left_absorptive T -> 
     @check_right_left_absorptive (S * T)
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive  
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
          Certify_Not_Right_Left_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive  ((s1, t), (s2, t))
end. 

Definition bop_product_right_right_absorptive_check : 
   ∀ {S T : Type} (s : S) (t : T),  
     @check_right_right_absorptive S -> 
     @check_right_right_absorptive T -> 
     @check_right_right_absorptive (S * T) 
:= λ {S T} s t dS dT,  
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive  
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
          Certify_Not_Right_Right_Absorptive  ((s, t1), (s, t2))
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive  ((s1, t), (s2, t))
end.




Definition bops_product_exists_id_ann_certify
           {S T : Type} 
           (PS : @exists_id_ann_certificate S)
           (PT : @exists_id_ann_certificate T) :
             @exists_id_ann_certificate (S * T) := 
match PS with 
| Id_Ann_Cert_None         => Id_Ann_Cert_None 
| Id_Ann_Cert_Id_None idS  =>
  match PT with 
  | Id_Ann_Cert_None               => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT        => Id_Ann_Cert_Id_None (idS, idT) 
  | Id_Ann_Cert_None_Ann annT      => Id_Ann_Cert_None 
  | Id_Ann_Cert_Equal idT_annT     => Id_Ann_Cert_Id_None (idS, idT_annT) 
  | Id_Ann_Cert_Not_Equal (idT, _) => Id_Ann_Cert_Id_None (idS, idT) 
  end   
| Id_Ann_Cert_None_Ann annS =>
  match PT with 
  | Id_Ann_Cert_None                  => Id_Ann_Cert_None
  | Id_Ann_Cert_Id_None idT           => Id_Ann_Cert_None
  | Id_Ann_Cert_None_Ann annT         => Id_Ann_Cert_None_Ann (annS, annT) 
  | Id_Ann_Cert_Equal (idT_annT)     => Id_Ann_Cert_None_Ann (annS, idT_annT) 
  | Id_Ann_Cert_Not_Equal (_, annT)   => Id_Ann_Cert_None_Ann (annS, annT) 
  end   
| Id_Ann_Cert_Equal idS_annS  =>
  match PT with 
  | Id_Ann_Cert_None                  => Id_Ann_Cert_None
  | Id_Ann_Cert_Id_None idT           => Id_Ann_Cert_Id_None (idS_annS, idT)
  | Id_Ann_Cert_None_Ann annT         => Id_Ann_Cert_None_Ann (idS_annS, annT) 
  | Id_Ann_Cert_Equal idT_annT        => Id_Ann_Cert_Equal (idS_annS, idT_annT) 
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Not_Equal ((idS_annS, idT), (idS_annS, annT))
  end   
| Id_Ann_Cert_Not_Equal (idS, annS)  =>
  match PT with 
  | Id_Ann_Cert_None                  => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT           => Id_Ann_Cert_Id_None (idS, idT) 
  | Id_Ann_Cert_None_Ann annT         => Id_Ann_Cert_None_Ann (annS, annT)
  | Id_Ann_Cert_Equal idT_annT        => Id_Ann_Cert_Not_Equal ((idS, idT_annT), (annS, idT_annT))
  | Id_Ann_Cert_Not_Equal (idT,annT)  => Id_Ann_Cert_Not_Equal ((idS, idT), (annS, annT))
  end   
end. 


Definition id_ann_certs_product 
  {S T: Type}
  (pS : @id_ann_certificates S) 
  (pT : @id_ann_certificates T) : 
        @id_ann_certificates (S * T) := 
let pS_id_ann_plus_times_d := id_ann_plus_times_d pS in 
let pS_id_ann_times_plus_d := id_ann_times_plus_d pS in 
let pT_id_ann_plus_times_d := id_ann_plus_times_d pT in 
let pT_id_ann_times_plus_d := id_ann_times_plus_d pT in 
{|
  id_ann_plus_times_d := bops_product_exists_id_ann_certify pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; id_ann_times_plus_d := bops_product_exists_id_ann_certify pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.

Definition dually_bounded_certs_product 
  {S T: Type}
  (pS : @dually_bounded_certificates S)
  (pT : @dually_bounded_certificates T) : 
        @dually_bounded_certificates (S * T) := 
{|
  bounded_plus_id_is_times_ann :=
    match bounded_plus_id_is_times_ann pS, bounded_plus_id_is_times_ann pT with
    | Assert_Exists_Id_Ann_Equal s, Assert_Exists_Id_Ann_Equal t => Assert_Exists_Id_Ann_Equal (s, t)
   end                                                                                                
; bounded_times_id_is_plus_ann :=
    match bounded_times_id_is_plus_ann pS, bounded_times_id_is_plus_ann pT with
    | Assert_Exists_Id_Ann_Equal s, Assert_Exists_Id_Ann_Equal t => Assert_Exists_Id_Ann_Equal (s, t)
   end                                                                                                
|}. 

Definition pid_is_tann_certs_product
 {S T: Type}
 (pS : @pid_is_tann_certificates S)
 (pT : @pid_is_tann_certificates T) : 
         @pid_is_tann_certificates (S * T) := 
let pS_id_ann_plus_times   := pid_is_tann_plus_times pS in 
let pS_id_ann_times_plus_d := pid_is_tann_times_plus_d pS in 
let pT_id_ann_plus_times   := pid_is_tann_plus_times pT in 
let pT_id_ann_times_plus_d := pid_is_tann_times_plus_d pT in 
{|
  pid_is_tann_plus_times   :=
    match pS_id_ann_plus_times,  pT_id_ann_plus_times with
    | Assert_Exists_Id_Ann_Equal s, Assert_Exists_Id_Ann_Equal t => Assert_Exists_Id_Ann_Equal (s, t)
   end                                                                                                
; pid_is_tann_times_plus_d :=bops_product_exists_id_ann_certify pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.

Definition pann_is_tid_certs_product
 {S T: Type}
 (pS : @pann_is_tid_certificates S)
 (pT : @pann_is_tid_certificates T) : 
        @pann_is_tid_certificates (S * T) := 
let pS_id_ann_plus_times_d := pann_is_tid_plus_times_d pS in 
let pS_id_ann_times_plus := pann_is_tid_times_plus pS in 
let pT_id_ann_plus_times_d := pann_is_tid_plus_times_d pT in 
let pT_id_ann_times_plus := pann_is_tid_times_plus pT in 
{|
  pann_is_tid_plus_times_d := bops_product_exists_id_ann_certify pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; pann_is_tid_times_plus   :=
    match pS_id_ann_times_plus, pT_id_ann_times_plus with
    | Assert_Exists_Id_Ann_Equal s, Assert_Exists_Id_Ann_Equal t => Assert_Exists_Id_Ann_Equal (s, t)
   end                                                                                                
      
|}.



Definition bs_certs_product : 
  ∀ {S T : Type}, 
        S -> T -> @bs_certificates S -> @bs_certificates T -> @bs_certificates (S * T) 
:= λ {S T} s t bsS bsT, 
{|
  bs_left_distributive_d      := bop_product_left_distributive_check s t
                                     (bs_left_distributive_d bsS)
                                     (bs_left_distributive_d bsT)
; bs_right_distributive_d     := bop_product_right_distributive_check s t
                                     (bs_right_distributive_d bsS)
                                     (bs_right_distributive_d bsT)
; bs_left_left_absorptive_d   := bop_product_left_left_absorptive_check s t 
                                     (bs_left_left_absorptive_d bsS)
                                     (bs_left_left_absorptive_d bsT)
; bs_left_right_absorptive_d  := bop_product_left_right_absorptive_check s t 
                                     (bs_left_right_absorptive_d bsS)
                                     (bs_left_right_absorptive_d bsT)
; bs_right_left_absorptive_d  := bop_product_right_left_absorptive_check s t
                                     (bs_right_left_absorptive_d bsS)
                                     (bs_right_left_absorptive_d bsT)
; bs_right_right_absorptive_d := bop_product_right_right_absorptive_check s t
                                     (bs_right_right_absorptive_d bsS)
                                     (bs_right_right_absorptive_d bsT)

|}.

Definition bs_product : ∀ {S T : Type},  @bs S -> @bs T -> @bs (S * T)
:= λ {S T} bsS bsT, 
   {| 
     bs_eqv         := eqv_product (bs_eqv bsS) (bs_eqv bsT) 
   ; bs_plus        := bop_product (bs_plus bsS) (bs_plus bsT) 
   ; bs_times       := bop_product (bs_times bsS) (bs_times bsT) 
   ; bs_plus_certs  := sg_certs_product (eqv_witness (bs_eqv bsS)) (eqv_witness (bs_eqv bsT)) (bs_plus_certs bsS) (bs_plus_certs bsT) 
   ; bs_times_certs := sg_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_times_certs bsS) 
                           (bs_times_certs bsT)
   ; bs_id_ann_certs := id_ann_certs_product (bs_id_ann_certs bsS) (bs_id_ann_certs bsT)
   ; bs_certs       := bs_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_certs bsS) 
                           (bs_certs bsT)
   ; bs_ast        := Ast_bs_product(bs_ast bsS, bs_ast bsT)
   |}. 


Definition semiring_certs_product : 
  ∀ {S T : Type}, S -> T -> @semiring_certificates S -> @semiring_certificates T ->  @semiring_certificates (S * T)
:= λ {S T} s t srS srT, 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_left_left_absorptive_d   := bop_product_left_left_absorptive_check s t
                                         (semiring_left_left_absorptive_d srS)
                                         (semiring_left_left_absorptive_d srT)
; semiring_left_right_absorptive_d  := bop_product_left_right_absorptive_check s t 
                                         (semiring_left_right_absorptive_d srS)
                                         (semiring_left_right_absorptive_d srT)   
|}.


(*
Definition presemiring_product : ∀ {S T : Type},  @presemiring S ->  @presemiring T -> @presemiring (S * T)
:= λ S T s1 s2,
let wS := eqv_witness (presemiring_eqv s1) in
let wT := eqv_witness (presemiring_eqv s2) in
let fS := eqv_new (presemiring_eqv s1) in
let fT := eqv_new (presemiring_eqv s2) in
let eqS := eqv_eq (presemiring_eqv s1) in
let eqT := eqv_eq (presemiring_eqv s2) in
let addS := presemiring_plus s1 in
let mulS := presemiring_times s1 in
let addT := presemiring_plus s2 in 
let mulT := presemiring_times s2 in 
{| 
     presemiring_eqv          := eqv_product (presemiring_eqv s1) (presemiring_eqv s2) 
   ; presemiring_plus         := bop_product addS addT
   ; presemiring_times        := bop_product mulS mulT
   ; presemiring_plus_certs   := sg_C_certs_product eqS eqT addS addT wS fS wT fT (presemiring_plus_certs s1) (presemiring_plus_certs s2) 
   ; presemiring_times_certs  := sg_certs_product wS wT (presemiring_times_certs s1) (presemiring_times_certs s2)
   ; presemiring_id_ann_certs := id_ann_certs_product (presemiring_id_ann_certs s1) (presemiring_id_ann_certs s2) 
   ; presemiring_certs        := semiring_certs_product wS wT (presemiring_certs s1) (presemiring_certs s2)
   ; presemiring_ast          := Ast_bs_product (presemiring_ast s1, presemiring_ast s2)
|}.


Definition semiring_product : ∀ {S T : Type},  @semiring S ->  @semiring T -> @semiring (S * T)
:= λ S T s1 s2,
let wS := eqv_witness (semiring_eqv s1) in
let wT := eqv_witness (semiring_eqv s2) in
let fS := eqv_new (semiring_eqv s1) in
let fT := eqv_new (semiring_eqv s2) in
let eqS := eqv_eq (semiring_eqv s1) in
let eqT := eqv_eq (semiring_eqv s2) in
let addS := semiring_plus s1 in
let mulS := semiring_times s1 in
let addT := semiring_plus s2 in
let mulT := semiring_times s2 in 
{| 
     semiring_eqv          := eqv_product (semiring_eqv s1) (semiring_eqv s2) 
   ; semiring_plus         := bop_product addS addT
   ; semiring_times        := bop_product mulS mulT
   ; semiring_plus_certs   := sg_C_certs_product eqS eqT addS addT wS fS wT fT (semiring_plus_certs s1) (semiring_plus_certs s2) 
   ; semiring_times_certs  := sg_certs_product wS wT (semiring_times_certs s1) (semiring_times_certs s2)
   ; semiring_id_ann_certs := pid_is_tann_certs_product (semiring_id_ann_certs s1) (semiring_id_ann_certs s2)        
   ; semiring_certs        := semiring_certs_product wS wT (semiring_certs s1) (semiring_certs s2)
   ; semiring_ast          := Ast_bs_product (semiring_ast s1, semiring_ast s2)
|}.

*)

Definition dioid_certs_product {S T : Type} (CS: @dioid_certificates S) (CT : @dioid_certificates T) : 
        @dioid_certificates (S * T) := 
{|
  dioid_left_distributive      := Assert_Left_Distributive  
; dioid_right_distributive     := Assert_Right_Distributive 
; dioid_left_left_absorptive   := Assert_Left_Left_Absorptive  
; dioid_left_right_absorptive  := Assert_Left_Right_Absorptive 
|}.


(*
Definition pre_dioid_product {S T : Type} :  @pre_dioid S -> @pre_dioid T -> @pre_dioid_NS (S * T) 
:= λ bsS bsT,
let eqvS   := pre_dioid_eqv bsS   in
let eqvT   := pre_dioid_eqv bsT   in
let rS     := eqv_eq eqvS in 
let rT     := eqv_eq eqvT in 
let s      := eqv_witness eqvS in
let f      := eqv_new eqvS in
let t      := eqv_witness eqvT in
let g      := eqv_new eqvT in
let plusS  := pre_dioid_plus bsS  in 
let plusT  := pre_dioid_plus bsT  in
let timesS := pre_dioid_times bsS in 
let timesT := pre_dioid_times bsT in 
{| 
     pre_dioid_NS_eqv        := eqv_product eqvS eqvT 
   ; pre_dioid_NS_plus       := bop_product plusS plusT 
   ; pre_dioid_NS_times      := bop_product timesS timesT 
   ; pre_dioid_NS_plus_certs := sg_CI_to_CINS_certs_product rS rT plusS plusT s f t g 
                           (pre_dioid_plus_certs bsS) 
                           (pre_dioid_plus_certs bsT) 
   ; pre_dioid_NS_times_certs := msg_certs_product s t 
                           (pre_dioid_times_certs bsS) 
                           (pre_dioid_times_certs bsT)
   ; pre_dioid_NS_id_ann_certs := id_ann_certs_product 
                           (pre_dioid_id_ann_certs bsS) 
                           (pre_dioid_id_ann_certs bsT)                           
   ; pre_dioid_NS_certs    := dioid_certs_product 
                                        (pre_dioid_certs bsS) 
                                       (pre_dioid_certs bsT)
   ; pre_dioid_NS_ast        := Ast_bs_product(pre_dioid_ast bsS, pre_dioid_ast bsT) (* FIX *) 
|}. 
*) 

  
End CAS.

Section MCAS.

Open Scope list_scope.
Open Scope string_scope.     

Definition mcas_bs_product {S T : Type} (A : @bs_mcas S) (B : @bs_mcas T) : @bs_mcas (S * T)  := 
  match bs_mcas_cast_up A, bs_mcas_cast_up B  with
  | BS_bs C, BS_bs D            => bs_classify (BS_bs (bs_product C D))
  | BS_Error sl1,  BS_Error sl2 => BS_Error (sl1 ++ sl2) 
  | _,  BS_Error sl2            => BS_Error sl2
  | BS_Error sl1, _             => BS_Error sl1                                       
  | _, _                        => BS_Error ("internal error : A_bs_mcas_product" :: nil) 
  end.
    
End MCAS.   
  


Section Verify.


Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable plusS timesS : binary_op S.
  Variable plusT timesT : binary_op T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma bop_product_left_distributive_check_correct : 
  ∀ (pS_d : bop_left_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_left_distributive_decidable T rT plusT timesT), 
     bop_product_left_distributive_check wS wT  
       (p2c_left_distributive S rS plusS timesS pS_d)
       (p2c_left_distributive T rT plusT timesT pT_d)
     = 
     @p2c_left_distributive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bop_product_left_distributive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 [s2 s3]] nldS]] [ ldT | [ [t1 [t2 t3]] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_right_distributive_check_correct : 
  ∀ (pS_d : bop_right_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_right_distributive_decidable T rT plusT timesT), 
   bop_product_right_distributive_check wS wT 
       (p2c_right_distributive S rS plusS timesS pS_d)
       (p2c_right_distributive T rT plusT timesT pT_d)
     = 
     p2c_right_distributive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bop_product_right_distributive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros 
       [ ldS | [ [s1 [s2 s3]] nldS]] 
       [ ldT | [ [t1 [t2 t3]] nldT]]; compute; reflexivity. 
Qed. 


(*
Lemma bop_product_plus_id_is_times_ann_assert_correct : 
  ∀ (pS_d : bops_id_equals_ann S rS plusS timesS)
     (pT_d : bops_id_equals_ann T rT plusT timesT), 
   p2c_plus_id_equals_times_ann_assert (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann S T rS rT plusS timesS plusT timesT pS_d pT_d)
   =
   bop_product_plus_id_equals_times_ann_assert
      (p2c_plus_id_equals_times_ann_assert S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann_assert T rT plusT timesT pT_d). 
Proof. intros [iS [piS paS]] [iT [piT paT]]; compute; reflexivity. Qed. 



Lemma bop_product_plus_id_is_times_ann_check_correct : 
  ∀ (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
     (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT pS_d pT_d)
   =
   bop_product_plus_id_equals_times_ann_check 
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros [ [iS [piS paS]] | neqS] [[iT [piT paT]] | neqT]; compute; reflexivity. Qed.


Lemma bop_product_times_id_is_plus_ann_assert_correct : 
  ∀ (pS_d : bops_id_equals_ann S rS timesS plusS)
     (pT_d : bops_id_equals_ann T rT timesT plusT), 
   p2c_times_id_equals_plus_ann_assert (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann S T rS rT timesS plusS timesT plusT pS_d pT_d)
   =
   bop_product_times_id_equals_plus_ann_assert
      (p2c_times_id_equals_plus_ann_assert S rS plusS timesS pS_d)
      (p2c_times_id_equals_plus_ann_assert T rT plusT timesT pT_d). 
Proof. intros [iS [piS paS]] [iT [piT paT]]; compute; reflexivity. Qed. 

Lemma bop_product_times_id_equals_plus_ann_check_correct : 
  ∀ (pS_d : bops_id_equals_ann_decidable S rS timesS plusS)
     (pT_d : bops_id_equals_ann_decidable T rT timesT plusT), 
   p2c_times_id_equals_plus_ann (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT timesS plusS timesT plusT pS_d pT_d)
   = 
   bop_product_times_id_equals_plus_ann_check 
      (p2c_times_id_equals_plus_ann S rS plusS timesS pS_d) 
      (p2c_times_id_equals_plus_ann T rT plusT timesT pT_d). 
Proof. intros [ [iS [piS paS]] | neqS]  [[iT [piT paT]] | neqT] ; compute; reflexivity. Qed. 
*) 


Lemma bop_product_left_left_absorbtive_check_correct : 
  ∀ (pS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_left_absorptive_decidable T rT plusT timesT), 
   bop_product_left_left_absorptive_check wS wT 
       (p2c_left_left_absorptive S rS plusS timesS pS_d)
       (p2c_left_left_absorptive T rT plusT timesT pT_d)
     = 
     p2c_left_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_left_left_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_left_right_absorbtive_check_correct : 
  ∀ (pS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_right_absorptive_decidable T rT plusT timesT), 
   bop_product_left_right_absorptive_check wS wT 
       (p2c_left_right_absorptive S rS plusS timesS pS_d)
       (p2c_left_right_absorptive T rT plusT timesT pT_d)
     = 
     p2c_left_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_left_right_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_right_left_absorbtive_check_correct : 
  ∀ (pS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_left_absorptive_decidable T rT plusT timesT), 
   bop_product_right_left_absorptive_check wS wT 
       (p2c_right_left_absorptive S rS plusS timesS pS_d)
       (p2c_right_left_absorptive T rT plusT timesT pT_d)
     = 
     p2c_right_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_right_left_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 

Lemma bop_product_right_right_absorbtive_check_correct : 
  ∀ (pS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_right_absorptive_decidable T rT plusT timesT), 
   bop_product_right_right_absorptive_check wS wT
       (p2c_right_right_absorptive S rS plusS timesS pS_d)
       (p2c_right_right_absorptive T rT plusT timesT pT_d)
     = 
     p2c_right_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (bops_product_right_right_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. intros [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed. 


Lemma  correct_bs_certs_product : 
  ∀ (bsS : bs_proofs S rS plusS timesS)
     (bsT : bs_proofs T rT plusT timesT), 
    bs_certs_product wS wT (P2C_bs S rS plusS timesS bsS) (P2C_bs T rT plusT timesT bsT)
    =
    P2C_bs (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
       (bs_proofs_product S T rS rT plusS timesS plusT timesT wS wT bsS bsT). 
Proof. intros bsS bsT. 
       unfold bs_certs_product, bs_proofs_product, P2C_bs; simpl. 
       rewrite bop_product_left_distributive_check_correct. 
       rewrite bop_product_right_distributive_check_correct.
(*       
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
*)
       rewrite bop_product_left_left_absorbtive_check_correct. 
       rewrite bop_product_left_right_absorbtive_check_correct. 
       rewrite bop_product_right_left_absorbtive_check_correct. 
       rewrite bop_product_right_right_absorbtive_check_correct. 
       reflexivity. 
Defined.

Lemma  correct_semiring_certs_product : 
  ∀ (eqvS : eqv_proofs S rS)
     (eqvT : eqv_proofs T rT)
     (bsS : semiring_proofs S rS plusS timesS)
     (bsT : semiring_proofs T rT plusT timesT), 
    semiring_certs_product wS wT (P2C_semiring S rS plusS timesS bsS) (P2C_semiring T rT plusT timesT bsT)
    =
    P2C_semiring (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
       (semiring_proofs_product S T rS rT plusS timesS plusT timesT wS wT eqvS eqvT bsS bsT). 
Proof. intros eqvS eqvT bsS bsT. 
       unfold semiring_certs_product, semiring_proofs_product, P2C_semiring; simpl.
(*       
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
*) 
       rewrite bop_product_left_left_absorbtive_check_correct. 
       rewrite bop_product_left_right_absorbtive_check_correct. 
       reflexivity. 
Defined.


Lemma bops_product_exists_id_ann_correct 
  (bS1 bS2 : binary_op S)
  (bT1 bT2 : binary_op T)
  (pS : exists_id_ann_decidable S rS bS1 bS2)
  (pT : exists_id_ann_decidable T rT bT1 bT2) : 
  p2c_exists_id_ann (S * T) (brel_product rS rT) (bop_product bS1 bT1) (bop_product bS2 bT2)
                            (bops_product_exists_id_ann_decide S T rS rT bS1 bS2 bT1 bT2 pS pT)
  =
  bops_product_exists_id_ann_certify (p2c_exists_id_ann S rS bS1 bS2 pS)
                                     (p2c_exists_id_ann T rT bT1 bT2 pT).                           
Proof. unfold p2c_exists_id_ann, bops_product_exists_id_ann_decide, bops_product_exists_id_ann_certify; simpl. 
       destruct pS; simpl.
       + destruct pT; simpl. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]; destruct p0 as [[idT C] D]; simpl. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct b as [idT_annT D]; simpl. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct b as [[idT annT] D]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct p0 as [C [annT D]]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct b as [idT_annT C]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct b as [[idT annT] C]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct b as [idS_annS A]; destruct p as [C D]. reflexivity. 
         ++ destruct b as [idS_annS A]; destruct p as [[idT C] D]; simpl. reflexivity. 
         ++ destruct b as [idS_annS A]; destruct p as [C [annT D]]; simpl. reflexivity. 
         ++ destruct b as [idS_annS [A B]]; destruct b0 as [idT_annT [C D]]; simpl. reflexivity. 
         ++ destruct b as [idS_annS [A B]]; destruct b0 as [[idT annT] [[C D] E]]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [D E]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [[idT D] E]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct p as [D [annT E]]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct b0 as [idT_annT [D E]]; simpl. reflexivity. 
         ++ destruct b as [[idS annS] [[A B] C]]; destruct b0 as [[idT annT] [[D E] F]]; simpl. reflexivity. 
Qed. 



Lemma  correct_id_ann_certs_product : 
  ∀ (pS : id_ann_proofs S rS plusS timesS)
     (pT : id_ann_proofs T rT plusT timesT), 
    id_ann_certs_product (P2C_id_ann S rS plusS timesS pS) (P2C_id_ann T rT plusT timesT pT) 
    = 
    P2C_id_ann (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
                       (id_ann_proofs_product S T rS rT plusS timesS plusT timesT pS pT). 
Proof. intros pS pT. 
       unfold id_ann_certs_product, id_ann_proofs_product, P2C_id_ann; simpl.
       rewrite bops_product_exists_id_ann_correct.
       rewrite bops_product_exists_id_ann_correct.        
       reflexivity. 
Qed.


Lemma  correct_dually_bounded_certs_product : 
  ∀ (pS : dually_bounded_proofs S rS plusS timesS)
     (pT : dually_bounded_proofs T rT plusT timesT), 
    dually_bounded_certs_product (P2C_dually_bounded S rS plusS timesS pS) (P2C_dually_bounded T rT plusT timesT pT) 
    = 
    P2C_dually_bounded (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
                                (dually_bounded_proofs_product S T rS rT plusS timesS plusT timesT pS pT). 
Proof. intros pS pT. 
       unfold dually_bounded_certs_product, dually_bounded_proofs_product, P2C_dually_bounded; simpl.
       destruct pS; destruct pT.
       destruct A_bounded_plus_id_is_times_ann as [pidS_tannS [A B]]. 
       destruct A_bounded_times_id_is_plus_ann as [tidS_pannS [C D]]. 
       destruct A_bounded_plus_id_is_times_ann0 as [pidT_tannT [E F]]. 
       destruct A_bounded_times_id_is_plus_ann0 as [tidT_pannT [G H]].
       unfold p2c_exists_id_ann_equal; simpl. 
       reflexivity. 
Qed.

Lemma  correct_pid_is_tann_certs_product : 
  ∀ (pS : pid_is_tann_proofs S rS plusS timesS)
     (pT : pid_is_tann_proofs T rT plusT timesT), 
    pid_is_tann_certs_product (P2C_pid_is_tann S rS plusS timesS pS) (P2C_pid_is_tann T rT plusT timesT pT) 
    = 
    P2C_pid_is_tann (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
                                (pid_is_tann_proofs_product S T rS rT plusS timesS plusT timesT pS pT). 
Proof. intros pS pT. 
       unfold pid_is_tann_certs_product, pid_is_tann_proofs_product, P2C_pid_is_tann; simpl.
       destruct pS; destruct pT.
       rewrite bops_product_exists_id_ann_correct. simpl. 
       destruct A_pid_is_tann_plus_times as [pidS_tannS [A B]]. 
       destruct A_pid_is_tann_plus_times0 as [pidT_tannT [C D]]. 
       unfold p2c_exists_id_ann_equal; simpl. 
       reflexivity. 
Qed.

Lemma  correct_pann_is_tid_certs_product : 
  ∀ (pS : pann_is_tid_proofs S rS plusS timesS)
     (pT : pann_is_tid_proofs T rT plusT timesT), 
    pann_is_tid_certs_product (P2C_pann_is_tid S rS plusS timesS pS) (P2C_pann_is_tid T rT plusT timesT pT) 
    = 
    P2C_pann_is_tid (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
                                (pann_is_tid_proofs_product S T rS rT plusS timesS plusT timesT pS pT). 
Proof. intros pS pT. 
       unfold pann_is_tid_certs_product, pann_is_tid_proofs_product, P2C_pann_is_tid; simpl.
       destruct pS; destruct pT.
       rewrite bops_product_exists_id_ann_correct. simpl. 
       destruct A_pann_is_tid_times_plus as [idS_annS [A B]]. 
       destruct A_pann_is_tid_times_plus0 as [idT_annT [C D]]. 
       unfold p2c_exists_id_ann_equal; simpl. 
       reflexivity. 
Qed.



End ChecksCorrect.

Theorem correct_bs_product : ∀ (S T : Type) (bsS: A_bs S) (bsT : A_bs T), 
   bs_product (A2C_bs S bsS) (A2C_bs T bsT)
   =
   A2C_bs (S * T) (A_bs_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_product, A_bs_product, A2C_bs; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_bs_certs_product.
       rewrite correct_id_ann_certs_product. 
       reflexivity. 
Qed.


Theorem correct_mcas_bs_product (S T : Type) (bsS : A_bs_mcas S) (bsT : A_bs_mcas T): 
         mcas_bs_product (A2C_mcas_bs S bsS) (A2C_mcas_bs T bsT) 
         = 
         A2C_mcas_bs (S * T) (A_mcas_bs_product S T bsS bsT).
Proof. unfold mcas_bs_product, A_mcas_bs_product. 
       rewrite correct_bs_mcas_cast_up.
       rewrite correct_bs_mcas_cast_up.       
       Time destruct (A_bs_cas_up_is_error_or_bs S bsS) as [[l1 A] | [s1 A]];
       destruct (A_bs_cas_up_is_error_or_bs T bsT) as [[l2 B] | [s2 B]].
       + rewrite A, B. simpl. reflexivity. 
       + rewrite A, B. simpl. reflexivity.
       + rewrite A, B. simpl. reflexivity.
       + rewrite A, B. simpl. rewrite correct_bs_product.
         apply correct_bs_classify_bs. 
Qed. 


(*
Theorem correct_presemiring_product : ∀ (S T : Type) (bsS: A_presemiring S) (bsT : A_presemiring T), 
   presemiring_product (A2C_presemiring S bsS) (A2C_presemiring T bsT)
   =
   A2C_presemiring (S * T) (A_presemiring_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold presemiring_product, A_presemiring_product, A2C_presemiring; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_C_certs_product. 
       rewrite <- correct_semiring_certs_product.
       rewrite correct_id_ann_certs_product. 
       reflexivity. 
Qed. 



Theorem correct_pre_dioid_product : ∀ (S T : Type) (bsS: A_pre_dioid S) (bsT : A_pre_dioid T), 
   pre_dioid_product (A2C_pre_dioid S bsS) (A2C_pre_dioid T bsT)
   =
   A2C_pre_dioid_NS (S * T) (A_pre_dioid_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold pre_dioid_product, A_pre_dioid_product, A2C_pre_dioid, A2C_pre_dioid_NS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_msg_certs_product.
       rewrite correct_id_ann_certs_product.        
       rewrite <- correct_sg_CI_to_CINS_certs_product. 
       unfold P2C_dioid. unfold dioid_certs_product. 
       reflexivity. 
Qed. 

Theorem correct_semiring_product : ∀ (S T : Type) (bsS: A_semiring S) (bsT : A_semiring T), 
   semiring_product (A2C_semiring S bsS) (A2C_semiring T bsT)
   =
   A2C_semiring (S * T) (A_semiring_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold semiring_product, A_semiring_product, A2C_semiring; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_C_certs_product. 
       rewrite <- correct_semiring_certs_product.
       rewrite correct_pid_is_tann_certs_product. 
       reflexivity. 
Qed. 

*) 





(* lattice? *) 

End Verify.   
