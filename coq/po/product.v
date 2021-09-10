Require Import Coq.Bool.Bool.    

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.product. (* some properties proved here *) 
Require Import CAS.coq.eqv.minset.  (* for bottoms *) 

Require Import CAS.coq.sg.and. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Section Theory.

Variable S  : Type. 
Variable T  : Type.
Variable wS : S. 
Variable wT : T.

Variable eqS : brel S. 
Variable eqT : brel T.

Variable lteS : brel S. 
Variable lteT : brel T.


Variable lteReflS : brel_reflexive S lteS.
Variable lteReflT : brel_reflexive T lteT.

Variable trnS : brel_transitive S lteS. 
Variable trnT : brel_transitive T lteT.



Notation "a <*> b"  := (brel_product a b) (at level 15).



Lemma ord_product_not_reflexive_left : ∀ (t : T),   (brel_not_reflexive S lteS) 
               → brel_not_reflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_reflexive. intros t [s P]. 
        exists (s, t). compute. rewrite P. reflexivity. 
Defined. 

Lemma ord_product_not_reflexive_right : ∀ (s : S),   (brel_not_reflexive T lteT) 
               → brel_not_reflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_reflexive. intros s [t P]. 
        exists (s, t). compute. rewrite P. rewrite lteReflS; auto. Defined. 

Definition ord_product_reflexive_decide: 
   ∀ (s : S) (t : T),    
     brel_reflexive_decidable S lteS → 
     brel_reflexive_decidable T lteT → 
        brel_reflexive_decidable (S * T) (lteS <*> lteT)
:= λ s t dS dT,  
       match dS with 
       | inl refS => 
         match dT with 
         | inl refT     => inl _ (brel_product_reflexive S T lteS lteT refS refT)
         | inr not_refT => inr _ (ord_product_not_reflexive_right s not_refT)
         end 
       | inr not_refS   => inr _ (ord_product_not_reflexive_left t not_refS)
       end. 

Lemma ord_product_irreflexive_left : brel_irreflexive S lteS -> brel_irreflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_irreflexive. intros irr [s t]. compute. rewrite (irr s). reflexivity. Defined. 

Lemma ord_product_irreflexive_right : brel_irreflexive T lteT -> brel_irreflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_irreflexive. intros irr [s t]. compute. rewrite (irr t). case_eq(lteS s s); intro H; auto. Defined. 

Lemma ord_product_not_irreflexive : brel_not_irreflexive S lteS -> brel_not_irreflexive T lteT -> 
           brel_not_irreflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_irreflexive. intros [s P] [t Q]. exists (s, t). compute. rewrite P, Q; auto. Defined. 

Definition ord_product_irreflexive_decide: 
     brel_irreflexive_decidable S lteS → 
     brel_irreflexive_decidable T lteT → 
        brel_irreflexive_decidable (S * T) (lteS <*> lteT)
:= λ dS dT,  
       match dS with 
       | inl irrS => inl _ (ord_product_irreflexive_left irrS)
       | inr not_irrS   => 
         match dT with 
         | inl irrT     => inl _ (ord_product_irreflexive_right irrT)
         | inr not_irrT => inr _ (ord_product_not_irreflexive not_irrS not_irrT)
         end 
       end. 



Lemma ord_product_antisymmetric :
  (brel_antisymmetric S eqS lteS) → (brel_antisymmetric T eqT lteT)
  → brel_antisymmetric (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros AS AT [s1 t1] [s2 t2]; simpl. 
       intros A B.
       apply bop_and_elim in A. destruct A as [A1 A2].
       apply bop_and_elim in B. destruct B as [B1 B2].
       apply bop_and_intro; auto. 
Qed. 

Lemma ord_product_not_antisymmetric_left : brel_not_antisymmetric S eqS lteS → 
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [ [s1 s2] [[A B] C]]. 
       exists ((s1, wT), (s2, wT)). compute. 
       rewrite A. rewrite B. rewrite C.  rewrite lteReflT. auto. 
Defined. 

Lemma ord_product_not_antisymmetric_right : brel_not_antisymmetric T eqT lteT → 
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [ [t1 t2] [[A B] C]]. 
       exists ((wS, t1), (wS, t2)). compute. 
       rewrite A. rewrite B. rewrite C.  rewrite (lteReflS wS).
       case_eq(eqS wS wS); intro D; auto. 
Defined. 



Definition ord_product_antisymmetric_decide: 
  S -> T -> brel_antisymmetric_decidable S eqS lteS → brel_antisymmetric_decidable T eqT lteT → 
        brel_antisymmetric_decidable (S * T) (eqS <*> eqT) (lteS <*> lteT)
:= λ wS wT dS dT,  
       match dS with 
       | inl asymS => 
         match dT with 
         | inl asymT     => inl _ (ord_product_antisymmetric asymS asymT)
         | inr not_asymT => inr _ (ord_product_not_antisymmetric_right not_asymT)
         end 
       | inr not_asymS   => inr _ (ord_product_not_antisymmetric_left not_asymS)
       end.


Lemma ord_product_exists_bottom :
  (brel_exists_qo_bottom S eqS lteS) → (brel_exists_qo_bottom T eqT lteT)
  → brel_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [s [A B]] [t [C D]]. exists (s, t). split. 
     intros [a b]. compute. rewrite (A a). rewrite (C b); auto. 
     intros [a b]. compute.
     case_eq(lteS s a); intro E; case_eq(lteS a s); intro F; intros I J; auto. 
     rewrite (B _ E F). rewrite (D _ I J); auto. 
     discriminate J. discriminate I. discriminate J. 
Defined. 


Lemma ord_product_not_exists_bottom_left :
  (brel_not_exists_qo_bottom S eqS lteS) → brel_not_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N s) as [[w L] | [w [[A B] C]]]. 
       left. exists (w, t). compute. rewrite L; auto. 
       right. exists (w, t). compute. rewrite A, B, C. 
       rewrite (lteReflT t). auto. 
Defined. 

Lemma ord_product_not_exists_bottom_right (refS : brel_reflexive S eqS) :
  (brel_not_exists_qo_bottom T eqT lteT) → brel_not_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N t) as [[w L] | [w [[A B] C]]]. 
       left. exists (s, w). compute. rewrite L. rewrite (lteReflS s); auto. 
       right. exists (s, w). compute. rewrite A, B, C. 
       rewrite (lteReflS s), (refS s); auto. 
Defined.


Definition ord_product_exists_bottom_decide (refS : brel_reflexive S eqS)
     (DS : brel_exists_qo_bottom_decidable S eqS lteS)
     (DT : brel_exists_qo_bottom_decidable T eqT lteT) : 
           brel_exists_qo_bottom_decidable (S * T) (eqS <*> eqT) (lteS <*> lteT) := 
match DS with 
| inl botS  => match DT with
               | inl botT => inl (ord_product_exists_bottom botS botT)
               | inr nbot => inr (ord_product_not_exists_bottom_right refS nbot)
               end 
| inr nbot => inr (ord_product_not_exists_bottom_left nbot)
end.


Lemma ord_product_exists_top :
  (brel_exists_qo_top S eqS lteS) → (brel_exists_qo_top T eqT lteT)
  → brel_exists_qo_top (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [s [A B]] [t [C D]]. exists (s, t). split. 
     intros [a b]. compute. rewrite (A a). rewrite (C b); auto. 
     intros [a b]. compute.
     case_eq(lteS s a); intro E; case_eq(lteS a s); intro F; intros I J; auto. 
     rewrite (B _ E F). rewrite (D _ I J); auto. 
     discriminate J. discriminate I. discriminate J. 
Defined. 

Lemma ord_product_not_exists_top_left :
  (brel_not_exists_qo_top S eqS lteS) 
  → brel_not_exists_qo_top (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N s) as [[w L] | [w [[A B] C]]]. 
       left. exists (w, t). compute. rewrite L; auto. 
       right. exists (w, t). compute. rewrite A, B, C. 
       rewrite (lteReflT t). auto. 
Defined. 


Lemma ord_product_not_exists_top_right (refS : brel_reflexive S eqS) :
  (brel_not_exists_qo_top T eqT lteT) 
  → brel_not_exists_qo_top (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N t) as [[w L] | [w [[A B] C]]]. 
       left. exists (s, w). compute. rewrite L. rewrite (lteReflS s); auto. 
       right. exists (s, w). compute. rewrite A, B, C. 
       rewrite (lteReflS s), (refS s); auto. 
Defined. 


Definition ord_product_exists_top_decide (refS : brel_reflexive S eqS)
     (DS : brel_exists_qo_top_decidable S eqS lteS)
     (DT : brel_exists_qo_top_decidable T eqT lteT) : 
           brel_exists_qo_top_decidable (S * T) (eqS <*> eqT) (lteS <*> lteT) := 
match DS with 
| inl topS  => match DT with
               | inl topT => inl (ord_product_exists_top topS topT)
               | inr ntop => inr (ord_product_not_exists_top_right refS ntop)
               end 
| inr ntop => inr (ord_product_not_exists_top_left ntop)
end.


Close Scope nat_scope. 

Lemma total_split (U : Type) (eq lte: brel U) (s : U) ( f : U -> U) :
      brel_reflexive U eq ->  
      brel_reflexive U lte ->
      brel_congruence U eq lte ->     
      brel_total U lte -> 
      brel_not_trivial U lte f -> 
      brel_antisymmetric U eq lte -> 
      {s1 : U & {s2 : U & (lte s2 s1 = true) * (lte s1 s2 = false) }}. 
Proof. intros ref lteRef cong tot Pf anti. 
       destruct (Pf s) as [L R].
       case_eq(lte s (f s)); intro F1;  case_eq(lte (f s) s); intro F2.
          assert (A := anti _ _ F1 F2).
          rewrite (cong _ _ _ _ A (ref (f s))) in L. 
          rewrite lteRef in L. discriminate L. 
          exists (f s); exists s; split; assumption. 
          exists s; exists (f s); split; assumption. 
          destruct (tot s (f s)) as [F | F].          
             rewrite F in F1. discriminate.
             rewrite F in F2. discriminate.
Defined.

Lemma ord_product_not_total_v1 ( f : S -> S) (g : T -> T) :
      brel_reflexive S eqS ->
      brel_congruence S eqS lteS ->       
      brel_total S lteS -> 
      brel_not_trivial S lteS f ->
      brel_not_trivial T lteT g ->       
      brel_antisymmetric S eqS lteS -> 
              brel_not_total (S * T) (lteS <*> lteT). 
Proof. intros refS lteCong TS NTS NTT ANS.
       destruct (total_split S eqS lteS wS f refS lteReflS lteCong TS NTS ANS) as [s1 [s2 [A B]]].
       exists ((s1, wT), (s2, g wT)). compute. 
       rewrite A, B. destruct (NTT wT) as [C D]. 
       rewrite D; auto. 
Defined.



Lemma ord_product_not_total_left :
   brel_not_total S lteS -> brel_not_total (S * T) (lteS <*> lteT). 
Proof. intros [[s1 s2] [A B]]. exists ((s1, wT), (s2, wT)). compute. 
       rewrite A, B; auto. 
Defined.


Lemma ord_product_not_total_right (lteRef : brel_reflexive S lteS):
   brel_not_total T lteT -> brel_not_total (S * T) (lteS <*> lteT). 
Proof. intros [[t1 t2] [A B]]. exists ((wS, t1), (wS, t2)). compute. 
       rewrite A, B; auto. rewrite (lteRef wS). auto. 
Defined.

(*
Lemma ord_product_not_total (s1 s2 : S) (t1 t2 : T) :
   brel_not_total (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_total. exists ((s1, t1), (s2, t2)).
       compute. 
       case_eq(lteS s1 s2); intro A. 
          case_eq(lteS s2 s1); intro B; auto.
             case_eq(lteT t1 t2); intro C; case_eq(lteT t2 t1); intro D; auto. 
                admit. (* not(s1 <= s2), s2 <= s1, t1 <= t2 t2 <= t1)  *)      
                admit. (* not(s1 <= s2), s2 <= s1, t1 <= t2 not(t2 <= t1))  *)      
                admit. (* not(s1 <= s2), s2 <= s1, not(t1 <= t2) t2 <= t1)  *)                
             case_eq(lteT t1 t2); intro C; auto.
                admit. (* not(s1 <= s2), not(s2 <= s1), t1 <= t2)  *)      
          case_eq(lteS s2 s1); intro B; auto. 
             case_eq(lteT t2 t1); intro C; auto.
                admit. (* not(not(s1 <= s2), s2 <= s1, t2 <= t1)  *)
Admitted. 
 *)



(* bottoms *)
Section Bottoms.

(* interesting that these not needed until now *)   
Variable symS : brel_symmetric S eqS.
Variable refT : brel_reflexive T eqT.
Variable symT : brel_symmetric T eqT. 

Definition bop_product_w (BS : list S) (BT : list T) (fS : S ->S) (fT : T -> T) (p : S * T) :=
  match p with (s, t) =>
               if in_set eqS BS s 
               then if in_set eqT BT t 
                    then (s, t)
                    else (s, fT t)
               else if in_set eqT BT t 
                    then (fS s, t)
                    else (fS s, fT t)
  end.  

Definition map_mk_pairs: S -> finite_set T -> finite_set (S * T) :=
   fix f a Y := 
      match Y with
         | nil => nil 
         | b :: rest => (a, b) :: (f a rest)
      end.

Definition set_product : finite_set S -> finite_set T -> finite_set (S * T) :=
   fix f x y := 
      match x with
         | nil => nil 
         | a :: rest => (map_mk_pairs a y) ++ (f rest y) 
      end.


Lemma in_set_map_mk_pairs_elim (a s : S) (t : T) (BT : list T): 
      in_set (eqS <*> eqT) (map_mk_pairs a BT) (s, t) = true -> (eqS a s = true) * (in_set eqT BT t = true). 
Proof. induction BT; intro H. 
          compute in H. discriminate H. 
          unfold map_mk_pairs in H. fold map_mk_pairs in H. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(eqS a s); intro G. 
                 rewrite G in H. split; auto. 
                 apply in_set_cons_intro; auto. 
                 rewrite G in H. discriminate H. 

             destruct (IHBT H) as [J K]. 
             split; auto. 
                apply in_set_cons_intro; auto. 
          apply brel_product_symmetric; auto. 
Qed.

Lemma in_set_product_elim (s : S) (t : T) (BS : list S) (BT : list T) :
  in_set (eqS <*> eqT) (set_product BS BT) (s, t) = true -> (in_set eqS BS s = true) * (in_set eqT BT t = true).
Proof. induction BS; intro H. 
       compute in H. discriminate H.
       unfold set_product in H. fold set_product in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H]. 
          apply in_set_map_mk_pairs_elim in H; auto. destruct H as [H1 H2].
          split; auto. 
             apply in_set_cons_intro; auto. 
       
          destruct (IHBS H) as [J K].        
          split; auto. 
             apply in_set_cons_intro; auto. 
             apply brel_product_symmetric; auto. 
Qed.


Lemma in_set_map_mk_pairs_intro (a s : S) (t : T) (BT : list T): 
    (eqS a s = true) -> (in_set eqT BT t = true) -> in_set (eqS <*> eqT) (map_mk_pairs a BT) (s, t) = true.
Proof. induction BT; intros H1 H2.
       compute in H2. discriminate H2. 

       unfold map_mk_pairs. fold map_mk_pairs. 
       apply in_set_cons_intro; auto. 
       apply brel_product_symmetric; auto. 
       apply in_set_cons_elim in H2; auto. 
       destruct H2 as [H2 | H2]. 
          left. compute. rewrite H1, H2. reflexivity. 
          right. apply IHBT; auto. 
Qed. 

Lemma in_set_product_intro (s : S) (t : T) (BS : list S) (BT : list T) :
 (in_set eqS BS s = true) -> (in_set eqT BT t = true) -> in_set (eqS <*> eqT) (set_product BS BT) (s, t) = true. 
Proof. intros A B. induction BS. 
          compute in A. discriminate A. 

          unfold set_product. fold set_product. 
          apply in_set_concat_intro; auto. 
          apply in_set_cons_elim in A; auto.           
          destruct A as [A | A]. 
             left. apply in_set_map_mk_pairs_intro; auto. 
             right. exact (IHBS A). 
Qed. 

Lemma set_product_is_antichain (BS : list S) (BT : list T) :
  is_antichain S eqS lteS BS -> is_antichain T eqT lteT BT -> 
  is_antichain (S * T) (eqS <*> eqT) (lteS <*> lteT) (set_product BS BT).
Proof. unfold is_antichain. intros IS IT.
       intros [s1 t1] H1 [s2 t2] H2.
       apply in_set_product_elim in H1; auto. destruct H1 as [H1L H1R].
       apply in_set_product_elim in H2; auto.  destruct H2 as [H2L H2R].
       assert (H3 := IS s1 H1L s2 H2L). apply equiv_or_incomp_elim in H3.
       assert (H4 := IT t1 H1R t2 H2R). apply equiv_or_incomp_elim in H4.
       apply equiv_or_incomp_intro. 
       destruct H3 as [A |A]; destruct H4 as [C | C]. 
          left. apply equiv_intro.
             compute. apply equiv_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A, C. reflexivity.
             
             compute. apply equiv_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B, D. reflexivity. 

             
          right. apply incomp_intro. 
             compute. apply equiv_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A, C. reflexivity.
             
             compute. apply equiv_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B, D. reflexivity. 
          
          right. apply incomp_intro. 
             compute. apply incomp_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A. reflexivity.
             
             compute. apply incomp_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B. reflexivity. 

          right. apply incomp_intro. 
             compute. apply incomp_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A. reflexivity.
             
             compute. apply incomp_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B. reflexivity. 
Qed. 


Lemma ord_product_bottoms_set_is_finite :
  (bottoms_set_is_finite S eqS lteS) → (bottoms_set_is_finite T eqT lteT)
  → bottoms_set_is_finite (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. unfold bottoms_set_is_finite. 
       intros [[BS fS] [IS PS]] [[BT fT] [IT PT]]. 
       exists (set_product BS BT, bop_product_w BS BT fS fT). split. 
          apply set_product_is_antichain; auto.   
          intros [s t]. unfold bop_product_w.
          (* assert (iS := idemS s). apply symS in iS.
          assert (iT := idemT t). apply symT in iT.            *) 
          destruct (PS s) as [A | [A B]];
          destruct (PT t) as [D | [D E]]. 
             left. apply in_set_product_intro; auto.

             rewrite A. case_eq(in_set eqT BT t); intro G. 
                left. apply in_set_product_intro; auto.
                right. split. 
                   apply in_set_product_intro; auto.
                   apply below_intro. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [E _]. exact E. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [_ E]. exact E. 

             rewrite D. case_eq(in_set eqS BS s); intro G. 
                left. apply in_set_product_intro; auto.
                right. split. 
                   apply in_set_product_intro; auto.
                   apply below_intro. 
                      compute. apply below_elim in B. destruct B as [B _]. rewrite B. apply lteReflT. 
                      compute. apply below_elim in B. destruct B as [_ B]. rewrite B. reflexivity. 

             case_eq(in_set eqS BS s); intro G; case_eq(in_set eqT BT t); intro H.
                left. apply in_set_product_intro; auto. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   apply below_intro. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [E _]. exact E. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [_ E]. exact E. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   apply below_intro. 
                      compute.  apply below_elim in B. destruct B as [B _]. rewrite B. apply lteReflT. 
                      compute. apply below_elim in B. destruct B as [_ B]. rewrite B. reflexivity. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   apply below_intro. 
                      compute. apply below_elim in B. destruct B as [B _]. rewrite B. 
                               apply below_elim in E. destruct E as [E _]. exact E. 
                      compute. apply below_elim in B. destruct B as [_ B]. rewrite B. 
                               apply below_elim in E. destruct E as [_ E]. reflexivity. 
Qed. 


Definition set_product_proj1 (B : finite_set (S * T)) : finite_set S :=
  List.map (λ p, match p with (s, _) => s end) B.

Definition set_product_proj2 (B : finite_set (S * T)) : finite_set T :=
  List.map (λ p, match p with (_, t) => t end) B.

(*
Lemma in_set_product_proj1_intro (B : finite_set (S * T)) :
  ∀ (s : S) (t : T) ,  
     in_set (rS <*> rT) B (s, t) = true -> in_set rS (set_product_proj1 B) s = true. 
Proof. induction B; intros s t H. 
          compute in H. discriminate H. 
          unfold set_product_proj1. 
          destruct a as [s' t']. 
          unfold List.map. fold (List.map (λ p : S * T, let (s0, _) := p in s0) B). 
          apply in_set_cons_intro; auto. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(rS s' s); intro J. 
               left. reflexivity. 
               rewrite J in H. discriminate H.

            right. exact (IHB s t H). 
          apply brel_product_symmetric; auto. 
Qed.

Lemma in_set_product_proj2_intro (B : finite_set (S * T)) :
  ∀ (s : S) (t : T) ,  
     in_set (rS <*> rT) B (s, t) = true -> in_set rT (set_product_proj2 B) t = true. 
Proof. induction B; intros s t H. 
          compute in H. discriminate H. 
          unfold set_product_proj2. 
          destruct a as [s' t']. 
          unfold List.map. fold (List.map (λ p : S * T, let (_, t0) := p in t0) B). 
          apply in_set_cons_intro; auto. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(rT t' t); intro J. 
               left. reflexivity. 
               rewrite J in H. 
               case_eq(rS s' s); intro K; rewrite K in H; discriminate H. 

              right. exact (IHB s t H). 
          apply brel_product_symmetric; auto. 
Qed.

*)
Lemma in_set_product_proj1_elim (B : finite_set (S * T)) :
  ∀ (s : S),  
     in_set eqS (set_product_proj1 B) s = true -> {t : T & in_set (eqS <*> eqT) B (s, t) = true}. 
Proof. induction B; intros s H. 
       compute in H. discriminate H. 
       unfold set_product_proj1 in H. 
       destruct a as [s' t']. 
       unfold List.map in H. fold (List.map (λ p : S * T, let (s0, _) := p in s0) B) in H. 
       apply in_set_cons_elim in H; auto. 
       destruct H as [H | H]. 
          exists t'.
          apply in_set_cons_intro; auto.
          apply brel_product_symmetric; auto.
          left. compute. rewrite H. apply refT. 
          destruct (IHB s H) as [t P]. 
          exists t. 
          apply in_set_cons_intro; auto.
          apply brel_product_symmetric; auto.
Qed.


(* For the cases of bottoms_set_not_is_finite 
   we need to extract antichains over S or T from an antichain over S * T. 
   Just doing simple projections doesn't work.  For example, suppose 

    (s2, t2) # (s1, t1)

   There are two situations where the neither projection will be an antichain. 
    That is [(s1 < s2) and (t2 < t1)] 
    and [(s2 < s1) and (t1 < t2)].  

    The solution is to take minsets of projections! 

 *)


Definition negation_v1 (X : finite_set (S * T)) : finite_set S :=
      uop_minset lteS (set_product_proj1 X). 

Definition negation_v2 (X : finite_set (S * T)) : finite_set T :=
     uop_minset lteT (set_product_proj2 X). 


Definition product_not_finite_v1 (F : finite_set S -> S) (B : finite_set (S * T)) : S * T :=
     (F (negation_v1 B), wT). 

Definition product_not_finite_v2 (F : finite_set T -> T) (X : finite_set (S * T)) : S * T :=
     (wS, F (negation_v2 X)). 


Lemma negation_v1_is_antichain (B : finite_set (S * T)) : is_antichain S eqS lteS (negation_v1 B).
Admitted.

Lemma negation_v2_is_antichain (B : finite_set (S * T)) : is_antichain T eqT lteT (negation_v2 B).
Admitted.

Lemma lemma10 (F : finite_set S -> S) (B : finite_set (S * T)) : 
     in_set (eqS <*> eqT) B (F (negation_v1 B), wT) = true
     -> in_set eqS (negation_v1 B) (F (negation_v1 B)) = true. 
Admitted.


Lemma in_set_negation_v1_intro (B : finite_set (S * T)) :
  ∀ (s : S) (t : T) ,  
     in_set (eqS <*> eqT) B (s, t) = true -> in_set eqS (negation_v1 B) s = true. 
Admitted. 

(* need glb on T *) 
Lemma ord_product_something_not_is_finite_v1 : 
  bottoms_set_not_is_finite S eqS lteS →
     bottoms_set_not_is_finite (S * T) (eqS <*> eqT) (lteS <*> lteT).
Proof. unfold bottoms_set_not_is_finite.
       intros [F A].
       exists (product_not_finite_v1 F).
       intros B I. 
       assert (C := negation_v1_is_antichain B).
       destruct (A (negation_v1 B) C) as [D E]. 
       unfold product_not_finite_v1.
       split. 
          case_eq(in_set (eqS <*> eqT) B (F (negation_v1 B), wT)); intro G; auto.
             apply lemma10 in G. rewrite G in D. discriminate D. 
          
          intros [s t] G. 
          assert (G' := in_set_negation_v1_intro _ _ _ G).
          apply below_false_intro.
          assert (H := E s G').           apply below_false_elim in H. 
          destruct H as [H | H].
             left. unfold brel_product. rewrite H. compute. reflexivity.

             unfold brel_product. 
             case_eq(lteT t wT); intro K;  case_eq(lteT wT t); intro J.  
                rewrite H. right. compute. reflexivity. 

                left. case_eq(lteS s (F (negation_v1 B)) ); intro L; auto. 
                   admit. 
                
                rewrite H. right. compute. reflexivity. 

                left. apply bop_and_false_intro. right. reflexivity. 
Admitted.

(*
Lemma bop_product_something_not_is_finite_v2 (commT : bop_commutative T rT bT): 
  something_not_is_finite T rT bT →
     something_not_is_finite (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold something_not_is_finite.
       intros [F A]. 
       exists (product_not_finite_v2 F).
       intros B I. 
       assert (C := set_product_is_interesting_v2 B I).
       destruct (A (set_product_proj2 B) C) as [D E]. 
       unfold product_not_finite_v2.
       split. 
          case_eq(in_set (rS <*> rT) B (wS, F (set_product_proj2 B))); intro G; auto.
             apply in_set_product_proj2_intro in G. 
             rewrite G in D. discriminate D. 
          
          intros [s t] G. 
          assert (G' := in_set_product_proj2_intro _ _ _ G).
          unfold bop_product. unfold brel_product. 
          destruct (E t G') as [H | H].
             left. rewrite H. apply andb_is_false_right. right. reflexivity. 

             case_eq(rT t (t *T F (set_product_proj2 B))); intro K. 
                assert (J := commT t (F (set_product_proj2 B))). 
                assert (L := transT _ _ _ K J).              
                apply symT in H. 
                assert (M := transT _ _ _ L H). 
                assert (N := in_set_right_congruence _ rT symT transT _ _ _ M G'). 
                rewrite N in D. discriminate D. 
                
                left. apply andb_is_false_right. right. reflexivity. 
Defined. 
*)
End Bottoms. 
End Theory.

Section ACAS.

Definition po_product_proofs (S T : Type) (eqS lteS : brel S) (wS : S) 
               (P : po_proofs S eqS lteS)  (eqT lteT : brel T) (wT : T) (Q : po_proofs T eqT lteT) :
    po_proofs (S * T) (brel_product eqS eqT) (brel_product lteS lteT) := 
let lteReflS := A_po_reflexive _ _ _ P in
let lteReflT := A_po_reflexive _ _ _ Q in
let lteTrnS := A_po_transitive _ _ _ P in
let lteTrnT := A_po_transitive _ _ _ Q in    
{|
  A_po_congruence        := brel_product_congruence S T eqS eqT lteS lteT (A_po_congruence S eqS lteS P) (A_po_congruence T eqT lteT Q)
; A_po_reflexive         := brel_product_reflexive S T lteS lteT lteReflS lteReflT 
; A_po_transitive        := brel_product_transitive S T lteS lteT lteTrnS lteTrnT 
; A_po_antisymmetric     := ord_product_antisymmetric S T eqS eqT lteS lteT (A_po_antisymmetric S eqS lteS P) (A_po_antisymmetric T eqT lteT Q)
; A_po_not_total         := ord_product_not_total_left S T wT lteS lteT (A_po_not_total S eqS lteS P)
|}.
     
  

Definition ord_po_wo_product_proofs (S T : Type) (eqS lteS : brel S) (wS : S) 
               (P : po_proofs S eqS lteS)  (eqT lteT : brel T) (wT : T) (Q : wo_proofs T eqT lteT) :
    qo_proofs (S * T) (brel_product eqS eqT) (brel_product lteS lteT) := 
let lteReflS := A_po_reflexive _ _ _ P in
let lteReflT := A_wo_reflexive _ _ _ Q in
let lteTrnS := A_po_transitive _ _ _ P in
let lteTrnT := A_wo_transitive _ _ _ Q in    
{|
  A_qo_congruence        := brel_product_congruence S T eqS eqT lteS lteT (A_po_congruence S eqS lteS P) (A_wo_congruence T eqT lteT Q)
; A_qo_reflexive         := brel_product_reflexive S T lteS lteT lteReflS lteReflT 
; A_qo_transitive        := brel_product_transitive S T lteS lteT lteTrnS lteTrnT 
; A_qo_not_antisymmetric := ord_product_not_antisymmetric_right S T wS eqS eqT lteS lteT lteReflS (A_wo_not_antisymmetric T eqT lteT Q)
; A_qo_not_total         := ord_product_not_total_left S T wT lteS lteT (A_po_not_total S eqS lteS P)
|}.
     
  
End ACAS.

Section CAS.

Definition ord_po_wo_product_certs {S T : Type} (wS : S) (P : @po_certificates S)  (wT : T) (Q : @wo_certificates T) :
    @qo_certificates (S * T) := 
{|
  qo_congruence        := Assert_Brel_Congruence 
; qo_reflexive         := Assert_Reflexive
; qo_transitive        := Assert_Transitive
; qo_not_antisymmetric := match wo_not_antisymmetric Q with
                          | Assert_Not_Antisymmetric (t1, t2) => Assert_Not_Antisymmetric ((wS, t1), (wS, t2))
                          end
; qo_not_total       := match po_not_total P with
                          | Assert_Not_Total (s1, s2) => Assert_Not_Total ((s1, wT), (s2, wT))
                          end
|}.
  

End CAS.

Section Verify.


Lemma correct_ord_po_wo_product_certs (S T: Type) (eqS lteS : brel S) (wS : S) 
               (P : po_proofs S eqS lteS)  (eqT lteT : brel T) (wT : T) (Q : wo_proofs T eqT lteT) :
   ord_po_wo_product_certs wS (P2C_po S eqS lteS P) wT (P2C_wo T eqT lteT Q) 
   =   
   P2C_qo _ _ _ (ord_po_wo_product_proofs S T eqS lteS wS P eqT lteT wT Q). 
Proof. destruct P. destruct Q.
       unfold ord_po_wo_product_certs, ord_po_wo_product_proofs, P2C_qo, P2C_po, P2C_wo. 
       destruct A_wo_not_antisymmetric as [[t1 t2] [[A B] C]];                                                                
       destruct A_po_not_total as [[s1 s2] [D E]]; simpl.               
       unfold p2c_not_antisymmetric_assert. simpl. 
       unfold p2c_not_total_assert. simpl. 
       reflexivity. 
Qed. 
End Verify.   
  
