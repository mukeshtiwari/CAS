Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.cast_up. 

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Section Computation.

Definition brel_left_lex : ∀ {S T : Type}, brel S → brel T → brel (S * T) 
:= λ {S T} lteS lteT x y,  
   match x, y with
   | (a, b), (c, d) => bop_or (below lteS c a)
                              (bop_and (equiv lteS a c) (lteT b d)) 
   end.

End Computation.   

Section Theory.

Variable S  : Type. 
Variable T  : Type. 

Variable eqS  : brel S.
Variable conS : brel_congruence S eqS eqS. 
Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.
Variable trnS : brel_transitive S eqS.

Variable eqT : brel T. 
Variable conT : brel_congruence T eqT eqT. 
Variable refT : brel_reflexive T eqT.
Variable trnT : brel_transitive T eqT.

Variable lteS    : brel S. 
Variable lteConS : brel_congruence S eqS lteS. 

Variable lteT    : brel T. 
Variable lteConT : brel_congruence T eqT lteT. 


Notation "p <*> q" := (brel_product p q) (at level 15).
Notation "p [*] q" := (brel_left_lex p q) (at level 15).


Notation "a =S b"   := (eqS a b = true) (at level 15).
Notation "a !=S b"  := (eqS a b = false) (at level 15).
Notation "a =T b"   := (eqT a b = true) (at level 15).
Notation "a !=T b"  := (eqT a b = false) (at level 15).
Notation "a <=S b"  := (lteS a b = true) (at level 15).
Notation "a !<=S b" := (lteS a b = false) (at level 15).
Notation "a <=T b"  := (lteT a b = true) (at level 15).
Notation "a !<=T b" := (lteT a b = false) (at level 15).
Notation "a <S b"   := (below lteS b a = true) (at level 15).
Notation "a !<S b"  := (below lteS b a = false) (at level 15).
Notation "a <T b"   := (below lteT b a = true) (at level 15).
Notation "a !<T b"  := (below lteT b a = false) (at level 15).


Lemma brel_left_lex_congruence : brel_congruence (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]; intros H1 H2.
       unfold brel_product in H1, H2. 
       destruct (bop_and_elim _ _ H1) as [C1 C2].
       destruct (bop_and_elim _ _ H2) as [C3 C4].
       unfold brel_left_lex. 
       rewrite (equiv_congruence S eqS lteS lteConS _ _ _ _ C1 C3). 
       rewrite (lteConT _ _ _ _ C2 C4). 
       rewrite (below_congruence S eqS lteS lteConS _ _ _ _ C3 C1). 
       reflexivity.
Qed.        

Lemma brel_left_lex_reflexive 
      (lteRefS : brel_reflexive S lteS)
      (lteRefT : brel_reflexive T lteT) : 
        brel_reflexive (S * T) (lteS [*] lteT). 
Proof. intros [s t]. unfold brel_left_lex.
       apply bop_or_intro. right.
       apply bop_and_intro.
          apply equiv_reflexive; auto. 
          apply lteRefT.
Qed.           

Lemma brel_left_lex_transitive
      (lteTrnS : brel_transitive S lteS)
      (lteTrnT : brel_transitive T lteT) :
         brel_transitive (S * T) (lteS [*] lteT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. unfold brel_left_lex.
       intros A B.
       apply bop_or_intro.        
       apply bop_or_elim in A. apply bop_or_elim in B. 
       destruct A as [A | A]; destruct B as [B | B]. 
       - left. apply (below_transitive S lteS lteTrnS _ _ _ A B). 
       - apply bop_and_elim in B. destruct B as [B1 B2]. 
         left. apply equiv_elim in B1. destruct B1 as [_ B1].
         apply (below_pseudo_transitive_right S lteS lteTrnS _ _ _ A B1). 
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply equiv_elim in A1. destruct A1 as [_ A1].
         left. apply (below_pseudo_transitive_left S lteS lteTrnS _ _ _ A1 B).
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply bop_and_elim in B. destruct B as [B1 B2].
         right.
         rewrite (lteTrnT _ _ _ A2 B2).
         rewrite (equiv_transitive S lteS lteTrnS _ _ _ B1 A1).
         compute. reflexivity. 
Qed.

Lemma brel_left_lex_antisymmetric
      (lteTrnS : brel_transitive S lteS)
      (asymS : brel_antisymmetric S eqS lteS)
      (asymT : brel_antisymmetric T eqT lteT) :  
         brel_antisymmetric (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. intros [s1 t1] [s2 t2]. unfold brel_left_lex.
       intros A B. 
       apply bop_or_elim in A. apply bop_or_elim in B.
       unfold brel_product. 
       destruct A as [A | A]; destruct B as [B | B]. 
       - assert (C := below_transitive S lteS lteTrnS _ _ _ A B).
         rewrite (below_not_reflexive S lteS s1) in C. discriminate C.
       - apply bop_and_elim in B. destruct B as [B1 B2]. 
         apply equiv_elim in B1. destruct B1 as [_ B1].
         assert (C := below_pseudo_transitive_right S lteS lteTrnS _ _ _ A B1). 
         rewrite (below_not_reflexive S lteS s1) in C. discriminate C.
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply equiv_elim in A1. destruct A1 as [_ A1].
         assert (C := below_pseudo_transitive_left S lteS lteTrnS _ _ _ A1 B).
         rewrite (below_not_reflexive S lteS s1) in C. discriminate C.
       - apply bop_and_elim in A. destruct A as [A1 A2].
         apply bop_and_elim in B. destruct B as [B1 B2].
         rewrite (asymT _ _ A2 B2).
         apply equiv_elim in A1. destruct A1 as [A1 A3].
         rewrite (asymS _ _ A3 A1).         
         compute. reflexivity. 
Qed.

Lemma brel_left_lex_not_antisymmetric_v1 (wT : T)
      (lteRefT : brel_reflexive T lteT)
      (nasymS : brel_not_antisymmetric S eqS lteS) : 
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct nasymS as [[s1 s2] [[A B] C]].
       exists ((s1, wT), (s2, wT)); simpl. split.
       + split. 
         ++ apply bop_or_intro.
            right. apply bop_and_intro.
            +++ apply equiv_intro; auto. 
            +++ apply lteRefT. 
         ++ apply bop_or_intro.
            right. apply bop_and_intro.
            +++ apply equiv_intro; auto.
            +++ apply lteRefT.
       + apply bop_and_false_intro.
         left. exact C.
Defined.

Lemma brel_left_lex_not_antisymmetric_v2 (wS : S)
      (lteRefS : brel_reflexive S lteS)
      (nasymT : brel_not_antisymmetric T eqT lteT) : 
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct nasymT as [[t1 t2] [[A B] C]].
       exists ((wS, t1), (wS, t2)); simpl. split.
       + split. 
         ++ apply bop_or_intro.
            right. apply bop_and_intro.
            +++ apply equiv_intro; auto. 
            +++ exact A. 
         ++ apply bop_or_intro.
            right. apply bop_and_intro.
            +++ apply equiv_intro; auto.
            +++ exact B. 
       + apply bop_and_false_intro.
         right. exact C.
Defined.

Definition brel_left_lex_antisymmetric_decide
   (wS : S) (wT : T)
   (lteRefS : brel_reflexive S lteS)
   (lteRefT : brel_reflexive T lteT)
   (lteTrnS : brel_transitive S lteS)   
   (symS_d : brel_antisymmetric_decidable S eqS lteS)
   (symT_d : brel_antisymmetric_decidable T eqT lteT) :
     brel_antisymmetric_decidable (S * T) (eqS <*> eqT) (lteS [*] lteT) :=
  match symS_d with
  | inl symS  =>
    match symT_d with
    | inl symT  => inl (brel_left_lex_antisymmetric lteTrnS symS symT)
    | inr nsymT => inr (brel_left_lex_not_antisymmetric_v2 wS lteRefS nsymT)
    end 
  | inr nsymS => inr (brel_left_lex_not_antisymmetric_v1 wT lteRefT nsymS)         
  end.


(* do we need this?  Will we ever have a non-transitive order??? 
Lemma brel_left_lex_not_antisymmetric_v3 (wT : T)
      (lteRefS : brel_reflexive S lteS)
      (nlteTrnS : brel_not_transitive S lteS)
      (asymS : brel_antisymmetric S eqS lteS)
      (asymT : brel_antisymmetric T eqT lteT) :  
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct nlteTrnS as [[s1 [s2 s3]] [[A B] C]].
       case_eq(lteS s2 s1); intro D; case_eq(lteS s3 s2); intro E.
       + assert (I := asymS _ _ A D).
         assert (J := asymS _ _ B E).
         assert (K := trnS _ _ _ I J).
         rewrite (lteConS _ _ _ _ K (refS s3)) in C.
         rewrite (lteRefS s3) in C. discriminate C. 
       + assert (I := asymS _ _ A D).
         rewrite <- (lteConS _ _ _ _ I (refS s3)) in B. 
         rewrite B in C. discriminate C. 
       + assert (J := asymS _ _ B E).
         rewrite <- (lteConS _ _ _ _ (refS s1) (symS _ _ J)) in A.
         rewrite A in C. discriminate C. 
       + case_eq(lteS s1 s3); intro I;  case_eq(lteS s3 s1); intro J.
         ++ rewrite I in C. discriminate C. 
         ++ rewrite I in C. discriminate C. 
         ++ admit. 
         ++ admit. 
Admitted. 
 *)

Lemma brel_left_lex_trivial
      (trivS : order_trivial S lteS)
      (trivT : order_trivial T lteT) : 
        order_trivial (S * T) (lteS [*] lteT). 
Proof. intros [s t] [s' t']. unfold brel_left_lex.
       apply bop_or_intro. right.
       apply bop_and_intro.
          apply equiv_intro; auto. 
          apply trivT.
Qed.           

Lemma brel_left_lex_not_trivial_v1 (wT : T) 
      (ntrivS : order_not_trivial S lteS) : 
        order_not_trivial (S * T) (lteS [*] lteT). 
Proof. destruct ntrivS as [[s s'] P].
       exists ((s, wT), (s', wT)). compute.
       rewrite P. reflexivity. 
Defined.       

Lemma brel_left_lex_not_trivial_v2 (wS : S)
      (lteRefS : brel_reflexive S lteS)      
      (ntrivT : order_not_trivial T lteT) : 
        order_not_trivial (S * T) (lteS [*] lteT). 
Proof. destruct ntrivT as [[t t'] P].
       exists ((wS, t), (wS, t')). compute.
       rewrite P. rewrite (lteRefS wS). reflexivity. 
Defined.

Definition brel_left_lex_trivial_decide
   (wS : S) (wT : T)
   (lteRefS : brel_reflexive S lteS)            
   (trvS_d : order_trivial_decidable S lteS)
   (trvT_d : order_trivial_decidable T lteT) :
     order_trivial_decidable (S * T) (lteS [*] lteT) :=
  match trvS_d with
  | inl trvS  =>
    match trvT_d with
    | inl trvT  => inl (brel_left_lex_trivial trvS trvT)
    | inr ntrvT => inr (brel_left_lex_not_trivial_v2 wS lteRefS ntrvT)
    end 
  | inr ntrvS => inr (brel_left_lex_not_trivial_v1 wT ntrvS)         
  end.



Lemma brel_left_lex_total
      (totS : brel_total S lteS)
      (totT : brel_total T lteT) : 
        brel_total (S * T) (lteS [*] lteT). 
Proof. intros [s t] [s' t']; compute. 
       destruct (totS s s') as [A | A]; 
       destruct (totT t t') as [B | B]; rewrite A, B.
       + case_eq(lteS s' s); intro C; auto. 
       + case_eq(lteS s' s); intro C; auto. 
       + case_eq(lteS s s'); intro C; auto.
       + case_eq(lteS s s'); intro C; auto.
Qed.           

Lemma brel_left_lex_not_total_v1 (wT : T) 
      (ntotS : brel_not_total S lteS) : 
        brel_not_total (S * T) (lteS [*] lteT). 
Proof. destruct ntotS as [[s s'] [A B]]. 
       exists ((s, wT), (s', wT)); compute.
       rewrite A, B; auto.
Defined.


Lemma brel_left_lex_not_total_v2 (wS : S)
      (lteRefS : brel_reflexive S lteS)            
      (ntotT : brel_not_total T lteT) : 
        brel_not_total (S * T) (lteS [*] lteT). 
Proof. destruct ntotT as [[t t'] [A B]]. 
       exists ((wS, t), (wS, t')); compute.
       rewrite (lteRefS wS). rewrite A, B; auto.
Defined.


Definition brel_left_lex_total_decide
   (wS : S) (wT : T)
   (lteRefS : brel_reflexive S lteS)            
   (totS_d : brel_total_decidable S lteS)
   (totT_d : brel_total_decidable T lteT) :
     brel_total_decidable (S * T) (lteS [*] lteT) :=
  match totS_d with
  | inl totS  =>
    match totT_d with
    | inl totT  => inl (brel_left_lex_total totS totT)
    | inr ntotT => inr (brel_left_lex_not_total_v2 wS lteRefS ntotT)
    end 
  | inr ntotS => inr (brel_left_lex_not_total_v1 wT ntotS)         
  end.



Lemma brel_left_lex_exists_qo_top
      (topS : brel_exists_qo_top S eqS lteS)
      (topT : brel_exists_qo_top T eqT lteT) : 
        brel_exists_qo_top (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct topS as [s [A B]]; destruct topT as [t [C D]].
       exists (s, t). unfold brel_is_qo_top. split.
       + intros [s' t']. compute. 
         rewrite (A s').
         case_eq(lteS s s'); intro E; auto. 
       + intros [s' t'] E F. compute in *.
         rewrite (A s') in E, F.
         case_eq(lteS s s'); intro I.
         ++ rewrite I in E, F.
            rewrite (B _ I (A s')).
            exact (D _ E F).
         ++ rewrite I in E.
            discriminate E. 
Defined. 


Lemma brel_left_lex_not_exists_qo_top_v1 
      (lteRefT : brel_reflexive T lteT)            
      (ntopS : brel_not_exists_qo_top S eqS lteS) : 
        brel_not_exists_qo_top (S * T) (eqS <*> eqT) (lteS [*] lteT). 
 Proof. intros [s t]. unfold brel_not_is_qo_top.
       destruct (ntopS s) as [[s' A] | [s' [[B C] D]]].
       + left. exists (s', t). compute. rewrite A; auto.
       + right. exists (s', t). compute.
         rewrite B, C, D. rewrite (lteRefT t); auto. 
Defined. 

Lemma brel_left_lex_not_exists_qo_top_v2
      (lteRefS : brel_reflexive S lteS)
      (lteRefT : brel_reflexive T lteT)                  
      (topS : brel_exists_qo_top S eqS lteS)
      (ntopT : brel_not_exists_qo_top T eqT lteT) : 
        brel_not_exists_qo_top (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct topS as [s [L R]]; intros [s' t].
       unfold brel_not_is_qo_top.       
       destruct (ntopT t) as [[t' B] | [t' [[A B] C]]].
       + left. exists (s, t'). compute. rewrite B, (L s').
         case_eq(lteS s s'); intro C; auto.
       + right. exists (s', t'). compute.
         rewrite (lteRefS s'), A, B, C, (refS s'); auto. 
Defined. 

Definition brel_left_lex_exists_qo_top_decide
   (lteRefS : brel_reflexive S lteS)           
   (lteRefT : brel_reflexive T lteT)                       
   (topS_d : brel_exists_qo_top_decidable S eqS lteS)
   (topT_d : brel_exists_qo_top_decidable T eqT lteT) :
     brel_exists_qo_top_decidable (S * T) (eqS <*> eqT) (lteS [*] lteT) :=
  match topS_d with
  | inl topS  =>
    match topT_d with
    | inl topT  => inl (brel_left_lex_exists_qo_top topS topT)
    | inr ntopT => inr (brel_left_lex_not_exists_qo_top_v2 lteRefS lteRefT topS ntopT)
    end 
  | inr ntopS => inr (brel_left_lex_not_exists_qo_top_v1 lteRefT ntopS)         
  end.


Lemma brel_left_lex_exists_qo_bottom 
      (bottomS : brel_exists_qo_bottom S eqS lteS)
      (bottomT : brel_exists_qo_bottom T eqT lteT) : 
        brel_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct bottomS as [s [A B]]; destruct bottomT as [t [C D]].
       exists (s, t). split. 
       + intros [s' t']. compute.
         rewrite (A s'), (C t').
         case_eq(lteS s' s); intro E; auto.
       + intros [s' t'] E F.
         compute in E, F.
         rewrite (A s') in E, F.
         rewrite (C t') in E. 
         compute.
         case_eq(lteS s' s); intro I; rewrite I in E, F.
         ++ rewrite (B s' (A s') I).
            rewrite (D t' (C t') F); auto.
         ++ discriminate F. 
Defined. 

Lemma brel_left_lex_not_exists_qo_bottom_v1
      (lteRefT : brel_reflexive T lteT)                       
      (nbottomS : brel_not_exists_qo_bottom S eqS lteS) : 
        brel_not_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. intros [s t]. destruct (nbottomS s) as [[s' A] | [s' [[A B] C]]].
       + left. exists (s', t). compute. rewrite A; auto.
       + right. exists (s', t). compute.
         rewrite A, B, C. rewrite (lteRefT t); auto.
Defined. 

Lemma brel_left_lex_not_exists_qo_bottom_v2
      (lteRefS : brel_reflexive S lteS)           
      (bottomS : brel_exists_qo_bottom S eqS lteS)
      (nbottomT : brel_not_exists_qo_bottom T eqT lteT) : 
        brel_not_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS [*] lteT). 
Proof. destruct bottomS as [s [A B]]; intros [s' t].
       destruct (nbottomT t) as [[t' C] | [t' [[C D] E]]].
       + left. exists (s, t'). compute. rewrite (A s'), C.
         case_eq(lteS s' s); intro D; auto.
       + right. exists (s', t'). compute.
         rewrite (lteRefS s'), C, D, E, (refS s'); auto. 
Defined. 


Definition brel_left_lex_exists_qo_bottom_decide
   (lteRefS : brel_reflexive S lteS)           
   (lteRefT : brel_reflexive T lteT)                       
   (bottomS_d : brel_exists_qo_bottom_decidable S eqS lteS)
   (bottomT_d : brel_exists_qo_bottom_decidable T eqT lteT) :
     brel_exists_qo_bottom_decidable (S * T) (eqS <*> eqT) (lteS [*] lteT) :=
  match bottomS_d with
  | inl bottomS  =>
    match bottomT_d with
    | inl bottomT  => inl (brel_left_lex_exists_qo_bottom bottomS bottomT)
    | inr nbottomT => inr (brel_left_lex_not_exists_qo_bottom_v2 lteRefS bottomS nbottomT)
    end 
  | inr nbottomS => inr (brel_left_lex_not_exists_qo_bottom_v1 lteRefT nbottomS)         
  end.


End Theory. 


Section ACAS.

Section Proofs. 
Variable S    : Type.
Variable T    : Type.
Variable wS   : S.
Variable wT   : T. 
Variable eqS  : brel S.
Variable lteS : brel S.
Variable eqT  : brel T.
Variable lteT : brel T. 

Definition left_lex_or_proofs
           (pS : or_proofs S eqS lteS)
           (pT : or_proofs T eqT lteT) := 
let congS   := A_or_congruence _ _ _ pS in
let lteRefS := A_or_reflexive _ _ _ pS in
let lteTrnS := A_or_transitive _ _ _ pS in
let symS_d  := A_or_antisymmetric_d _ _ _ pS in
let totS_d  := A_or_total_d _ _ _ pS in
let trvS_d  := A_or_trivial_d _ _ _ pS in
let congT   := A_or_congruence _ _ _ pT in
let lteRefT := A_or_reflexive _ _ _ pT in
let lteTrnT := A_or_transitive _ _ _ pT in
let symT_d  := A_or_antisymmetric_d _ _ _ pT in
let totT_d  := A_or_total_d _ _ _ pT in
let trvT_d  := A_or_trivial_d _ _ _ pT in
{|    
  A_or_congruence      := brel_left_lex_congruence S T eqS eqT lteS congS lteT congT 
; A_or_reflexive       := brel_left_lex_reflexive S T lteS lteT lteRefS lteRefT 
; A_or_transitive      := brel_left_lex_transitive S T lteS lteT lteTrnS lteTrnT 
; A_or_antisymmetric_d := brel_left_lex_antisymmetric_decide S T eqS eqT lteS lteT wS wT lteRefS lteRefT lteTrnS symS_d symT_d 
; A_or_total_d         := brel_left_lex_total_decide S T lteS lteT wS wT lteRefS totS_d totT_d 
; A_or_trivial_d       := brel_left_lex_trivial_decide S T lteS lteT wS wT lteRefS trvS_d trvT_d 
|}.
  
End Proofs.


Section Combinators.

Open Scope string_scope.

Definition A_or_left_lex {S T : Type} (A : A_or S) (B : A_or T) : A_or (S * T) :=
let eqvS   := A_or_eqv _ A in
let eqvT   := A_or_eqv _ B in
let refS   := A_eqv_reflexive _ _ (A_eqv_proofs _ eqvS)  in 
let wS     := A_eqv_witness _ eqvS in 
let wT     := A_eqv_witness _ eqvT in
let eqS    := A_eqv_eq _ eqvS in 
let eqT    := A_eqv_eq _ eqvT in
let lteS   := A_or_lte _ A in 
let lteT   := A_or_lte _ B in
let topS_d := A_or_exists_top_d _ A in
let topT_d := A_or_exists_top_d _ B in
let botS_d := A_or_exists_bottom_d _ A in
let botT_d := A_or_exists_bottom_d _ B in 
let pS     := A_or_proofs _ A in
let pT     := A_or_proofs _ B in
let lteRefS := A_or_reflexive _ _ _ pS in
let lteRefT := A_or_reflexive _ _ _ pT in 
{|
  A_or_eqv             := A_eqv_product _ _ eqvS eqvT 
; A_or_lte             := brel_left_lex lteS lteT 
; A_or_exists_top_d    := brel_left_lex_exists_qo_top_decide S T eqS refS eqT lteS lteT lteRefS lteRefT topS_d topT_d 
; A_or_exists_bottom_d := brel_left_lex_exists_qo_bottom_decide S T eqS refS eqT lteS lteT lteRefS lteRefT botS_d botT_d 
; A_or_proofs          := left_lex_or_proofs S T wS wT eqS lteS eqT lteT pS pT
; A_or_ast             := Ast_or_llex (A_or_ast _ A, A_or_ast  _ B)
|}.
End Combinators.   

End ACAS.   

Section AMCAS.

  Open Scope string_scope. 

  Definition A_mcas_or_left_lex  {S T : Type} (A : @A_or_mcas S) (B : @A_or_mcas T) : @A_or_mcas (S * T) :=
    match A_or_mcas_cast_up A, A_or_mcas_cast_up B with
    | A_OR_Error sl1, A_OR_Error sl2 => A_OR_Error (sl1 ++ sl2)
    | A_OR_Error sl1, _ => A_OR_Error sl1
    | _, A_OR_Error sl2 => A_OR_Error sl2                 
    | A_OR_or A', A_OR_or B' => A_or_classify (A_OR_or (A_or_left_lex A' B'))
    | _, _ => A_OR_Error ("mcas_or_left_lex: internal error" :: nil)
    end. 

End AMCAS.

Section CAS.


Section Proofs. 
Variable S    : Type.
Variable T    : Type.
Variable wS   : S.
Variable wT   : T. 
Variable eqS  : brel S.
Variable lteS : brel S.
Variable eqT  : brel T.
Variable lteT : brel T.


Definition brel_left_lex_total_certify
   (wS : S) (wT : T)
   (totS_d : @certify_total S)
   (totT_d : @certify_total T) : 
     @certify_total (S * T) :=
  match totS_d with
  | Certify_Total  =>
    match totT_d with
    | Certify_Total  => Certify_Total
    | Certify_Not_Total (t1, t2) => Certify_Not_Total ((wS, t1), (wS, t2))
    end 
  | Certify_Not_Total (s1, s2) => Certify_Not_Total ((s1, wT), (s2, wT))
  end.




Definition brel_left_lex_trivial_certify
   (wS : S) (wT : T)
   (totS_d : @order_trivial_certifiable S)
   (totT_d : @order_trivial_certifiable T) : 
     @order_trivial_certifiable (S * T) :=
  match totS_d with
  | Certify_Order_Trivial  =>
    match totT_d with
    | Certify_Order_Trivial  => Certify_Order_Trivial
    | Certify_Order_Not_Trivial (t1, t2) => Certify_Order_Not_Trivial ((wS, t1), (wS, t2))
    end 
  | Certify_Order_Not_Trivial (s1, s2) => Certify_Order_Not_Trivial ((s1, wT), (s2, wT))
  end.

Definition brel_left_lex_antisymmetric_certify
   (wS : S) (wT : T)
   (totS_d : @certify_antisymmetric S)
   (totT_d : @certify_antisymmetric T) : 
     @certify_antisymmetric (S * T) :=
  match totS_d with
  | Certify_Antisymmetric  =>
    match totT_d with
    | Certify_Antisymmetric  => Certify_Antisymmetric
    | Certify_Not_Antisymmetric (t1, t2) => Certify_Not_Antisymmetric ((wS, t1), (wS, t2))
    end 
  | Certify_Not_Antisymmetric (s1, s2) => Certify_Not_Antisymmetric ((s1, wT), (s2, wT))
  end.

Definition left_lex_or_certs
           (pS : @or_certificates S)
           (pT : @or_certificates T) := 
let symS_d  := or_antisymmetric_d pS in
let totS_d  := or_total_d pS in
let trvS_d  := or_trivial_d pS in
let symT_d  := or_antisymmetric_d pT in
let totT_d  := or_total_d pT in
let trvT_d  := or_trivial_d pT in
{|    
  or_congruence      := Assert_Brel_Congruence 
; or_reflexive       := Assert_Reflexive 
; or_transitive      := Assert_Transitive
; or_antisymmetric_d := brel_left_lex_antisymmetric_certify wS wT symS_d symT_d 
; or_total_d         := brel_left_lex_total_certify wS wT totS_d totT_d 
; or_trivial_d       := brel_left_lex_trivial_certify wS wT trvS_d trvT_d 
|}.

Definition brel_left_lex_exists_qo_bottom_certify
   (bottomS_d : @certify_exists_qo_bottom S)
   (bottomT_d : @certify_exists_qo_bottom T) :
     @certify_exists_qo_bottom (S * T) :=
  match bottomS_d with
  | Certify_Exists_Qo_Bottom s  =>
    match bottomT_d with
    | Certify_Exists_Qo_Bottom t  => Certify_Exists_Qo_Bottom (s, t)
    | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
    end 
  | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
  end.

Definition brel_left_lex_exists_qo_top_certify
   (bottomS_d : @certify_exists_qo_top S)
   (bottomT_d : @certify_exists_qo_top T) :
     @certify_exists_qo_top (S * T) :=
  match bottomS_d with
  | Certify_Exists_Qo_Top s  =>
    match bottomT_d with
    | Certify_Exists_Qo_Top t  => Certify_Exists_Qo_Top (s, t)
    | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
    end 
  | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
  end.

  
End Proofs. 
 

Section Combinators.

Open Scope string_scope.

Definition or_left_lex {S T : Type} (A : @or S) (B : @or T) : @or (S * T) :=
let eqvS   := or_eqv A in
let eqvT   := or_eqv B in
let wS     := eqv_witness eqvS in 
let wT     := eqv_witness eqvT in
let lteS   := or_lte A in 
let lteT   := or_lte B in
let topS_d := or_exists_top_d A in
let topT_d := or_exists_top_d B in
let botS_d := or_exists_bottom_d A in
let botT_d := or_exists_bottom_d B in
let pS     := or_certs A in
let pT     := or_certs B in
{|
  or_eqv             := eqv_product eqvS eqvT 
; or_lte             := brel_left_lex lteS lteT 
; or_exists_top_d    := brel_left_lex_exists_qo_top_certify _ _ topS_d topT_d 
; or_exists_bottom_d := brel_left_lex_exists_qo_bottom_certify _ _ botS_d botT_d 
; or_certs          := left_lex_or_certs S T wS wT pS pT 
; or_ast             := Ast_or_llex (or_ast A, or_ast  B)
|}.

End Combinators.   
  
End CAS.   

Section MCAS.

  Open Scope string_scope. 

  Definition mcas_or_left_lex  {S T : Type} (A : @or_mcas S) (B : @or_mcas T) : @or_mcas (S * T) :=
    match or_mcas_cast_up A, or_mcas_cast_up B with
    | OR_Error sl1, OR_Error sl2 => OR_Error (sl1 ++ sl2)
    | OR_Error sl1, _ => OR_Error sl1
    | _, OR_Error sl2 => OR_Error sl2                 
    | OR_or A', OR_or B' => or_classify (OR_or (or_left_lex A' B'))
    | _, _ => OR_Error ("mcas_or_left_lex: internal error" :: nil)
    end. 

End MCAS.   

Section Verify.

Section Proofs.

Variable S    : Type. 
Variable T    : Type.
Variable wS   : S.
Variable wT   : T. 
Variable eqS  : brel S.
Variable lteS : brel S.
Variable eqT  : brel T.
Variable lteT : brel T.


Lemma correct_left_lex_exists_qo_top_certify
      (refS    : brel_reflexive S eqS)                 
      (lteRefS : brel_reflexive S lteS)           
      (lteRefT : brel_reflexive T lteT)                       
      (topS_d : brel_exists_qo_top_decidable S eqS lteS)
      (topT_d : brel_exists_qo_top_decidable T eqT lteT) :      
  p2c_exists_qo_top_check (S * T)
      (brel_product eqS eqT)
      (brel_left_lex lteS lteT)
      (brel_left_lex_exists_qo_top_decide S T eqS refS eqT lteS lteT lteRefS lteRefT topS_d topT_d)
  =
  brel_left_lex_exists_qo_top_certify S T
      (p2c_exists_qo_top_check S eqS lteS topS_d)
      (p2c_exists_qo_top_check T eqT lteT topT_d).
Proof. destruct topS_d as [[s [A B]] | A];
       destruct topT_d as [[t [C D]] | C]; simpl; try reflexivity.
Qed.

Lemma correct_left_lex_exists_qo_bottom_certify
      (refS    : brel_reflexive S eqS)                 
      (lteRefS : brel_reflexive S lteS)           
      (lteRefT : brel_reflexive T lteT)                       
      (bottomS_d : brel_exists_qo_bottom_decidable S eqS lteS)
      (bottomT_d : brel_exists_qo_bottom_decidable T eqT lteT) :
  p2c_exists_qo_bottom_check (S * T)
      (brel_product eqS eqT)
      (brel_left_lex lteS lteT)
      (brel_left_lex_exists_qo_bottom_decide S T eqS refS eqT lteS lteT lteRefS lteRefT bottomS_d bottomT_d)
  =
  brel_left_lex_exists_qo_bottom_certify S T
      (p2c_exists_qo_bottom_check S eqS lteS bottomS_d)
      (p2c_exists_qo_bottom_check T eqT lteT bottomT_d).
Proof. destruct bottomS_d as [[s [A B]] | A];
       destruct bottomT_d as [[t [C D]] | C]; simpl; try reflexivity.
Qed.

Lemma correct_left_lex_antisymmetric_certify
  (lteRefS : brel_reflexive S lteS)           
  (lteRefT : brel_reflexive T lteT)                       
  (lteTrnS : brel_transitive S lteS)                       
  (asymS_d : brel_antisymmetric_decidable S eqS lteS)
  (asymT_d : brel_antisymmetric_decidable T eqT lteT) : 
     p2c_antisymmetric_check (S * T)
        (brel_product eqS eqT)
        (brel_left_lex lteS lteT)
        (brel_left_lex_antisymmetric_decide S T eqS eqT lteS lteT wS wT
            lteRefS lteRefT lteTrnS asymS_d asymT_d)
     =
      brel_left_lex_antisymmetric_certify S T wS wT
        (p2c_antisymmetric_check S eqS lteS asymS_d)
        (p2c_antisymmetric_check T eqT lteT asymT_d).
Proof. destruct asymS_d as [A | [[s1 s2] [[A B] C]]]; 
       destruct asymT_d as [D | [[t1 t2] [[D E] F]]];
       simpl; try reflexivity. 
Qed. 


Lemma correct_left_lex_total_certify
  (lteRefS : brel_reflexive S lteS)                 
  (totS_d : brel_total_decidable S lteS)
  (totT_d : brel_total_decidable T lteT) : 
      p2c_total_check (S * T) (brel_left_lex lteS lteT)
                      (brel_left_lex_total_decide S T lteS lteT wS wT lteRefS totS_d totT_d)
      =
      brel_left_lex_total_certify S T wS wT      
        (p2c_total_check S lteS totS_d)                      
        (p2c_total_check T lteT totT_d).
Proof. destruct totS_d as [A | [[s1 s2] [A B]]]; 
       destruct totT_d as [C | [[t1 t2] [C D]]];
       simpl; reflexivity. 
Qed. 

Lemma correct_left_lex_trivial_certify
  (lteRefS : brel_reflexive S lteS)                       
  (trvS_d : order_trivial_decidable S lteS)
  (trvT_d : order_trivial_decidable T lteT) : 
      p2c_order_trivial_certificate (S * T) (brel_left_lex lteS lteT)
        (brel_left_lex_trivial_decide S T lteS lteT wS wT lteRefS trvS_d trvT_d)
      =
      brel_left_lex_trivial_certify S T wS wT
        (p2c_order_trivial_certificate S lteS trvS_d)
        (p2c_order_trivial_certificate T lteT trvT_d). 
Proof. destruct trvS_d as [A | [[s1 s2] A]]; 
       destruct trvT_d as [C | [[t1 t2] C]];
       simpl; reflexivity. 
Qed. 


  Lemma correct_left_lex_or_certs (pS : or_proofs S eqS lteS) (pT : or_proofs T eqT lteT) : 
        P2C_or (brel_product eqS eqT) (brel_left_lex lteS lteT)
               (left_lex_or_proofs S T wS wT eqS lteS eqT lteT pS pT)
        = 
        left_lex_or_certs S T wS wT (P2C_or eqS lteS pS) (P2C_or eqT lteT pT). 
  Proof. destruct pS, pT; unfold P2C_or, left_lex_or_proofs, left_lex_or_certs; simpl.
         rewrite correct_left_lex_antisymmetric_certify.
         rewrite correct_left_lex_total_certify. 
         rewrite correct_left_lex_trivial_certify.
         reflexivity. 
  Qed. 
    
  End Proofs.     

Section Combinators.
  
  Theorem correct_or_left_lex (S T : Type) (A : A_or S) (B : A_or T) :
    or_left_lex (A2C_or A) (A2C_or B) = A2C_or (A_or_left_lex A B).
  Proof. destruct A, B. unfold or_left_lex, A_or_left_lex, A2C_or; simpl.
         rewrite correct_eqv_product.
         rewrite correct_left_lex_or_certs. 
         rewrite correct_left_lex_exists_qo_bottom_certify.
         rewrite correct_left_lex_exists_qo_top_certify.          
         reflexivity. 
  Qed.

  Theorem correct_mcas_or_left_lex (S T : Type) (A : @A_or_mcas S) (B : @A_or_mcas T) :
    mcas_or_left_lex (A2C_mcas_or A) (A2C_mcas_or B) = A2C_mcas_or (A_mcas_or_left_lex A B).
  Proof. unfold mcas_or_left_lex, A_mcas_or_left_lex.
         rewrite correct_or_mcas_cast_up.
         rewrite correct_or_mcas_cast_up.         
         destruct (A_or_cast_up_is_error_or_or S A) as [[l1 A'] | [s1 A']];
         destruct (A_or_cast_up_is_error_or_or T B) as [[l2 B'] | [s2 B']].
         + rewrite A', B'. simpl. reflexivity.
         + rewrite A', B'. simpl. reflexivity.
         + rewrite A', B'. simpl. reflexivity.
         + rewrite A', B'. simpl. 
           rewrite correct_or_left_lex. 
           apply correct_or_classify_or. 
  Qed.
  
End Combinators.

End Verify.   
