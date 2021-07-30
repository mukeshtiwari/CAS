Require Import Coq.Bool.Bool.    

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.


Require Import CAS.coq.eqv.product. (* some properties proved here *) 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.in_set. 

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
     apply andb_is_true_right. 
     apply andb_is_true_left in A. destruct A as [A1 A2].
     apply andb_is_true_left in B. destruct B as [B1 B2].
     rewrite (AS _ _ A1 B1). rewrite (AT _ _ A2 B2); auto.  
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
  