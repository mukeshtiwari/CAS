Require Import Coq.Bool.Bool. 
Require Import CAS.coq.common.base. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.sg.product. 


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

(* *********************************** *) 


Lemma bop_product_id_equals_ann : 
      bops_id_equals_ann S rS addS mulS → 
      bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT). split.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
Defined. 

Lemma bop_product_not_id_equals_ann_left : 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H s) as [ [s' [L | R]] | [s' [L | R]]].
          left. exists (s', t). left. compute. rewrite L. reflexivity. 
          left. exists (s', t). right. compute. rewrite R. reflexivity.           
          right. exists (s', t). left. compute. rewrite L. reflexivity. 
          right. exists (s', t). right. compute. rewrite R. reflexivity.           
Defined. 

Lemma bop_product_not_id_equals_ann_right : 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H t) as [ [t' [L | R]] | [t' [L | R]]].
          left. exists (s, t'). left. compute. rewrite L. case_eq( rS (s +S s) s); intro K; reflexivity. 
          left. exists (s, t'). right. compute. rewrite R. case_eq( rS (s +S s) s); intro K; reflexivity.           
          right. exists (s, t'). left. compute. rewrite L. case_eq( rS (s *S s) s); intro K; reflexivity. 
          right. exists (s, t'). right. compute. rewrite R. case_eq( rS (s *S s) s); intro K; reflexivity.           
Defined. 


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
       
Definition bop_product_id_equals_ann_decide : 
      bops_id_equals_ann_decidable S rS addS mulS → bops_id_equals_ann_decidable T rT addT mulT →  
        bops_id_equals_ann_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bop_product_id_equals_ann ieaS ieaT)
     | inr nieaT => inr _ (bop_product_not_id_equals_ann_right nieaT)
     end 
   | inr nieaS   => inr _ (bop_product_not_id_equals_ann_left nieaS)
   end. 


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

  Definition bs_proofs_product : 
  ∀ (S T: Type) 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 
     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 
        bs_proofs (S * T) 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT)
:= λ S T rS rT plusS timesS plusT timesT s t eqvS eqvT pS pT, 
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
; A_bs_plus_id_is_times_ann_d := 
     bop_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT 
        (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)
        (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)
; A_bs_times_id_is_plus_ann_d :=  
     bop_product_id_equals_ann_decide S T rS rT timesS plusS timesT plusT  
        (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
        (A_bs_times_id_is_plus_ann_d T rT plusT timesT pT)
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
   ; A_bs_proofs    := bs_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_proofs S bsS) 
                           (A_bs_proofs T bsT) 
   ; A_bs_ast        := Ast_bs_product(A_bs_ast S bsS, A_bs_ast T bsT)
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

; A_semiring_plus_id_is_times_ann_d   :=
     bop_product_id_equals_ann_decide S T rS rT addS mulS addT mulT  
        (A_semiring_plus_id_is_times_ann_d S rS addS mulS srS)
        (A_semiring_plus_id_is_times_ann_d T rT addT mulT srT)                                  

; A_semiring_times_id_is_plus_ann_d   :=
     bop_product_id_equals_ann_decide S T rS rT mulS addS mulT addT  
        (A_semiring_times_id_is_plus_ann_d S rS addS mulS srS)
        (A_semiring_times_id_is_plus_ann_d T rT addT mulT srT)                                  
                                                                     
; A_semiring_left_left_absorptive_d   :=
    bops_product_left_left_absorptive_decide S T rS rT s t addS mulS addT mulT
        (A_semiring_left_left_absorptive_d S rS addS mulS srS)
        (A_semiring_left_left_absorptive_d T rT addT mulT srT)                                  

; A_semiring_left_right_absorptive_d  :=
    bops_product_left_right_absorptive_decide S T rS rT s t addS mulS addT mulT
        (A_semiring_left_right_absorptive_d S rS addS mulS srS)
        (A_semiring_left_right_absorptive_d T rT addT mulT srT)                                  

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
   ; A_semiring_proofs       := semiring_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                                   (A_semiring_proofs S sr1)
                                   (A_semiring_proofs T sr2)                                   
   ; A_semiring_ast  := Ast_semiring_product (A_semiring_ast S sr1, A_semiring_ast T sr2)
|}.

Definition A_dioid_product : ∀ (S T : Type),  A_dioid S ->  A_dioid T -> A_dioid (S * T) 
:= λ S T sr1 sr2,
let eqvS   := A_dioid_eqv S sr1   in
let eqvT   := A_dioid_eqv T sr2   in
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
let plusS  := A_dioid_plus S sr1  in 
let plusT  := A_dioid_plus T sr2  in
let timesS := A_dioid_times S sr1 in 
let timesT := A_dioid_times T sr2 in 
{| 
     A_dioid_eqv          := A_eqv_product S T eqvS eqvT 
   ; A_dioid_plus         := bop_product plusS plusT 
   ; A_dioid_times        := bop_product timesS timesT 
   ; A_dioid_plus_proofs  := sg_CI_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                                (A_dioid_plus_proofs S sr1)
                                (A_dioid_plus_proofs T sr2)                                 
   ; A_dioid_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                                (A_dioid_times_proofs S sr1)
                                (A_dioid_times_proofs T sr2)                                 
   ; A_dioid_proofs       := semiring_proofs_product S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                                   (A_dioid_proofs S sr1)
                                   (A_dioid_proofs T sr2)                                   
   ; A_dioid_ast  := Ast_dioid_product (A_dioid_ast S sr1, A_dioid_ast T sr2)
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
   ; A_distributive_lattice_proofs  := distributive_lattice_proofs_product S T rS rT joinS meetS joinT meetT peqvS peqvT  
                                   (A_distributive_lattice_proofs S sr1)
                                   (A_distributive_lattice_proofs T sr2)                                   
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_product (A_distributive_lattice_ast S sr1, A_distributive_lattice_ast T sr2)
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
   ; A_lattice_proofs  := lattice_proofs_product S T rS rT joinS meetS joinT meetT s t peqvS peqvT  
                                   (A_lattice_proofs S sr1)
                                   (A_lattice_proofs T sr2)                                   
   ; A_lattice_ast  := Ast_lattice_product (A_lattice_ast S sr1, A_lattice_ast T sr2)
|}.

  

End ACAS.


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

Definition bop_product_plus_id_is_times_ann_check : 
   ∀ {S T : Type},  
     @check_plus_id_equals_times_ann S -> 
     @check_plus_id_equals_times_ann T -> 
     @check_plus_id_equals_times_ann (S * T) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann  
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann  
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 

Definition bop_product_times_id_equals_plus_ann_check : 
   ∀ {S T : Type},  
     @check_times_id_equals_plus_ann S -> 
     @check_times_id_equals_plus_ann T -> 
     @check_times_id_equals_plus_ann (S * T) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann  
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann 
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
; bs_plus_id_is_times_ann_d   := bop_product_plus_id_is_times_ann_check 
                                     (bs_plus_id_is_times_ann_d bsS)
                                     (bs_plus_id_is_times_ann_d bsT)
; bs_times_id_is_plus_ann_d   := bop_product_times_id_equals_plus_ann_check 
                                     (bs_times_id_is_plus_ann_d bsS)
                                     (bs_times_id_is_plus_ann_d bsT)
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
   ; bs_plus_certs  := sg_certs_product
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_plus_certs bsS) 
                           (bs_plus_certs bsT) 
   ; bs_times_certs := sg_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_times_certs bsS) 
                           (bs_times_certs bsT) 
   ; bs_certs       := bs_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_certs bsS) 
                           (bs_certs bsT) 
   ; bs_ast         := Ast_bs_product(bs_ast bsS, bs_ast bsT)
   |}. 


Definition semiring_certs_product : 
  ∀ {S T : Type}, S -> T -> @semiring_certificates S -> @semiring_certificates T ->  @semiring_certificates (S * T)
:= λ {S T} s t srS srT, 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_plus_id_is_times_ann_d   := bop_product_plus_id_is_times_ann_check 
                                         (semiring_plus_id_is_times_ann_d srS)
                                         (semiring_plus_id_is_times_ann_d srT)                                         
; semiring_times_id_is_plus_ann_d   := bop_product_times_id_equals_plus_ann_check 
                                         (semiring_times_id_is_plus_ann_d srS)
                                         (semiring_times_id_is_plus_ann_d srT)                                         
; semiring_left_left_absorptive_d   := bop_product_left_left_absorptive_check s t
                                         (semiring_left_left_absorptive_d srS)
                                         (semiring_left_left_absorptive_d srT)
; semiring_left_right_absorptive_d  := bop_product_left_right_absorptive_check s t 
                                         (semiring_left_right_absorptive_d srS)
                                         (semiring_left_right_absorptive_d srT)   
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
   ; semiring_certs        := semiring_certs_product wS wT (semiring_certs s1) (semiring_certs s2) 
   ; semiring_ast          := Ast_semiring_product (semiring_ast s1, semiring_ast s2)
|}.

Definition dioid_product : ∀ (S T : Type),  @dioid S ->  @dioid T -> @dioid (S * T) 
:= λ S T sr1 sr2,
let eqvS   := dioid_eqv sr1   in
let eqvT   := dioid_eqv sr2   in
let rS     := eqv_eq eqvS  in 
let rT     := eqv_eq eqvT  in
let s      := eqv_witness eqvS in
let f      := eqv_new eqvS in
let t      := eqv_witness eqvT in
let g      := eqv_new eqvT in
let plusS  := dioid_plus sr1  in 
let plusT  := dioid_plus sr2  in
let timesS := dioid_times sr1 in 
let timesT := dioid_times sr2 in 
{| 
     dioid_eqv         := eqv_product eqvS eqvT 
   ; dioid_plus        := bop_product plusS plusT 
   ; dioid_times       := bop_product timesS timesT 
   ; dioid_plus_certs  := sg_CI_certs_product rS rT plusS plusT s f t g (dioid_plus_certs sr1)(dioid_plus_certs sr2)
   ; dioid_times_certs := sg_certs_product s t (dioid_times_certs sr1) (dioid_times_certs sr2)
   ; dioid_certs       := semiring_certs_product s t (dioid_certs sr1) (dioid_certs sr2) 
   ; dioid_ast         := Ast_dioid_product (dioid_ast sr1, dioid_ast sr2)
|}.
  
End CAS.

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


Lemma bop_product_plus_id_is_times_ann_check_correct : 
  ∀ (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
     (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product rS rT)
      (bop_product plusS plusT)
      (bop_product timesS timesT)
      (bop_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT pS_d pT_d)
   = 
   bop_product_plus_id_is_times_ann_check 
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. Qed. 


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
Proof. intros [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. Qed. 

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
  ∀ (eqvS : eqv_proofs S rS)
     (eqvT : eqv_proofs T rT)
     (bsS : bs_proofs S rS plusS timesS)
     (bsT : bs_proofs T rT plusT timesT), 
    bs_certs_product wS wT (P2C_bs S rS plusS timesS bsS) (P2C_bs T rT plusT timesT bsT)
    =
    P2C_bs (S * T) (brel_product rS rT) (bop_product plusS plusT) (bop_product timesS timesT) 
       (bs_proofs_product S T rS rT plusS timesS plusT timesT wS wT eqvS eqvT bsS bsT). 
Proof. intros eqvS eqvT bsS bsT. 
       unfold bs_certs_product, bs_proofs_product, P2C_bs; simpl. 
       rewrite bop_product_left_distributive_check_correct. 
       rewrite bop_product_right_distributive_check_correct. 
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
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
       rewrite bop_product_plus_id_is_times_ann_check_correct. 
       rewrite bop_product_times_id_equals_plus_ann_check_correct.
       rewrite bop_product_left_left_absorbtive_check_correct. 
       rewrite bop_product_left_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 



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
       reflexivity. 
Qed. 


Theorem correct_dioid_product : ∀ (S T : Type) (bsS: A_dioid S) (bsT : A_dioid T), 
   dioid_product S T (A2C_dioid S bsS) (A2C_dioid T bsT)
   =
   A2C_dioid (S * T) (A_dioid_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold dioid_product, A_dioid_product, A2C_dioid; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_CI_certs_product. 
       rewrite <- correct_semiring_certs_product. 
       reflexivity. 
Qed. 

End Verify.   
  