
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.order. 

Section Compute. 

Definition brel_lte_left:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, eq x (b x y). 

End Compute. 

Section Theory.

Variable S  : Type. 

Variable eq : brel S.
Variable eqCong : brel_congruence S eq eq.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable trnS : brel_transitive S eq.
Definition symS_dual := brel_symmetric_implies_dual S eq symS. 

Variable b     : binary_op S.
Variable congS : bop_congruence S eq b.
Variable assoS : bop_associative S eq b.
Variable idemS : bop_idempotent S eq b.
Variable commS : bop_commutative S eq b.

Variable wS : S.
Variable f : S -> S.
Variable Pf   : brel_not_trivial S eq f.
  

Lemma po_from_sg_left_congruence : brel_congruence S eq (brel_lte_left eq b).
Proof. compute. intros s t u v H1 H2. apply eqCong; auto. Qed.

Lemma po_from_sg_left_reflexive : brel_reflexive S  (brel_lte_left eq b).
Proof. compute. intro s. auto. Qed.

(*
Print po_from_sg_left_reflexive.

po_from_sg_left_reflexive =  λ s : S, symS (b s s) s (idemS s)

*) 

Lemma po_from_sg_left_transitive : brel_transitive S  (brel_lte_left eq b).
Proof. compute. intros s t u H1 H2.
       assert (A : eq (b s t) (b s (b t u)) = true).
          apply congS; auto. 
       assert (B : eq (b s (b t u)) (b (b s t) u) = true).
          apply symS. apply assoS; auto.    
       assert (C : eq (b (b s t) u) (b s u) = true).
          apply congS; auto.           
       assert (D := trnS _ _ _ H1 A).
       assert (E := trnS _ _ _ D B).
       assert (F := trnS _ _ _ E C).
       exact F.
Qed.

(* 
Print po_from_sg_left_transitive. 

po_from_sg_left_transitive = 
    λ (s t u : S) (H1 : eq s (b s t) = true) (H2 : eq t (b t u) = true), 
      let A : eq (b s t) (b s (b t u)) = true       := congS s t s (b t u) (refS s) H2 in
      let B : eq (b s (b t u)) (b (b s t) u) = true := symS (b (b s t) u) (b s (b t u)) (assoS s t u) in
      let C : eq (b (b s t) u) (b s u) = true       := congS (b s t) u s u (symS s (b s t) H1) (refS u) in
      let D : eq s (b s (b t u)) = true             := trnS s (b s t) (b s (b t u)) H1 A in
      let E : eq s (b (b s t) u) = true             := trnS s (b s (b t u)) (b (b s t) u) D B in
      let F : eq s (b s u) = true                   := trnS s (b (b s t) u) (b s u) E C in 
      F
: brel_transitive S (brel_lte_left eq b)
*) 

Lemma po_from_sg_left_antisymmetric : brel_antisymmetric S eq (brel_lte_left eq b).
Proof. compute. intros s t H1 H2.
       assert (A := commS s t). 
       apply symS in H2. 
       assert (B := trnS _ _ _ H1 A).
       assert (C := trnS _ _ _ B H2).
       exact C. 
Qed.

(*
Print po_from_sg_left_antisymmetric.

po_from_sg_left_antisymmetric = 
   λ (s t : S) (H1 : eq s (b s t) = true) (H2 : eq t (b t s) = true),
     let A : eq (b s t) (b t s) = true := commS s t in
     let H3 : eq (b t s) t = true      := symS t (b t s) H2 in
     let B : eq s (b t s) = true       := trnS s (b s t) (b t s) H1 A in
     let C : eq s t = true             := trnS s (b t s) t B H3 in C
*) 

Lemma po_from_sg_left_total (selS : bop_selective S eq b) : brel_total S (brel_lte_left eq b).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       left. apply symS; auto.        
       right.
       assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A). 
Qed.

(*
Print po_from_sg_left_total.

po_from_sg_left_total = 
   λ (selS : bop_selective S eq b) (s t : S), 
     let s0 := selS s t in
       match s0 with
       | inl H => inl (symS (b s t) s H)
       | inr H => inr (let A : eq (b s t) (b t s) = true := commS s t in
                       let H0 : eq t (b s t) = true      := symS (b s t) t H 
                       in 
                          trnS t (b s t) (b t s) H0 A
                      )
       end
*)

Lemma po_from_sg_left_not_total (nselS : bop_not_selective S eq b) : brel_not_total S (brel_lte_left eq b).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute.
       apply symS_dual in A. rewrite A.
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C B). 
       apply symS_dual in D. rewrite D. 
       auto.        
Defined.

(*
Print po_from_sg_left_not_total.


po_from_sg_left_not_total = 
   λ nselS : bop_not_selective S eq b, 
     let (x, x0) := nselS in
     ( 
       let (s, t) as p
       return ((let (s, t) := p in (eq (b s t) s = false) * (eq (b s t) t = false)) → brel_not_total S (brel_lte_left eq b)) 
           := x 
       in λ y : (eq (b s t) s = false) * (eq (b s t) t = false), 
                let (A, B) := y 
                in  existT
                           (λ z : S * S, let (s0, t0) := z in
                              (brel_lte_left eq b s0 t0 = false) *
                              (brel_lte_left eq b t0 s0 = false))
                           (s, t)
                           (let A0 : eq s (b s t) = false := symS_dual (b s t) s A 
                            in
                               eq_ind_r
                                    (λ b0 : bool, (b0 = false) * (eq t (b t s) = false))
                                    (let C : eq (b s t) (b t s) = true := commS s t 
                                     in 
                                        let D : eq (b t s) t = false :=
                                                brel_transititivity_implies_dual S eq trnS (b s t) (b t s) t C B 
                                        in
                                           let D0 : eq t (b t s) = false := symS_dual (b t s) t D 
                                           in
                                              eq_ind_r (λ b : bool, (false = false) * (b = false))
                                                       (eq_refl, eq_refl) D0) A0)
    ) x0

*) 

Definition po_from_sg_left_total_decide (D : bop_selective_decidable S eq b) : 
  brel_total_decidable S (brel_lte_left eq b)
  := match D with
     | inl sel  => inl (po_from_sg_left_total sel)
     | inr nsel => inr (po_from_sg_left_not_total nsel)
     end.

Lemma po_from_sg_left_is_top (s : S) (idS : bop_is_id S eq b s) : brel_is_top S (brel_lte_left eq b) s. 
Proof. compute. intro t.
       destruct (idS t) as [_ B].
       apply symS. exact B. 
Defined. 

Lemma po_from_sg_left_exists_top (idS : bop_exists_id S eq b) : brel_exists_qo_top S eq (brel_lte_left eq b).
Proof. destruct idS as [s A]. exists s. split. 
       apply po_from_sg_left_is_top; auto.
       intros a. compute. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined. 

Lemma po_from_sg_left_not_exists_top (nidS : bop_not_exists_id S eq b) : brel_not_exists_qo_top S eq (brel_lte_left eq b).
Proof. compute. intros a. left. 
       destruct (nidS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined.

Definition po_from_sg_left_not_exists_top_decide (D : bop_exists_id_decidable S eq b) : brel_exists_qo_top_decidable S eq (brel_lte_left eq b) :=
  match D with
  | inl idS  => inl (po_from_sg_left_exists_top idS)
  | inr nidS => inr (po_from_sg_left_not_exists_top nidS)
  end. 

Lemma po_from_sg_left_is_bottom (s : S) (annS : bop_is_ann S eq b s) : brel_is_qo_bottom S eq (brel_lte_left eq b) s.
Proof. compute. split.
       intro t. destruct (annS t) as [B _]. apply symS. exact B. 
       intros a. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined. 

Lemma po_from_sg_left_exists_bottom (annS : bop_exists_ann S eq b) : brel_exists_qo_bottom S eq (brel_lte_left eq b).
Proof. destruct annS as [s A]. exists s. apply po_from_sg_left_is_bottom; auto. Defined. 


Lemma po_from_sg_left_equiv (s t : S)
      (H1 : eq t (b t s) = true)
      (H2 : eq s (b s t) = true) : equiv (brel_lte_left eq b) s t = true. 
Proof. compute.  rewrite H1, H2. reflexivity. Qed.

Lemma po_from_sg_left_below (s t : S)
      (H1 : eq t (b t s) = true)
      (H2 : eq s (b s t) = false) : below (brel_lte_left eq b) s t = true. 
Proof. compute.  rewrite H1, H2. reflexivity. Qed. 

Lemma po_from_sg_left_incomp (s t : S)
      (H1 : eq t (b t s) = false)
      (H2 : eq s (b s t) = false) : incomp (brel_lte_left eq b) s t = true. 
Proof. compute.  rewrite H1, H2. reflexivity. Qed.



Lemma po_from_sg_left_bottoms_set_is_finite (sif : something_is_finite S eq b) :
       bottoms_set_is_finite S eq (brel_lte_left eq b). 
Proof. destruct sif as [[B w] [Q P]].
       exists (B, w). split. 

       (* is_antichain S eq (brel_lte_left eq b) B *)
       unfold is_antichain.
       intros s A t C. compute.
       assert (D := Q s A t C). 
       destruct D as [[E F] | [E F]]; rewrite E, F; reflexivity. 

       intro s. destruct (P s) as [A | A]. 
          left. exact A. 
          destruct A as [A1 [A2 A3]]. right. split. 
             (* in_set eq B (w s) = true *)
             exact A1. 
             (* below (brel_lte_left eq b) s (w s) = true *)
             compute. rewrite A2, A3. reflexivity. 
Defined.

Lemma po_from_sg_left_bottoms_set_not_is_finite (sif : something_not_is_finite S eq b) :
       bottoms_set_not_is_finite S eq (brel_lte_left eq b). 
Proof. destruct sif as [F A].
       unfold bottoms_set_not_is_finite.
       exists F. 
       intros B C.

          assert (D : is_interesting S eq b B).
             unfold is_interesting. unfold is_antichain in C. 
             intros s D t E.
             assert (bC := commS s t). 
             assert (G := C s D t E). apply equiv_or_incomp_elim in G.
             unfold brel_lte_left in G.              
             destruct G as [G | G]. 
                apply equiv_elim in G. left. 
                destruct G as [G1 G2]. split.
                   exact G2. 
                   exact G1. 
                
                apply incomp_elim in G. right. 
                destruct G as [G1 G2]. split.                   
                   exact G2. 
                   exact G1. 
          destruct (A B D) as [E G].
          split. 
            exact E.           
            intros s H.
            assert (I := G s H).
            apply below_false_intro.
            unfold brel_lte_left. 
            exact I. 
Defined. 



       
(*
Lemma po_from_sg_left_not_exists_bottom (nannS : bop_not_exists_ann S eq b) : brel_not_exists_bottom S (brel_lte_left eq b).
Proof. compute. intros a.
       destruct (nannS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. exact A. 
          apply symS_dual. assert (B := commS c a). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
Defined. 
*) 
(*
Definition from_sg_left_bottoms (a: S) (x: unit)  := a :: nil.
Definition from_sg_left_lower (a b : S) := a.               
Definition from_sg_left_bottoms_finite_witness (a : S) := (from_sg_left_bottoms a, from_sg_left_lower a).


Lemma po_from_sg_left_bottoms_finite (annS : bop_exists_ann S eq b) : bottoms_finite S eq (brel_lte_left eq b).
Proof. unfold bottoms_finite. destruct annS as [ c A]. compute in A. 
       exists (from_sg_left_bottoms_finite_witness c). 
       simpl. intro s.
       destruct (A s) as [B C]. unfold from_sg_left_lower. unfold brel_lte_left.
       rewrite refS. simpl. split; auto. 
Defined.

Lemma po_from_sg_left_not_bottoms_finite (nannS : bop_not_exists_ann S eq b) : bottoms_finite S eq (brel_lte_left eq b).
Proof. unfold bop_not_exists_ann in nannS. 
*) 


(*  NOTE: we will insist that there is an ann so that from_sg_left has a bottom. 
*) 
End Theory.


Section ACAS.


Definition po_from_sg_left_proofs 
    (S : Type) 
    (eq  : brel S)
    (eqvP : eqv_proofs S eq)    
    (b : binary_op S)
    (id_d : bop_exists_id_decidable S eq b)
    (ann : bop_exists_ann S eq b)
    (P : sg_CINS_proofs S eq b):=
let asso := A_sg_CINS_associative _ _ _ P in
let cong := A_sg_CINS_congruence _ _ _ P in
let comm := A_sg_CINS_commutative _ _ _ P in
let idem := A_sg_CINS_idempotent _ _ _ P in
let nsel := A_sg_CINS_not_selective _ _ _ P in
let congS := A_eqv_congruence _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let refS := A_eqv_reflexive _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in 
{|
  A_po_congruence       := po_from_sg_left_congruence S eq congS symS b cong 
; A_po_reflexive        := po_from_sg_left_reflexive S eq symS b idem  
; A_po_transitive       := po_from_sg_left_transitive S eq refS symS trnS b cong asso 
; A_po_antisymmetric    := po_from_sg_left_antisymmetric S eq symS trnS b comm 
; A_po_not_total        := po_from_sg_left_not_total S eq symS trnS b comm nsel
(*; A_po_total_d          := po_from_sg_left_total_decide S eq symS trnS b comm sel_d*) 
(*; A_po_bottoms_finite_d := inl (po_from_sg_left_bottoms_finite S eq refS symS b ann) *) 
|}.


End ACAS.

Section CAS.

Definition po_from_sg_left_certs 
    {S : Type} 
    (id_d : @check_exists_id S)
    (ann : @assert_exists_ann S)
    (P : @sg_CINS_certificates S) :=
{|
  po_congruence       := Assert_Brel_Congruence
; po_reflexive        := Assert_Reflexive
; po_transitive       := Assert_Transitive
; po_antisymmetric    := Assert_Antisymmetric
; po_not_total        := match sg_CINS_not_selective P with
                         | Assert_Not_Selective p => Assert_Not_Total p
                         end 
(*; po_bottoms_finite_d := match ann with
                         | Assert_Exists_Ann a => Certify_Bottoms_Finite (from_sg_left_bottoms_finite_witness S a)
                         end
*) 
|}.

End CAS.


Section Verify.

(*
  
Theorem correct_po_from_sg_left (S : Type) (sgS : A_sg_CI_with_ann S): 
         po_from_sg_left (A2C_sg_CI_with_ann S sgS) 
         = 
         A2C_po_with_bottom S (A_po_from_sg_left S sgS). 
Proof. unfold po_from_sg_left, A_po_from_sg_left, A2C_sg_CI_with_ann, A2C_po_with_bottom; simpl.
       unfold po_from_sg_left_certs; unfold po_from_sg_left_proofs. unfold P2C_po; simpl. 
       destruct (A_sg_CI_wa_exists_id_d S sgS) as [[i A] | A];
       destruct (A_sg_CI_wa_exists_ann S sgS) as [a B];
       destruct (A_sg_CI_selective_d S) as [sel | [[c d] [C D]]]; simpl; reflexivity. 
Qed.

*)   
 
End Verify.   
