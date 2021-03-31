Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts. 

Definition brel_lte_left:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, eq x (b x y). 

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

Lemma po_from_sg_left_antisymmetric : brel_antisymmetric S eq (brel_lte_left eq b).
Proof. compute. intros s t H1 H2.
       assert (A := commS s t). 
       apply symS in H2. 
       assert (B := trnS _ _ _ H1 A).
       assert (C := trnS _ _ _ B H2).
       exact C. 
Qed.

Lemma po_from_sg_left_total (selS : bop_selective S eq b) : brel_total S (brel_lte_left eq b).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       left. apply symS; auto.        
       right.
       assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A). 
Qed.

Lemma po_from_sg_left_not_total (nselS : bop_not_selective S eq b) : brel_not_total S (brel_lte_left eq b).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute.
       apply symS_dual in A. rewrite A.
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C B). 
       apply symS_dual in D. rewrite D. 
       auto.        
Defined. 

Lemma po_from_sg_left_exists_top (idS : bop_exists_id S eq b) : brel_exists_top S (brel_lte_left eq b).
Proof. destruct idS as [s A]. unfold bop_is_id in A. 
       exists s. compute. intro t.
       destruct (A t) as [_ B].
       apply symS. exact B. 
Defined. 

Lemma po_from_sg_left_not_exists_top (nidS : bop_not_exists_id S eq b) : brel_not_exists_top S (brel_lte_left eq b).
Proof. compute. intros a.
       destruct (nidS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined. 

Lemma po_from_sg_left_exists_bottom (annS : bop_exists_ann S eq b) : brel_exists_bottom S (brel_lte_left eq b).
Proof. destruct annS as [s A]. unfold bop_is_ann in A. 
       exists s. compute. intro t.
       destruct (A t) as [B _].
       apply symS. exact B. 
Defined. 

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

(*  NOTE: we will insist that there is an ann.  

     *******************************************************
     if (S, b) is a group, then lte is eq, and bottoms = S. 
     *******************************************************

   Is there some other way to ensure that bottoms not infinite? 

*) 
End Theory.


Section ACAS.


Definition po_from_sg_left_proofs 
    (S : Type) 
    (eq po : brel S)
    (eqvP : eqv_proofs S eq)    
    (b : binary_op S)
    (id_d : bop_exists_id_decidable S eq b)
    (ann : bop_exists_ann S eq b)    
    (P : sg_CI_proofs S eq b):=
let asso := A_sg_CI_associative _ _ _ P in
let cong := A_sg_CI_congruence _ _ _ P in
let comm := A_sg_CI_commutative _ _ _ P in
let idem := A_sg_CI_idempotent _ _ _ P in
let seld := A_sg_CI_selective_d _ _ _ P in
let congS := A_eqv_congruence _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let refS := A_eqv_reflexive _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in 
{|
  A_po_congruence       := po_from_sg_left_congruence S eq congS symS b cong 
; A_po_reflexive        := po_from_sg_left_reflexive S eq symS b idem  
; A_po_transitive       := po_from_sg_left_transitive S eq refS symS trnS b cong asso 
; A_po_antisymmetric    := po_from_sg_left_antisymmetric S eq symS trnS b comm 
; A_po_total_d          := match seld with
                           | inl sel => inl (po_from_sg_left_total S eq symS trnS b comm sel)
                           | inr nsel => inr (po_from_sg_left_not_total S eq symS trnS b comm nsel)
                           end
; A_po_bottoms_finite_d := inl (po_from_sg_left_bottoms_finite S eq refS symS b ann) 
|}.



Definition A_po_from_sg_left (S : Type) (sg: A_sg_CI_with_ann S) : A_po_with_bottom S :=
let eqv  := A_sg_CI_wa_eqv _ sg in
let eqvP := A_eqv_proofs _ eqv in  
let eq   := A_eqv_eq _ eqv in
let b    := A_sg_CI_wa_bop _ sg in
let lte  := brel_lte_left eq b in
let symS := A_eqv_symmetric _ _ eqvP in
let refS := A_eqv_reflexive _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in
let exists_id := A_sg_CI_wa_exists_id_d _ sg in
let exists_ann := A_sg_CI_wa_exists_ann _ sg in
let P := A_sg_CI_wa_proofs _ sg in
let comm := A_sg_CI_commutative _ _ _ P in 
{|
  A_powb_eqv              := eqv
 ; A_powb_lte           := lte
 ; A_powb_exists_top_d   := match exists_id with
                            | inl id => inl (po_from_sg_left_exists_top S eq symS b id)
                            | inr nid => inr (po_from_sg_left_not_exists_top S eq symS trnS b comm nid )
                            end
; A_powb_exists_bottom  := po_from_sg_left_exists_bottom S eq symS  b exists_ann 
; A_powb_proofs         := po_from_sg_left_proofs  S eq lte eqvP b (A_sg_CI_wa_exists_id_d _ sg) (A_sg_CI_wa_exists_ann _ sg) P 
; A_powb_ast            := Ast_po_from_sg_left (A_sg_CI_wa_ast _ sg)
|}.
  


End ACAS.

Section CAS.

Definition po_from_sg_left_certs 
    {S : Type} 
    (id_d : @check_exists_id S)
    (ann : @assert_exists_ann S)    
    (P : @sg_CI_certificates S) :=
let seld := sg_CI_selective_d P in
{|
  po_congruence       := Assert_Brel_Congruence
; po_reflexive        := Assert_Reflexive
; po_transitive       := Assert_Transitive
; po_antisymmetric    := Assert_Antisymmetric
; po_total_d          := match seld with
                           | Certify_Selective => Certify_Total 
                           | Certify_Not_Selective p => Certify_Not_Total p 
                           end
; po_bottoms_finite_d := match ann with
                         | Assert_Exists_Ann a => Certify_Bottoms_Finite (from_sg_left_bottoms_finite_witness S a)
                         end
|}.

Print sg_CI_with_ann. 

Definition po_from_sg_left {S : Type} (sg: @sg_CI_with_ann S) : @po_with_bottom S :=
let eqv  := sg_CI_wa_eqv sg in
let eqvP := eqv_certs eqv in  
let eq   := eqv_eq eqv in
let b    := sg_CI_wa_bop  sg in
let lte  := brel_lte_left eq b in
let exists_id := sg_CI_wa_exists_id_d sg in
let exists_ann := sg_CI_wa_exists_ann sg in
let P := sg_CI_wa_certs sg in
{|
  powb_eqv            := eqv
 ; powb_lte           := lte
 ; powb_exists_top_d  := match exists_id with
                            | Certify_Exists_Id id => Certify_Exists_Top id
                            | Certify_Not_Exists_Id => Certify_Not_Exists_Top 
                            end
 ; powb_exists_bottom  := match exists_ann with
                          | Assert_Exists_Ann a => Assert_exists_bottom a
                          end 
; powb_certs         := po_from_sg_left_certs  (sg_CI_wa_exists_id_d sg) (sg_CI_wa_exists_ann sg) P 
; powb_ast            := Ast_po_from_sg_left (sg_CI_wa_ast sg)
|}.
  
  

End CAS.

Section Verify.

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
  
 
End Verify.   
  