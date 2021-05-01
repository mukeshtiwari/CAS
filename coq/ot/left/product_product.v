Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.ot.properties.
Require Import CAS.coq.ot.structures.



Require Import CAS.coq.eqv.product.
Require Import CAS.coq.po.product. 
Require Import CAS.coq.tr.left.product. 




Section Theory.
  
  Variable S    : Type.
  Variable LS   : Type.
  Variable eqS  : brel S.
  Variable wS   : S.
  Variable wLS  : LS.
  Variable lteS : brel S.
  Variable ltrS : left_transform LS S .

  Variable T    : Type.
  Variable LT   : Type.
  Variable eqT  : brel T.
  Variable wT   : T.
  Variable wLT  : LT.
  Variable lteT : brel T.
  Variable ltrT : left_transform LT T.

  Notation "a <*> b" := (brel_product a b) (at level 15).
  Notation "a [*] b" := (ltr_product a b) (at level 15).


  Lemma olt_product_monotone :
        olt_monotone LS S lteS ltrS -> olt_monotone LT T lteT ltrT -> 
          olt_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
  Proof.
        intros MS MT [l1 l2] [s1 t1] [s2 t2]; compute.
        case_eq(lteS s1 s2); intro A; case_eq(lteT t1 t2); intros B C; auto.  
           rewrite MS; auto.  rewrite MT; auto. 
           discriminate C. discriminate C. discriminate C. discriminate C. 
  Defined.

Lemma olt_product_strictly_increasing_inc_sinc :
        olt_increasing LS S lteS ltrS -> olt_strictly_increasing LT T lteT ltrT -> 
          olt_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. unfold olt_strictly_increasing. unfold olt_increasing. 
       intros INC SINC [lS lT] [s t]. destruct (SINC lT t) as [A B]; auto. 
       compute. rewrite A. rewrite B. rewrite INC. 
       case_eq(lteS (ltrS lS s) s); intro C; auto.        
Defined.


Lemma olt_product_strictly_monotone_inc_sinc :
  olt_monotone LS S lteS ltrS -> olt_monotone LT T lteT ltrT ->
          olt_strictly_monotone LT T lteT ltrT -> 
          olt_strictly_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. unfold olt_strictly_monotone. unfold olt_monotone. 
       intros MS MT SM [lS lT] [s1 t1] [s2 t2]. 
       compute. intros A B.
       case_eq(lteS s1 s2); intro C; case_eq(lteS s2 s1); intro D.

           rewrite C in A. rewrite D in B. 
           destruct (SM lT _ _ A B) as [E F]. rewrite E. rewrite F. 
           split. 
              case_eq(lteS (ltrS lS s1) (ltrS lS s2)); intro G; auto.
                 assert (H := MS lS _ _ C).
                 rewrite H in G. discriminate G. 
              case_eq(lteS (ltrS lS s2) (ltrS lS s1)); intro G; auto. 

           rewrite C in A. rewrite D in B. 
           assert (E := MS lS s1 s2 C). rewrite E.
           assert (F := MT lT t1 t2 A). rewrite F. split; auto. 
           case_eq(lteS (ltrS lS s2) (ltrS lS s1) ); intro G; case_eq(lteT (ltrT lT t2) (ltrT lT t1)); intro H; auto. 
              case_eq(lteT t2 t1); intro I. 
                 admit.
                 destruct (SM lT _ _ A I) as [J K]. 
                 rewrite K in H. discriminate H. 
              
           rewrite C in A. discriminate A. 

           rewrite C in A. discriminate A. 
Defined.


End Theory.

Section ACAS.

(* THINK ABOUT THIS HACK *) 


Definition olt_product_qoltr_msi_proofs (LS S LT T : Type) (lteS : brel S) (ltrS : left_transform LS S) (PS : poltr_mi_proofs LS S lteS ltrS)
           (lteT : brel T) (ltrT : left_transform LT T) (PT : qoltr_msi_proofs LT T lteT ltrT) :
           qoltr_msi_proofs (LS * LT) (S * T) (brel_product lteS lteT) (ltr_product ltrS ltrT) :=
let MS := A_poltr_mi_monotone LS S lteS ltrS PS in
let MT := A_qoltr_msi_monotone LT T lteT ltrT PT in   
let INCS := A_poltr_mi_increasing LS S lteS ltrS PS in   
let SINCT := A_qoltr_msi_strictly_increasing LT T lteT ltrT PT in   
{|
  A_qoltr_msi_monotone             := olt_product_monotone S LS lteS ltrS T LT lteT ltrT MS MT 
; A_qoltr_msi_strictly_increasing  := olt_product_strictly_increasing_inc_sinc S LS lteS ltrS T LT lteT ltrT INCS SINCT
|}.




Definition olt_product_with_bottom_proofs (S T : Type) (eqS lteS : brel S) (eqT lteT : brel T) (eqvP : eqv_proofs S eqS)
    (lteReflS : brel_reflexive S lteS) (lteReflT : brel_reflexive T lteT) 
    (PS : with_bottom_proofs S eqS lteS)  (PT : with_bottom_proofs T eqT lteT) := 
let refS   := A_eqv_reflexive S eqS eqvP in
let topS_d := A_with_bottom_exists_top_d _ _ _ PS in
let topT_d := A_with_bottom_exists_top_d _ _ _ PT in                                    
let botS   := A_with_bottom_exists _ _ _ PS in
let botT   := A_with_bottom_exists _ _ _ PT in                                  
{|
  A_with_bottom_exists_top_d       := ord_product_exists_top_decidable S T eqS eqT lteS lteT lteReflS lteReflT refS topS_d topT_d 
; A_with_bottom_exists             := ord_product_exists_bottom S T eqS eqT lteS lteT botS botT 
|}.


Definition A_product_qoltr_monotone_strictly_increasing (LS S LT T : Type) 
    (P : A_poltr_monotone_increasing LS S) 
    (Q : A_wpltr_monotone_strictly_increasing LT T) :
         A_qoltr_monotone_strictly_increasing (LS * LT) (S * T) :=
let eqvS := A_poltr_mi_carrier _ _ P in
let eqS := A_eqv_eq _ eqvS in
let eqvPS := A_eqv_proofs _ eqvS in
let refS := A_eqv_reflexive _ _ eqvPS in 
let eqvLS := A_poltr_mi_label _ _ P in
let eqLS := A_eqv_eq _ eqvLS in
let wS := A_eqv_witness _ eqvS in
let wLS := A_eqv_witness _ eqvLS in 
let lteS := A_poltr_mi_lte _ _ P in  
let ltrS := A_poltr_mi_ltr _ _ P in  
let POS := A_poltr_mi_lte_proofs _ _ P in
let lteReflS := A_po_reflexive _ _ _ POS in 
let PTS := A_poltr_mi_ltr_proofs _ _ P in
let PS := A_poltr_mi_proofs _ _ P in

let eqvT := A_wpltr_msi_carrier _ _ Q in
let eqT := A_eqv_eq _ eqvT in
let eqvPT := A_eqv_proofs _ eqvT in
let refT := A_eqv_reflexive _ _ eqvPT in 
let eqvLT := A_wpltr_msi_label _ _ Q in
let eqLT := A_eqv_eq _ eqvLT in
let wT := A_eqv_witness _ eqvT in
let wLT := A_eqv_witness _ eqvLT in 
let lteT := A_wpltr_msi_lte _ _ Q in  
let ltrT := A_wpltr_msi_ltr _ _ Q in  
let POT := A_wpltr_msi_lte_proofs _ _ Q in
let lteReflT := A_wp_reflexive _ _ _ POT in 
let PTT := A_wpltr_msi_ltr_proofs _ _ Q in
let PT := A_wpltr_msi_proofs _ _ Q in
{|
  A_qoltr_msi_carrier      := A_eqv_product S T eqvS eqvT
; A_qoltr_msi_label        := A_eqv_product LS LT eqvLS eqvLT
; A_qoltr_msi_lte          := brel_product lteS lteT
; A_qoltr_msi_ltr          := ltr_product ltrS ltrT
; A_qoltr_msi_lte_proofs   := ord_po_wp_product_proofs S T eqS lteS wS POS eqT lteT wT POT
; A_qoltr_msi_ltr_proofs   := ltr_product_proofs LS S LT T eqS eqLS wS wLS ltrS refS PTS eqT eqLT wT wLT ltrT refT PTT
; A_qoltr_msi_bottom_proofs := olt_product_with_bottom_proofs S T eqS lteS eqT lteT eqvPS lteReflS lteReflT
                                (A_poltr_mi_bottom_proofs _ _ P) (A_wpltr_msi_bottom_proofs _ _ Q) 
; A_qoltr_msi_proofs       := olt_product_qoltr_msi_proofs LS S LT T lteS ltrS PS lteT ltrT PT 
; A_qoltr_msi_ast          := Ast_bs_product (A_poltr_mi_ast _ _ P, A_wpltr_msi_ast _ _ Q) (* FIX *)
|}.
  
End ACAS.

Section CAS.

(* move some of this to po/product .... *) 
Definition olt_product_qoltr_msi_certs {LS S LT T : Type} (PS : @poltr_mi_certificates LS S) (PT : @qoltr_msi_certificates LT T) :=
{|
  qoltr_msi_monotone             := @Assert_Olt_Monotone (LS * LT) (S * T)
; qoltr_msi_strictly_increasing  := @Assert_Olt_Strictly_Increasing (LS * LT) (S * T)
|}.


Definition ord_product_exists_top_check {S T : Type}
     (DS : @check_exists_qo_top S)
     (DT : @check_exists_qo_top T) : 
           @check_exists_qo_top (S * T) := 
match DS with 
| Certify_Exists_Qo_Top topS   =>
               match DT with
               |  Certify_Exists_Qo_Top topT => Certify_Exists_Qo_Top (topS, topT) 
               |  Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top 
               end 
| Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top 
end.


Definition ord_product_exists_bottom_assert {S T : Type}
     (DS : @assert_exists_qo_bottom S)
     (DT : @assert_exists_qo_bottom T) : 
           @assert_exists_qo_bottom (S * T) := 
match DS, DT with 
| Assert_Exists_Qo_Bottom botS, Assert_Exists_Qo_Bottom botT =>  
     Assert_Exists_Qo_Bottom (botS, botT)
end.

Definition olt_product_with_bottom_certs {S T : Type} 
    (PS : @with_bottom_certs S)  (PT : @with_bottom_certs T) := 
let topS_d := with_bottom_exists_top_d PS in
let topT_d := with_bottom_exists_top_d PT in                                    
let botS   := with_bottom_exists PS in
let botT   := with_bottom_exists PT in                                  
{|
  with_bottom_exists_top_d       := ord_product_exists_top_check topS_d topT_d 
; with_bottom_exists             := ord_product_exists_bottom_assert botS botT 
|}.



Definition product_qoltr_monotone_strictly_increasing {LS S LT T : Type}
    (P : @poltr_monotone_increasing LS S) 
    (Q : @wpltr_monotone_strictly_increasing LT T) :
         @qoltr_monotone_strictly_increasing (LS * LT) (S * T) :=
let eqvS := poltr_mi_carrier P in
let eqvLS := poltr_mi_label P in
let wS := eqv_witness eqvS in
let lteS := poltr_mi_lte P in  
let ltrS := poltr_mi_ltr P in  
let wLS := eqv_witness eqvLS in 
let POS := poltr_mi_lte_certs P in
let PTS := poltr_mi_ltr_certs P in
let PS := poltr_mi_certs P in

let eqvT := wpltr_msi_carrier Q in
let eqvLT := wpltr_msi_label Q in
let wT := eqv_witness eqvT in
let wLT := eqv_witness eqvLT in
let lteT := wpltr_msi_lte Q in  
let ltrT := wpltr_msi_ltr Q in  
let POT := wpltr_msi_lte_certs Q in
let PTT := wpltr_msi_ltr_certs Q in
let PT := wpltr_msi_certs Q in
{|
  qoltr_msi_carrier     := eqv_product eqvS eqvT
; qoltr_msi_label       := eqv_product eqvLS eqvLT
; qoltr_msi_lte         := brel_product lteS lteT
; qoltr_msi_ltr         := ltr_product ltrS ltrT
; qoltr_msi_lte_certs   := ord_po_wp_product_certs wS POS wT POT
; qoltr_msi_ltr_certs   := ltr_product_certs wS wLS PTS wT wLT PTT
; qoltr_msi_bottom_certs := olt_product_with_bottom_certs (poltr_mi_bottom_certs P) (wpltr_msi_bottom_certs Q)                                              
; qoltr_msi_certs       := olt_product_qoltr_msi_certs PS PT 
; qoltr_msi_ast         := Ast_bs_product (poltr_mi_ast P, wpltr_msi_ast Q) (* FIX *)
|}.


End CAS.

Section Verify.


Lemma correct_olt_product_qoltr_msi_proofs (LS S LT T : Type)
            (lteS : brel S) (ltrS : left_transform LS S) (PS : poltr_mi_proofs LS S lteS ltrS)
            (lteT : brel T) (ltrT : left_transform LT T) (PT : qoltr_msi_proofs LT T lteT ltrT) :
   olt_product_qoltr_msi_certs (P2C_poltr_mi LS S lteS ltrS PS) (P2C_qoltr_msi LT T lteT ltrT PT)
   =
   P2C_qoltr_msi _ _ _ _ (olt_product_qoltr_msi_proofs LS S LT T lteS ltrS PS lteT ltrT PT).
Proof. unfold olt_product_qoltr_msi_certs, olt_product_qoltr_msi_proofs, P2C_qoltr_msi, P2C_poltr_mi; simpl.
       reflexivity. 
Qed. 


Lemma correct_olt_product_with_bottom_certs (S T : Type) (eqS lteS : brel S) (eqT lteT : brel T) (eqvP : eqv_proofs S eqS)
       (lteReflS : brel_reflexive S lteS) (lteReflT : brel_reflexive T lteT) 
       (PS : with_bottom_proofs S eqS lteS)  (PT : with_bottom_proofs T eqT lteT): 

  olt_product_with_bottom_certs (P2C_with_bottom S eqS lteS PS) (P2C_with_bottom T eqT lteT PT)
  =     
  P2C_with_bottom _ _ _ (olt_product_with_bottom_proofs S T eqS lteS eqT lteT eqvP lteReflS lteReflT PS PT). 
Proof. unfold olt_product_with_bottom_certs, olt_product_with_bottom_proofs, P2C_with_bottom; simpl. 
       destruct PS, PT.
       destruct A_with_bottom_exists_top_d as [[tS [A1 A2]] | NTS];
       destruct A_with_bottom_exists_top_d0 as [[tT [B1 B2]] | NTT];       
       destruct A_with_bottom_exists as [bS [C1 C2]]; 
       destruct A_with_bottom_exists0 as [bT [D1 D2]];                
       unfold ord_product_exists_top_check, p2c_exists_qo_top_check; simpl; auto. 
Qed.

Theorem correct_product_qoltr_monotone_strictly_increasing (LS S LT T : Type) 
    (P : A_poltr_monotone_increasing LS S) 
    (Q : A_wpltr_monotone_strictly_increasing LT T) :
  product_qoltr_monotone_strictly_increasing (A2C_poltr_monotone_increasing _ _ P) (A2C_wpltr_monotone_strictly_increasing _ _ Q)
  =
  A2C_qoltr_monotone_strictly_increasing _ _ (A_product_qoltr_monotone_strictly_increasing _ _ _ _ P Q). 
Proof. unfold product_qoltr_monotone_strictly_increasing, A_product_qoltr_monotone_strictly_increasing,
       A2C_qoltr_monotone_strictly_increasing, A2C_poltr_monotone_increasing, A2C_wpltr_monotone_strictly_increasing; simpl. 
       destruct P. destruct Q. simpl.
       rewrite correct_eqv_product. rewrite correct_eqv_product. 
       rewrite <- correct_ord_po_wp_product_certs. 
       rewrite <- correct_ltr_product_certs. 
       unfold olt_product_qoltr_msi_proofs, olt_product_qoltr_msi_certs, P2C_qoltr_msi; simpl.
       rewrite <- correct_olt_product_with_bottom_certs. 
       reflexivity. 
Qed.





End Verify.   