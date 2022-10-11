Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.nat. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.cast_up.
Require Import CAS.coq.po.from_sg. 

Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus. 

Require Import CAS.coq.uop.properties.

Section Computation.

Fixpoint manger_llex_merge
           {S T : Type}
           (eq : brel S)
           (bT : binary_op T)
           (Y : finite_set (S * T))
           (p1 : S * T) :=
  match Y with
  | nil => p1 :: nil
  | p2 :: Y' =>
    match p1, p2 with
    | (s1, t1), (s2, t2) =>
      if eq s1 s2
      then (s1, bT t1 t2) :: Y' 
      else p2 :: (manger_llex_merge eq bT Y' p1) 
    end 
  end.

Definition uop_manger_collect_general 
          {S T : Type}
          (eq : brel S)
          (bT : binary_op T) 
          (Y : finite_set (S * T))
          (X : finite_set (S * T))  : finite_set (S * T) :=
  fold_left (manger_llex_merge eq bT) X Y.

Definition uop_manger_collect
          {S T : Type}
          (eq : brel S)
          (bT : binary_op T) 
          (X : finite_set (S * T))  : finite_set (S * T) :=
  uop_manger_collect_general eq bT nil X.   


Definition bop_manger_collect_union
           {S T : Type}
           (eqS : brel S)
           (eqT : brel T)                       
           (bT : binary_op T) : binary_op (finite_set (S * T))
  := λ X Z, uop_manger_collect eqS bT (bop_union (brel_product eqS eqT) X Z). 

Definition bop_manger_collect_lift_product
           {S T : Type}
           (eqS : brel S)
           (eqT : brel T)                       
           (addT : binary_op T)
           (mulS : binary_op S)
           (mulT : binary_op T) : binary_op (finite_set (S * T))                     
  := λ X Z, uop_manger_collect eqS addT (bop_lift (brel_product eqS eqT) (bop_product mulS mulT) X Z). 


Definition lte_ignore_snd
           {S T : Type}
           (lte : brel S) : brel (S * T)
  := λ p1 p2,
    match p1, p2 with
    | (s1, t1), (s2, t2) => lte s1 s2
    end. 


Definition uop_manger_llex
           {S T : Type}
           (eqS lte : brel S)
           (eqT : brel T)  : unary_op (finite_set (S * T))          
  := uop_minset (lte_ignore_snd lte). 

Definition bop_manger_llex
           {S T : Type}
           (eqS lte : brel S)
           (eqT : brel T)            
           (addT : binary_op T) : binary_op (finite_set (S * T))
  := λ X Z, uop_manger_llex eqS lte eqT (bop_manger_collect_union eqS eqT addT X Z). 

Definition bop_manger_product
           {S T : Type}
           (lteS eqS : brel S)
           (eqT : brel T)                       
           (addT : binary_op T)
           (mulS : binary_op S)
           (mulT : binary_op T) : binary_op (finite_set (S * T))
  := λ X Z, uop_manger_llex eqS lteS eqT (bop_manger_collect_lift_product eqS eqT addT mulS mulT X Z). 


End Computation.

Section Testing.

(*  S = nat * nat, T = nat *) 
   
Local Definition eqS := brel_product brel_eq_nat brel_eq_nat. 
Local Definition addS := bop_product bop_min bop_min. 
Local Definition lteS := brel_lte_left eqS addS. 
Local Definition mulS := bop_product bop_plus bop_plus. 

Local Definition eqT  := brel_eq_nat.
Local Definition addT := bop_min. 
Local Definition mulT := bop_plus.

Local Definition manger_add := bop_manger_llex eqS lteS eqT addT.
Local Definition manger_mul := bop_manger_product lteS eqS eqT addT mulS mulT. 
(*
  Check manger_add.
  binary_op (finite_set (nat * nat * nat))
 *)

Open Scope nat_scope. 

Local Definition s1 := ((1, 2), 8) :: nil.
Local Definition s2 := ((3, 5), 9) :: nil.
Local Definition s3 := ((0, 5), 9) :: nil.
Local Definition s4 := ((1, 2), 10) :: nil.
Local Definition s5 := ((1, 2), 1):: ((1, 2), 2)::((1, 2), 3) :: nil.
Compute (manger_add s1 s2). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s3). (* = (0, 5, 9) :: (1, 2, 8) :: nil *)
Compute (manger_add s1 s4). (* = (1, 2, 8) :: nil *)
Compute (manger_add s1 s1). (* = (1, 2, 8) :: nil *)
Compute (manger_add s5 nil). (* = (1, 2, 1) :: nil *)
Compute (manger_add nil s5). (* = (1, 2, 1) :: nil *)
Compute (manger_mul s1 s2). (* = (4, 7, 17) :: nil *) 
Compute (manger_mul s2 s5). (* = (4, 7, 10) :: nil *)
Compute (manger_add (manger_mul s5 s1) (manger_mul s5 s3)). (* (1, 7, 10) :: (2, 4, 9) :: nil *) 
Compute (manger_mul s5 (manger_add s1 s3)).                 (* (2, 4, 9) :: (1, 7, 10) :: nil *) 

End Testing.   


Section Theory.

Variables (S T : Type)
          (lteS eqS : brel S)
          (eqT : brel T)
          (mulS : binary_op S)
          (addT : binary_op T)
          (mulT : binary_op T)
          (refS : brel_reflexive S eqS)
          (refT : brel_reflexive T eqT)
          (symS : brel_symmetric S eqS)
          (symT : brel_symmetric T eqT)
          (trnS : brel_transitive S eqS)
          (trnT : brel_transitive T eqT).

Local Notation "[MM]":= (manger_llex_merge eqS addT) (at level 70).
Local Notation "[CG]" := (uop_manger_collect_general eqS addT) (at level 70).
Local Notation "[C]"  := (uop_manger_collect eqS addT) (at level 70).
Local Infix "[CU]" := (bop_manger_collect_union eqS eqT addT) (at level 70).
Local Infix "[CP]" := (bop_manger_collect_lift_product eqS eqT addS addT mulS mulT) (at level 70).
Local Infix "[U]"  := (bop_union (brel_product eqS eqT)) (at level 70).

Local Notation "[EQ]"  := (brel_set (brel_product eqS eqT)) (at level 70). 
Local Definition set_S_T_equal a b := [EQ] a b = true . 
Local Infix "=ST="  := set_S_T_equal (at level 70).


Local Notation "[MS]" := (uop_manger_llex eqS lteS eqT) (at level 70).
Local Infix "[ML]" := (bop_manger_llex eqS lteS eqT addT) (at level 70).
Local Infix "[MP]" := (bop_manger_product lteS eqS eqT addS addT mulS mulT) (at level 70).

Lemma eq_ST_reflexive : brel_reflexive _ ([EQ]). 
Proof. intro X.
       apply brel_set_reflexive; auto.
       + apply brel_product_reflexive; auto.
       + apply brel_product_symmetric; auto.
Qed. 

Lemma eq_ST_symmetric : brel_symmetric _ ([EQ]). 
Proof. intro X. apply brel_set_symmetric. Qed.

Lemma eq_ST_transitive : brel_transitive _ ([EQ]). 
Proof. intro X.
       apply brel_set_transitive; auto.
       + apply brel_product_reflexive; auto.
       + apply brel_product_symmetric; auto.
       + apply brel_product_transitive; auto.
Qed.

Lemma uop_manger_collect_general_shift : 
            ∀ X Z p, [CG] Z (p :: X) =ST= [CG] ([MM] Z p) X. 
Proof. intros X Z p.
       unfold uop_manger_collect_general. simpl. 
       apply eq_ST_reflexive. 
Qed. 

Lemma uop_manger_collect_general_congruence : bop_congruence _ ([EQ]) ([CG]). 
Admitted.

Lemma uop_manger_collect_general_idempotent :
  ∀ X Y : finite_set (S * T), [CG] Y ([CG] nil X) =ST= [CG] Y X.
Proof. intro X.
       induction X.
       + intro Y.
         unfold uop_manger_collect_general. 
         unfold fold_left at 3. unfold fold_left at 2.
         unfold fold_left.
         apply eq_ST_reflexive.
       + intro Y.
         Search fold_left. 
         (*
             IHX : ∀ Y : finite_set (S * T), [CG] Y ([CG] nil X) =ST= [CG] Y X
             ============================
             [CG] Y ([CG] nil (a :: X)) =ST= [CG] Y (a :: X)
                 

              [CG] Y ([CG] nil (a :: X))
              == 
              [CG] Y ([CG] (a :: nil) X)
              == 

              [CG] ([MM] Y a) X 
              == 
              [CG] Y (a :: X)
          *)
         assert (A := uop_manger_collect_general_shift X nil a).
         unfold manger_llex_merge in A.
         assert (B := uop_manger_collect_general_congruence _ _ _ _ (eq_ST_reflexive Y) A).
         assert (C := uop_manger_collect_general_shift X Y a).
         assert (D : ([CG]) Y (([CG]) (a :: nil) X) =ST= ([CG]) (([MM]) Y a) X).
         {
           unfold uop_manger_collect_general at 2.
           unfold uop_manger_collect_general at 1.
           unfold uop_manger_collect_general at 1.
(*

           fold_left f (fold_left f l (a :: nil)) l1
           =?=           
           fold_left f l (f l1 a) 

           l =  [v1, v2, .... vk]
           l1 = [u1, u2, .... um]                 

           fold_left f l (f l1 a)  = f v1 ... (f vk-1 (f vk (f l1 a)) ...)

           fold_left f l (a :: nil)  f v1 ... (f vk-1 (f vk (a :: nil)) ...)
                                                                                     
          fold_left f (fold_left f l (a :: nil)) l1 = f u1 ..... (f um (f v1 ... (f vk-1 (f vk (a :: nil)) ...)))

          f v1 ... (f vk-1 (f vk (f [u1, u2, .... um] a)) ...)
          = ? =                                                          
          f u1 ..... (f um (f v1 ... (f vk-1 (f vk (a :: nil)) ...)))                                                                                        *)                  
         } 
Admitted.

Lemma uop_manger_collect_idempotent : ∀ X : finite_set (S * T),  [C] ([C] X) =ST= ([C] X).
Proof.   intro X. unfold uop_manger_collect. apply uop_manger_collect_general_idempotent. Qed.



Lemma uop_manger_collect_general_union_shift : 
    ∀ X Y Z : finite_set (S * T), [CG] Z (X [U] Y) =ST= [CG] ([CG] Z X) Y. 
Proof. intros X.
       induction X. 
       unfold uop_manger_collect_general.
       + intros Y Z. simpl.
         admit.  (* OK, nil [U] Y = Y, and fold_left congruence *)
       + intros Y Z.
         (*
            IHX : ∀ Y Z, ([CG]) Z (X [U] Y) =ST= ([CG]) (([CG]) Z X) Y
            ============================
           ([CG]) Z (a :: X [U] Y) =ST= ([CG]) (([CG]) Z (a :: X)) Y


            [CG] Z (a :: X [U] Y)
            == 
            [CG] Z (a :: (X [U] Y))
            == 
            [CG] ([MM] Z a) (X [U] Y)
            == 
            [CG] ([CG] ([MM] Z a) X) Y  
            == 
            [CG] ([CG] Z (a :: X)) Y
          *) 
         admit.
Admitted. 
        


         
Lemma uop_manger_collect_union_left_invariant :
     ∀ X Y : finite_set (S * T),  [C] (([C] X) [U] Y) =ST= [C] (X [U] Y).
Proof. intros X Y.
       unfold uop_manger_collect.


  

Lemma bop_manger_collect_union_associative :
  bop_associative _  (brel_set (brel_product eqS eqT)) (bop_manger_collect_union eqS eqT addT). 
Proof. unfold bop_associative.
       intros X Y Z.
       (* ([EQ]) ((X [CU] Y) [CU] Z) (X [CU] (Y [CU] Z)) = true *)
       unfold bop_manger_collect_union.
       (* ([EQ]) (([C]) (([C]) (X [U] Y) [U] Z)) 
                 (([C]) (X [U] ([C]) (Y [U] Z))) = true
*)


(*
Should check if it is a reduction first? 

   "addition" : 

   X + Y = X mllex Y = M (C (U X Y))

   for bs, what is multiplication going to look like? 

   X * Y = = M (C (bop_lift (bop_product mulS mulT) X Y))   

   Better: 

   X +' Y = C (U X Y)
   X *' Y = C (bop_lift (bop_product mulS mulT) X Y) 

   X + Y = M (X +' Y)
   X * Y = M (X *' Y)

   Show M is a reduction over (+', *') 
   1) M (M X) = M X 
   2) M (M(X) +' Y) = M (X +' Y) 
   3) M (M(X) *' Y) = M (X *' Y) 
      M (X *' M(Y)) = M (X *' Y) 

*) 

Lemma bop_manger_lex_associative :
  bop_associative _ (brel_set (brel_product eqS eqT)) (bop_manger_lex eqS lte eqT bT) . 
Proof. intros X Y Z.       
       unfold bop_manger_lex.

       
(* 
  brel_set (brel_product eqS eqT)
    (uop_minset (lte_ignore_snd lte)
       (manger_llex_collect eqS bT nil
          (bop_union (brel_product eqS eqT)
             (uop_minset (lte_ignore_snd lte)
                (manger_llex_collect eqS bT nil
                   (bop_union (brel_product eqS eqT) X Y))) Z)))
    (uop_minset (lte_ignore_snd lte)
       (manger_llex_collect eqS bT nil
          (bop_union (brel_product eqS eqT) X
             (uop_minset (lte_ignore_snd lte)
                (manger_llex_collect eqS bT nil
                   (bop_union (brel_product eqS eqT) Y Z)))))) = true


    (M lte_ST (C eqS bT nil (U eq_ST (M lte_ST (C eqS bT nil (U eq_ST X Y))) Z)))
    (M lte_ST (C eqS bT nil (U eq_ST X (M lte_ST (C eqS bT nil (U eq_ST Y Z))))))

    C eqS bT nil (U eq_ST X Y) 
    =?= 
    C eqS bT (C eqS bT nil X) Y 


    M lte_ST (C eqS bT nil (U eq_ST (M lte_ST (C eqS bT nil (U eq_ST X Y))) Z))
    = 
    M lte_ST (C eqS bT nil (U eq_ST (M lte_ST (C eqS bT (C eqS bT nil X) Y)) Z))
    = 
    M lte_ST (C eqS bT (M lte_ST (C eqS bT (C eqS bT nil X) Y)) Z)
    =
      .... 
    = 
    M lte_ST (C eqS bT (C eqS bT nil X) (M lte_ST (C eqS bT (C eqS bT nil Y) Z)))
    = 
    M lte_ST (C eqS bT nil (U eq_ST X (M lte_ST (C eqS bT (C eqS bT nil Y) Z))))
    = 
    M lte_ST (C eqS bT nil (U eq_ST X (M lte_ST (C eqS bT nil (U eq_ST Y Z)))))


    [M (C (U [M (C (U X Y))] Z))]
    [M (C (U X [M (C (U Y Z))]))]



*)        


Admitted.        
End Theory.   
