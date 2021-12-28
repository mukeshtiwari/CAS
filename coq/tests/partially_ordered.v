Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Extraction.


Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.minset_union. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.product. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast_up. 
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.max_min.
Require Import CAS.coq.bs.product.
Require Import CAS.coq.bs.add_one. 
Require Import CAS.coq.bs.add_zero.
Require Import CAS.coq.bs.minset_union_lift. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.
Require Import CAS.coq.os.from_bs_left.

Open Scope nat. 

Definition self :=
{|
  constant_ascii := "SELF"
; constant_latex := "\\bot"
|}.

Definition infinity :=
{|
  constant_ascii := "INF"
; constant_latex := "\\infty"
|}.

Check A_min_plus.
(*
   A_min_plus : A_selective_cancellative_pre_dioid_with_one nat
 *)
Check A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one. 
(*
     : ∀ S : Type, A_selective_cancellative_pre_dioid_with_one S → A_selective_pre_dioid_with_one S
*)
Check A_add_zero_to_selective_pre_dioid_with_one.
(*
     : ∀ S : Type, A_selective_pre_dioid_with_one S → cas_constant → A_selective_dioid (with_constant S)
*)          
Definition A_shortest_paths :=
      A_add_zero_to_selective_pre_dioid_with_one _
           (A_selective_pre_dioid_with_one_from_selective_cancellative_pre_dioid_with_one _ A_min_plus)
           infinity. 
Check A_shortest_paths. 
(* A_selective_dioid (with_constant nat) *) 

Check A_max_min.
(*
   A_max_min : A_selective_distributive_prelattice_with_zero nat
*) 
Check A_selective_pre_dioid_with_zero_from_selective_distributive_prelattice_with_zero.
(*
     : ∀ S : Type, A_selective_distributive_prelattice_with_zero S → A_selective_pre_dioid_with_zero S
*)          
Check A_add_one_to_selective_pre_dioid_with_zero.         
(*
     : ∀ S : Type, A_selective_pre_dioid_with_zero S → cas_constant → A_selective_dioid (with_constant S)
*) 
Definition A_widest_paths := 
     A_add_one_to_selective_pre_dioid_with_zero _ 
        (A_selective_pre_dioid_with_zero_from_selective_distributive_prelattice_with_zero _ A_max_min)
        self. 
Check A_widest_paths. 
(*
     : A_selective_dioid (with_constant nat)
*) 
Check A_dioid_product_from_selective_dioids. 
(*
    : ∀ S T : Type, A_selective_dioid S → A_selective_dioid T → A_dioid (S * T)
*) 
Definition A_shortest_and_widest_paths :=
  A_dioid_product_from_selective_dioids _ _ A_shortest_paths A_widest_paths.

Definition nsel := A_sg_CI_not_selective _ _ _ (A_dioid_plus_proofs _ A_shortest_and_widest_paths). 
Definition pnsel := projT1 nsel. 
Eval cbv in pnsel. 
(*
(inl {| constant_ascii := "INF"; constant_latex := "\\infty" |},
       inl {| constant_ascii := "SELF"; constant_latex := "\\bot" |},
       (inr 0, inr 0))
     : with_constant nat * with_constant nat *
       (with_constant nat * with_constant nat)
*) 

Definition step1 := A_posg_from_dioid _ A_shortest_and_widest_paths. 
Check step1.
(*
     : A_bounded_monotone_increasing_posg
         (with_constant nat * with_constant nat)
 *)
Definition nt := A_po_not_total _ _ _ (A_bmiposg_lte_proofs _ step1). 
Check nt.
(*
     : brel_not_total (with_constant nat * with_constant nat)
         (A_bmiposg_lte (with_constant nat * with_constant nat) step1)
 *)
Definition pnt := projT1 nt. 
Check pnt. 
(*     : with_constant nat * with_constant nat *
       (with_constant nat * with_constant nat)
Eval cbv in pnt.
 *)

Check A_minset_union_lift_from_bounded_monotone_increasing_posg.
(*
     : ∀ S : Type, A_bounded_monotone_increasing_posg S → A_dioid (finite_set S)
*) 
Check A_posg_from_dioid. 
(* 
     : ∀ S : Type, A_dioid S → A_bounded_monotone_increasing_posg S
*)

Definition A_minset_union_lift_from_dioid (S: Type) (D : A_dioid S) : A_dioid (finite_set S) :=
    A_minset_union_lift_from_bounded_monotone_increasing_posg _ (A_posg_from_dioid _ D).

Definition A_shortest_widest_pareto_paths := 
  A_minset_union_lift_from_dioid _ A_shortest_and_widest_paths.

Check A_shortest_widest_pareto_paths. 
(*      : A_dioid (finite_set (with_constant nat * with_constant nat))  *)






Open Scope list_scope.

Definition plus := A_dioid_plus _ A_shortest_widest_pareto_paths. 
Definition times := A_dioid_times _ A_shortest_widest_pareto_paths.
Check plus. 
Definition v (a b : nat) : with_constant nat * with_constant nat := (inr a, inr b). 
Definition set1 : finite_set (with_constant nat * with_constant nat):= (v 10 10) :: nil.
Definition set2 : finite_set (with_constant nat * with_constant nat):= (v 100 100) :: nil.

Eval cbv in (plus set1 set2).
Eval cbv in (times set1 set2). 
Eval cbv in times (plus set1 set2) (plus set1 set2).
    
(* NOW, do this again in AMCAS. *) 

Check A_bs_mcas_min_plus.   (* : A_bs_mcas nat *) 
Check A_bs_mcas_max_min.    (* : A_bs_mcas nat *) 

Check A_bs_mcas_add_one.
(*  : ∀ S : Type, A_bs_mcas S → cas_constant → A_bs_mcas (with_constant S) *) 

Check A_bs_mcas_add_zero.
(*  : ∀ S : Type, A_bs_mcas S → cas_constant → A_bs_mcas (with_constant S) *) 

Check A_bs_mcas_product.
(*  : ∀ S T : Type, A_bs_mcas S → A_bs_mcas T → A_bs_mcas (S * T) *)

Definition test := A_bs_mcas_product _ _
                                     (A_bs_mcas_add_zero _ A_bs_mcas_min_plus infinity)
                                     (A_bs_mcas_add_one _ A_bs_mcas_max_min self).
Check test. 

Check A_bs_mcas_minset_union_lift. 
(*      : ∀ S : Type, A_bs_mcas S → A_bs_mcas (finite_set S) *)

Definition test2 := A_bs_mcas_minset_union_lift _ test.
Check test2. 
(*      : A_os_mcas (with_constant nat * with_constant nat) *) 


(*
Definition test3 := match test2 with | A_BS_dioid _ D => Some(A2C_dioid _ D) | _ => None end.
Check test3.

Definition t := Eval cbv in (match test3 with | None => None | Some d => Some(dioid_plus_certs _ d) end).
*) 
(* t contains dependent type junk! 

Print t. 

Assert_Not_Selective e 
is over 18K lines long! 

Extraction t. 
*) 

Definition p := Eval cbv in (match (match A_bs_from_mcas _ test with | A_BS_bs _ b => Some (A2C_bs _ b) | _ => None end) with
                             | None => None
                             | Some b => Some(asg_selective_d (bs_plus_certs b))
                             end). 
Print p.
(*
p = 
Some
  (Certify_Not_Selective
     (inl {| constant_ascii := "INF"; constant_latex := "\\infty" |},
     inl {| constant_ascii := "SELF"; constant_latex := "\\bot" |},
     (inr 0, inr 0)))
     : option check_selective
*) 

(*********************** NOW, do this again in MCAS. **************************************) 


Check bs_mcas_min_plus.   (* : bs_mcas  *) 
Check bs_mcas_max_min.    (* : bs_mcas *) 

Check bs_mcas_add_one.
(*  : bs_mcas S → cas_constant → bs_mcas *) 

Check bs_mcas_add_zero.
(*  : bs_mcas S → cas_constant → bs_mcas *) 

Check bs_mcas_product.
(*  :      : bs_mcas → bs_mcas → bs_mcas
where
?S : [ |- Type]
?T : [ |- Type]
*)

Definition mtest := bs_mcas_product (bs_mcas_add_zero bs_mcas_min_plus infinity)
                               (bs_mcas_add_one bs_mcas_max_min self).
Check mtest.  (*      : bs_mcas *)  

Eval cbv in match mtest with BS_bs B => bs_classify B | _ => BS_Error "nope" end. 
(* is a BS_dioid *) 

(* implement this *) 
Check posg_from_bs.  (* : bs_mcas → os_mcas*) 

(* implement this 
A_minset_union_lift_from_bounded_monotone_increasing_posg
becomes 
 *)
Check os_mcas_minset_union_lift. (* : os_mcas → bs_mcas *)

Definition bs_mcas_minset_union_lift {S : Type} (A : @bs_mcas S) : @bs_mcas (finite_set S) :=
  os_mcas_minset_union_lift (posg_from_bs A).

Definition mtest2 := bs_mcas_minset_union_lift mtest. 
Eval cbv in mtest2. 
