Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.minset_union. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.product. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.product.
Require Import CAS.coq.bs.add_one. 
Require Import CAS.coq.bs.add_zero. 

Open Scope nat. 
Definition one1 :=
{|
  constant_ascii := "one1"
; constant_latex := "one1"
|}.

Definition infinity :=
{|
  constant_ascii := "INF"
; constant_latex := "\\infty"
|}.

Check A_sg_CI_minset_union_from_po.
(* 
   A_sg_CI_minset_union_from_po  : ∀ S : Type, A_po S → A_sg_CI (finite_set S)
*) 
Check A_po_product.
(*
   A_po_product : ∀ S T : Type, A_po S → A_po T → A_po (S * T)
*) 


(*  

(1) think of of Martelli ... 


From (S, <=, x) 
  
   N(P(S), <=, x) = (min_set_union(<=), minset_lift(<=, x))

   M(P(S), <=, x) = (minset_lift(<=, x), min_set_union(<=))


left(union)      : A = A union B     iff B subset A iff A superset B 
right(intersect) : B = A intersect B iff B subset A iff A superset B

left(intersect) : A = A intersect B iff A subset B iff B superset A 
right(union)    : B = A union B     iff A subset B iff B superset A 


From (subset, union) 
  
   N(subset, union) = (min_set_union(subset), minset_lift(subset, union))

   M(subset, union) = (minset_lift(subset, union), min_set_union(subset))   (martelli's semiring) 

? Generalize to

   N(<=, (.)) = (minset_union(<=), minset_lift(<=, (.)))             minset_union_lift 
   M(<=, (.)) = (minset_lift(<=, (.)), minset_union(<=))             minset_lift_union
*) 





(* 
Now, look at SIGCOMM 2020 

One way? 

let bs_sigcomm2020_with_paths = 
   bs_add_one self (
          bs_min_set_union_lift_from_posg (
	      posg_extend_right (posg_from_bs_left bs_bw_times_sp) (sg_sequence (ti_pair ti_int ti_int))))

              extend_right((<=, (.)), (@)) = (<=', (#)) 

              (a, b) (#) (c, d) = (a (.) c, b (@) d) 
              (a, b) <=' (c, d) = a <= c 

              now, minset_union_lift 

              = (minset_union(<='), minset_lift(<=', (#)) 

              NOTE: no reason to hope that idempotent(minset_lift(<=', (#)))

              BUT. when does (<=', (#)) satisfy these? 
              
                    LSM2 : a <' b => ca <' cb 
                    RSM2 : a <' b => ac <' bc

              when (<=, (.)) does?   yes. 

                    LSM1 : a < b => ca < cb 
                    RSM1 : a < b => ac < bc
             
             Note: (posg_from_bs_left bs_bw_times_sp) does not but 
                   (posg_from_bs_left bs_sp_times_sp) does (well, if we ignore 0!  REALLY need order-transform) 
              Note: product needs only one to be strictly increasing! 

              is bw monotone? NO.
                          b <= a 
                          a = max(a, b) => min(a, c) =?= max(min(a, c), min(a, b)) 
              a <  c:                          a               a          b       OK 
              b <= c <= a:                     c               c          b       OK 
              c < b <= a :                     c               c          b   ****NO****



             Q : does bs_min_set_union_lift_from_posg result in counter example to distributivity? 

             see minset_union_lift.v 

            (LM : os_left_monotone lteS bS)
            (RM : os_right_monotone lteS bS)             
            (DDD : (brel_antisymmetric S rS lteS) +  ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))) :       

            BUT, can we get a counter-example to distributitivity with something like this? 

            (LM : os_left_monotone lteS bS)
            (RM : os_right_monotone lteS bS)             
            (nanti : brel_not_antisymmetric S rS lteS)   x~y, x<>y
            (NLSM  : os_not_left_strictly_monotone lteS bS)   a << b and ca !<< cb 

                  {c} (ms{a, b}) <?> ms {ca, cb} 
                          a 
                  {ca} <?> ms {ca, cb} 

           cases 1) cb <= ca ????? 
                 2) ca ~ cb but ca<>cb OK 
                 3) ca << cb  contradiction
                 3) ca # cb  OK 
*) 



(*
(*Roadmap 


TODO

po/
  product (versions for qo with bottom) 

os/
  product (versions for qo with bottom) 
  sg -> (trivial, sg) 
  (length, concat) 

bs -> (po, sg) -> (po_with_bottom, sg_with_id) -> bs 
bs -> (po, sg) -> (qo, sg) -> (qo_with_bottom, sg_with_id) -> bs 

bs_min_set_union_lift_from_posg 
  (posg_add_bottom self (
        posg_extend_right (
            posg_from_bs_left bs_bw_times_sp)
            sg_edge_paths))


A_monotone_posg_from_predioid (S : Type) : A_predioid_with_id S -> A_monotone_posg S


1) bs_bw_times_sp

                    id     ann 
   + = max x min    _       _
   x = min x +      _       _

2) bs_bw_times_sp.

3) use A_monotone_posg_from_predioid  (Why id?) 

4) construct posg_edge_paths (with length?, so strictly increasing) 

5) posg direct product 3 and 4. 

6) transform 5 to ordered transform 

7) add_bottom_id to 6 (don't allow bottom in labels in order to preserve strictness) 

8) minset_union_lift on 7 to produce distrubutive semigrop transform (AME) 

*) 

Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures. 
Require Import CAS.coq.bs.product_product.
Require Import CAS.coq.bs.add_ann_add_id. 
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.max_min.
Require Import CAS.coq.bs.cast_up.
Require Import CAS.coq.ot.properties.
Require Import CAS.coq.ot.structures. 
Require Import CAS.coq.ot.left.length_cons.
Require Import CAS.coq.ot.left.from_bs_left.
Require Import CAS.coq.ot.left.product_product. 

Definition one1 :=
{|
  constant_ascii := "one1"
; constant_latex := "one1"
|}.

(*
ppa          : pre_path_algebra_NS
ppa_with_one : pre_path_algebra_with_one
poltr_mi     : poltr_monotone_increasing           
length_cons  : wpltr_monotone_strictly_increasing  
olt_msi      : qoltr_monotone_structly_increasing  
*)


Definition ppa := pre_path_algebra_product pre_path_algebra_max_min pre_path_algebra_min_plus. 

Definition ppa_with_one := add_one_to_pre_path_algebra ppa one1.

Definition poltr_mi := pre_path_algebra_to_poltr_mi _ ppa_with_one. 

Definition length_cons := length_cons_wpltr_monotone_strictly_increasing (eqv_product eqv_eq_nat eqv_eq_nat). 

Definition olt_msi := product_qoltr_monotone_strictly_increasing poltr_mi length_cons. 


Eval cbv in olt_msi. 

Eval cbv in ppa_with_one. 

Check length_cons. 

Open Scope nat.

Definition bs1 := bs_product bs_min_plus bs_max_min.

Print bs1.

(* Compute bs1. *) 


Eval cbv in bs_plus_certs bs1.

Eval cbv in bs_times_certs bs1. 

Eval cbv in bs_certs bs1.

Eval cbv in bs_certs bs_min_plus.

Eval cbv in bs_certs bs_max_min. 

Eval cbv in bs_min_plus.

Eval cbv in length_cons_wpltr_monotone_structly_increasing.

Definition plus := bs_plus bs1.

Eval cbv in plus (1, 2) (3, 4).

Definition times := bs_times bs1.

Eval cbv in times (1, 2) (3, 4).

(*
let bs_sigcomm2020_with_paths = 
   bs_add_one self (
          bs_min_set_union_lift_from_posg (
	      posg_extend_right (posg_from_bs_left bs_bw_times_sp) (sg_sequence (ti_pair ti_int ti_int))))
*)

Definition edge_paths := sg_concat (eqv_product eqv_eq_nat eqv_eq_nat).

Eval hnf in edge_paths. 
Eval cbv in sg_certs edge_paths. 

(* to do 

  1) posg_from_bs_left
  2) posg_extend_right
  3) finish bs_min_set_union_lift_from_posg

*) 
*)
