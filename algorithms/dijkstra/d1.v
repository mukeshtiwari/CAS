(***********************************************************************)
(* This file contains a formalization of some of the ideas from this   *)
(* paper (referred to as RIE below).                                   *) 
(*                                                                     *)
(*    Routing in Equilibrium.                                          *)
(*    João Luís Sobrinho and Timothy G. Griffin.                       *)
(*    19th International Symposium on Mathematical                     *)
(*    Theory of Networks and Systems (MTNS 2010).                      *)
(*    http://www.cl.cam.ac.uk/~tgg22/publications/routing_in_equilibrium_mtns_2010.pdf *) 
(*                                                                     *)
(***********************************************************************)
(* April 2012                      *)
(* Timothy G. Griffin              *)
(* University of Cambridge         *)
(* tgg22@cam.ac.uk                 *)
(* http://www.cl.cam.ac.uk/~tgg22/ *)


Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype finfun path.
Require Import bigop prime finset binomial ssralg perm zmodp matrix. 

Require Import Coq.Unicode.Utf8. 

Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* I still haven't decided if using Unicode is a good idea..... *) 
Notation "A ∈ B" := (A \in B) (at level 60). 
Notation "A ∉ B" := (~~(A \in B)) (at level 60). 
Notation "⟦ n ⟧" := ('I_ n) (at level 0).  (** ⟦ n ⟧ is the set {0, 1, ... n-1} *) 

Section Dijkstra. 

(* The algebraic signature                                 *) 
Variable T        : eqType .    (* the carrier type        *) 
Variable plus_op  : T → T → T.  (* addition                *) 
Variable times_op : T → T → T.  (* multiplication          *)
Variable one      : T.          (* multiplicative identity *) 
Variable zero     : T.          (* additive identity       *) 

Notation "A ⊕ B" := (plus_op A B) (at level 50, left associativity). 
Notation "A ◎ B" := (times_op A B) (at level 40, left associativity). 

(* The (left) natural order (lno) induced by ⊕.            *) 
(* Note the RIE paper uses the right natural order (rno).  *) 
Definition lno (a b : T) := a ⊕ b == a. 
Notation "A ≦ B" := (lno A B) (at level 60). 

Notation "𝕄( m )" := ('M[T]_ m)  (at level 0).           (* m x m matrices         *) 
Notation "𝕍( m )" := ('rV[T]_ m)  (at level 0).          (* 1 x m row vectors      *) 
Notation "ℙ( m )" := ('rV[seq ⟦ m ⟧]_ m)  (at level 0).  (* 1 x m vectors of paths *) 
Notation "⨁_ ( i < m ) F" := (\big[plus_op/zero]_(i < m) F)
  (at level 36, F at level 36, op, i, m at level 50, format "'[' ⨁_ ( i  <  m )  F ']'").
Notation "⨁_ ( i ∈ s ) F" := (\big[plus_op/zero]_(i <- s) F)
  (at level 36, F at level 36, op, i, s at level 50, format "'[' ⨁_ ( i  ∈  s )  F ']'").

(***********************************************************************)
(* Dijkstra's Algorithm.                                               *)
(***********************************************************************)
Open Scope ring_scope. 

Variable n : nat.                             (* number of nodes in graph/network    *) 
Variable 𝐀 : 𝕄(n).                            (* the adjacency matrix                *) 
Variable 𝐀_diag : ∀ x : ⟦ n ⟧, 𝐀 x x = zero.  
Definition 𝐈 : 𝕄(n) :=                        (* the multiplicative identity matrix *) 
   \matrix_(i, j) (if i == j then one else zero). 

(* A (dijkstra) state keeps track of nodes visited, the priority queue, 
and the current estimate.  The paths are not really needed but will be used
(eventially) to explore the distinction between local and global optimality *) 
Definition state := ((seq ⟦ n ⟧) * (seq ⟦ n ⟧) * 𝕍(n) * ℙ(n))%type. 
Definition visited    (s : state) := s.1.1.1. 
Definition priority_Q (s : state) := s.1.1.2. 
Definition estimate   (s : state) := s.1.2.
Definition paths      (s : state) := s.2.

(* A preorder induced on the indicies of a vector by 
   the ≦-order on the vector elements.  *) 
Definition index_preorder (v : 𝕍(n)) (a b : ⟦ n ⟧) := (v 0 a) ≦ (v 0 b). 


Definition initial_state (i : ⟦ n ⟧) : state := 
   let S   :=  filter (fun x => x != i) (ord_enum n) in 
   let est := \row_j (𝐈 i j  ⊕ 𝐀 i j)in 
   let pq  := sort (index_preorder est) S in 
   let vis := [:: i] in 
   (vis, pq, est, \row_j (if i == j then [:: i] else [:: j; i])). 

(* just relax! *) 
Definition relax (s : seq ⟦ n ⟧) (v : 𝕍(n)) (u : ⟦ n ⟧) := 
     \row_(j < n) (if j ∈ s then v 0 j ⊕ ((v 0 u) ◎ (𝐀 u j)) else v 0 j). 

Definition adjust_paths (s : seq ⟦ n ⟧) (v : 𝕍(n)) (pv : ℙ(n)) (u : ⟦ n ⟧) := 
     \row_(j < n) (if (j ∉ s) || ((j ∈ s) && ((v 0 j) ≦ (v 0 u) ◎ (𝐀 u j)))
                   then pv 0 j 
                   else j :: (pv 0 u)).  

(* Edsger takes one small step ... *) 
Definition dijkstra_step (p : state) : state := 
  match (priority_Q p) with 
  | [::] => p 
  | u :: tl => 
    let new_estimate := relax tl (estimate p) u                  in 
    let new_Q        := sort (index_preorder new_estimate) tl    in 
    let new_vis      := u::(visited p)                           in 
    let new_paths    := adjust_paths tl (estimate p) (paths p) u in 
    (new_vis, new_Q, new_estimate, new_paths)
  end. 

Definition dijkstra_iteration (i : ⟦ n ⟧) : state := 
   iter n.-1 dijkstra_step (initial_state i). 
   
(* 𝕯 i j == the weight of the right local solution from i to j, calculated *) 
(* by Dijkstra's algorithm.                                                *) 
Definition 𝕯 (i j : ⟦ n ⟧) : T := estimate (dijkstra_iteration i) 0 j. 

(***************************************************************) 
(* The minimal requirements for computing right-local          *) 
(* optima using Dijkstra's algoroithm.                         *) 
(* Very little is required of ◎.                               *) 
(***************************************************************) 

(* ⊕ is a semi-lattice with a total order.                     *) 
Variable plus_associative      : ∀x y z, x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z. 
Variable plus_commutative      : ∀x y, x ⊕ y = y ⊕ x. 
Variable plus_selective        : ∀x y, (x ⊕ y == x) || (x ⊕ y == y). 

(* identities                                                   *) 
(* Note : only a left identity is needed for multiplication,    *) 
(* while the RIE paper seems to imply a full identity, yet a    *) 
(* right identity of ◎ is never used in the proof below.        *) 
Variable zero_is_left_plus_id  : ∀x, zero ⊕ x = x. 
Variable one_is_left_times_id  : ∀x, one ◎ x = x. 

(* one is additive annihilator                                   *) 
(* Note: RIE paper does not seem to state this as a              *) 
(* requirement, but instead states that zero is a multiplicative *) 
(* annihilator (which is never actually used in the proof below).*) 
Variable one_is_left_plus_ann  : ∀x, one ⊕ x = one. 
Variable one_is_right_plus_ann : ∀x, x ⊕ one = one. 

(* right absorbtion                                              *) 
Variable right_absorption      : ∀ a b : T, a ⊕ (a ◎ b) == a.

(***************************************************************) 
(* A few useful facts.                                         *)
(***************************************************************) 

Lemma zero_is_right_plus_id : ∀x, x ⊕ zero = x.
Proof. move=> x. rewrite plus_commutative. by apply zero_is_left_plus_id. Qed. 

Lemma lno_transitive : ∀ a b c : T,  a ≦ b → b ≦ c  → a ≦ c. 
Proof. 
rewrite /lno => a b c p q. 
rewrite -(eqP p) -plus_associative. 
by rewrite (eqP q). 
Qed. 

Lemma lno_right_increasing : ∀ a b : T,  a ≦ a ◎ b. 
Proof. move=> a b. rewrite /lno. by apply: right_absorption. Qed. 

Lemma lno_total : ∀ a b : T,  (a ≦ b) || (b ≦ a). 
Proof. 
rewrite /lno => a b. 
case/orP: (plus_selective a b). 
  move=> p. rewrite (eqP p). apply/orP. 
  by left. 

  move=> p. rewrite plus_commutative in p. rewrite (eqP p). apply/orP. 
  by right. 
Qed. 

(* OK, one strange thing about the lno is that one ≦ a ≦ zero.  ;-) *) 
Lemma one_is_bottom : ∀ a, one ≦ a. 
Proof. rewrite /lno => a. by rewrite one_is_left_plus_ann. Qed. 

Lemma plus_is_upper : ∀ a b c : T,  a ≦ b → a ≦ c  → a ≦ b ⊕ c. 
Proof. 
rewrite /lno => a b c p q. rewrite plus_associative. 
by rewrite (eqP p) (eqP q). 
Qed. 

Lemma index_preorder_transitive : ∀ v : 𝕍(n), transitive (index_preorder v). 
Proof.
rewrite /transitive. move=> v y x z. 
rewrite /index_preorder. move=> p q. 
by apply (lno_transitive p q). 
Qed. 

Lemma index_preorder_total : ∀ v : 𝕍(n), total (index_preorder v).
Proof.
move=> v. rewrite /total. move=> x y. 
rewrite /index_preorder. by apply lno_total. 
Qed. 

Lemma 𝐈_diag : ∀ x : ⟦ n ⟧, 𝐈 x x = one.
Proof. 
rewrite /𝐈 . 
unlock matrix_of_fun fun_of_matrix => x. 
rewrite /=. rewrite ffunE /=.
have fact : x == x. by []. 
by rewrite fact.
Qed. 

Lemma 𝐈_off_diag : ∀  x y : ⟦ n ⟧, x != y  → 𝐈 x y = zero.
Proof. 
rewrite /𝐈 . 
unlock matrix_of_fun fun_of_matrix => x y Neq. 
rewrite /=.
rewrite ffunE /=.
have fact : x == y = false. by apply negbTE. 
by rewrite fact.
Qed. 

(***************************************************************) 
(* A few auxiliary lemmas useful in the development.           *) 
(* Some of these may already exist in some corner of           *) 
(*   the ssreflect library....                                 *) 
(***************************************************************) 

Lemma not_in_cons : ∀ X : eqType, ∀ u t : X, ∀ s : seq X, 
    u ∉ (t :: s) = (u != t) && (u ∉ s). 
Proof.
move=> X u t s.
apply negbLR. 
rewrite negb_and. 
rewrite !negb_involutive. 
by rewrite in_cons. 
Qed. 

Lemma all_elim : ∀ X : eqType, ∀ P : pred X, ∀ s : seq X, ∀ w : X, 
   (w ∈ s) → (all P s) → (P w). 
Proof. 
move => X P s.
elim: s.
   by move=> w H. 

   move=> t s Ind w Q. 
   rewrite in_cons in Q. 
   case/orP: Q. 
     move=> Ewt. rewrite (eqP Ewt). 
     rewrite /all. 
     case/andP. 
     by move => W _ .

     move=> wIn. rewrite /all. 
     case/andP. move=> _ W. 
     by apply Ind.
Qed. 

Lemma head_of_sorted_is_least : ∀ ord : rel ⟦ n ⟧, 
     total ord → transitive ord  → 
      ∀ u : ⟦ n ⟧, ∀ s t : seq ⟦ n ⟧, 
       sort ord s = u :: t → ∀ w : ⟦ n ⟧, w ∈ t → ord u w. 
Proof. 
  move => ord total trans u s. 
  elim: s. 
     by move=> t H w Q. 

     move=> h tl Ind_s t. 
     elim: t. 
        by move=> Q w w_in_t. 

        move=> k s Ind_t Q w w_in_t. 
        have is_sorted : sorted ord ([:: u, k & s]).         
           have fact: sorted ord (sort ord (h::tl)). by apply sorted_sort. 
           by rewrite Q in fact. 
        rewrite /sorted in is_sorted.
        have u_least : all (ord u) (k::s). by apply order_path_min. 
        by apply (all_elim w_in_t). 
Qed. 

Lemma sort_preserves_mem : ∀ ord : rel ⟦ n ⟧, ∀ u : ⟦ n ⟧, ∀ s : seq ⟦ n ⟧, 
   u ∈ s → u ∈ sort ord s. 
Proof. 
move => ord u s H. 
have fact: sort ord s =i s. by apply mem_sort. 
rewrite /eq_mem in fact. 
by rewrite fact. 
Qed. 

Lemma mem_sort_implies_mem : ∀ ord : rel ⟦ n ⟧, ∀ u : ⟦ n ⟧, ∀ s : seq ⟦ n ⟧, 
   u ∈ sort ord s  → u ∈ s. 
Proof. 
move => ord u s H. 
have fact: sort ord s =i s. by apply mem_sort. 
rewrite /eq_mem in fact. 
by rewrite fact in H. 
Qed. 

Lemma sort_preserves_not_mem : ∀ ord : rel ⟦ n ⟧, ∀ u : ⟦ n ⟧, ∀ s : seq ⟦ n ⟧, 
   u ∉ s → u ∉ sort ord s. 
Proof. 
move => ord u s H. apply/negP. move/negP : H => H. move => F. 
by exact: (H (mem_sort_implies_mem F)). 
Qed. 

(* A specially tailored version of eq_bigr that exposes the range membership. *) 
Lemma eq_bigr2 : 
       ∀ R : Type,
       ∀ idx : R,
       ∀ op : R → R → R,
       ∀ I : eqType,
       ∀ r : seq I,
       ∀ P : pred I,  
       ∀ F1 F2 : I → R, 
  (∀ i, ((P i) && (i \in r) ) → F1 i = F2 i) →
  \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
Proof.
move=> R idx op I r P F1 F2 eqF12. 
rewrite big_cond_seq.
(* I want to do 2 rewrites using "big_cond_seq" but can't.  why? *) 
have whywhy: \big[op/idx]_(i <- r | P i) F2 i 
          = 
         \big[op/idx]_(i <- r | P i && (i ∈ r)) F2 i. 
   by rewrite big_cond_seq.
rewrite whywhy. 
apply eq_bigr. 
exact: eqF12. 
Qed.

(* I found "rewrite mxE" difficult to control. 
   It often does the wrong thing! This lemma is used 
   to tame it for a special case. 
*) 
Lemma row_elim : ∀ X : Type,  ∀ w : ⟦ n ⟧, ∀ F : ⟦ n ⟧ → X,  
     (\row_j F j) 0 w = F w. 
Proof. move => X w F. by rewrite mxE. Qed. 



(*******************************

INVARIANTS 

*********************************)


Definition is_invariant_of (X : Type) (f : X → X) (P : X → Prop) := 
   ∀ x : X, P x → P (f x). 

(* if P holds for an initial state, and is an invariant under *)
(* transformation f, then P holds for all iterations of f    *) 
Lemma iteration_invariant: 
   ∀ X : Type, 
   ∀ f : X → X, 
   ∀ P : X → Prop, 
   ∀ x : X, 
   P x  → is_invariant_of f P  →  ∀ n,  P (iter n f x). 
Proof. 
move=> X f P x H Q m. 
elim: m. 
  by rewrite /iter /=. 
  
  move=> k F. 
  rewrite iterS. 
  rewrite /is_invariant_of in Q. 
  by apply Q. 
Qed. 


(* Invariants for initial_state/dijkstra_step. 
-- Yes, the first invariant (INV_permutation) covers
   the following three, but I found them easier to work with. 
*) 
Definition INV_permutation (s : state) := 
   perm_eq (priority_Q s ++ visited s) (index_enum (ordinal_finType n)). 

   Definition INV_visited_or_priority_Q (s : state) := 
      ∀ u : ⟦ n ⟧,  (u ∈ visited s) || (u ∈ priority_Q s). 

   Definition INV_visited_not_in_priority_Q (s : state) := 
      ∀ u : ⟦ n ⟧,  u ∈ visited s → u ∉ priority_Q s. 

   Definition INV_uniq_priority_Q (s : state) := 
      uniq (priority_Q s).

Definition INV_i_visited (i : ⟦ n ⟧) (s : state) := 
   i ∈ visited s. 

Definition INV_visited_closer (i : ⟦ n ⟧) (s : state) := 
   ∀ j u : ⟦ n ⟧,  j ∈ (visited s) → u ∈ (priority_Q s) → 
           (estimate s) 0 j ≦ (estimate s) 0 u. 

Definition INV_priority_Q (s : state) := ∀ h u : ⟦ n ⟧, ∀ tl : seq ⟦ n ⟧,  
   priority_Q s = h :: tl → (u ∈ tl) → estimate s 0 h ≦  estimate s 0 u. 

Definition INV_estimate (i : ⟦ n ⟧) (s : state) := 
    ∀ j : ⟦ n ⟧, estimate s 0 j = 𝐈 i j ⊕ ⨁_(q ∈ visited s) (estimate s 0 q ◎ 𝐀 q j).  

(*******************************

INVARIANTS hold for initial state 

*********************************)

(* TODO : master the manipulation of permutations in ssreflect .... *) 
Hypothesis INV_permutation_init : ∀ i : ⟦ n ⟧, INV_permutation (initial_state i). 

Lemma INV_i_visited_init : ∀ i : ⟦ n ⟧, INV_i_visited i (initial_state i). 
Proof. 
rewrite /INV_i_visited /initial_state /visited /= => i. 
by rewrite mem_seq1. 
Qed. 

Lemma INV_visited_or_priority_Q_init : ∀ i : ⟦ n ⟧, INV_visited_or_priority_Q (initial_state i). 
Proof. 
rewrite /INV_visited_or_priority_Q /initial_state /visited /priority_Q /= => i u. 
have Eqd : (u == i) || (u != i). by apply: orbN. 
case/orP: Eqd. 
   move=> Eui. rewrite (eqP Eui). apply/orP. left. by rewrite mem_seq1. 

   move=> Nui. apply/orP. right. apply sort_preserves_mem . 
   rewrite mem_filter. apply/andP. split. 
      by []. 
      by apply mem_ord_enum. 
Qed. 

Lemma INV_visited_not_in_priority_Q_init : ∀ i : ⟦ n ⟧, INV_visited_not_in_priority_Q (initial_state i). 
Proof. 
rewrite /INV_visited_not_in_priority_Q /initial_state /visited /priority_Q /= => i u. 
rewrite mem_seq1. move => Eui. rewrite (eqP Eui). 
apply sort_preserves_not_mem. 
rewrite mem_filter.
apply/nandP. left. 
apply/negP => F. 
move/negP : F => F. 
by apply: F. 
Qed. 


Lemma INV_uniq_priority_Q_init : ∀ i : ⟦ n ⟧, INV_uniq_priority_Q (initial_state i). 
Proof. 
rewrite /INV_uniq_priority_Q /initial_state /visited /estimate /priority_Q /= => i. 
rewrite sort_uniq. 
apply filter_uniq. 
by apply ord_enum_uniq.
Qed. 

Lemma INV_visited_closer_init : ∀ i : ⟦ n ⟧, INV_visited_closer i (initial_state i). 
Proof. 
rewrite /INV_visited_closer /initial_state /visited /priority_Q /= => i j u. 
rewrite mem_seq1 => ji. rewrite (eqP ji) => H. 
rewrite !row_elim.
rewrite 𝐀_diag zero_is_right_plus_id 𝐈_diag. 
by rewrite one_is_bottom. 
Qed. 

Lemma INV_priority_Q_init : ∀ i : ⟦ n ⟧, INV_priority_Q (initial_state i). 
Proof. 
rewrite /INV_priority_Q /initial_state /priority_Q /= => i u w tl P w_in_tl. 
move/head_of_sorted_is_least: P => P.
apply P. 
   apply index_preorder_total. 
   apply index_preorder_transitive. 
   by exact: w_in_tl. 
Qed. 

Lemma INV_estimate_init : ∀ i : ⟦ n ⟧, INV_estimate i (initial_state i). 
Proof. 
rewrite /INV_estimate /initial_state /visited /= => i j. 
rewrite big_cons  big_nil.
rewrite zero_is_right_plus_id. 
rewrite !row_elim.
rewrite 𝐈_diag. 
rewrite one_is_left_plus_ann. 
by rewrite one_is_left_times_id. 
Qed. 

(*******************************

INVARIANTS hold on dijkstra step. 

Note that they are not entirely independent, 
this is the reason for AUGmented invariantes below. 

*********************************)

(* TODO : master the manipulation of permutations in ssreflect .... *) 
Hypothesis INV_permutation_holds : is_invariant_of dijkstra_step INV_permutation.

Lemma INV_visited_or_priority_Q_holds : is_invariant_of dijkstra_step INV_visited_or_priority_Q.
Proof. 
rewrite /is_invariant_of.  move => [[[vis pq] v] pathv]. 
rewrite /INV_visited_or_priority_Q /visited /priority_Q /=.
case: pq. 
   move => H u. 
   case/orP : (H u). 
      move => u_in_vis. apply/orP. left. 
         by rewrite /dijkstra_step /visited /=.      
      by move=> F. 

   move => h tl H u. 
   case/orP : (H u). 
      move => u_in_vis. apply/orP. left. 
         rewrite /dijkstra_step /visited /=.      
         rewrite in_cons. apply/orP. 
         by right. 
      rewrite in_cons. 
      case/orP. 
         move=> Euh. rewrite (eqP Euh). 
         rewrite /dijkstra_step /priority_Q /=.  
         apply/orP. left. rewrite in_cons.    
         apply/orP. 
         by left. 

         rewrite /dijkstra_step /priority_Q /= => uIn. 
         apply/orP. right. 
         by apply sort_preserves_mem . 
Qed. 

Lemma INV_uniq_priority_Q_holds : is_invariant_of dijkstra_step INV_uniq_priority_Q.
Proof. 
move=> [[[vis pq] v] pathv]. rewrite /INV_uniq_priority_Q /priority_Q /=. 
case pq. 
  by []. 
  
  rewrite /dijkstra_step /= => o s. 
  case/andP => H P.
  by rewrite sort_uniq. 
Qed.


(* TODO : clean up the way the AUGmented invariants are done .... *) 

Definition AUG_visited_not_in_priority_Q (s : state) := 
   INV_uniq_priority_Q s /\ INV_visited_not_in_priority_Q s. 

Lemma AUG_visited_not_in_priority_Q_init : ∀ i : ⟦ n ⟧, 
   AUG_visited_not_in_priority_Q (initial_state i). 
Proof. 
rewrite/AUG_visited_not_in_priority_Q => i.  split.
   by apply INV_uniq_priority_Q_init. 
   by apply INV_visited_not_in_priority_Q_init. 
Qed. 


Lemma AUG_visited_not_in_priority_Q_holds : is_invariant_of dijkstra_step AUG_visited_not_in_priority_Q.
Proof. 
rewrite /is_invariant_of. move=> [[[vis pq] v] pathv]. 
rewrite /AUG_visited_not_in_priority_Q. 
move => [H1 H2]. split. 
   by apply: (INV_uniq_priority_Q_holds H1). 

   move: H1 H2.   
   rewrite /INV_visited_or_priority_Q /visited /priority_Q /=.
   case: pq. 
   move => _ _. 
      by rewrite /dijkstra_step /INV_visited_not_in_priority_Q /visited /=.      

   rewrite /dijkstra_step /INV_visited_not_in_priority_Q /priority_Q /visited /=. 
   move => t s UPQ H u Q. 
   rewrite in_cons in Q. 
   apply sort_preserves_not_mem. 
   case/orP : Q. 
     move => Eut. rewrite /INV_uniq_priority_Q /= in UPQ. rewrite (eqP Eut). by move/andP : UPQ => [F _]. 
    
     move => uIn. 
     have fact: u ∉ (t :: s). by apply H. 
     rewrite not_in_cons in fact. by move/andP : fact => [_ F]. 
Qed. 



Lemma INV_i_visited_holds : ∀ i : ⟦ n ⟧, is_invariant_of dijkstra_step (INV_i_visited i). 
Proof. 
rewrite /is_invariant_of => i [[[vis pq] v] pathv]. 
rewrite /dijkstra_step /INV_i_visited /visited /priority_Q /=.
case: pq; rewrite /=.
  by move => F. 
  move => t _ H. rewrite in_cons. apply/orP. 
  by right.
Qed. 

Lemma INV_priority_Q_holds : is_invariant_of dijkstra_step INV_priority_Q.
Proof. 
move=> [[[vis pq] v] pathv]. 
case pq. 
  by rewrite /INV_priority_Q /priority_Q /= => H u h tl F.

  rewrite /INV_priority_Q /estimate /visited /priority_Q /= => o s H u h tl Q h_in_tl.
  move/head_of_sorted_is_least: Q => Q. 
  apply Q.
     apply index_preorder_total. 
     apply index_preorder_transitive. 
     by exact: h_in_tl. 
Qed.


Definition AUG_visited_closer (i : ⟦ n ⟧) (s : state) := 
   ((((
   INV_permutation s                 /\
   INV_visited_or_priority_Q s)      /\ 
   AUG_visited_not_in_priority_Q s)  /\ 
   INV_uniq_priority_Q s)            /\ 
   INV_priority_Q s)                 /\ 
   INV_visited_closer i s.

Lemma AUG_visited_closer_init : ∀ i : ⟦ n ⟧, AUG_visited_closer i (initial_state i). 
Proof. 
move=> i. 
rewrite /AUG_visited_closer. split. 
   split. 
      split. 
        split. 
          split. 
             by apply INV_permutation_init. 
             by apply INV_visited_or_priority_Q_init. 
          by apply AUG_visited_not_in_priority_Q_init. 
        by apply INV_uniq_priority_Q_init. 
     by apply INV_priority_Q_init. 
  by apply INV_visited_closer_init. 
Qed. 


Lemma AUG_visited_closer_holds : ∀ i : ⟦ n ⟧, is_invariant_of dijkstra_step (AUG_visited_closer i).
Proof. 
move=> i. 
rewrite /is_invariant_of /AUG_visited_closer /INV_visited_closer. 
move=>[[[vis pq] v] pathv].
rewrite /estimate /visited /priority_Q /=. 
move=> [[[[[PM PA] DJ] H0] H1] H2]. split. 
   split. 
      split. 
        split.
           split. 
              by apply: (INV_permutation_holds PM).
              by apply: (INV_visited_or_priority_Q_holds PA).
           by apply: (AUG_visited_not_in_priority_Q_holds DJ).
        by apply: (INV_uniq_priority_Q_holds H0). 
      by apply: (INV_priority_Q_holds H1). 
   
   move: PM PA DJ H0 H1 H2. 
   case pq; rewrite /=.
      by move=> PM PA DJ H0 H1 H2 j u jin F.  

      move=> u tl _  _  [_ DJ] H0 H1 H2 j w. (* ugly ! *) 
      rewrite /visited /=.
      rewrite in_cons. 
      case/orP. 
         move=> ju. rewrite (eqP ju). 
         move => P. 

         rewrite /index_preorder /relax.
         rewrite !row_elim.
         have w_in : w ∈ tl. 
            by apply (mem_sort_implies_mem P).
         have u_Nin : u ∈ tl = false. 
            rewrite /INV_uniq_priority_Q /priority_Q /= in H0. case/andP: H0. 
            move=> F _.  
            by move/negPf : F => F. 
         rewrite w_in u_Nin. 
         apply: plus_is_upper.
            rewrite /INV_priority_Q /priority_Q /= in H1. by apply (H1 u w tl). 
            by apply lno_right_increasing. 

    (* j ∈ vis *) 
        move=> jin P.
        rewrite /relax. 
        rewrite !row_elim.
        have jNin : j ∈ tl = false. 
           rewrite /INV_visited_not_in_priority_Q /visited /priority_Q /= in DJ. 
           have F : j ∉ (u :: tl). by apply: (DJ j jin). 
           rewrite in_cons in F. 
           move/norP : F => F. 
           case: F. move => _ F. 
           by move/negPf : F => F.         
        have win : w ∈ tl = true. by apply (mem_sort_implies_mem P). 
        rewrite jNin win. 
        apply plus_is_upper.  
           apply H2. by []. rewrite in_cons.  apply/orP. by right.
 
           have M : v 0 j ≦ v 0 u. 
              apply (H2 j u jin).  rewrite in_cons. apply/orP. by left. 
           apply (lno_transitive M). 
           by apply lno_right_increasing. 
Qed. 


Definition AUG_estimate (i : ⟦ n ⟧) (s : state) := 
   (AUG_visited_closer i s) /\ (INV_estimate i s).

Lemma AUG_estimate_init : ∀ i : ⟦ n ⟧, AUG_estimate i (initial_state i). 
Proof. 
rewrite/AUG_estimate => i.  split.
   by apply AUG_visited_closer_init. 
   by apply INV_estimate_init. 
Qed. 


(* TODO : clean up this messy proof. *) 
Lemma AUG_estimate_holds : ∀ i : ⟦ n ⟧, is_invariant_of dijkstra_step (AUG_estimate i).
Proof. 
rewrite /is_invariant_of /AUG_estimate /INV_estimate => i [[[vis pq] v] pathv].
rewrite /visited /estimate /=.
move => [H12 H3]. split. 
   by apply: (AUG_visited_closer_holds H12). 
   
   move=> j. 
   move: H12 H3. 
   have jLoc : ((j ∈ vis) || (j ∉ vis)). by apply: orbN. 
   case/orP : jLoc => jLoc. 
      (* jLoc : j ∈ vis *) 
      case pq; rewrite /=. move=> H12 H3. 
         by apply: H3.

      move=> u tl. rewrite /visited /=.
      move=> [[[[[PM PA] [ _ DJ]] H0] H1] H2] H3.  (* ugly ! *) 
      rewrite big_cons. 
      rewrite !row_elim.     
      have jNins : j ∈ tl = false. 
         rewrite /INV_visited_not_in_priority_Q /visited /priority_Q /= in DJ.         
         have M : j ∉ (u :: tl). by apply DJ.
         move/negPf : M => M.  
         rewrite in_cons in M. 
         move/norP : M => M.  
         case: M. move=> _ M. 
         by move/negPf : M => M.  
      have uNins : u ∈ tl = false.    
        rewrite /INV_uniq_priority_Q /priority_Q /= in H0.
        case: H0. case/andP. move=> H0 _.         
        by move/negPf : H0 => H0.         
      rewrite uNins jNins. 
      have Eq : 𝐈 i j ⊕ (v 0 u ◎ 𝐀 u j ⊕ ⨁_(j0 ∈ vis) ((relax tl v u) 0 j0 ◎ 𝐀 j0 j))
               = (𝐈 i j ⊕ ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j)) ⊕ (v 0 u ◎ 𝐀 u j).  
         rewrite {1}plus_associative. 
         (* rewrite plus_commutative.   this does not work!  *) 
         have whywhy : 𝐈 i j ⊕ v 0 u ◎ 𝐀 u j = (v 0 u ◎ 𝐀 u j) ⊕ 𝐈 i j. 
            by rewrite plus_commutative. 
         rewrite whywhy. 
         rewrite -{1}plus_associative. 
         rewrite plus_commutative. 
         rewrite /relax. 
         have boring : ⨁_(j0 ∈ vis) ((\row_j1 (if j1 ∈ tl
                             then v 0 j1 ⊕ v 0 u ◎ 𝐀 u j1
                             else v 0 j1)) 0 j0 ◎ 𝐀 j0 j) = 
                       ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j). 
            apply eq_bigr2. 
            move=> k P. 
            case: P. move => kIn. 
            rewrite row_elim. 
              have kNin : k ∈ tl = false.
                 rewrite /INV_visited_not_in_priority_Q /visited /priority_Q /= in DJ. 
                 have M : k ∉ (u :: tl). by apply DJ.
                 move/negPf : M => M.  
                 rewrite in_cons in M. 
                 move/norP : M => M.  
                 case: M. move=> _ M. 
                 by move/negPf : M => M.  
              by rewrite kNin.                
         by rewrite boring. 
      rewrite Eq.
      rewrite -H3. 
      have Restate : v 0 j ≦ v 0 u ◎ 𝐀 u j. 
         have sfact : v 0 j ≦ v 0 u. 
            rewrite /INV_visited_closer /visited /priority_Q /= in H2. 
            apply H2. 
              by [].
              rewrite in_cons. apply/orP. by left. 
         by rewrite (lno_transitive sfact (lno_right_increasing (v 0 u) (𝐀 u j) )).
      rewrite /lno in Restate. 
      by rewrite (eqP Restate).

      (* jLoc : j ∉ vis *) 
      case pq; rewrite /=. move=> H12 H3. 
         by apply: H3.

      move=> u tl. rewrite /visited /=.
      move=> [[[[[PM PA] DJ] H0] H1] H2] H3. 
      rewrite big_cons. 
      have Eq: ⨁_(j0 ∈ vis) ((relax tl v u) 0 j0 ◎ 𝐀 j0 j) = 
               ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j). 
         apply eq_bigr2. 
         move=> k M. 
         have kNin : k ∈ tl = false. 
            rewrite /INV_visited_not_in_priority_Q /visited /priority_Q /= in DJ.         
            have kNin2 : k ∉ (u :: tl). apply DJ. by case/andP: M. 
            rewrite in_cons in kNin2.
            move/norP : kNin2 => kNin2.
            case: kNin2. move=> _ kNin2.
            by move/negPf : kNin2 => kNin2.   
         rewrite /relax. 
         rewrite row_elim.
         by rewrite kNin.
      rewrite Eq. 
      have Eq2 : 𝐈 i j ⊕ ((relax tl v u) 0 u ◎ 𝐀 u j ⊕ ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j)) =
                 (𝐈 i j ⊕ ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j)) ⊕ (relax tl v u) 0 u ◎ 𝐀 u j. 
        rewrite -plus_associative.
        have strange: (relax tl v u) 0 u ◎ 𝐀 u j ⊕ ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j)
                      = ⨁_(j0 ∈ vis) (v 0 j0 ◎ 𝐀 j0 j) ⊕ (relax tl v u) 0 u ◎ 𝐀 u j. 
           by rewrite plus_commutative. (* I want to do this directly to original goal! *) 
        by rewrite strange. 
     rewrite Eq2. 
     rewrite -(H3 j). 
     rewrite /INV_visited_or_priority_Q /visited /priority_Q /= in PA.         
     rewrite /INV_uniq_priority_Q /visited /priority_Q /= in H0. 
     rewrite !/relax. 
     rewrite !row_elim. 
     have uNin: u ∈ tl = false. 
        move/andP : H0 => H0. case: H0. move=> H0 _. by move/negPf : H0 => H0.  
     rewrite uNin.
     have jIn : j ∈ (u :: tl). 
        case/orP: (PA j). 
           move => F. move/negPf : jLoc => jLoc.  rewrite jLoc in F. discriminate F. 
           by move=> F. 
     rewrite in_cons in jIn. 
     case/orP : jIn => jIn. 
        rewrite (eqP jIn). rewrite uNin.
        by rewrite (eqP (right_absorption _ _)). 
        by rewrite jIn. 
Qed. 

Lemma main : ∀i : ⟦n ⟧, ∀n : nat, AUG_estimate i (iter n dijkstra_step (initial_state i)). 
Proof. 
move=> i. 
apply iteration_invariant. 
  apply AUG_estimate_init. 
  apply AUG_estimate_holds. 
Qed.


(* these must be easy .... sob sob sob, weep weep weep ...  *) 
Hypothesis count_ord_enum_minus_one : ∀ k : nat, ∀i : ⟦ k ⟧, 
   count (fun x : ⟦ k ⟧ => x != i) (ord_enum k) = k.-1. 

Hypothesis priority_Q_length : ∀i : ⟦n ⟧, ∀ k : nat, 
   size (priority_Q (iter k dijkstra_step (initial_state i))) = ((n.-1) - k)%nat. 

Hypothesis priority_Q_empty : 
   ∀i : ⟦n ⟧, priority_Q (iter n.-1 dijkstra_step (initial_state i)) = [::]. 


(* Build monoid structure to use with the one application of eq_big_perm.        *) 
(* Seems like a hack at this point --- should probably use canonical structures  *) 
(* to associate this info with T much earlier .... but how ???                   *) 
Definition monoid := @Monoid.Law T zero plus_op plus_associative 
                         zero_is_left_plus_id zero_is_right_plus_id. 
Definition comm_monoid := @Monoid.ComLaw T zero monoid plus_commutative. 


Lemma 𝕯_right_local_solution : 
        ∀ i j : ⟦ n ⟧, 𝕯 i j = 𝐈 i j ⊕ ⨁_(q < n) (𝕯 i q ◎ 𝐀 q j).  
Proof. 
rewrite /𝕯 /dijkstra_iteration => i j.
have from_main : AUG_estimate i (iter n.-1 dijkstra_step (initial_state i)). 
   by exact: main i n.-1.
rewrite /AUG_estimate in from_main. 
case: from_main. move=> H from_main. 
rewrite /INV_estimate in from_main. 
rewrite from_main.
have Eq: ⨁_(q ∈ visited (iter n.-1 dijkstra_step (initial_state i))) 
           ((estimate (iter n.-1 dijkstra_step (initial_state i))) 0 q ◎ 𝐀 q j) 
         =
          ⨁_(q ∈ index_enum (ordinal_finType n)) 
            ((estimate (iter n.-1 dijkstra_step (initial_state i))) 0 q ◎ 𝐀 q j). 
   apply (@eq_big_perm T zero comm_monoid).
   rewrite /AUG_visited_closer in H. 
   case: H. move=> [[[[PM _] _] _] _] _. (* at this point, only need first invariant *) 
   rewrite /INV_permutation in PM. 
   by rewrite priority_Q_empty /= in PM. 
by rewrite Eq.
Qed. 


(***************************************************************) 
(* Show that paths built by dijkstra interation actually are   *)
(* paths with correct end points.                              *) 
(***************************************************************) 

(* olast is like the ohead function of ssreflect ...  *) 
Definition olast (p : seq ⟦ n ⟧) := 
  match p with 
  | [::] => @None ⟦ n ⟧
  | x :: s => Some (last x s)
  end . 

(* OK, OK, I'm a lazy bumb ... *) 
Hypothesis ohead_rev : ∀ s, ohead (rev s) = olast s. 
Hypothesis olast_rev : ∀ s, olast (rev s) = ohead s. 
Hypothesis olast_some: ∀ j, ∀ s, olast s == Some j → s != [::]. 
Hypothesis olast_cons : ∀ j, ∀ s, s != [::] → olast (j :: s) = olast s. 

(* boolean predicate "𝓟 p i j" is true when p is a path from i to j *) 
Definition 𝓟 p i j := (ohead p == Some i) && (olast p == Some j). 

Definition INV_paths (i : ⟦ n ⟧) (s : state) := 
    ∀ j : ⟦ n ⟧, 𝓟 (rev (paths s 0 j)) i j. 

Lemma INV_paths_init : ∀ i : ⟦ n ⟧, INV_paths i (initial_state i). 
Proof. 
rewrite /INV_paths /initial_state /visited /= => i. 
move=> j. rewrite /𝓟. 
rewrite row_elim. 
have fact :  ((i == j) || (i != j)). by apply: orbN. 
case/orP: fact => F. 
   rewrite F /=. apply/andP. by split. 
   move/negbTE : F => F. rewrite F /=. apply/andP. by split.
Qed. 

Lemma INV_paths_holds : ∀ i : ⟦ n ⟧, is_invariant_of dijkstra_step (INV_paths i). 
Proof. 
move => i. 
rewrite /is_invariant_of. 
move => [[[vis pq] v] pathv]. 
case pq. 
   rewrite /INV_paths /dijkstra_step /paths /=.  by move => F.   
   rewrite /INV_paths /dijkstra_step /paths /estimate /= => u tl. 
   move => H j. 
   rewrite /adjust_paths row_elim. 
   case: ((j ∉ tl) || ((j ∈ tl) &&  (v 0 j ≦ v 0 u ◎ 𝐀 u j))). 
      by apply H. 
      have fact: ohead (rev (pathv 0 u)) == Some i /\ olast (rev (pathv 0 u)) == Some u. 
        rewrite /𝓟 in H. apply/andP. by apply H. 
      rewrite /𝓟.
      rewrite ohead_rev olast_rev in fact. 
      apply/andP. split.  
         rewrite ohead_rev. case: fact => F _. rewrite olast_cons. by []. by apply (olast_some F). 
         by rewrite olast_rev /=.
Qed. 


(***************************************************************) 
(* Show that paths built by dijkstra interation actually have  *)
(* the the expected weights.                                   *) 
(***************************************************************) 

(*   (right ) path weight function 𝔀 : 

𝔀 [x_1, x_2 ... x_n-1 x_n] := [(𝐀 x_1 x_2) ◎ (𝐀 x_2 x_3) ◎ ...  ] ◎ (𝐀 x_n-1 x_n)

defined using ssreflect functions 

foldl f a [x_1, x_2 ... x_n-1 x_n]  := f (f ... (f a x_1) ... x_n-1) x_n        
pairmap f [x_1, x_2 ... x_n-1 x_n]  := [:: f a x_1; f x_1 x_2; ...; f x_n-1 x_n]                
               
*) 

Definition 𝔀 p := 
   match p with 
   | [::] => one 
   | [:: x] => one 
   | h :: tl => foldl times_op one (pairmap 𝐀 h tl) 
   end. 

Definition INV_weight (i : ⟦ n ⟧) (s : state) := 
    ∀ j : ⟦ n ⟧, estimate s 0 j == 𝔀 (rev (paths s 0 j)).

Lemma INV_weight_init : ∀ i : ⟦ n ⟧, INV_weight i (initial_state i). 
Proof. 
rewrite /INV_weight /initial_state /estimate /= => i j. 
rewrite !row_elim /=. 
have fact : (i == j) || (i != j). by apply: orbN. 
case/orP: fact => F. 
   rewrite F (eqP F) /=. rewrite 𝐈_diag 𝐀_diag. by rewrite zero_is_right_plus_id. 
   rewrite (𝐈_off_diag F). move/negbTE : F => F. rewrite F /=. 
   by rewrite one_is_left_times_id zero_is_left_plus_id. 
Qed. 

(* UGLY (but true) HACK --- Fix this!  *) 
Hypothesis weight_rev_hack : ∀ u j : ⟦ n ⟧, ∀ pathv : ℙ(n), 
   𝔀 (rev (pathv 0 u)) ◎ 𝐀 u j == 𝔀 (rcons (rev (pathv 0 u)) j). 

Lemma INV_weight_holds : ∀ i : ⟦ n ⟧, is_invariant_of dijkstra_step (INV_weight i). 
Proof. 
move => i. 
rewrite /is_invariant_of. 
move => [[[vis pq] v] pathv]. 
case pq. 
   rewrite /INV_weight /dijkstra_step /paths /=.  
   by move => F.   

   rewrite /INV_weight /dijkstra_step /paths /estimate /= => u tl H j.    
   rewrite /adjust_paths row_elim. 
   have fact: ((j ∉ tl) || ((j ∈ tl) &&  (v 0 j ≦ v 0 u ◎ 𝐀 u j)))
              || 
              ~~((j ∉ tl) || ((j ∈ tl) && (v 0 j ≦ v 0 u ◎ 𝐀 u j))). by apply: orbN. 
   case/orP : fact => fact. 
      rewrite fact. case/orP : fact => fact. 
         rewrite /relax. rewrite row_elim. rewrite (negbTE fact). 
         by apply H. 

         rewrite /relax. rewrite row_elim. 
         move/andP : fact => [fact1 fact2]. rewrite fact1.
         rewrite /lno in fact2. rewrite (eqP fact2). 
         by apply H. 
         
      rewrite negb_or in fact. move/andP : fact => [fact1 fact2]. 
      rewrite /relax. rewrite row_elim. 
      move/negPn : fact1 => fact1. rewrite fact1 /=.
      rewrite negb_and in fact2. case/orP : fact2. 
         move => jNin. rewrite fact1 /= in jNin. discriminate jNin. 
         move => F. move/negbTE : F => F. rewrite F. 

      rewrite /lno in F. 
      have sel : (v 0 j ⊕ v 0 u ◎ 𝐀 u j == v 0 j)
       || (v 0 j ⊕ v 0 u ◎ 𝐀 u j == v 0 u ◎ 𝐀 u j). 
         by apply (plus_selective (v 0 j) (v 0 u ◎ 𝐀 u j)).
      have fact : v 0 j ⊕ v 0 u ◎ 𝐀 u j == v 0 u ◎ 𝐀 u j. 
         case/orP: sel => Q.  rewrite Q in F. discriminate F. 
         by rewrite Q. 

     rewrite (eqP fact). rewrite (eqP (H u)).
     rewrite rev_cons.
     by apply weight_rev_hack. (* ugh! too tired to fix now .... *)       
Qed. 

(***************************************************************) 
(* TODO : show that with distributivity, we have the classical *) 
(* results for Dijkstra as another invariant.                  *) 
(***************************************************************) 

Variable leff_distributive     : ∀ a b c : T, a ◎ (b ⊕ c) == (a ◎ b) ⊕ (a ◎ c).
Variable right_distributive    : ∀ a b c : T, (b ⊕ c) ◎ a == (b ◎ a) ⊕ (c ◎ a).

Definition INV_best_path (i : ⟦ n ⟧) (s : state) := 
   ∀ j : ⟦ n ⟧, (j ∈ visited s) → 
       ∀ p : seq ⟦ n ⟧, (𝓟 p i j) → (estimate s 0 j) ≦ 𝔀 p. 

(* to be continued ... *) 

End Dijkstra. 
