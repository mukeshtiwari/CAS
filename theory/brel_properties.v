Require Import CAS.code.basic_types. 


Close Scope nat. 

(* 
****************************************************************

(S, =) 

T = {s in S | P(s) } 

P(s) == r(s) = s

*****************************************************************




   This file constains properties for boolean relations, 

       Definition brel (S : Type) := S → S → bool.  

   Functions of this type are used in two ways: 
   (1) implementing equivalence relations, 
   (2) implementing quasi-, partial-, and total-orders. 

   Several remarks are are in needed to clarify the implementation 
   of equivalence relations. 

   ===============================================================
                          Remark 1 
   ===============================================================
   Given an S: Type, and an equivalence relation eq : brel S, 
   we make much use of an assumption that simplifies many proofs: 

   ASSUMPTION: The relation is not trivial. 

   Simply put, this means that there exists s, t : S, such that eq s t = false. 
   However, a definition such as 

       Definition brel_non_trivial (S : Type) (eq : brel S) 
       := {s : S & {t : S & eq s t = false}}. 

   is not enough. It turns out we need something like 

       { s1 : S & {s2 : S & ∀ (i : S), eq s1 s2 = false }}

   or better yet (from a clean extraction point of view) something like 
        
      negate : { f : S -> S & ∀ (i : S), eq i (f i) = false }. 

   With this second form we will also need 

      witness : exists s, s = s

   to enure that S is not trivial.  

   The "negate" is needed in our development since 

        bop_not_exists_id S eq (bop_left S).

   expands to 

        ∀ i : S, {s : S & (eq i s = false) + (r s s = false)}

   and 

        bop_not_exists_id S r (bop_right S).

   expands to 

        ∀ i : S, {s : S & (r s s = false) + (r i s = false)}

   ===============================================================
                          Remark 2 
   ===============================================================
   
   Some of our constructions (such minimal sets, anti-chains) use 
   carrier sets of the form 
  
         T = { s : S & eq s (r s) = true} 

   for some function r, where r will be called a reduction. 
   The problem here is that we want our code to be extracted
   into a standard programmng language (such as Ocaml) where 
   T will be captured in a datatype. Since Ocaml does not have
   subtypes, in general, we are stuck. 

   Let's consider two approaches to building equivalence relations 
   over such sets, the classical way and a "datatype friendly" way
   (used in this coq implementation). 


   I) Building a new equivalence relation the classical way. 

      (S, =) is an equivalence relation and r : S -> S. 
      Define S_r = {s in S | r(s) = s }. 
      Now, (S_r, =) is an equivalence relation. Think of r as 
      selecting the representative of a class. 

   II) Building a new equivalence in a "datatype friendly" way. 

       Suppose that each S can be represented as a datatype. 
       In addition, suppose that we have represented an 
       equivalence relation as a triple 

            E = (S, =, r) 

       where 
              = is and equivalence relation over S. 

              r : S -> S 

       is a function that selects a representative element of a class. 
       E is meant to represent (S_r, =) in the following way. 
       The equaliy is now 
 
           a =_r b iff r(a) = r(b) 

       Is this an equivalence relation? We only need to know that r 
       is congruent w.r.t =. 

         reflexivity  : a =_r a, since r(a) = r(a)          
         symmetry     : if a =_r b, then r(a) = r(b), so r(b) = r(a), and b =_r a. 
         transitivity : if a =_r b and b =_r c. 
                        then r(a) = r(b) and r(b) = r(c), 
                        to r(a) = r(c), that is a =_r c. 

       Now, suppose we have a binary operation + over S to be considered 
       as a binary operator over S_r.  We need concruence, 

             a =_r b and c =_r d -> a + c =_r b + d, 

       or 

             r(a) = r(b) and r(c) = r(d) -> r(a) + r(c) = r(b) + r(d). 

       So it is enough to have congruence of r w.r.t. = and conguence of + w.r.t. =. 

       The actual operation is now 

               a +_r b == r(a + b) 

       commutative : a +_r b = b +_r c 

                r(a + b) = r(b + a)                 (so a+b = b+a -> a +_r b = b +_r c) 

       not_commutative : exists a b, a +_r b <> b +_r c 

                  exists a b, r(a + b) <> r(b + c)  (Yikes! this implies a+b<>b+a) 



       THINK of MINSET-UNION 







       Suppose + is commutative wrt =:  a + b = b + a. Then clearly it is 
       wrt =_r, since r is congruent. However, if 
       not(a + b = b + a), it could still be that r(a + b) = r(b + a). 

       


       

      
   III) Building a new equivalence in a "datatype friendly" way. 

       Suppose that each S can be represented as a datatype. 
       In addition, suppose that we have represented an 
       equivalence relation as a triple 

             (S, =, rep) 

       where 
              = is and equivalence relation over S. 

              rep : S -> S 

       is a function that selects a representative element of a class
       and we know 

            brel_rep_correct : forall s : S, rep(s) = s.  

       Now, given r we build a new triple over the same datatype  
 
               (S, =_r, r o rep) 

      where a =_r b holds iff r(a) = r(b) holds. We need to maintain 

            brel_rep_correct : forall s : S, r(rep(s)) =_r s.  

      That is, 

            forall s : S, r(r(rep(s))) = r(s).  

      Thus we need to know that r is idempotent, 

            brel_rep_idempotent : for all s : S, r(r(s)) = r(s).  

      It is easy to check that (S, =_r, r o rep) is an eqivalence relation:  

      reflexivity : since r(a) = r(a) we have a =_r a. 
      symmetry    : since r(a) = r(b) imples r(b) = r(a), 
                    we have a =_r b implies b =_r a. 
      transitivity : if a =_r b and b =_r c. 
                     then r(a) = r(b) and r(b) = r(c), 
                     to r(a) = r(c), that is a =_r c. 

      However, by Remark 1 we need to know if the new relation is non-trivial. 
      
      suppose that for (S, =, rep) we know 

         witness : exists s, s = s 
         negate  : exists f, all s, not(s = f(s))


      For (S, =_r, r o rep) we need  

         witness : exists s, r(s) = r(s) 
         negate  : exists g, all s, not(r(s) = r(g(s)))

      The witness constraint is easily maintained with the witness for (S, =, rep). 
      However, the negate constraint leads to some difficulties.   Since there seems 
      to be no general way to find such a g, this function must be selected on 
      a case-by-case basis.  For example, for a minset X we want 
   
               min(g(X)) <> min(X), 

     so we could define  

               g(X) = if empty (X) then {witness) else {} 

     without every knowing what the function f was. 

     Examples. 

     (nat, eq_nat, uop_id) 

     Current finite set : From (S, =, rep) we build 
     (list S, eq_set, duplicate_elim o rep) 
     whrere X eq_set Y iff X subset Y and Y subset X and 
     X subset Y if forall x in X, x in Y. 
     Here x in Y means exists y in Y, x = y. 

   ===============================================================
                          Remark 3 
   ===============================================================

    Of course this "datatype friendly" equivalence relation will 
    interact with all properties involving equality. These may induce 
    additional constraints on representation functions. 

    We have (S, =, rep). 

    Congruence: Suppose we have a binary operator + over S.   

     We want a = b and c = d -> a + c = b + d. 


     a = b -> r a = r b. 

    want : 
       1) r(a) = r(r(a))            (implied by 2 or 3 if exists id) 
       2) r(a . b) = r(r(a) . b)    
       3) r(a . b) = r(a . r(b))    (implied by 2 if . commutative) 
       4) r(a . b) = r(r(a) . r(b)) (implied by 2 and 3) 

    Define S_r = {a in S | r(a) = a} 
    Define ._r as 
        a ._r b == r(a . b) 

    congruence : for all a, b, c, d in S_r, a = b and c =d -> a ._r c = b ._r d. 
    Proof. a = r(a) 
           b = r(b) 
           c = r(c) 
           d = r(d) 
           H1 : a = b 
           H2 : c = d. 

           a ._r c = b ._r d === r(a . c) = r (b . d), then use cong of r and . 
    Qed. 

    associativity. 
    Proof. 
       a ._r (b ._r c) 
     = r(a . r(b . c)) 
     = r(a . (b . c))   (by 3) 
     = r((a . b) . c)   
     = r(r(a . b) . c)  (by 2) 
     = (a ._r b) ._r c) 
    Qed. 
   

   II) We have A = (S, =, rep, .) 

        = is equiv relation 

        a = rep(a), where rep is a representation function 
 
     Build a new structure 

      B = (S, =_r, r o rep, .) 

      where a =_r b  == r(a) = r(b). 

      we want 

      a  =_r  r(rep(a)) <--> r(a) = r(r(rep(a))) 

      but by (1: r(a) = r(r(a))) this reduces to 

      r(a) = r(rep(a)), which we should get from cong of r and a = rep(a). 

      associativity? 

      a . (b .c) =_r (a . b) .c  === r(a . (b .c)) = r((a . b) .c)
      but assoc(.) and cong r imply this holds. 

    congruence : for all a, b, c, d in S, a =_r b and c =_r d -> a . c =_r b . d. 
    Proof. H1 : r(a) = r(b) 
           H2 : r(c) = r(d). 

                r(a) . r(c) = r(c) . r(d)         (by cong of .) 
            --> r(r(a) . r(c)) = r(r(c) . r(d))   (by cong of r)
           ---> r(a . c) = r(c . d)               (by 4) 
           <--> a . c =_r c . d 
   [] 

*) 



Definition brel_witness (S : Type) (r : brel S) 
    := {s : S & r s s = true}. 

Definition brel_negate (S : Type) (r : brel S) 
    := {f : S -> S & ∀ s : S, (r s (f s) = false) * (r (f s) s = false) }. 

Record brel_nontrivial (S : Type) (r : brel S) := {
  brel_nontrivial_witness   : brel_witness S r 
; brel_nontrivial_negate    : brel_negate S r 
}.  

Definition brel_congruence (S : Type) (eq : brel S) (r : brel S) := 
   ∀ s t u v : S, eq s u = true → eq t v = true → r s t = r u v. 


Definition brel_reflexive (S : Type) (r : brel S) := 
    ∀ s : S, r s s = true. 

Definition brel_not_reflexive (S : Type) (r : brel S) := 
    {s : S &  r s s = false}. 

Definition brel_reflexive_decidable (S : Type) (r : brel S) := 
    (brel_reflexive S r) + (brel_not_reflexive S r). 

Lemma brel_reflexive_covered : forall (S : Type) (r : brel S), 
    ((brel_reflexive S r) * (brel_not_reflexive S r)) -> False. 
Proof. intros S r [refS [s P]].  rewrite (refS s) in P. discriminate. Defined. 


Definition brel_transitive (S : Type) (r : brel S) := 
    ∀ s t u: S, (r s t = true) → (r t u = true) → (r s u = true). 

(* aka intransitive *) 
Definition brel_not_transitive (S : Type) (r : brel S) 
(*    {s : S & {t : S & {u: S & (r s t = true) * (r t u = true) * (r s u = false)}}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r s t = true) * (r t u = true) * (r s u = false)  end}. 

Definition brel_transitive_decidable (S : Type) (r : brel S) := 
   (brel_transitive S r) + (brel_not_transitive S r). 

Definition brel_symmetric (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = true) → (r t s = true). 

Definition brel_not_symmetric (S : Type) (r : brel S) 
(*    {s : S & {t : S & (r s t = true) * (r t s = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = false) end}. 

Definition brel_symmetric_decidable (S : Type) (r : brel S) := 
   (brel_symmetric S r) + (brel_not_symmetric S r).


Definition brel_rep_correct (S : Type) (eq : brel S) (r : unary_op S) := 
   ∀ s : S, eq s (r s) = true. 

Definition brel_rep_idempotent (S : Type) (eq : brel S) (r : unary_op S) := 
   ∀ s : S, eq (r (r s)) (r s) = true. 




Require Import CAS.code.uop. 

Lemma identity_rep_correct : ∀ (S : Type) (eq : brel S), 
             brel_reflexive S eq -> brel_rep_correct S eq (uop_id S). 
Proof. intros S eq refS s. compute. apply refS. Qed. 

Lemma identity_rep_idempotent : ∀ (S : Type) (eq : brel S), 
             brel_reflexive S eq -> brel_rep_idempotent S eq (uop_id S). 
Proof. intros S eq refS s. compute. apply refS. Qed. 





(*  Needed? 

Definition prefix_injective (S : Type) (n : nat) (f : nat -> S) (r : brel S), 
    := ∀ s t : nat, s <= n -> t <= n -> r (f s) (f t) = true -> s = t. 

Definition brel_finite (S : Type) (r : brel S) 
    := { n : nat & {f : nat -> S & ∀ s : S { m : nat & (m <= n) * (r (f m) s = true)}}}

Definition brel_not_finite (S : Type) (r : brel S) 
    := ∀ n : nat, ∀ f : nat -> S, {s : S &  ∀ m : nat , (m <= n)  -> (r (f m) s = false} ) }}

*) 


Definition brel_strict (S : Type) (r : brel S) (lt : brel S) := 
   ∀ s t : S, lt s t = true → r s t = false. 

Definition brel_not_strict (S : Type) (r : brel S) (lt : brel S) 
(*    {s : S & { t : S & (lt s t = true) * (r s t = true)}}. *) 
   := { z : S * S & match z with (s, t) => (lt s t = true) * (r s t = true) end}. 

Definition brel_strict_decidable (S : Type) (r : brel S) (lt : brel S) := 
   (brel_strict S r lt) + (brel_not_strict S r lt). 

Lemma brel_strict_covered : forall (S : Type) (r : brel S) (lt : brel S),  
   ((brel_strict S r lt) * (brel_not_strict S r lt)) -> False.  
Proof. intros S r lt [str [[s t] [L R]]]. rewrite (str s t L) in R. discriminate. Defined. 

(* 
    asymmetric iff  anti-symmetric  and irreflexive
               iff brel_strict S r r 
*) 
Definition brel_asymmetric (S : Type) (r : brel S) := 
   ∀ s t : S, r s t = true → r t s = false. 

Definition brel_not_asymmetric (S : Type) (r : brel S) 
(*   {s : S & {t : S & (r s t = true) * (r t s = true)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = true) end}. 


Definition brel_asymmetric_decidable (S : Type) (r : brel S) := 
   (brel_asymmetric S r) + (brel_not_asymmetric S r). 



Definition brel_total (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = true) + (r t s = true). 

Definition brel_not_total (S : Type) (r : brel S) 
(*     {s : S & { t : S & (r s t = false) * (r t s = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = false) * (r t s = false) end}. 

Definition brel_total_decidable (S : Type) (r : brel S) := 
    (brel_total S r) + (brel_not_total S r).

Definition brel_irreflexive (S : Type) (r : brel S) := 
    ∀ s : S, r s s = false. 

Definition brel_not_irreflexive (S : Type) (r : brel S) := 
    {s : S & r s s = true}. 

Definition brel_irreflexive_decidable (S : Type) (r : brel S) := 
   (brel_irreflexive S r) + (brel_not_irreflexive S r). 


Definition brel_has_2_chain (S : Type) (r : brel S) 
  (*  {s : S & {t : S & {u : S & (r s t = true) * (r t u = true)}}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) =>  (r s t = true) * (r t u = true) end}. 

Definition brel_not_has_2_chain (S : Type) (r : brel S) := 
   ∀ s t u : S, r s t = true → r t u = false. 

Definition brel_has_2_chain_decidable (S : Type) (r : brel S) := 
   (brel_has_2_chain S r) + (brel_not_has_2_chain S r). 


Definition brel_bop_compatible_right (S : Type) (r : brel S) (b : binary_op S) := 
   ∀ (s u v : S), r s u = true -> r s v = true -> r s (b u v) = true.


(* r2 w.r.t r1*) 


Definition brel_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) := 
    ∀ s t : S, (r2 s t = true) → (r2 t s = true) → (r1 s t = true). 


Definition brel_not_antisymmetric (S : Type) (r1 : brel S) (r2 : brel S) 
(*   {s : S & {t : S & (r2 s t = true) * (r2 t s = true) * (r1 s t = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r2 s t = true) * (r2 t s = true) * (r1 s t = false) end}. 

Definition brel_antisymmetric_decidable (S : Type) (r1 : brel S) (r2 : brel S) := 
   (brel_antisymmetric S r1 r2) + (brel_not_antisymmetric S r1 r2). 


(* brel2 *) 


Definition brel2_left_congruence (S T : Type) (r1 : brel S) (r2 : brel2 S T) := 
    ∀ (t : T) (s1 s2 : S), r1 s1 s2 = true -> r2 s1 t = r2 s2 t. 
(*

Definition brel2_left_congruence (S T : Type) (r1 : brel S) (r2 : brel2 S T) := 
    ∀ (s1 s2 : S) (t : T), r1 s1 s2 = true -> r2 s1 t = true ->  r2 s2 t = true. 
*) 

Definition brel2_right_congruence (S T : Type) (r1 : brel T) (r2 : brel2 S T) := 
    ∀ (s : S) (t1 t2 : T), r1 t1 t2 = true -> r2 s t1 = true ->  r2 s t2 = true. 

Definition brel2_congruence (S T : Type) (rS : brel S) (rT : brel T) (r : brel2 S T) := 
    ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> r s1 t1 = r s2 t2. 


(* top and bottom 

  LEFT and RIGHT versions? 
*) 

Definition brel_is_bottom (S : Type) (lte : brel S) (b : S) 
    := ∀ s : S, (lte b s = true).

Definition brel_not_is_bottom (S : Type) (lte : brel S) (b : S)
    := {s : S & lte b s = false }.

Definition brel_exists_bottom (S : Type) (r : brel S)
    := {b : S & brel_is_bottom S r b}.

Definition brel_not_exists_bottom (S : Type) (r : brel S)
    := ∀ b : S, brel_not_is_bottom S r b.

Definition brel_exists_bottom_decidable  (S : Type) (r : brel S) := 
    (brel_exists_bottom S r) + (brel_not_exists_bottom S r). 

Definition brel_is_top (S : Type) (lte : brel S) (b : S) 
    := ∀ s : S, (lte s b = true).

Definition brel_not_is_top (S : Type) (lte : brel S) (b : S)
    := {s : S & lte s b = false }.

Definition brel_exists_top (S : Type) (r : brel S) 
    := {b : S & brel_is_top S r b}.

Definition brel_not_exists_top (S : Type) (r : brel S)
    := ∀ b : S, brel_not_is_top S r b.

Definition brel_exists_top_decidable  (S : Type) (r : brel S) := 
    (brel_exists_top S r) + (brel_not_exists_top S r). 

(* bProp 

   Move this to another file ... 
*) 

Definition bProp_congruence (S : Type) (eq : brel S) (P : bProp S) := 
   ∀ s t : S, eq s t = true → P s = P t. 
