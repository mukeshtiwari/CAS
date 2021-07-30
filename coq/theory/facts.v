(* this file is currently a random collection of facts .... *) 
Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List. 
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.os.properties. 

Open Scope list_scope. 

(* false elim? *) 
Lemma abort : ∀ S : Type,  False  → S. 
Proof. intros S F. destruct F. Qed.

Lemma cons_not_nil : ∀ (S : Type) (a : S) (X : list S), a :: X ≠ nil. 
Proof. intros S a X. discriminate. Defined. 

Lemma list_lemma1 :          
  ∀ (S : Type) (l : list S) (s : S), s :: l = (s :: nil) ++ l. 
Proof. intros S l s. rewrite <- (List.app_nil_l l) at 1. 
       rewrite List.app_comm_cons. reflexivity. 
Defined. 


Lemma bool_disj : ∀ b : bool, (b = true) + (b = false). 
Proof. induction b; auto. Defined. 

Definition equal_true (x : bool) : option (x = true) := 
    match bool_disj x with 
    | inl p => Some p 
    | inr _ => None 
    end . 
Lemma eqb_bool_to_prop  : ∀ s t: bool, eqb s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto.  Defined. 

Lemma beq_nat_to_prop  : ∀ s t: nat, beq_nat s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto; discriminate. Defined. 

Lemma orb_is_true_left : ∀ b1 b2 : bool, b1 || b2 = true → (b1 = true) + (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       left; reflexivity. 
       left. reflexivity. 
       right. reflexivity. 
       left. assumption. 
Defined. 

Lemma orb_is_true_right : ∀ b1 b2 : bool, (b1 = true) + (b2 = true) → b1 || b2 = true. 
Proof. induction b1; induction b2; simpl; intros [H | H]; auto. Defined. 

Lemma orb_is_false_left : ∀ b1 b2 : bool, b1 || b2 = false → (b1 = false) * (b2 = false). 
Proof. induction b1; induction b2; simpl; intros; split.   
       assumption. assumption. assumption. reflexivity. 
       reflexivity. assumption. reflexivity. reflexivity.
Defined. 

Lemma andb_is_true_left : ∀ b1 b2 : bool, b1 && b2 = true → (b1 = true) * (b2 = true). 
Proof. induction b1; induction b2; simpl; intros.  
       split; reflexivity. 
       split. reflexivity. assumption. 
       split. assumption. reflexivity. 
       split. assumption. assumption. 
Defined. 

Lemma andb_is_true_right : ∀ b1 b2 : bool, (b1 = true) * (b2 = true) → b1 && b2 = true. 
Proof. induction b1; induction b2; simpl. 
       intro. reflexivity. 
       intros [_ F]. assumption. 
       intros [F _]. assumption. 
       intros [F _]. assumption. 
Defined. 



Lemma andb_is_false_left : ∀ b1 b2 : bool, b1 && b2 = false → (b1 = false) + (b2 = false). 
Proof. induction b1; induction b2; simpl; intros.  
       discriminate. 
       right. reflexivity. 
       left. reflexivity. 
       right. reflexivity. 
Defined. 

Lemma andb_is_false_right : ∀ b1 b2 : bool, (b1 = false) + (b2 = false) → b1 && b2 = false. 
Proof. induction b1; induction b2; simpl. 
       intros [F | F]. assumption. assumption. 
       intros. reflexivity. 
       intros. reflexivity. 
       intros. reflexivity. 
Defined. 

(*  Note: we could use andb_true_iff here, but it is opaque and so does 
    not play well with evaluation/extraction
*) 
Lemma andb_true_implies : ∀ b1 b2 : bool, b1 && b2 = true →  (b1 = true)  ∧  (b2 = true). 
Proof. 
   induction b1; induction b2. 
   intro. split; reflexivity. 
   simpl. intro. discriminate. 
   simpl. intro. discriminate. 
   simpl. intro. discriminate. 
Defined. 




Lemma negb_true_elim : ∀ b: bool, negb b = true → b = false. 
Proof. induction b; simpl; intro H. rewrite H. reflexivity. reflexivity. Defined. 

Lemma negb_false_elim : ∀ b: bool, negb b = false → b = true. 
Proof. induction b; simpl; intro H. reflexivity. rewrite H. reflexivity. Defined. 

Lemma negb_true_intro : ∀ b: bool, b = false → negb b = true. 
Proof. induction b; simpl; intro H. rewrite H. reflexivity. reflexivity. Defined. 

Lemma negb_false_intro : ∀ b: bool, b = true → negb b = false. 
Proof. induction b; simpl; intro H. reflexivity. rewrite H. reflexivity. Defined. 


(* cas-specific facts *) 



Definition brel_symmetric_dual (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = false) → (r t s = false). 

Definition bop_commutative_dual (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ s t u : S, (r (b s t) u = false) → (r (b t s) u = false). 


Definition brel_transitive_dual (S : Type) (r : brel S) := 
   ∀ (s t u : S), r s t = true -> r s u = false -> r t u = false.   



(* brel_transititivity_contrasitive 

       (∀ s t u : S, r s t = true → r t u = true  → r s u = true)
      → ∀ s t u : S, r s t = true → r s u = false → r t u = false
*) 

Lemma brel_transititivity_implies_dual : ∀ (S: Type) (r : brel S), 
      brel_transitive S r -> brel_transitive_dual S r. 
Proof. 
      unfold brel_transitive, brel_transitive_dual.
      intros S r Tr s t u H K. 
      case_eq (r t u); intro F.
         rewrite (Tr s t u H F) in K. assumption. 
         reflexivity. 
Defined. 

Lemma bop_commutative_implies_dual : ∀ (S: Type) (r : brel S) (b : binary_op S), 
      brel_transitive S r -> 
      bop_commutative S r b -> bop_commutative_dual S r b. 
Proof. intros S r b transS commS s t u H. 
       assert (C := commS s t). 
       assert (D := brel_transititivity_implies_dual S r transS). 
       unfold brel_transitive_dual in D. 
       apply (D (b s t) (b t s) u C H).     
Defined. 


Lemma brel_symmetric_implies_dual : ∀ (S: Type) (r : brel S), 
      brel_symmetric S r -> brel_symmetric_dual S r. 
Proof. unfold brel_symmetric, brel_symmetric_dual.
       intros S r symS s t H. 
       case_eq (r t s); intro F.
          rewrite (symS t s F) in H. assumption. 
          reflexivity. 
Defined. 

Lemma brel_transitive_dual_v2 (S : Type) (eq : brel S) (sym : brel_symmetric S eq) (trans : brel_transitive S eq) : 
  ∀ s t u: S, (eq s t = false) → (eq t u = true) → (eq s u = false).
Proof. intros s t u H1 H2.
       exact (brel_symmetric_implies_dual S eq sym _ _
                  (brel_transititivity_implies_dual S eq trans t u s H2
                          (brel_symmetric_implies_dual S eq sym _ _ H1))). 
Qed.        



Lemma brel_transitive_dual_v3 (S : Type) (eq : brel S) (sym : brel_symmetric S eq) (trans : brel_transitive S eq)  : 
  ∀ s t u: S, (eq s t = true) → (eq t u = false) → (eq s u = false).
Proof. intros s t u H1 H2.
       exact (brel_transititivity_implies_dual S eq trans t s u (sym _ _ H1) H2). 
Qed.        



(* NB : this is HOW symmetric should be DEFINED ! *) 
Lemma brel_sym_lemma : ∀ (S : Type) (r : brel S) (s u : S), 
      brel_symmetric S r → r s u = r u s. 
Proof. intros S r s u symS. 
       case_eq(r s u); intro K. apply symS in K. rewrite K. reflexivity. 
       apply (brel_symmetric_implies_dual _ _ symS) in K. rewrite K. reflexivity. 
Defined.        



Definition brel_transitive_twist (S : Type) (r : brel S) := 
    (∀ a b c : S, r a b = true → r a c = true → r b c = true). 

Lemma negb_bProp_congruence :
  ∀ (S : Type) (eq r : brel S), 
    brel_reflexive S eq -> 
    brel_congruence S eq r -> 
      ∀ (a : S), bProp_congruence S eq (λ y : S, negb (r y a)). 
Proof. intros S eq r refS cong a. unfold bProp_congruence. 
       intros s t E. assert (A := cong _ _ _ _ E (refS a)). 
       rewrite A. reflexivity. 
Defined. 


Lemma brel_congruence_self : ∀ (S : Type) (r : brel S),  
      brel_symmetric S r →
      brel_transitive S r →
         brel_congruence S r r.  
Proof. intros S r symS transS s u t w H Q. 
       case_eq(r s u); intro K. 
          assert (J: r s w = true). apply (transS _ _ _ K Q). 
          assert (M: r t w = true). apply symS in H. 
             apply (transS _ _ _ H J). rewrite M. reflexivity. 
       assert (J := brel_transititivity_implies_dual _ _ transS _ _ _ H K).       
       apply (brel_symmetric_implies_dual _ _ symS) in J.        
       assert (M := brel_transititivity_implies_dual _ _ transS _ _ _ Q J).       
       apply (brel_symmetric_implies_dual _ _ symS) in M. rewrite M. reflexivity. 
Defined.        



(*
u(s + t) = u (t + s)
         = u ((u t) + s)
         = u (s + (u t))
*) 
Lemma bop_commutative_left_implies_right_invariant : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S),
     brel_symmetric S r →
     brel_transitive S r →
     bop_commutative S r b →
     uop_congruence S r u →
     uop_bop_left_invariant S r u b →
        uop_bop_right_invariant S r u b.  
Proof. intros S r u b symS transS comm_b cong_u. 
       unfold uop_bop_left_invariant, uop_bop_right_invariant. 
       intros H s t. 
       assert (A := comm_b s t). 
       assert (B := comm_b s (u t)). 
       assert (Au := cong_u _ _ A). 
       assert (Bu := cong_u _ _ B). apply symS in Bu. 
       assert (Hu := H t s). 
       assert (T1 := transS _ _ _ Au Hu). 
       assert (T2 := transS _ _ _ T1 Bu). assumption. 
Defined. 


(* 
u((u s) + (u t)) = u((u s) + t) = u(s + t)    
*) 
Lemma uop_bop_invariant_left_intro : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S),
     brel_symmetric S r →
     brel_transitive S r →
     bop_commutative S r b →
     uop_congruence S r u →
     uop_bop_left_invariant S r u b → uop_bop_invariant S r u b.  
Proof. intros S r u b symS transS comm_b cong_u. unfold uop_bop_left_invariant, uop_bop_invariant. 
       intros I_l s t. 
       assert (I_r := bop_commutative_left_implies_right_invariant S r u b symS transS comm_b cong_u I_l).      
       unfold uop_bop_left_invariant in I_r. unfold uop_bop_right_invariant in I_r. 
       assert(A := I_l s t). 
       assert(B := I_r (u s) t). 
       assert(T := transS _ _ _ A B). assumption. 
Defined. 


Lemma idempotent_uop_uop_congruence : ∀ (S : Type) (r : brel S)  (u : unary_op S), 
      brel_symmetric S r →
      brel_transitive S r →
      uop_idempotent S r u → 
          uop_uop_congruence S r u u. 
Proof. intros S r u symS transS idem. unfold uop_uop_congruence. intros s t H. 
       assert (A := idem s). assert (B := idem t). 
       assert (C := brel_congruence_self S r symS transS _ _ _ _ A B). rewrite H in C. assumption. 
Defined. 


Open Scope nat_scope. 
(* 
plus_Snm_nSm: ∀ n m : nat, S n + m = n + S m
plus_Sn_m: ∀ n m : nat, S n + m = S (n + m)
*) 
Lemma plus_SS : ∀ s t : nat, S s + S t = S(S(s + t)). 
Proof. intros s t. rewrite plus_Snm_nSm. 
       rewrite plus_comm at 1. 
       rewrite plus_Sn_m. 
       rewrite plus_Sn_m. 
       rewrite plus_comm at 1. 
       reflexivity. 
Defined. 

Lemma injection_S : ∀ s t : nat, s = t -> S s = S t. 
Proof. intros s t H. rewrite H. reflexivity. Defined. 

Lemma injective_S : ∀ s t : nat, S s = S t -> s = t. 
Proof. intros s t H. injection H. auto. Defined. 

Close Scope nat_scope. 


Lemma bop_left_distributive_implies_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
           bop_left_distributive S r b1 b2 -> bop_right_distributive S r b1 b2. 
Proof. intros S r b1 b2 transS cong1 c1 c2 ld s t u.
       assert (fact1 := ld s t u).        
       assert (fact2 := c2 s u). 
       assert (fact3 := c2 s t). 
       assert (fact4 := c2 (b1 t u) s). 
       assert (fact5 := transS _ _ _ fact4 fact1). 
       assert (fact6 : r (b1 (b2 s t) (b2 s u)) (b1 (b2 t s) (b2 u s)) = true). 
          apply (cong1 _ _ _ _ fact3 fact2). 
       assert (fact7 := transS _ _ _ fact5 fact6). 
       assumption. 
Defined. 


Lemma bop_not_left_distributive_implies_not_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
           bop_not_left_distributive S r b1 b2 -> bop_not_right_distributive S r b1 b2. 
Proof. intros S r b1 b2 transS cong1 c1 c2 [[a [b c]] NLD].
       exists (a, (b, c)). 
       case_eq(r (b2 (b1 b c) a) (b1 (b2 b a) (b2 c a))); intro H; auto. 
       assert (fact1 := c2 a (b1 b c)).
       assert (fact2 := transS _ _ _ fact1 H).        
       assert (fact3 := c2 b a).
       assert (fact4 := c2 c a).
       assert (fact5 := cong1 _ _ _ _ fact3 fact4).
       assert (fact6 := transS _ _ _ fact2 fact5).               
       rewrite fact6 in NLD. 
       discriminate NLD. 
Defined. 


Lemma bop_left_distributive_decidable_implies_right_decidable : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
        bop_left_distributive_decidable S r b1 b2 -> bop_right_distributive_decidable S r b1 b2.
Proof. intros S r b1 b2 transS cong1 c1 c2 [LD | NLD].
       left. apply bop_left_distributive_implies_right; auto. 
       right. apply bop_not_left_distributive_implies_not_right; auto. 
Defined.


(* Id, Ann are unique *) 

Lemma bop_id_unique : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (p : bop_exists_id S r b)        
                        (q : bop_exists_id S r b), r (projT1 p) (projT1 q) = true.             
Proof. intros S r symS trnS b [s1 P] [s2 Q]. simpl.  
       destruct (Q s1) as [_ R1]. destruct (P s2) as [L2 _]. 
       apply symS in R1. apply (trnS _ _ _ R1 L2). 
Defined.                         

Lemma bop_is_id_equal : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (x : S )
                        (y : S )
                        (p : bop_is_id S r b x)        
                        (q : bop_is_id S r b y), r x y = true.             
Proof. intros S r symS trnS b x y p q. 
       destruct (q x) as [_ R1]. destruct (p y) as [L2 _]. 
       apply symS in R1. apply (trnS _ _ _ R1 L2). 
Defined.                         


Lemma bop_ann_unique : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (p : bop_exists_ann S r b)        
                        (q : bop_exists_ann S r b), r (projT1 p) (projT1 q) = true.             
Proof. intros S r symS trnS b [s1 P] [s2 Q]. simpl.  
       destruct (Q s1) as [_ R1]. destruct (P s2) as [L2 _]. 
       apply symS in L2. apply (trnS _ _ _ L2 R1). 
Defined.                         

Lemma bop_is_ann_equal : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (x : S )
                        (y : S )
                        (p : bop_is_ann S r b x)        
                        (q : bop_is_ann S r b y), r x y = true.             
Proof. intros S r symS trnS b x y p q.  
       destruct (q x) as [_ R1]. destruct (p y) as [L2 _]. 
       apply symS in L2. apply (trnS _ _ _ L2 R1). 
Defined.


Lemma bop_not_is_id_intro (S : Type) (r : brel S) (id s : S) (bS : binary_op S)
                          (symS : brel_symmetric S r) (trnS : brel_transitive S r) : bop_is_id S r bS id -> r id s = false -> bop_not_is_id S r bS s.
Proof. intros ID F. exists id. destruct (ID s) as [L R]. 
       left. case_eq(r (bS s id) id); intro J; auto. apply symS in J.
       assert (K := trnS _ _ _ J R). rewrite K in F. exact F. 
Defined.

Lemma bop_not_is_ann_intro (S : Type) (r : brel S) (a s : S) (bS : binary_op S)
                          (symS : brel_symmetric S r) (trnS : brel_transitive S r) : bop_is_ann S r bS a -> r a s = false -> bop_not_is_ann S r bS s.
Proof. intros ID F. exists a. destruct (ID s) as [L R]. 
       left. case_eq(r (bS s a) s); intro J; auto. apply symS in R.
       assert (K := trnS _ _ _ R J). rewrite K in F. exact F. 
Defined.


Lemma sym_as_rewrite : ∀ {S : Type} {rS : brel S}, brel_symmetric S rS -> ∀ s1 s2 : S,  rS s1 s2 = rS s2 s1.
Proof. intros S rS symS s1 s2.
       case_eq(rS s1 s2); intro H1; case_eq(rS s2 s1); intro H2.
       reflexivity.
       rewrite (symS _ _ H1) in H2. discriminate.
       rewrite (symS _ _ H2) in H1. discriminate.
       reflexivity.
Qed.        

(*

          P                   
    ∀ x, P(x) = true     


       not_P                   not_anti_P 
    {x & P(x) = false }    {x & P(x) = true } 

                                anti_P                
                           ∀ x, P(x) = false    


Definition bop_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = true. 

Definition bop_not_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := { z : S * S & match z with (s, t) =>  r (b s t) s = false end }. 

Definition bop_anti_left (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b s t) = false. 

Definition bop_not_anti_left (S : Type) (r : brel S) (b : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b s t) = true end }. 


LC(s, t, u) = r (b s t) (b s u) = true. 

Definition bop_left_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true. 

Definition bop_not_left_constant (S : Type) (r : brel S) (b : binary_op S)
   := { z : S * (S * S) & match z with (s, (t, u)) => r (b s t) (b s u) = false  end }. 



LK(s, t, u) == LC(s, t, u) -> r t u = true.

Definition bop_left_cancellative (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true -> r t u = true.

Definition bop_not_left_cancellative (S : Type) (r : brel S) (b : binary_op S)
   := { z : S * (S * S) & match z with (s, (t, u)) => (r (b s t) (b s u) = true) * (r t u = false) end }. 


*) 

(* =====================  IMPLICATIONS ===================== 


[


 1) No-id No-ann 
    1.1) Comm 
         1.1.1) Idempotent 
                1.1.1.1) Selective        [MAX] 
                1.1.1.2) not Selective 
         1.1.2) not Idempotent 
    1.2) not-Comm                         [LEFT, RIGHT]
 2) No-id ann 
    2.1) Comm 
         2.1.1) Idempotent 
                2.1.1.1) Selective         [MIN] 
                2.1.1.2) not Selective 
         2.1.2) not Idempotent 
    2.2) not-Comm 
 3) id No-ann 
    3.1) Comm 
         3.1.1) Idempotent 
                3.1.1.1) Selective 
                3.1.1.2) not Selective 
         3.1.2) not Idempotent            [PLUS] 
    3.2) not-Comm                         [CONCAT] 
 4) id ann
    4.1) Comm 
         4.1.1) Idempotent 
                4.1.1.1) Selective        [AND, OR] 
                4.1.1.2) not Selective    [UNION+ANN, INTERSECT+ID]
         4.1.2) not Idempotent            [TIMES] 
    4.2) not-Comm 


 1) Comm
    1.1) Idempotent 
    1.2) not-Idempotent
 2) not-Comm 
    2.1) Idempotent 
    2.2) not-Idempotent



Summary of implications 
                   NOT 
C = Commutative    c
I = Idempotent     i
S = Selective      s
N = id             n   (left/right?)
A = Ann            a   (left/right?)
K = cancellative   k   (left/right)
L = is left        l 
R = is right       r
Q = constant       q   (left/right)
Y = anti left      y 
Z = anti right     z


I  ->         y z 
S  -> I 
i  -> s 
K  -> a
K(id || not_id)  -> i 
lK -> lq
rK -> rq
C  ->   l r
N  ->   l r q y z 
A  -> k l r   y z

N A  -> k l r q y z 


CI         ->   l r q y z 
CIs        -> k l r q y z 
CI(S || s) -> k l r q y z 
CS         -> k l r q y z 

C(I || i)(S || s) -> 
   1) _ S -> k l r q y z 
   2) I s -> k l r q y z 
   3) i _ -> ? l r ? ? ? 
SW
Ci  -> ? l r ? ? ? 

b_k(a,b) = k 
   b_k : CikQyz
plus   : CiNK 


and    : CSNA
or     : CSNA 
min    : CSnA   
max    : CSNa 
union+ : CINA 
inter+ : CINA 

times  : CiNA
plus   : CiNK 
concat : cNK  
left   : L 
right  : R 

L  -> Scna(lk)(RK)r(LQ)(rQ)yz 
R  -> Scna(LK)(rk)l(lq)(RQ)yz 

CI x CI = CI 
CI x CS = CI 
CS x CI = CI 
CS x CS = CI 

CSNA CINA CSnA CSNa    

CINA x CINA = CINA 
CSNA x CSNA = CINA 
CINA x CSNA = CINA 
CSNA x CINA = CINA 

*) 


(* I *) 

Lemma bop_idempotent_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) , 
       brel_symmetric S r -> 
       bop_idempotent S r b -> 
       bop_not_anti_left S r b. 
Proof. intros S r b s symS idemS. 
       unfold bop_not_anti_left. 
       exists (cef_idempotent_implies_not_anti_left s); simpl. 
       assert (fact := idemS s). apply symS in fact. assumption. 
Defined. 

Lemma bop_idempotent_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S), 
       brel_symmetric S r -> 
       bop_idempotent S r b -> 
       bop_not_anti_right S r b. 
Proof. intros S r b s symS idemS. exists (cef_idempotent_implies_not_anti_right s); simpl. 
       assert (fact := idemS s). apply symS in fact. assumption. 
Defined. 


(* S *) 

Lemma bop_selective_implies_idempotent : ∀ (S : Type) (r : brel S) (b : binary_op S),
        bop_selective S r b -> bop_idempotent S r b.
Proof. intros S r b selS x. destruct (selS x x) as [H | H]; assumption. Defined. 


Lemma bop_selective_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S), 
       brel_symmetric S r -> 
       bop_selective S r b -> 
       bop_not_anti_left S r b. 
Proof. intros S r b s symS idemS. 
       apply bop_idempotent_implies_not_anti_left; auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 


Lemma bop_selective_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S), 
       brel_symmetric S r -> 
       bop_selective S r b -> 
       bop_not_anti_right S r b. 
Proof. intros S r b s symS idemS. 
       apply bop_idempotent_implies_not_anti_right; auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 

(* i *) 
Lemma bop_not_idempotent_implies_not_selective : ∀ (S : Type) (r : brel S) (b : binary_op S),
        bop_not_idempotent S r b -> bop_not_selective S r b. 
Proof. intros S r b [i Pi]. exists (i, i). auto. Defined. 


(* K *) 

Lemma bop_left_cancellative_implies_not_left_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       bop_left_cancellative S r b -> 
          bop_not_left_constant S r b. 
Proof. intros S r b s f Pf lcS. 
       unfold bop_not_left_constant. 
       exists (cef_left_cancellative_implies_not_left_constant s f). 
       unfold cef_left_cancellative_implies_not_left_constant. 
       case_eq(r (b s s) (b s (f s))); intro H. 
          apply lcS in H. 
          destruct (Pf s) as [L R]. 
          rewrite H in L. 
          assumption. 
          reflexivity. 
Defined. 

Lemma bop_right_cancellative_implies_not_right_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       bop_right_cancellative S r b -> 
          bop_not_right_constant S r b. 
Proof. intros S r b s f Pf rcS. 
       unfold bop_not_right_constant. 
       exists (cef_right_cancellative_implies_not_right_constant s f). 
       unfold cef_right_cancellative_implies_not_right_constant. 
       case_eq(r (b s s) (b (f s) s)); intro H. 
          apply rcS in H. 
          destruct (Pf s) as [L R]. 
          rewrite H in L. 
          assumption. 
          reflexivity. 
Defined. 

Lemma bop_left_cancellative_implies_not_exists_ann : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_left_cancellative S r b -> 
         bop_not_exists_ann S r b. 
Proof. intros S r b s f symS transS Pf lcS a. 
       destruct (Pf s) as [L R]. 
       case_eq(r (b a s) a); case_eq(r (b a (f s)) a); intros H K. 
          apply symS in K. 
          assert (T := transS _ _ _ H K). 
          apply lcS in T. 
          rewrite T in R. discriminate. 
          exists (f s).  left. assumption. 
          exists s. left. assumption. 
          exists s. left. assumption. 
Qed. 

Lemma bop_right_cancellative_implies_not_exists_ann : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_right_cancellative S r b -> 
         bop_not_exists_ann S r b. 
Proof. intros S r b s f symS transS Pf lcS a. 
       destruct (Pf s) as [L R]. 
       case_eq(r (b s a) a); case_eq(r (b (f s) a) a); intros H K. 
          apply symS in K. 
          assert (T := transS _ _ _ H K). 
          apply lcS in T. 
          rewrite T in R. discriminate. 
          exists (f s).  right. assumption. 
          exists s. right. assumption. 
          exists s. right. assumption. 
Qed. 


Lemma bop_left_cancellative_implies_any_idempotent_is_left_id : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      ∀ i : S, r (b i i) i = true -> ∀ s : S, r s (b i s) = true. 
Proof. intros S r b refS symS transS assS congS lcS i H s. 
       assert (A := assS i i s). 
       assert (B : r (b i s) (b (b i i) s) = true). 
           assert (C := congS _ _ _ _ H (refS s)). 
           apply symS in C.  
           assumption. 
       assert (C := transS _ _ _ B A).        
       assert (D := lcS _ _ _ C). 
       assumption. 
Qed. 


Lemma bop_right_cancellative_implies_any_idempotent_is_right_id : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_right_cancellative S r b -> 
      ∀ i : S, r (b i i) i = true -> ∀ s : S, r s (b s i) = true. 
Proof. intros S r b refS symS transS assS congS lcS i H s. 
       assert (A := assS s i i). 
       assert (B : r (b s i) (b s (b i i)) = true). 
           assert (C := congS _ _ _ _ (refS s) H). 
           apply symS in C.  
           assumption. 
       apply symS in A. assert (C := transS _ _ _ B A).        
       assert (D := lcS _ _ _ C). 
       assumption. 
Qed. 


Lemma bop_cancellative_implies_idempotent_is_id : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      ∀ i : S, r (b i i) i = true -> bop_is_id S r b i. 
Proof. intros S r b refS symS transS assS congS lcS rcS i H s.      
       split; apply symS.
       apply bop_left_cancellative_implies_any_idempotent_is_left_id; auto. 
       apply bop_right_cancellative_implies_any_idempotent_is_right_id; auto. 
Defined. 



Lemma bop_cancellative_and_exists_id_imply_not_idempotent : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (x : S) (f : S -> S), 
      brel_not_trivial S r f -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      bop_exists_id S r b -> 
         bop_not_idempotent S r b. 
Proof. intros S r b x f Pf refS symS transS assS congS lcS rcS [i Pi]. 
       exists (cef_cancellative_and_exists_id_imply_not_idempotent r x i f). 
       unfold cef_cancellative_and_exists_id_imply_not_idempotent. 
       case_eq(r x i); intro H. 
             case_eq(r (b (f x) (f x)) (f x)); intro F. 
                destruct (Pf x) as [L R].
                assert (A : bop_is_id S r b (f x)). 
                   apply bop_cancellative_implies_idempotent_is_id; auto.
                assert (B : r i (f x) = true). 
                   apply (bop_is_id_equal S r symS transS b); auto.
                assert (C := transS _ _ _ H B). 
                rewrite C in L. 
                assumption. 
                reflexivity. 
             case_eq(r (b x x) x); intro F. 
                assert (A : bop_is_id S r b x). 
                   apply bop_cancellative_implies_idempotent_is_id; auto.
                assert (B : r i x = true). 
                   apply (bop_is_id_equal S r symS transS b); auto.
                apply symS in B. 
                rewrite B in H. 
                assumption. 
                reflexivity. 
Defined. 


Lemma bop_cancellative_and_not_exists_id_imply_not_idempotent : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (x : S) (f : S -> S), 
      brel_not_trivial S r f -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      bop_not_exists_id S r b -> 
         bop_not_idempotent S r b. 
Proof. intros S r b x f Pf refS symS transS assS congS lcS rcS no_id. 
       exists x. 
          case_eq(r (b x x) x); intro F. 
             assert (A : bop_is_id S r b x). 
                apply bop_cancellative_implies_idempotent_is_id; auto.
             destruct (no_id x) as [y [J | J]]; destruct (A y) as [L R]. 
                rewrite L in J. assumption. 
                rewrite R in J. assumption. 
             reflexivity. 
Defined. 


Lemma bop_cancellative_implies_not_idempotent : 
  ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
      brel_not_trivial S r f -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      bop_exists_id_decidable S r b -> 
         bop_not_idempotent S r b. 
Proof. intros S r b s f Pf refS symS transS assS congS lcS rcS [ id | no_id]. 
       apply (bop_cancellative_and_exists_id_imply_not_idempotent S r b s f); auto.
       apply (bop_cancellative_and_not_exists_id_imply_not_idempotent S r b s f); auto. 
Defined. 

(* C *) 
Lemma bop_commutative_and_not_is_left_imply_not_is_right  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> bop_commutative S r b -> 
            bop_not_is_left S r b -> bop_not_is_right S r b.
Proof. intros S r b transS commS [[s1 s2] P]. exists (s2, s1). 
       assert (A := commS s1 s2). 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ A P). 
Defined. 


Lemma bop_commutative_and_left_constant_imply_right_constant  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> 
         bop_commutative S r b -> 
         bop_left_constant S r b -> bop_right_constant S r b.
Proof. intros S r b tranS commS lcS s t u.
       exact (tranS _ _ _ (commS t s) (tranS _ _ _ (lcS s t u) (commS s u))). 
Qed. 

Lemma bop_commutative_and_not_left_constant_imply_not_right_constant  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_symmetric S r -> 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_not_left_constant S r b -> bop_not_right_constant S r b.
Proof. intros S r b symS transS commS [ p P]. exists p. 
       destruct p as [s1 [s2 s3]]. 
       assert (A := commS s1 s2). 
       assert (B := brel_transititivity_implies_dual _ _ transS _ _ _ A P). 
       assert (C := brel_symmetric_implies_dual _ _ symS _ _ B). 
       assert (D := commS s1 s3). 
       assert (E := brel_transititivity_implies_dual _ _ transS _ _ _ D C). 
       assert (F := brel_symmetric_implies_dual _ _ symS _ _ E). 
       assumption. 
Defined. 


Lemma bop_commutative_and_not_anti_left_imply_not_anti_right : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_not_anti_left S r b -> bop_not_anti_right S r b.
Proof. intros S r b transS commS [[s1 s2] P]. exists (s1, s2). 
       assert (A := commS s1 s2). 
       assert (B := transS _ _ _ P A). 
       assumption. 
Defined. 



Lemma bop_commutative_and_left_cancellative_imply_right_cancellative  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_left_cancellative S r b -> bop_right_cancellative S r b.
Proof. intros S r b transS commS lcS s1 s2 s3 H. 
       assert (A : r (b s1 s2) (b s1 s3) = true). 
          assert (B := commS s1 s2). 
          assert (C := commS s3 s1). 
          assert (D := transS _ _ _ B H). 
          assert (E := transS _ _ _ D C). 
          assumption. 
       apply lcS in A. 
       assumption. 
Defined. 

Lemma bop_commutative_and_not_left_cancellative_imply_not_right_cancellative  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_symmetric S r -> 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_not_left_cancellative S r b -> bop_not_right_cancellative S r b.
Proof. intros S r b symS transS commS [ p P ]. 
       exists p. 
       destruct p as [s1 [s2 s3]]. destruct P as [L R]. split. 
          assert (A := commS s2 s1). 
          assert (B := commS s1 s3). 
          assert (C := transS _ _ _ A L). 
          assert (D := transS _ _ _ C B). 
          assumption. 
          assumption. 
Defined. 

Lemma bop_commutative_implies_not_is_left  : ∀ (S: Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
     brel_not_trivial S r f -> 
     brel_symmetric S r -> 
     brel_transitive S r -> 
        bop_commutative S r b -> bop_not_is_left S r b. 
Proof. intros S r b s f Pf symS transS commS. 
       exists (cef_commutative_implies_not_is_left r b s f).
       destruct (Pf s) as [L R].
       assert (C := commS s (f s)). 
       unfold cef_commutative_implies_not_is_left. 
       case_eq (r (b (f s) s) s); intro H. 
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ H) L).  
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ C) H).  
Defined. 


Lemma bop_commutative_implies_not_is_right  : ∀ (S: Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
     brel_not_trivial S r f -> 
     brel_symmetric S r -> 
     brel_transitive S r -> 
        bop_commutative S r b -> bop_not_is_right S r b. 
Proof. intros S r b s f Pf symS transS commS. 
       exists (cef_commutative_implies_not_is_right r b s f). 
       destruct (Pf s) as [L R].
       assert (C := commS (f s) s). 
       unfold cef_commutative_implies_not_is_right. 
       case_eq (r (b (f s) s) s); intro H. 
          apply symS in H.  
          apply brel_symmetric_implies_dual in R; auto. 
          assert (A := brel_transititivity_implies_dual _ _ transS _ _ _ H R).  
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ C A).  
          assumption. 
Defined. 


(* N *) 

Lemma exists_id_implies_not_left_constant : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
               brel_congruence S r r -> 
               brel_not_trivial S r f-> 
               bop_exists_id S r b -> 
                  bop_not_left_constant S r b. 
Proof. intros S r b s f congS Pf [i Pi].
       exists (i, (s, f s)).               
       destruct (Pi s) as [Ls Rs]. 
       destruct (Pi (f s)) as [Lf Rf]. 
       destruct (Pf s) as [L R]. 
       assert (C := congS _ _ _ _ Ls Lf). 
       rewrite L in C. 
       assumption. 
Defined. 


Lemma exists_id_implies_not_right_constant : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
               brel_congruence S r r -> 
               brel_not_trivial S r f -> 
               bop_exists_id S r b -> 
                  bop_not_right_constant S r b. 
Proof. intros S r b  s f congS Pf [i Pi].
       exists (i, (s, f s)).        
       destruct (Pi s) as [Ls Rs]. 
       destruct (Pi (f s)) as [Lf Rf]. 
       destruct (Pf s) as [L R]. 
       assert (C := congS _ _ _ _ Rs Rf). 
       rewrite L in C. 
       assumption. 
Defined. 

(* really : exists_right_id ... *) 
Lemma exists_id_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S -> 
               bop_exists_id S r b -> 
                  bop_not_anti_left S r b. 
Proof. intros S r b symS s [i Pi]. 
       exists (s, i). destruct (Pi s) as [L R]. 
       apply symS in R. assumption. 
Defined. 


(* really : exists_left_id ... *) 
Lemma exists_id_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S -> 
               bop_exists_id S r b -> 
                  bop_not_anti_right S r b. 
Proof. intros S r b symS s [i Pi]. 
       exists (s, i). destruct (Pi s) as [L R]. 
       apply symS in L. assumption. 
Defined. 


Lemma exists_id_implies_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_id S r b -> 
                  bop_not_is_left S r b. 
Proof. intros S r b f symS transS Pf [i Pi].
       exists (i, f i).       
       destruct (Pf i) as [L1 R1]. 
       destruct (Pi (f i)) as [L2 R2]. 
       apply symS in L2. 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ L2 R1). 
Defined. 

Lemma exists_id_implies_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_id S r b -> 
                  bop_not_is_right S r b. 
Proof. intros S r b f symS transS Pf [i Pi].
       exists (f i, i).       
       destruct (Pf i) as [L1 R1]. 
       destruct (Pi (f i)) as [L2 R2]. 
       apply symS in R2. 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ R2 R1). 
Defined. 

(* A *) 

Lemma exists_ann_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S -> 
               bop_exists_ann S r b -> 
                  bop_not_anti_left S r b. 
Proof. intros S r b symS s [a Pa]. 
       unfold bop_not_anti_left. 
       unfold bop_is_ann in Pa. 
       exists (a, s). destruct (Pa s) as [L R]. 
       apply symS in L. assumption. 
Defined. 


Lemma exists_ann_implies_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_ann S r b -> 
                  bop_not_is_left S r b. 
Proof. intros S r b f symS transS Pf [a Pa]. 
       destruct (Pf a) as [L1 R1]. 
       destruct (Pa (f a)) as [L2 R2]. 
       unfold bop_not_is_left. 
       unfold bop_is_ann in Pa. 
       exists (f a, a).
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ R2) L1). 
Defined. 

Lemma exists_ann_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S  -> 
               bop_exists_ann S r b -> 
                  bop_not_anti_right S r b. 
Proof. intros S r b symS s [a Pa]. 
       destruct (Pa s) as [L R]. 
       exists (a, s). 
       apply symS. assumption. 
Defined. 

Lemma exists_ann_implies_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_ann S r b -> 
                  bop_not_is_right S r b. 
Proof. intros S r b f symS transS Pf [a Pa]. 
       destruct (Pf a) as [L1 R1]. 
       destruct (Pa (f a)) as [L2 R2]. 
       unfold bop_not_is_right. 
       unfold bop_is_ann in Pa. 
       exists (a, f a).
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ L2) L1). 
Defined. 



Lemma exists_ann_implies_not_left_cancellative : 
     ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_reflexive S r -> 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       bop_exists_ann S r b -> 
                  bop_not_left_cancellative S r b. 
Proof. intros S r b s f refS congS Pf [a Pa]. 
       destruct (Pf s) as [L1 R1]. 
       destruct (Pa s) as [L2 R2]. 
       destruct (Pa (f s)) as [L3 R4]. 
       exists (a, (s, f s)). split. 
          assert (C := congS _ _ _ _ L2 L3). 
          rewrite (refS a) in C. 
          assumption.        
          assumption.        
Defined. 

Lemma exists_ann_implies_not_right_cancellative : 
     ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_reflexive S r -> 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       bop_exists_ann S r b -> 
                  bop_not_right_cancellative S r b. 
Proof. intros S r b s f refS congS Pf [a Pa]. 
       destruct (Pf s) as [L1 R1]. 
       destruct (Pa s) as [L2 R2]. 
       destruct (Pa (f s)) as [L3 R4]. 
       exists (a, (s, f s)). split. 
          assert (C := congS _ _ _ _ R2 R4). 
          rewrite (refS a) in C. 
          assumption.        
          assumption.        
Defined.




(* CI *) 

Lemma bop_idempotent_and_commutative_imply_not_left_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_transitive S r -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
          bop_not_left_constant S r b. 
Proof. intros S r b s f Pf congS refS transS idemS commS. 
       exists (cef_idempotent_and_commutative_imply_not_left_constant r b s f). 
       unfold cef_idempotent_and_commutative_imply_not_left_constant. 
       assert (A := idemS s). 
       assert (B := idemS (f s)). 
       case_eq(r (b (f s) s) s); intro H.
          assert (C := congS _ _ _ _ H B). 
          destruct (Pf s) as [L R]. 
          rewrite L in C.
          assumption. 
          case_eq(r (b s (f s)) (f s)); intro J.
             assert (C := congS _ _ _ _ J A). 
             destruct (Pf s) as [L R]. 
             rewrite R in C.
             assumption. 
             assert (C := commS (f s) s). 
             assert (D := brel_transititivity_implies_dual _ _ transS _ _ _ C H). 
             assert (E := congS _ _ _ _ (refS (b s (f s))) A). 
             rewrite D in E.
             assumption.                          
Defined. 


Lemma bop_idempotent_and_commutative_imply_not_right_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
          bop_not_right_constant S r b. 
Proof. intros S r b s f Pf congS refS symS transS idemS commS. 
       apply bop_commutative_and_not_left_constant_imply_not_right_constant; auto. 
       apply (bop_idempotent_and_commutative_imply_not_left_constant S r b s f); auto. 
Defined. 


(* CS *) 

Lemma bop_selective_and_commutative_imply_not_left_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_transitive S r -> 
       bop_selective S r b -> 
       bop_commutative S r b -> 
          bop_not_left_constant S r b. 
Proof. intros S r b s f Pf congS refS transS selS commS. 
       apply (bop_idempotent_and_commutative_imply_not_left_constant S r b s f); auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 


Lemma bop_selective_and_commutative_imply_not_right_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_selective S r b -> 
       bop_commutative S r b -> 
          bop_not_right_constant S r b. 
Proof. intros S r b s f Pf congS refS symS transS selS commS. 
       apply (bop_idempotent_and_commutative_imply_not_right_constant S r b s f); auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 



Lemma bop_selective_and_commutative_imply_not_left_cancellative : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_selective S r b -> 
      bop_commutative S r b -> 
      bop_not_left_cancellative S r b.
Proof. intros S r b s f symS transS Pf selS commS. 
       exists (cef_selective_and_commutative_imply_not_left_cancellative  r b s f). 
       assert (idemS := bop_selective_implies_idempotent S r b selS).
       destruct (Pf s) as [L R]. 
       unfold cef_selective_and_commutative_imply_not_left_cancellative. 
       destruct (selS s (f s)) as [H | H]. 
          rewrite H. split. 
             assert (I := idemS s). 
             apply symS in H. 
             assert (T := transS _ _ _ I H). 
             assumption. 
             assumption. 
          assert (F : r (b s (f s)) s = false). 
             apply symS in H. 
             assert (A := brel_transititivity_implies_dual _ _ transS _ _ _ H R). 
             assumption. 
          rewrite F. split. 
             assert (I := idemS (f s)). 
             apply symS in H. 
             assert (T1 := transS _ _ _ I H). 
             assert (C := commS s (f s)). 
             assert (T2 := transS _ _ _ T1 C). 
             assumption. 
             assumption. 
Defined. 


Lemma bop_selective_and_commutative_imply_not_right_cancellative : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_selective S r b -> 
      bop_commutative S r b -> 
         bop_not_right_cancellative S r b. 
Proof. intros S r b s f symS transS Pf selS commS. 
       apply bop_commutative_and_not_left_cancellative_imply_not_right_cancellative; auto. 
       apply (bop_selective_and_commutative_imply_not_left_cancellative S r b s f); auto. 
Defined. 



(* CIs *) 


Lemma bop_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S), 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_not_selective S r b -> 
          bop_not_left_cancellative S r b. 
Proof. intros S r b congS refS symS transS assS b_congS idemS commS [[s1 s2]  [H1 H2]]. 
       exists (cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative  b s1 s2). 
       unfold cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative. split. 
          assert (A : r (b (b s1 s2) s1) (b s1 s2) = true). 
             assert (B := b_congS _ _ _ _ (commS s1 s2) (refS s1)). 
             assert (C := assS s2 s1 s1). 
             assert (D := b_congS _ _ _ _ (refS s2) (idemS s1)). 
             assert (E := commS s2 s1). 
             assert (F := transS _ _ _ B C). 
             assert (G := transS _ _ _ F D). 
             assert (H := transS _ _ _ G E). 
             assumption. 
          assert (B : r (b (b s1 s2) s2) (b s1 s2) = true). 
             assert (C := assS s1 s2 s2). 
             assert (D := b_congS _ _ _ _ (refS s1) (idemS s2)). 
             assert (T := transS _ _ _ C D). 
             assumption. 
          assert (C := congS _ _ _ _ A B). 
          rewrite (refS (b s1 s2)) in C. 
          assumption. 
          case_eq(r s1 s2); intro F. 
             assert (I := idemS s1). 
             assert (C := b_congS _ _ _ _ (refS s1) F). 
             apply symS in C. 
             assert (T := transS _ _ _ C I). 
             rewrite T in H1.
             assumption. 
             reflexivity. 
Defined. 

Lemma bop_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S), 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_not_selective S r b -> 
          bop_not_right_cancellative S r b. 
Proof. intros S r b congS refS symS transS assS b_congS idemS commS not_selS. 
       apply bop_commutative_and_not_left_cancellative_imply_not_right_cancellative; auto. 
       apply bop_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative; auto. 
Defined. 


(* CI(S || s) *) 

Lemma bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_selective_decidable S r b -> 
          bop_not_left_cancellative S r b. 
Proof. intros S r b s f congS Pf refS symS transS assS b_congS idemS commS [selS | not_selS]. 
       apply (bop_selective_and_commutative_imply_not_left_cancellative S r b s f); auto. 
       apply bop_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative; auto. 
Defined. 

Lemma bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_selective_decidable S r b -> 
          bop_not_right_cancellative S r b. 
Proof. intros S r b s f congS Pf refS symS transS assS b_congS idemS commS d_selS. 
       apply bop_commutative_and_not_left_cancellative_imply_not_right_cancellative; auto. 
       apply (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f); auto. 
Defined. 


(* for bops_ ... 


LD( +,* )  left distributive       a * (b + c) = (a * b) + (a * c) 
RD( +,* )  right distributive      (b + c) * a = (b * a) + (c * a)
LA( +,* )  left absorptive         a = a + (a * b) 
RA( +,* )  right absorptive        a = (a * b) + a
0A( +,* ) plus id is times ann     id+ * a = id+ = a * id+
OA( *,+ ) times id is times ann    id* + a = id* = a + id*

LD( +,* )  a * (b + c) = (a * b) + (a * c) 
LD( *,+ )  a + (b * c) = (a + b) * (a + c) 
RD( +,* )  (b + c) * a = (b * a) + (c * a)
RD( *,+ )  (b * c) + a = (b + a) * (c + a)
LA( +,* )  a = a + (a * b) 
LA( *,+ )  a = a * (a + b) 
RA( +,* )  a = (a * b) + a
0A( +,* )  id+ * a = id+ = a * id+
OA( *,+ )  id* + a = id* = a + id*


---------------------------------------------------------
LD( +,* ) C( * ) -> RD( +,* ) 
LA( +,* ) C( * ) -> RA( +,* ) 

C( + ), C( * ), LA( *, + ), a = a + b -> b = a * b 
                LA( +, * ), b = a * b -> a = a + b

LA( +, * ),  LA( *, + )             -> I( + )
LA( +, * ),  LA( *, + )             -> I( * )

C( * ), LA( +, * ),  LA( *, + ), LD( +, * ) -> LD( *, + ) 
---------------------------------------------------------
---------------------------------------------------------
I( * ), LD( +,* ) -> LA( +,* )
I( + ), LD( *,+ ) -> LA( *,+ )

   a + (b * c) = (a + b) * (a + c) 
   a + (a * b) = (a + a) * (a + b) 
               = a * (a + b)         I( + )

---------------------------------------------------------
S( + ), LD( *,+ ) 

   a + (b * c) = (a + b) * (a + c) 

---------------------------------------------------------




*) 

(*
   LD( +,* ) C( * ) -> RD( +,* ) 
*) 
Lemma bops_left_distributive_and_times_commutative_imply_right_distributive : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_congruence S rS rS ->         
        bop_congruence S rS plusS ->         
        bop_commutative S rS timesS ->         
        bop_left_distributive S rS plusS timesS -> 
           bop_right_distributive S rS plusS timesS. 
Proof. intros S rS plusS timesS congS cong_plusS commS ldS s1 s2 s3. 
       unfold bop_commutative in commS. 
       unfold bop_left_distributive in ldS. 
       unfold bop_congruence in cong_plusS. 
       unfold brel_congruence in congS. 
       assert (A := commS s1 (plusS s2 s3)). 
       assert (B := commS s1 s2).
       assert (C := commS s1 s3).
       assert (D := cong_plusS _ _ _ _ B C). 
       assert (E := congS _ _ _ _ A D). 
       assert (F := ldS s1 s2 s3). 
       rewrite F in E. 
       rewrite <- E. 
       reflexivity. 
Qed. 

(* 
     LA( +,* ) C( * ) -> RA( +,* ) 

Lemma bops_left_absorption_and_times_commutative_imply_right_absorption : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS ->         
        brel_transitive S rS ->         
        bop_congruence S rS plusS ->         
        bop_commutative S rS timesS ->         
        bops_left_absorption S rS plusS timesS -> 
           bops_right_absorption S rS plusS timesS. 
Proof. intros S rS plusS timesS refS transS cong_plusS commS laS s1 s2. 
       unfold bop_commutative in commS. 
       unfold bops_left_absorption in laS. 
       unfold bop_congruence in cong_plusS. 
       assert (B := commS s1 s2).
       assert (C := refS s1).
       assert (D := laS s1 s2). 
       assert (E := cong_plusS _ _ _ _ C B). 
       assert (F := transS _ _ _ D E). 
       assumption. 
Qed. 
*) 

(* 


Lemma bops_explore : 
      ∀ (S : Type) 
        (rS : brel S) 
        (plusS timesS : binary_op S)
        (LA1 : bops_left_absorption S rS plusS timesS)    (* a = a + (a * b) *)
        (LA2 : bops_left_absorption S rS timesS plusS)    (* a = a * (a + b) *)
        (RA1 : bops_right_absorption S rS plusS timesS)   (* a = (a * b) + a *) 
        (RA2 : bops_right_absorption S rS timesS plusS),  (* a = (a + b) * a *) 
        bop_left_distributive S rS plusS timesS ->        (* a * (b + c) = (a * b) + (a * c) *) 
           bop_right_distributive S rS timesS plusS. 
Proof. unfold bops_left_absorption, 
              bops_right_absorption,
              bop_left_distributive, 
              bop_left_distributive. 
       intros S rS plusS timesS LA1 LA2 RA1 RA2 ldS s1 s2 s3. 
 Qed. 
*) 


(* 
   C( + ), C( * ), LA( *, +), a = a + b -> b = a * b 

Lemma bops_lattice_test_1 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS timesS -> 
        bop_commutative S rS plusS ->         
        bop_commutative S rS timesS ->         
        bops_left_absorption S rS timesS plusS -> 
           ∀ (a b : S), rS a (plusS a b) = true -> rS b (timesS a b) = true. 
Proof. intros S rS plusS timesS refS symS transS cong_times comm_plus comm_times laS a b H. 
       assert (A := laS b a). 
       assert (B := comm_plus a b). 
       assert (C := transS _ _ _ H B).
       assert (D := cong_times _ _ _ _ (refS b) C). 
       apply symS in A. 
       assert (E := transS _ _ _ D A). 
       assert (F := comm_times a b).        
       assert (G := transS _ _ _ F E). apply symS. 
       assumption. 
Qed. 

*) 

(* 
   LA( +, * ), b = a * b -> a = a + b

Lemma bops_lattice_test_2 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS plusS -> 
        bops_left_absorption S rS plusS timesS -> 
           ∀ (a b : S), rS b (timesS a b) = true -> rS a (plusS a b) = true.  
Proof. intros S rS plusS timesS refS symS transS cong_plus laS a b H. 
       assert (A := laS a b). 
       assert (C := cong_plus _ _ _ _ (refS a) H). 
       apply symS in C. 
       assert (D := transS _ _ _ A C). 
       assumption. 
Qed. 
*) 

(* 
   LA( +, * ),  LA( *, + ) -> I( + )

Lemma bops_lattice_test_3 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS plusS ->  
        bops_left_absorption S rS plusS timesS ->       
        bops_left_absorption S rS timesS plusS -> 
           bop_idempotent S rS plusS. 
Proof. intros S rS plusS timesS refS symS transS cong_plus la1 la2 a. 
       unfold bops_left_absorption in *. 
       assert (A := la1 a (plusS a a)).
       assert (B := la2 a a). 
       assert (C := cong_plus _ _ _ _ (refS a) B). 
       apply symS in A. 
       assert (D := transS _ _ _ C A). 
       assumption. 
Qed.

*) 

(* 
   LA( +, * ),  LA( *, + ) -> I( * )

Lemma bops_lattice_test_4 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS timesS ->
        bops_left_absorption S rS plusS timesS ->       
        bops_left_absorption S rS timesS plusS -> 
           bop_idempotent S rS timesS. 
Proof. intros S rS plusS timesS refS symS transS cong_times la1 la2 a. 
       unfold bops_left_absorption in *. 
       assert (A := la2 a (timesS a a)).
       assert (B := la1 a a). 
       assert (C := cong_times _ _ _ _ (refS a) B). 
       apply symS in A. 
       assert (D := transS _ _ _ C A). 
       assumption. 
Qed.
*) 

(* 
   C ( * ), LA( +, * ),  LA( *, + ), LD( +, * ) -> LD( *, + ) 

Lemma bops_lattice_test_5 : 
      ∀ (S : Type) (rS : brel S) (b1 b2 : binary_op S),       
        brel_congruence S rS rS ->         
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS b1 ->
        bop_associative S rS b1 ->
        bop_commutative S rS b2 ->
        bops_left_absorption S rS b1 b2 ->       
        bops_left_absorption S rS b2 b1 -> 
           bop_left_distributive S rS b1 b2 -> bop_left_distributive S rS b2 b1.
Proof. intros S rS b1 b2 congS refS symS transS cong_b1 assoc_b1 comm_b2 la1 la2 ldS s1 s2 s3. 
       (* outline : (page 86 of Davey and Priestley)
            (s1 + s2) * (s1 + s3) 
          = ldS 
            ((s1 + s2) * s1) + ((s1 + s2) * s3)  
          = comm_b2, la2 
            s1 + (s3 * (s1 + s2))
          = ldS 
            s1 + ((s3 * s1) + (s3 * s2))
          = assoc 
            (s1 + (s3 * s1)) + (s3 * s2))
          = comm_b2, la1 
            s1 + (s2 * s3))
       *) 
       assert (A := ldS (b1 s1 s2) s1 s3). 
       assert (B : rS (b1 (b2 (b1 s1 s2) s1) (b2 (b1 s1 s2) s3))
                      (b1 s1 (b2 (b1 s1 s2) s3)) = true). 
          assert (C := la2 s1 s2).           
          assert (D := comm_b2 s1 (b1 s1 s2)). 
          assert (E := transS _ _ _ C D). 
          apply cong_b1. apply symS. assumption. apply refS. 
       assert (C := transS _ _ _ A B). 
       assert (D : rS (b1 s1 (b2 (b1 s1 s2) s3))
                      (b1 s1 (b2 s2 s3)) = true).
          assert (rdS := bops_left_distributive_and_times_commutative_imply_right_distributive S
                           rS b1 b2 congS cong_b1 comm_b2 ldS). 
          assert (E := rdS s3 s1 s2). 
          assert (F := cong_b1 _ _ _ _ (refS s1) E).           
          assert (G := assoc_b1 s1 (b2 s1 s3) (b2 s2 s3)). 
          apply symS in G. 
          assert (H := transS _ _ _ F G). 
          assert (I := la1 s1 s3). 
          assert (J := cong_b1 _ _ _ _ I (refS (b2 s2 s3))). apply symS in J. 
          assert (K := transS _ _ _ H J). 
          assumption. 
       assert (E := transS _ _ _ C D). 
       apply symS. assumption. 
Qed.
*) 


(* 
(B ∧ A) ∨ (C ∧ A) = [(B ∧ A) ∨ C] ∧ A.

B ≤ A implies B ∨ (C ∧ A) = (B ∨ C) ∧ A.

*) 
Definition bop_right_modular_eq (S : Type) (r : brel S) (b1 b2 : binary_op S)
   := ∀ a b c : S, r (b1 (b2 b a) (b2 c a)) (b2 (b1 (b2 b a) c) a) = true. 



(****************************************************************************************** 

This is same as theory.bop_product.bop_not_left_or_not_right

This justifies the semigroup attribute 

*) 
Lemma brel_nontrivial_implies_not_bop_is_left_and_bop_is_right : 
      ∀ (S : Type) (rS : brel S) (s : S) (f : S -> S),  
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        brel_not_trivial S rS f -> 
        ∀ (bS : binary_op S), ((bop_is_left S rS bS) * (bop_is_right S rS bS)) -> False. 
Proof. unfold bop_is_left, bop_is_right. 
       intros S rS s f symS tranS Pf bS [ ilS irS ]. 
       assert (A := ilS s (f s)). 
       assert (B := irS s (f s)). 
       apply symS in A. 
       assert (C := tranS _ _ _ A B). 
       destruct (Pf s) as [F _]. 
       rewrite F in C. 
       discriminate. 
Qed. 

(*
Definition bop_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = true. 

Definition bop_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) t = true. 

Definition bop_anti_left (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b s t) = false. 

Definition bop_anti_right (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b t s) = false. 

Definition bop_left_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true. 

Definition bop_right_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b t s) (b u s) = true. 

*) 


(* absorption 

Definition bops_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 s t) s) = true.

Definition bops_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.
 *)

Lemma bops_left_right_absorptive_implies_right_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_right_absorptive S r b1 b2 -> bops_right_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 abs s t.
       assert (fact1 := abs s t).
       assert (fact2 := comm_b1 s (b2 t s)). 
       apply (transS _ _ _ fact1 fact2). 
Defined.

Lemma bops_not_left_right_absorptive_implies_not_right_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r ->
        bop_commutative S r b1 -> 
        bops_not_left_right_absorptive S r b1 b2 -> bops_not_right_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 [[s s'] P]. exists (s, s'). 
       case_eq(r s (b1 (b2 s' s) s)); intro J.
          assert (fact1 := comm_b1 (b2 s' s) s). 
          assert (fact2 := transS _ _ _ J fact1).
          rewrite fact2 in P. discriminate. 
          reflexivity. 
Defined.

Definition bops_right_right_absorptive_decide_I : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_right_absorptive_decidable S r b1 b2 -> bops_right_right_absorptive_decidable S r b1 b2
:= λ S r b1 b2 trans comm lrad, 
   match lrad with 
   | inl lr  => inl _ (bops_left_right_absorptive_implies_right_right S r b1 b2 trans comm lr)
   | inr nlr => inr _ (bops_not_left_right_absorptive_implies_not_right_right S r b1 b2 trans comm nlr)
   end. 



Lemma bops_left_left_absorptive_implies_right_left: ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_left_absorptive S r b1 b2 -> bops_right_left_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 abs s t.
       assert (fact1 := abs s t).
       assert (fact2 := comm_b1 s (b2 s t)). 
       apply (transS _ _ _ fact1 fact2). 
Defined.

Lemma bops_not_left_left_absorptive_implies_not_right_left : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r ->
        bop_commutative S r b1 -> 
        bops_not_left_left_absorptive S r b1 b2 -> bops_not_right_left_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 [[s s'] P]. exists (s, s'). 
       case_eq(r s (b1 (b2 s s') s)); intro J.
          assert (fact1 := comm_b1 (b2 s s') s). 
          assert (fact2 := transS _ _ _ J fact1).
          rewrite fact2 in P. discriminate. 
          reflexivity. 
Defined.

Definition bops_right_left_absorptive_decide_I : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_left_absorptive_decidable S r b1 b2 -> bops_right_left_absorptive_decidable S r b1 b2
:= λ S r b1 b2 trans comm lrad, 
   match lrad with 
   | inl lr  => inl _ (bops_left_left_absorptive_implies_right_left S r b1 b2 trans comm lr)
   | inr nlr => inr _ (bops_not_left_left_absorptive_implies_not_right_left S r b1 b2 trans comm nlr)
   end. 






(*--------------------------*)



Lemma bops_left_left_absorptive_implies_left_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_reflexive S r -> 
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b2 -> 
        bops_left_left_absorptive S r b1 b2 -> bops_left_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 refS transS cong_b1 comm_b2 lla s t.
       assert (fact1 := lla s t).        
       assert (fact2 : r (b1 s (b2 s t)) (b1 s (b2 t s)) = true). apply cong_b1; auto. 
       apply (transS _ _ _ fact1 fact2). 
Defined. 


 Lemma bops_left_right_absorptive_implies_right_left : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),        brel_reflexive S r -> 
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
        bops_left_right_absorptive S r b1 b2 -> 
        bops_right_left_absorptive S r b1 b2. 
Proof. intros S r b1 b2 refS transS cong_b1 comm_b1 comm_b2 lra s t.
       assert (fact1 := lra s t).      
       assert (fact2 : r (b1 s (b2 t s)) (b1 (b2 s t) s) = true). 
          assert(fact3 := comm_b2 t s). 
          assert(fact4 := comm_b1 s (b2 t s)). 
          assert(fact5 : r (b1 (b2 t s) s) (b1 (b2 s t) s) = true). apply cong_b1; auto. 
          apply (transS _ _ _ fact4 fact5). 
       apply (transS _ _ _ fact1 fact2). 
Defined. 

Lemma bops_right_left_absorptive_implies_right_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_reflexive S r -> 
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b2 -> 
        bops_right_left_absorptive S r b1 b2 -> bops_right_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 refS transS cong_b1 comm_b2 lla s t.
       assert (fact1 := lla s t).        
       assert (fact2 : r (b1 (b2 s t) s) (b1 (b2 t s) s) = true). apply cong_b1; auto. 
       apply (transS _ _ _ fact1 fact2). 
Defined. 


(*************************************************** *)

Definition not_ex2 {S : Type} (eq : brel S) (s : S) (t : S) (u : S) : S -> (S -> S) :=
λ x y,
  if eq x y
  then x 
  else if eq x s
       then if eq y t
            then u 
            else t 
       else (* x <> s *)
            if eq y t 
            then if eq x u
                 then s 
                 else u 
            else (* x <> s, y <> t *)
                 if eq x u
                 then if eq y s 
                      then t 
                      else s
                 else (* x <> u, x <> s, y <> t *)
                      if eq x t
                      then if eq y s 
                           then u 
                           else s 
                      else t 
  . 

Lemma brel_at_least_thee_implies_not_exactly_two :
  ∀ (T : Type) (eq : brel T),
    brel_symmetric T eq ->
    brel_transitive T eq ->     
    brel_at_least_three T eq -> brel_not_exactly_two T eq.
Proof. intros T eq sy tr nalt. 
       exists (not_ex2 eq (fst (projT1 nalt)) (fst (snd (projT1 nalt))) (snd (snd (projT1 nalt)))). 
       destruct nalt as [[s [t u] ] [[P1 P2] P3]]. simpl. 
       intros  x y.  
       case_eq(eq x y); intro J.
       left; auto. 
       right. compute. rewrite J.
       case_eq(eq x s); intro K1.
          case_eq(eq y t); intro K2. 
             apply sy in K1. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K1 P2).        
             apply sy in K2. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K2 P3). auto.
             apply sy in K1. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K1 P1). auto.                   
          case_eq(eq y t); intro K2. 
             case_eq(eq x u); intro K3.  
                apply sy in K2. apply (brel_symmetric_implies_dual T eq sy) in P1. 
                rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K2 P1). auto.
                apply sy in K2. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K2 P3). auto.
             case_eq(eq x u); intro K3.               
                case_eq(eq y s); intro K4.
                    apply sy in K4. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K4 P1). 
                    apply sy in K3. apply (brel_symmetric_implies_dual T eq sy) in P3. 
                    rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K3 P3). auto.                    
                   split; auto.
                case_eq(eq x t); intro K5. 
                   case_eq(eq y s); intro K6. 
                      apply sy in K6. rewrite (brel_transititivity_implies_dual T eq tr _ _ _ K6 P2). auto.
                      split; auto.
                   split; auto. 
Defined. 


