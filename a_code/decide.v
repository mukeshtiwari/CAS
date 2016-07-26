Require Import Coq.Bool.Bool.    
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.eq_bool. 
Require Import CAS.theory.brel.eq_nat. 
Require Import CAS.theory.brel.eq_list. 
Require Import CAS.theory.brel.product. 
Require Import CAS.theory.brel.llte_llt. 
Require Import CAS.theory.brel.sum. 
Require Import CAS.theory.brel.add_constant. 
Require Import CAS.theory.brel.and_sym.
Require Import CAS.theory.brel.reduce. 
Require Import CAS.theory.brel.set. 
Require Import CAS.theory.brel.in_set. 

Require Import CAS.theory.bop.and. 
Require Import CAS.theory.bop.or. 
Require Import CAS.theory.bop.max. 
Require Import CAS.theory.bop.min. 
Require Import CAS.theory.bop.plus. 
Require Import CAS.theory.bop.times. 
Require Import CAS.theory.bop.concat. 
Require Import CAS.theory.bop.left. 
Require Import CAS.theory.bop.right. 
Require Import CAS.theory.bop.product. 
Require Import CAS.theory.bop.left_sum. 
Require Import CAS.theory.bop.right_sum. 
Require Import CAS.theory.bop.add_id. 
Require Import CAS.theory.bop.add_ann. 
Require Import CAS.theory.bop.then_unary. 
Require Import CAS.theory.bop.union. 
Require Import CAS.theory.bop.intersect. 
(* Require Import CAS.theory.bop.minset_union. *) 
Require Import CAS.theory.bop.llex. 

Require Import CAS.theory.bops.and_or.
Require Import CAS.theory.bops.or_and.
Require Import CAS.theory.bops.min_max.
Require Import CAS.theory.bops.max_min.
Require Import CAS.theory.bops.min_plus.
Require Import CAS.theory.bops.product_product.
Require Import CAS.theory.bops.llex_product.
Require Import CAS.theory.bops.add_ann_add_id.
Require Import CAS.theory.bops.union_intersect.
Require Import CAS.theory.bops.intersect_union.
Require Import CAS.theory.bops.add_id_add_ann. 
Require Import CAS.theory.bops.add_ann_add_id. 




Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 


Require Import CAS.code.check. 


(* add_ann *) 

Definition bop_add_ann_idempotent_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S), 
     bop_idempotent_decidable S rS bS  → 
        bop_idempotent_decidable (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_ann_idempotent S rS c bS idemS)
   | inr not_idemS => inr _ (bop_add_ann_not_idempotent S rS c bS not_idemS)
   end. 


Definition bop_add_ann_commutative_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S), 
     brel_reflexive S rS → 
     bop_commutative_decidable S rS bS  → 
       bop_commutative_decidable (with_constant S) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS ref dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_ann_commutative S rS c bS ref commS)
   | inr not_commS => inr _ (bop_add_ann_not_commutative S rS c bS not_commS)
   end. 


Definition bop_add_ann_selective_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S),  
     brel_reflexive S rS → 
     bop_selective_decidable S rS bS  → 
        bop_selective_decidable (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS refS dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_ann_selective S rS c bS refS selS)
   | inr not_selS   => inr _ (bop_add_ann_not_selective S rS c bS not_selS)
   end. 


Definition bop_add_ann_exists_id_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S),  
     brel_nontrivial S rS -> 
     brel_reflexive S rS → 
     bop_exists_id_decidable S rS bS  → 
     bop_exists_id_decidable (with_constant S ) (brel_add_constant S rS c) (bop_add_ann S bS c)
:= λ S rS c bS ntS refS dS,  
   let wS :=  brel_nontrivial_witness S rS ntS in 
   match dS with 
   | inl eann  => inl _ (bop_add_ann_exists_id S rS c bS refS eann)
   | inr neann => inr _ (bop_add_ann_not_exists_id S rS c bS wS neann)
   end. 


(* add_id *) 


Definition bop_add_id_selective_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S),  
     brel_reflexive S rS → 
     bop_selective_decidable S rS bS  → 
        bop_selective_decidable (with_constant S ) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS refS dS,  
   match dS with 
   | inl selS       => inl _ (bop_add_id_selective S rS c bS refS selS)
   | inr not_selS   => inr _ (bop_add_id_not_selective S rS c bS not_selS)
   end. 

Definition bop_add_id_commutative_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S), 
     brel_reflexive S rS → 
     bop_commutative_decidable S rS bS  → 
       bop_commutative_decidable (with_constant S) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS ref dS,  
   match dS with 
   | inl commS     => inl _ (bop_add_id_commutative S rS c bS ref commS)
   | inr not_commS => inr _ (bop_add_id_not_commutative S rS c bS not_commS)
   end. 

Definition bop_add_id_idempotent_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S), 
     bop_idempotent_decidable S rS bS  → 
        bop_idempotent_decidable (with_constant S ) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS dS,  
   match dS with 
   | inl idemS     => inl _ (bop_add_id_idempotent S rS c bS idemS)
   | inr not_idemS => inr _ (bop_add_id_not_idempotent S rS c bS not_idemS)
   end. 

Definition bop_add_id_exists_ann_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant) 
     (bS : binary_op S),  
     brel_nontrivial S rS -> 
     brel_reflexive S rS → 
     bop_exists_ann_decidable S rS bS  → 
     bop_exists_ann_decidable (with_constant S ) (brel_add_constant S rS c) (bop_add_id S bS c)
:= λ S rS c bS ntS refS dS,  
   let wS :=  brel_nontrivial_witness S rS ntS in 
   match dS with 
   | inl eann  => inl _ (bop_add_id_exists_ann S rS c bS refS eann)
   | inr neann => inr _ (bop_add_id_not_exists_ann S rS c bS wS neann)
   end. 


Definition bop_add_id_left_cancellative_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (c : cas_constant) 
     (b : binary_op S), 
     brel_symmetric S r -> 
     (bop_anti_left_decidable S r b) -> 
     bop_left_cancellative_decidable S r b -> 
        bop_left_cancellative_decidable (with_constant S ) 
              (brel_add_constant S r c) (bop_add_id S b c)
:= λ S r c b symS ad lcd,  
   match ad with 
   | inl anti_left     => 
        match lcd with 
        | inl lcanc     => inl _ (bop_add_id_left_cancellative S r c b symS anti_left lcanc)
        | inr not_lcanc => inr _ (bop_add_id_not_left_cancellative S r c b symS (inl _ not_lcanc))
        end 
   | inr not_anti_left => inr _ (bop_add_id_not_left_cancellative S r c b symS (inr _ not_anti_left))
   end. 

Definition bop_add_id_right_cancellative_decide : 
   ∀ (S : Type) 
     (r : brel S) 
     (c : cas_constant) 
     (b : binary_op S), 
     brel_symmetric S r -> 
     (bop_anti_right_decidable S r b) -> 
     bop_right_cancellative_decidable S r b -> 
        bop_right_cancellative_decidable (with_constant S ) 
              (brel_add_constant S r c) (bop_add_id S b c)
:= λ S r c b symS ad lcd,  
   match ad with 
   | inl anti_right     => 
        match lcd with 
        | inl lcanc     => inl _ (bop_add_id_right_cancellative S r c b symS anti_right lcanc)
        | inr not_lcanc => inr _ (bop_add_id_not_right_cancellative S r c b symS (inl _ not_lcanc))
        end 
   | inr not_anti_right => inr _ (bop_add_id_not_right_cancellative S r c b symS (inr _ not_anti_right))
   end. 

(* product *) 


Definition bop_product_idempotent_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_idempotent_decidable S rS bS -> 
     bop_idempotent_decidable T rT bT -> 
     bop_idempotent_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT wS wT dS dT,  
   match brel_nontrivial_witness S rS wS,  brel_nontrivial_witness T rT wT with 
   | existT s _, existT t _ => 
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_product_idempotent S T rS rT bS bT commS commT)
         | inr not_commT => inr _ (bop_product_not_idempotent_right S T rS rT bS bT s not_commT)
         end 
       | inr not_commS   => inr _ (bop_product_not_idempotent_left S T rS rT bS bT t not_commS)
       end
   end.

(*
Lemma bop_product_idempotent_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_idempotent_decidable_new S rS bS -> 
     bop_idempotent_decidable_new T rT bT -> 
     bop_idempotent_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] [wS PS] [wT PT]. 
       exists (check_idempotent_product_new S T s t wS wT). 
       destruct wS as [ LS | s1]; destruct wT as [ LT | t1]; simpl. 
           apply bop_product_idempotent; auto. 
           rewrite PT. rewrite andb_comm. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
Defined. 

*) 
Definition bop_product_commutative_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_commutative_decidable S rS bS -> 
     bop_commutative_decidable T rT bT -> 
     bop_commutative_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT wS wT dS dT,  
     match brel_nontrivial_witness S rS wS,  brel_nontrivial_witness T rT wT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_product_commutative S T rS rT bS bT commS commT)
         | inr not_commT => inr _ (bop_product_not_commutative_right S T rS rT bS bT s not_commT)
         end 
       | inr not_commS   => inr _ (bop_product_not_commutative_left S T rS rT bS bT t not_commS)
       end
   end. 

(*

Definition bop_product_commutative_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_commutative_decidable_new S rS bS -> 
     bop_commutative_decidable_new T rT bT -> 
     bop_commutative_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] [wS PS] [wT PT]. 
       exists (check_commutative_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 s2]]; destruct wT as [ LT | [t1 t2] ]; simpl. 
           apply bop_product_commutative; auto. 
           rewrite PT. rewrite andb_comm. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
Defined. 

*) 

Definition bop_product_left_cancellative_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_reflexive S rS  → 
     brel_reflexive T rT  → 
     bop_left_cancellative_decidable S rS bS -> 
     bop_left_cancellative_decidable T rT bT -> 
     bop_left_cancellative_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT wS wT refS refT dS dT,  
     match brel_nontrivial_witness S rS wS,  brel_nontrivial_witness T rT wT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl canS => 
         match dT with 
         | inl canT     => inl _ (bop_product_left_cancellative S T rS rT bS bT canS canT)
         | inr not_canT => inr _ (bop_product_not_left_cancellative_right S T rS rT bS bT s refS not_canT)
         end 
       | inr not_canS   => inr _ (bop_product_not_left_cancellative_left S T rS rT bS bT t refT not_canS)
       end
   end. 

(* 

Definition bop_product_left_cancellative_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_reflexive S rS  → 
     brel_reflexive T rT  → 
     bop_left_cancellative_decidable_new S rS bS -> 
     bop_left_cancellative_decidable_new T rT bT -> 
     bop_left_cancellative_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS refT [wS PS] [wT PT]. 
       exists (check_left_cancellative_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 [s2 s3]]]; destruct wT as [ LT | [t1 [t2 t3]] ]; simpl. 
           apply bop_product_left_cancellative; auto. 
           destruct PT as [PTL PTR]. split. 
              rewrite refS, PTL. simpl. reflexivity. 
              rewrite Ps, PTR. simpl. reflexivity. 
           destruct PS as [PSL PSR]. split.            
              rewrite refT, PSL. simpl. reflexivity. 
              rewrite PSR. simpl. reflexivity. 
           destruct PT as [PTL PTR]. destruct PS as [PSL PSR]. split. 
              rewrite refT, PSL. simpl. reflexivity. 
              rewrite PSR. simpl. reflexivity. 
Defined. 

*) 

Definition bop_product_right_cancellative_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_reflexive S rS  → 
     brel_reflexive T rT  → 
     bop_right_cancellative_decidable S rS bS -> 
     bop_right_cancellative_decidable T rT bT -> 
     bop_right_cancellative_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT wS wT refS refT dS dT,  
     match brel_nontrivial_witness S rS wS,  brel_nontrivial_witness T rT wT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl canS => 
         match dT with 
         | inl canT     => inl _ (bop_product_right_cancellative S T rS rT bS bT canS canT)
         | inr not_canT => inr _ (bop_product_not_right_cancellative_right S T rS rT bS bT s refS not_canT)
         end 
       | inr not_canS   => inr _ (bop_product_not_right_cancellative_left S T rS rT bS bT t refT not_canS)
       end
   end. 


(* 
Definition bop_product_right_cancellative_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_reflexive S rS  → 
     brel_reflexive T rT  → 
     bop_right_cancellative_decidable_new S rS bS -> 
     bop_right_cancellative_decidable_new T rT bT -> 
     bop_right_cancellative_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] refS refT [wS PS] [wT PT]. 
       exists (check_right_cancellative_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 [s2 s3]]]; destruct wT as [ LT | [t1 [t2 t3]] ]; simpl. 
           apply bop_product_right_cancellative; auto. 
           destruct PT as [PTL PTR]. split. 
              rewrite refS, PTL. simpl. reflexivity. 
              rewrite Ps, PTR. simpl. reflexivity. 
           destruct PS as [PSL PSR]. split.            
              rewrite refT, PSL. simpl. reflexivity. 
              rewrite PSR. simpl. reflexivity. 
           destruct PT as [PTL PTR]. destruct PS as [PSL PSR]. split. 
              rewrite refT, PSL. simpl. reflexivity. 
              rewrite PSR. simpl. reflexivity. 
Defined. 

*) 

Definition bop_product_is_left_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_is_left_decidable S rS bS  → 
     bop_is_left_decidable T rT bT  → 
     bop_is_left_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT ntS ntT dS dT,  
       match dS with 
       | inl leftS => 
         match dT with 
         | inl leftT     => inl _ (bop_product_is_left S T rS rT bS bT leftS leftT)
         | inr not_leftT => inr _ (bop_product_not_is_left_right S T rS rT bS bT ntS not_leftT)
         end 
       | inr not_leftS   => inr _ (bop_product_not_is_left_left S T rS rT bS bT ntT not_leftS)
       end. 

(*

Definition bop_product_is_left_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_is_left_decidable_new S rS bS  → 
     bop_is_left_decidable_new T rT bT  → 
     bop_is_left_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] [wS PS] [wT PT]. 
       exists (check_is_left_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 s2]]; destruct wT as [ LT | [t1 t2] ]; simpl. 
           apply bop_product_is_left; auto. 
           rewrite PT. rewrite andb_comm. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
Defined. 

*) 

Definition bop_product_is_right_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T),
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_is_right_decidable S rS bS  → 
     bop_is_right_decidable T rT bT  → 
     bop_is_right_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT ntS ntT dS dT,  
       match dS with 
       | inl rightS => 
         match dT with 
         | inl rightT     => inl _ (bop_product_is_right S T rS rT bS bT rightS rightT)
         | inr not_rightT => inr _ (bop_product_not_is_right_right S T rS rT bS bT ntS not_rightT)
         end 
       | inr not_rightS   => inr _ (bop_product_not_is_right_left S T rS rT bS bT ntT not_rightS)
       end . 

(* 
Definition bop_product_is_right_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_is_right_decidable_new S rS bS  → 
     bop_is_right_decidable_new T rT bT  → 
     bop_is_right_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] [wS PS] [wT PT]. 
       exists (check_is_right_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 s2]]; destruct wT as [ LT | [t1 t2] ]; simpl. 
           apply bop_product_is_right; auto. 
           rewrite PT. rewrite andb_comm. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
Defined. 

*) 


Definition bop_product_selective_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_symmetric S rS -> 
     brel_symmetric T rT -> 
     brel_transitive S rS -> 
     brel_transitive T rT -> 
     bop_is_left_decidable S rS bS  → 
     bop_is_left_decidable T rT bT  → 
     bop_is_right_decidable S rS bS  → 
     bop_is_right_decidable T rT bT  → 
     bop_selective_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT ntS ntT symS symT transS transT dlS dlT drS drT,  
       match dlS, dlT, drS, drT with 
       |                 _,                  _,    inl is_right_S,      inl is_right_T => 
          inl _ (bop_product_selective S T rS rT bS bT (inr _ (is_right_S, is_right_T)))

       |     inl is_left_S,      inl is_left_T,                 _,                   _ => 
          inl _ (bop_product_selective S T rS rT bS bT (inl _ (is_left_S, is_left_T)))

       | inr not_is_left_S,                  _,                 _,  inr not_is_right_T => 
          inr _ (bop_product_not_selective S T rS rT bS bT 
                                             (inl _ not_is_left_S) 
                                             (inr _ not_is_right_T) 
                                             (inl _ not_is_left_S, inr _ not_is_right_T))

       |                 _,  inr not_is_left_T, inr not_is_right_S,                  _ => 
          inr _ (bop_product_not_selective S T rS rT bS bT 
                                             (inr _ not_is_right_S) 
                                             (inl _ not_is_left_T) 
                                             (inr _ not_is_left_T, inl _ not_is_right_S))

       (* NB : use of abort *) 
       |     inl is_left_S,                  _,    inl is_right_S,                   _ => 
          abort _ (bop_not_left_or_not_right S rS bS ntS symS transS is_left_S is_right_S)

       |                 _,      inl is_left_T,                 _,      inl is_right_T => 
          abort _ (bop_not_left_or_not_right T rT bT ntT symT transT is_left_T is_right_T)
       end. 


(* 
Definition bop_product_selective_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_symmetric S rS -> 
     brel_symmetric T rT -> 
     brel_transitive S rS -> 
     brel_transitive T rT -> 
     bop_is_left_decidable_new S rS bS  → 
     bop_is_left_decidable_new T rT bT  → 
     bop_is_right_decidable_new S rS bS  → 
     bop_is_right_decidable_new T rT bT  → 
     bop_selective_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT ntS ntT symS symT transS transT
              [wLS LS] [wLT LT] [wRS RS] [wRT RT]. 
       assert (FS := brel_nontrivial_implies_not_bop_is_left_and_bop_is_right S rS symS transS ntS bS). 
       assert (FT := brel_nontrivial_implies_not_bop_is_left_and_bop_is_right T rT symT transT ntT bT). 
       destruct ntS as [[s Ps] [f Pf]]; destruct ntT as  [[t Pt] [g Pg]]. 
       exists (check_selective_product_new S T s t wLS wLT wRS wRT). 
       destruct wLS as [ k1 | [s1 s2]]; 
       destruct wLT as [ k2 | [t1 t2] ]; 
       destruct wRS as [ k3 | [s3 s4]]; 
       destruct wRT as [ k4 | [t3 t4] ]; 
       simpl. 
           apply bop_product_selective; auto. 
           apply bop_product_selective; auto. 
           apply bop_product_selective; auto. 
           apply bop_product_selective; auto. 
           apply bop_product_selective; auto. 
           apply bop_product_selective; auto. 
           assert (F := FS (LS, RS)). tauto.  
           split. 
              rewrite LT. rewrite andb_comm. simpl. reflexivity. 
              rewrite RS. simpl. reflexivity. 
           split. 
              rewrite LT. rewrite andb_comm. simpl. reflexivity. 
              rewrite RS. simpl. reflexivity. 
           apply bop_product_selective; auto. 
           split. 
              rewrite LS. simpl. reflexivity. 
              rewrite RT. rewrite andb_comm. simpl. reflexivity. 
           apply bop_product_selective; auto. 
           assert (F := FT (LT, RT)). tauto.  
           split. 
              rewrite LS. simpl. reflexivity. 
              rewrite RT. rewrite andb_comm. simpl. reflexivity. 
           apply bop_product_selective; auto. 
           split. 
              rewrite LS. simpl. reflexivity. 
              rewrite RT. rewrite andb_comm. simpl. reflexivity. 
           split. 
              rewrite LT. rewrite andb_comm. simpl. reflexivity. 
              rewrite RS. simpl. reflexivity. 
           split. 
              rewrite LS. simpl. reflexivity. 
              rewrite RT. rewrite andb_comm. simpl. reflexivity. 
Defined. 
*) 

Definition bop_product_selective_decide_commutative_case : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     brel_symmetric S rS -> 
     brel_symmetric T rT -> 
     brel_transitive S rS -> 
     brel_transitive T rT -> 
     bop_commutative S rS bS  → 
     bop_commutative T rT bT  → 
     bop_selective_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT ntS ntT symS symT transS transT commS commT,  
   bop_product_selective_decide S T rS rT bS bT ntS ntT symS symT transS transT 
      (inr _ (bop_commutative_implies_not_is_left _ _ _ ntS symS transS commS))
      (inr _ (bop_commutative_implies_not_is_left _ _ _ ntT symT transT commT))
      (inr _ (bop_commutative_implies_not_is_right _ _ _ ntS symS transS commS))
      (inr _ (bop_commutative_implies_not_is_right _ _ _ ntT symT transT commT)). 

Definition bop_product_exists_id_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT : binary_op T), 
     bop_exists_id_decidable S rS bS -> 
     bop_exists_id_decidable T rT bT -> 
     bop_exists_id_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_product_exists_id S T rS rT bS bT eS eT)
         | inr neT => inr _ (bop_product_not_exists_id S T rS rT bS bT (inr _ neT))
         end 
       | inr neS   => inr _ (bop_product_not_exists_id S T rS rT bS bT (inl _ neS))
       end. 

(* 
Definition bop_product_exists_id_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT : binary_op T), 
     bop_exists_id_decidable_new S rS bS -> 
     bop_exists_id_decidable_new T rT bT -> 
     bop_exists_id_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. intros S T rS rT bS bT [wS PS] [wT PT]. 
       exists (check_exists_id_product_new S T wS wT). 
       destruct wS as [s | uS]; destruct wT as [t | uT]; simpl. 
          apply bop_product_is_id; auto. 
          apply bop_product_not_exists_id; auto. 
          apply bop_product_not_exists_id; auto. 
          apply bop_product_not_exists_id; auto. 
Defined. 

*) 
Definition bop_product_exists_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT : binary_op T), 
     bop_exists_ann_decidable S rS bS -> 
     bop_exists_ann_decidable T rT bT -> 
     bop_exists_ann_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_product_exists_ann S T rS rT bS bT eS eT)
         | inr neT => inr _ (bop_product_not_exists_ann S T rS rT bS bT (inr _ neT))
         end 
       | inr neS   => inr _ (bop_product_not_exists_ann S T rS rT bS bT (inl _ neS))
       end. 


(* 
Definition bop_product_exists_ann_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT : binary_op T), 
     bop_exists_ann_decidable_new S rS bS -> 
     bop_exists_ann_decidable_new T rT bT -> 
     bop_exists_ann_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT).
Proof. intros S T rS rT bS bT [wS PS] [wT PT]. 
       exists (check_exists_ann_product_new S T wS wT). 
       destruct wS as [s | uS]; destruct wT as [t | uT]; simpl. 
          apply bop_product_is_ann; auto. 
          apply bop_product_not_exists_ann; auto. 
          apply bop_product_not_exists_ann; auto. 
          apply bop_product_not_exists_ann; auto. 
Defined. 

*) 

Definition bop_product_left_constant_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_left_constant_decidable S rS bS -> 
     bop_left_constant_decidable T rT bT -> 
     bop_left_constant_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT wS wT dS dT,  
     match brel_nontrivial_witness S rS wS,  brel_nontrivial_witness T rT wT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl PS => 
         match dT with 
         | inl PT     => inl _ (bop_product_left_constant S T rS rT bS bT PS PT)
         | inr nPT => inr _ (bop_product_not_left_constant_right S T rS rT bS bT s nPT)
         end 
       | inr nPS   => inr _ (bop_product_not_left_constant_left S T rS rT bS bT t nPS)
       end
   end. 

(* 

Definition bop_product_left_constant_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_left_constant_decidable_new S rS bS -> 
     bop_left_constant_decidable_new T rT bT -> 
     bop_left_constant_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] [wS PS] [wT PT]. 
       exists (check_left_constant_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 [s2 s3]]]; destruct wT as [ LT | [t1 [t2 t3]] ]; simpl. 
           apply bop_product_left_constant; auto. 
           rewrite PT. rewrite andb_comm. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
Defined. 

*) 

Definition bop_product_right_constant_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_right_constant_decidable S rS bS -> 
     bop_right_constant_decidable T rT bT -> 
     bop_right_constant_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT wS wT dS dT,  
     match brel_nontrivial_witness S rS wS,  brel_nontrivial_witness T rT wT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl PS => 
         match dT with 
         | inl PT     => inl _ (bop_product_right_constant S T rS rT bS bT PS PT)
         | inr nPT => inr _ (bop_product_not_right_constant_right S T rS rT bS bT s nPT)
         end 
       | inr nPS   => inr _ (bop_product_not_right_constant_left S T rS rT bS bT t nPS)
       end
   end. 


(* 
Definition bop_product_right_constant_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_right_constant_decidable_new S rS bS -> 
     bop_right_constant_decidable_new T rT bT -> 
     bop_right_constant_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [[s Ps] [f Pf]] [[t Pt] [g Pg]] [wS PS] [wT PT]. 
       exists (check_right_constant_product_new S T s t wS wT). 
       destruct wS as [ LS | [s1 [s2 s3]]]; destruct wT as [ LT | [t1 [t2 t3]] ]; simpl. 
           apply bop_product_right_constant; auto. 
           rewrite PT. rewrite andb_comm. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
           rewrite PS. simpl. reflexivity. 
Defined. 
*) 

Definition bop_product_anti_left_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     bop_anti_left_decidable S rS bS -> 
     bop_anti_left_decidable T rT bT -> 
     bop_anti_left_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT dS dT,  
   match dS with 
   | inl PS => inl _ (bop_product_anti_left S T rS rT bS bT (inl _ PS))
   | inr nPS   => 
     match dT with 
     | inl PT     => inl _ (bop_product_anti_left S T rS rT bS bT (inr _ PT))
     | inr nPT => inr _ (bop_product_not_anti_left S T rS rT bS bT nPS nPT)
     end 
   end. 


(* 

Definition bop_product_anti_left_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     bop_anti_left_decidable_new S rS bS -> 
     bop_anti_left_decidable_new T rT bT -> 
     bop_anti_left_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [wS PS] [wT PT]. 
       exists (check_anti_left_product_new S T wS wT). 
       destruct wS as [ LS | [s1 s2]]; destruct wT as [ LT | [t1 t2] ]; simpl. 
           apply bop_product_anti_left; auto. 
           apply bop_product_anti_left; auto. 
           apply bop_product_anti_left; auto. 
           rewrite PS, PT. simpl. reflexivity. 
Defined. 
*) 

Definition bop_product_anti_right_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     bop_anti_right_decidable S rS bS -> 
     bop_anti_right_decidable T rT bT -> 
     bop_anti_right_decidable (S * T) (brel_product S T rS rT) (bop_product S T bS bT)
:= λ S T rS rT bS bT dS dT,  
   match dS with 
   | inl PS => inl _ (bop_product_anti_right S T rS rT bS bT (inl _ PS))
   | inr nPS   => 
     match dT with 
     | inl PT     => inl _ (bop_product_anti_right S T rS rT bS bT (inr _ PT))
     | inr nPT => inr _ (bop_product_not_anti_right S T rS rT bS bT nPS nPT)
     end 
   end. 

(* 
Definition bop_product_anti_right_decide_new : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     bop_anti_right_decidable_new S rS bS -> 
     bop_anti_right_decidable_new T rT bT -> 
     bop_anti_right_decidable_new (S * T) (brel_product S T rS rT) (bop_product S T bS bT). 
Proof. intros S T rS rT bS bT [wS PS] [wT PT]. 
       exists (check_anti_right_product_new S T wS wT). 
       destruct wS as [ LS | [s1 s2]]; destruct wT as [ LT | [t1 t2] ]; simpl. 
           apply bop_product_anti_right; auto. 
           apply bop_product_anti_right; auto. 
           apply bop_product_anti_right; auto. 
           rewrite PS, PT. simpl. reflexivity. 
Defined. 


*) 


(* llex *)

Definition bop_llex_idempotent_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_witness S rS →  
     brel_witness T rT →  
     brel_reflexive S rS → 
     brel_reflexive T rT → 
     bop_idempotent_decidable S rS bS → 
     bop_idempotent_decidable T rT bT →  
     bop_idempotent_decidable (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT ntS ntT refS refT dS dT,  
     match ntS,  ntT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_llex_idempotent S T rS rT bS bT refS refT commS commT)
         | inr not_commT => inr _ (bop_llex_not_idempotent_right S T rS rT bS bT s refS not_commT)
         end 
       | inr not_commS   => inr _ (bop_llex_not_idempotent_left S T rS rT bS bT t not_commS)
       end
   end. 



Definition bop_llex_commutative_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_witness S rS →  
     brel_witness T rT → 
     brel_congruence S rS rS → 
     brel_reflexive S rS → 
     brel_symmetric S rS → 
     brel_transitive S rS → 
     brel_reflexive T rT → 
     bop_selective S rS bS → 
     bop_commutative_decidable S rS bS → 
     bop_commutative_decidable T rT bT → 
     bop_commutative_decidable (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT ntS ntT congS refS symS transS refT selS dS dT,  
     match ntS,  ntT with 
     | existT s _, existT t _ => 
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_llex_commutative S T rS rT bS bT congS refS symS transS refT selS commS commT)
         | inr not_commT => inr _ (bop_llex_not_commutative_right S T rS rT bS bT s refS not_commT)
         end 
       | inr not_commS   => inr _ (bop_llex_not_commutative_left S T rS rT bS bT t not_commS)
       end
   end. 




Definition bop_llex_selective_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_witness S rS -> 
     brel_reflexive S rS → 
     brel_symmetric S rS → 
     brel_transitive S rS →
     brel_congruence S rS rS → 
     bop_congruence S rS bS → 
     bop_commutative S rS bS → 
     bop_selective S rS bS → 
     brel_reflexive T rT →  
     bop_selective_decidable T rT bT  → 
     bop_selective_decidable (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT ntS refS symS transS r_cong b_cong commS selS refT d_selT, 
   match ntS with 
   | existT s _ => 
     match d_selT with 
     | inl selT => inl _ (bop_llex_selective S T rS rT bS bT refS symS transS refT r_cong b_cong commS selS selT)
     | inr not_selT => inr _ (bop_llex_not_selective S T rS rT bS bT s refS selS not_selT)
     end 
   end. 


Definition bop_llex_exists_id_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT : binary_op T), 
     brel_reflexive S rS -> 
     brel_symmetric S rS -> 
     brel_transitive S rS -> 
     brel_reflexive T rT -> 
     bop_commutative S rS bS -> 
     bop_exists_id_decidable S rS bS -> 
     bop_exists_id_decidable T rT bT -> 
     bop_exists_id_decidable (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT refS symS transS refT commS dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_llex_exists_id S T rS rT bS bT symS transS refT eS eT commS)
         | inr neT => inr _ (bop_llex_not_exists_id_right S T rS rT bS bT refS neT)
         end 
       | inr neS   => inr _ (bop_llex_not_exists_id_left S T rS rT bS bT refS neS)
       end. 

Definition bop_llex_exists_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT : binary_op T), 
     brel_reflexive S rS -> 
     brel_symmetric S rS -> 
     brel_transitive S rS -> 
     brel_reflexive T rT -> 
     bop_commutative S rS bS -> 
     bop_exists_ann_decidable S rS bS -> 
     bop_exists_ann_decidable T rT bT -> 
     bop_exists_ann_decidable (S * T) (brel_product S T rS rT) (bop_llex S T rS bS bT)
:= λ S T rS rT bS bT refS symS transS refT commS dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_llex_exists_ann S T rS rT bS bT symS transS refT eS eT commS)
         | inr neT => inr _ (bop_llex_not_exists_ann_right S T rS rT bS bT refS neT)
         end 
       | inr neS   => inr _ (bop_llex_not_exists_ann_left S T rS rT bS bT refS neS)
       end. 


(* sums *) 
(* right sum *) 

Definition bop_left_sum_idempotent_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     bop_idempotent_decidable S rS bS  → 
     bop_idempotent_decidable T rT bT  → 
     bop_idempotent_decidable (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_left_sum_idempotent S T rS rT bS bT commS commT)
     | inr not_commT => inr _ (bop_left_sum_not_idempotent_right S T rS rT bS bT not_commT)
     end 
   | inr not_commS   => inr _ (bop_left_sum_not_idempotent_left S T rS rT bS bT not_commS)
   end. 


Definition bop_left_sum_commutative_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_reflexive S rS → 
     bop_commutative_decidable S rS bS  → 
     bop_commutative_decidable T rT bT  → 
     bop_commutative_decidable (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT ref dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_left_sum_commutative S T rS rT bS bT ref commS commT)
     | inr not_commT => inr _ (bop_left_sum_not_commutative_right S T rS rT bS bT not_commT)
     end 
   | inr not_commS   => inr _ (bop_left_sum_not_commutative_left S T rS rT bS bT not_commS)
   end. 

Definition bop_left_sum_selective_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_reflexive S rS → 
     bop_selective_decidable S rS bS  → 
     bop_selective_decidable T rT bT  → 
     bop_selective_decidable (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT ref dS dT,  
   match dS with 
   | inl selS => 
     match dT with 
     | inl selT     => inl _ (bop_left_sum_selective S T rS rT bS bT ref selS selT)
     | inr not_selT => inr _ (bop_left_sum_not_selective_right S T rS rT bS bT not_selT)
     end 
   | inr not_selS   => inr _ (bop_left_sum_not_selective_left S T rS rT bS bT not_selS)
   end. 

Definition bop_left_sum_exists_id_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial T rT -> 
     brel_reflexive S rS → 
     bop_exists_id_decidable T rT bT  → 
     bop_exists_id_decidable (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT ntT ref dT,  
   let t := brel_get_nontrivial_witness T rT ntT in 
   match dT with 
   | inl eid  => inl _ (bop_left_sum_exists_id S T rS rT ref bS bT eid)
   | inr neid => inr _ (bop_left_sum_not_exists_id S T t rS rT bS bT neid)
   end. 


Definition bop_left_sum_exists_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_reflexive S rS → 
     bop_exists_ann_decidable S rS bS  → 
     bop_exists_ann_decidable (S + T) (brel_sum S T rS rT) (bop_left_sum S T bS bT)
:= λ S T rS rT bS bT ntS ref dS,  
   let s := brel_get_nontrivial_witness S rS ntS in 
   match dS with 
   | inl eann  => inl _ (bop_left_sum_exists_ann S T rS rT ref bS bT eann)
   | inr neann => inr _ (bop_left_sum_not_exists_ann S T s rS rT ref bS bT neann)
   end. 

(* right sum *) 


Definition bop_right_sum_idempotent_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     bop_idempotent_decidable S rS bS  → 
     bop_idempotent_decidable T rT bT  → 
     bop_idempotent_decidable (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_right_sum_idempotent S T rS rT bS bT commS commT)
     | inr not_commT => inr _ (bop_right_sum_not_idempotent_right S T rS rT bS bT not_commT)
     end 
   | inr not_commS   => inr _ (bop_right_sum_not_idempotent_left S T rS rT bS bT not_commS)
   end. 


Definition bop_right_sum_commutative_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_reflexive T rT → 
     bop_commutative_decidable S rS bS  → 
     bop_commutative_decidable T rT bT  → 
     bop_commutative_decidable (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT ref dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_right_sum_commutative S T rS rT bS bT ref commS commT)
     | inr not_commT => inr _ (bop_right_sum_not_commutative_right S T rS rT bS bT not_commT)
     end 
   | inr not_commS   => inr _ (bop_right_sum_not_commutative_left S T rS rT bS bT not_commS)
   end. 

Definition bop_right_sum_selective_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_reflexive T rT → 
     bop_selective_decidable S rS bS  → 
     bop_selective_decidable T rT bT  → 
     bop_selective_decidable (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT ref dS dT,  
   match dS with 
   | inl selS => 
     match dT with 
     | inl selT     => inl _ (bop_right_sum_selective S T rS rT bS bT ref selS selT)
     | inr not_selT => inr _ (bop_right_sum_not_selective_right S T rS rT bS bT not_selT)
     end 
   | inr not_selS   => inr _ (bop_right_sum_not_selective_left S T rS rT bS bT not_selS)
   end. 


Definition bop_right_sum_exists_id_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial S rS -> 
     brel_reflexive T rT → 
     bop_exists_id_decidable S rS bS  → 
     bop_exists_id_decidable (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT ntS ref dS,  
   let s := brel_get_nontrivial_witness S rS ntS in 
   match dS with 
   | inl eid  => inl _ (bop_right_sum_exists_id S T rS rT ref bS bT eid)
   | inr neid => inr _ (bop_right_sum_not_exists_id S T s rS rT bS bT neid)
   end. 



Definition bop_right_sum_exists_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (bS : binary_op S) 
     (bT: binary_op T), 
     brel_nontrivial T rT -> 
     brel_reflexive T rT → 
     bop_exists_ann_decidable T rT bT  → 
     bop_exists_ann_decidable (S + T) (brel_sum S T rS rT) (bop_right_sum S T bS bT)
:= λ S T rS rT bS bT ntT ref dT,  
   let t := brel_get_nontrivial_witness T rT ntT in 
   match dT with 
   | inl eann  => inl _ (bop_right_sum_exists_ann S T rS rT ref bS bT eann)
   | inr neann => inr _ (bop_right_sum_not_exists_ann S T t rS rT ref bS bT neann)
   end. 


(* ******************************** *)


Definition bop_product_left_distributive_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_left_distributive_decidable S rS addS mulS -> 
     bop_left_distributive_decidable T rT addT mulT -> 
     bop_left_distributive_decidable (S * T) 
         (brel_product S T rS rT) 
         (bop_product S T addS addT)
         (bop_product S T mulS mulT)
:= λ S T rS rT addS mulS addT mulT ntS ntT dS dT,  
  let wS := brel_nontrivial_witness S rS ntS in   
  let wT := brel_nontrivial_witness T rT ntT in 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (bop_product_left_distributive S T rS rT addS mulS addT mulT ldS ldT)
     | inr nldT => inr _ (bop_product_not_left_distributive_right S T rS rT addS mulS addT mulT wS nldT)
     end 
   | inr nldS   => inr _ (bop_product_not_left_distributive_left S T rS rT addS mulS addT mulT wT nldS)
   end. 

Definition bop_product_right_distributive_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
     brel_nontrivial S rS -> 
     brel_nontrivial T rT -> 
     bop_right_distributive_decidable S rS addS mulS -> 
     bop_right_distributive_decidable T rT addT mulT -> 
       bop_right_distributive_decidable (S * T) 
         (brel_product S T rS rT) 
         (bop_product S T addS addT)
         (bop_product S T mulS mulT)
:= λ S T rS rT addS mulS addT mulT ntS ntT dS dT,  
  let wS := brel_nontrivial_witness S rS ntS in   
  let wT := brel_nontrivial_witness T rT ntT in 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (bop_product_right_distributive S T rS rT addS mulS addT mulT ldS ldT)
     | inr nldT => inr _ (bop_product_not_right_distributive_right S T rS rT addS mulS addT mulT wS nldT)
     end 
   | inr nldS   => inr _ (bop_product_not_right_distributive_left S T rS rT addS mulS addT mulT wT nldS)
   end. 
       
Definition bop_product_id_equals_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_id_equals_ann_decidable S rS addS mulS → 
      bops_id_equals_ann_decidable T rT addT mulT →  
        bops_id_equals_ann_decidable (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T addS addT)
           (bop_product S T mulS mulT)
:= λ S T rS rT addS mulS addT mulT dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bop_product_id_equals_ann S T rS rT addS mulS addT mulT ieaS ieaT)
     | inr nieaT => inr _ (bop_product_not_id_equals_ann_right S T rS rT addS mulS addT mulT nieaT)
     end 
   | inr nieaS   => inr _ (bop_product_not_id_equals_ann_left S T rS rT addS mulS addT mulT nieaS)
   end. 


Definition bop_product_id_equals_id_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_id_equals_id_decidable S rS addS mulS → 
      bops_id_equals_id_decidable T rT addT mulT →  
        bops_id_equals_id_decidable (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T addS addT)
           (bop_product S T mulS mulT)
:= λ S T rS rT addS mulS addT mulT dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bop_product_id_equals_id S T rS rT addS mulS addT mulT ieaS ieaT)
     | inr nieaT => inr _ (bop_product_not_id_equals_id_right S T rS rT addS mulS addT mulT nieaT)
     end 
   | inr nieaS   => inr _ (bop_product_not_id_equals_id_left S T rS rT addS mulS addT mulT nieaS)
   end. 

Definition bop_product_ann_equals_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_ann_equals_ann_decidable S rS addS mulS → 
      bops_ann_equals_ann_decidable T rT addT mulT →  
        bops_ann_equals_ann_decidable (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T addS addT)
           (bop_product S T mulS mulT)
:= λ S T rS rT addS mulS addT mulT dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bop_product_ann_equals_ann S T rS rT addS mulS addT mulT ieaS ieaT)
     | inr nieaT => inr _ (bop_product_not_ann_equals_ann_right S T rS rT addS mulS addT mulT nieaT)
     end 
   | inr nieaS   => inr _ (bop_product_not_ann_equals_ann_left S T rS rT addS mulS addT mulT nieaS)
   end. 


Definition bops_product_left_left_absorptive_decide : 
   ∀ (S T : Type) 
     (s : S) 
     (t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_left_left_absorptive_decidable S rS addS mulS → 
      bops_left_left_absorptive_decidable T rT addT mulT → 
         bops_left_left_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product  _ _ addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T s t rS rT addS mulS addT mulT laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  
       inl _ (bop_product_left_left_absorptive S T rS rT addS mulS addT mulT laS laT)
   |inr not_laT => 
       inr _ (bop_product_not_left_left_absorptive_right S T rS rT addS mulS addT mulT s not_laT) 
   end 
|inr not_laS => 
      inr _ (bop_product_not_left_left_absorptive_left S T rS rT addS mulS addT mulT t not_laS ) 
end. 


Definition bops_product_left_right_absorptive_decide : 
   ∀ (S T : Type) 
     (s : S) 
     (t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_left_right_absorptive_decidable S rS addS mulS → 
      bops_left_right_absorptive_decidable T rT addT mulT → 
         bops_left_right_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product  _ _ addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T s t rS rT addS mulS addT mulT laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  
       inl _ (bop_product_left_right_absorptive S T rS rT addS mulS addT mulT laS laT)
   |inr not_laT => 
       inr _ (bop_product_not_left_right_absorptive_right S T rS rT addS mulS addT mulT s not_laT) 
   end 
|inr not_laS => 
      inr _ (bop_product_not_left_right_absorptive_left S T rS rT addS mulS addT mulT t not_laS ) 
end. 

Definition bops_product_right_left_absorptive_decide : 
   ∀ (S T : Type) 
     (s : S) 
     (t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_right_left_absorptive_decidable S rS addS mulS → 
      bops_right_left_absorptive_decidable T rT addT mulT → 
         bops_right_left_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product  _ _ addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T s t rS rT addS mulS addT mulT laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  
       inl _ (bop_product_right_left_absorptive S T rS rT addS mulS addT mulT laS laT)
   |inr not_laT => 
       inr _ (bop_product_not_right_left_absorptive_right S T rS rT addS mulS addT mulT s not_laT) 
   end 
|inr not_laS => 
      inr _ (bop_product_not_right_left_absorptive_left S T rS rT addS mulS addT mulT t not_laS ) 
end. 


Definition bops_product_right_right_absorptive_decide : 
   ∀ (S T : Type) 
     (s : S) 
     (t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      bops_right_right_absorptive_decidable S rS addS mulS → 
      bops_right_right_absorptive_decidable T rT addT mulT → 
         bops_right_right_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_product  _ _ addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T s t rS rT addS mulS addT mulT laS_d laT_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     =>  
       inl _ (bop_product_right_right_absorptive S T rS rT addS mulS addT mulT laS laT)
   |inr not_laT => 
       inr _ (bop_product_not_right_right_absorptive_right S T rS rT addS mulS addT mulT s not_laT) 
   end 
|inr not_laS => 
      inr _ (bop_product_not_right_right_absorptive_left S T rS rT addS mulS addT mulT t not_laS ) 
end. 




(* llex *) 

Definition bops_llex_product_left_distributive_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_witness S rS → 
      brel_reflexive S rS  → 
      brel_symmetric S rS  →  
      brel_transitive S rS  →  
      bop_congruence S rS mulS  →  
      bop_selective S rS addS  →      (* NB *) 
      bop_commutative S rS addS  →    (* NB *) 
      brel_nontrivial T rT → 
      brel_reflexive T rT  → 
      brel_symmetric T rT  →          
      brel_transitive T rT  → 
      bop_commutative T rT addT  →    (* NB *) 
      bop_left_cancellative_decidable S rS mulS  → 
      bop_left_constant_decidable T rT mulT → 
      bop_left_distributive_decidable S rS addS mulS → 
      bop_left_distributive_decidable T rT addT mulT → 
         bop_left_distributive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T rS rT addS mulS addT mulT wtS refS symS transS mulS_cong selS commS 
   ntT refT symT transT commT lcS_d lkT_d ldS_d ldT_d, 
match ldS_d with 
|inl ldS =>
   match ldT_d with 
   |inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (bop_llex_product_left_distributive
                           S T rS rT addS mulS addT mulT refS symS transS 
                           mulS_cong refT transT ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_llex_product_left_distributive
                           S T rS rT addS mulS addT mulT refS symS transS 
                           mulS_cong refT transT ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_llex_product_not_left_distributive_v3 
                                     S T rS rT addS mulS addT mulT symS transS selS 
                                     commS symT transT commT  not_lcS not_lkT)
            end 
       end 
   |inr not_ldT => inr _ (bop_llex_product_not_left_distributive_v2 
                            S T rS rT addS mulS addT mulT wtS refS not_ldT)
   end 
|inr not_ldS => inr _ (bop_llex_product_not_left_distributive_v1 
                        S T rS rT addS mulS addT mulT (brel_nontrivial_witness T rT ntT) not_ldS ) 
end. 

Definition bops_llex_product_right_distributive_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_witness S rS → 
      brel_reflexive S rS  → 
      brel_symmetric S rS  →  
      brel_transitive S rS  →  
      bop_congruence S rS mulS  →  
      bop_selective S rS addS  →      (* NB *) 
      bop_commutative S rS addS  →    (* NB *) 
      brel_nontrivial T rT → 
      brel_reflexive T rT  → 
      brel_symmetric T rT  →          
      brel_transitive T rT  → 
      bop_commutative T rT addT  →    (* NB *) 
      bop_right_cancellative_decidable S rS mulS  → 
      bop_right_constant_decidable T rT mulT → 
      bop_right_distributive_decidable S rS addS mulS → 
      bop_right_distributive_decidable T rT addT mulT → 
         bop_right_distributive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T rS rT addS mulS addT mulT wtS refS symS transS mulS_cong selS commS 
   ntT refT symT transT commT lcS_d lkT_d ldS_d ldT_d, 
match ldS_d with 
|inl ldS =>
   match ldT_d with 
   |inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (bop_llex_product_right_distributive
                           S T rS rT addS mulS addT mulT refS symS transS 
                           mulS_cong refT transT ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_llex_product_right_distributive
                           S T rS rT addS mulS addT mulT refS symS transS 
                           mulS_cong refT transT ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_llex_product_not_right_distributive_v3 
                                     S T rS rT addS mulS addT mulT symS transS selS 
                                     commS symT transT commT  not_lcS not_lkT)
            end 
       end 
   |inr not_ldT => inr _ (bop_llex_product_not_right_distributive_v2 
                            S T rS rT addS mulS addT mulT wtS refS not_ldT)
   end 
|inr not_ldS => inr _ (bop_llex_product_not_right_distributive_v1 
                        S T rS rT addS mulS addT mulT (brel_nontrivial_witness T rT ntT) not_ldS ) 
end. 


Definition bops_llex_product_id_equals_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS →
      bop_commutative S rS addS  →
      brel_reflexive T rT →  
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bops_id_equals_ann_decidable S rS addS mulS → 
      bops_id_equals_ann_decidable T rT addT mulT →  
        bops_id_equals_ann_decidable (S * T) 
           (brel_product S T rS rT) 
           (bop_llex S T rS addS addT)
           (bop_product S T mulS mulT)
:= λ S T rS rT addS mulS addT mulT refS symS transS commS refT symT transT dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bops_llex_product_id_equals_ann 
                               S T rS rT addS mulS addT mulT refS symS transS refT symT transT commS ieaS ieaT)
     | inr nieaT => inr _ (bops_llex_product_not_id_equals_ann_right 
                               S T rS rT addS mulS addT mulT refS nieaT)
     end 
   | inr nieaS   => inr _ (bops_llex_product_not_id_equals_ann_left 
                               S T rS rT addS mulS addT mulT nieaS)
   end. 

Definition bops_product_llex_id_equals_ann_decide : 
   ∀ (S T : Type) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_reflexive S rS → 
      brel_symmetric S rS → 
      brel_transitive S rS →
      bop_commutative S rS addS  →
      brel_reflexive T rT →  
      brel_symmetric T rT → 
      brel_transitive T rT → 
      bops_id_equals_ann_decidable S rS mulS addS  → 
      bops_id_equals_ann_decidable T rT mulT addT  →  
        bops_id_equals_ann_decidable (S * T) 
           (brel_product S T rS rT) 
           (bop_product S T mulS mulT)
           (bop_llex S T rS addS addT)
:= λ S T rS rT addS mulS addT mulT refS symS transS commS refT symT transT dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bops_product_llex_id_equals_ann 
                               S T rS rT addS mulS addT mulT refS symS transS refT symT transT commS ieaS ieaT)
     | inr nieaT => inr _ (bops_product_llex_not_id_equals_ann_right 
                               S T rS rT addS mulS addT mulT refS nieaT)
     end 
   | inr nieaS   => inr _ (bops_product_llex_not_id_equals_ann_left 
                               S T rS rT addS mulS addT mulT nieaS)
   end. 

(*
 LA(S) -> 
          LA(T) -> (LA(T) | nQ) -> LA(lex, product) 
          nLA(T) -> 
             nQ  -> (LA(T) | nQ) -> LA(lex, product) 
              Q -> (nLA(T) & Q) -> nLA(lex, product) 
nLA(S) -> nLA(lex, product) 

*)

Definition bops_llex_product_left_left_absorptive_decide : 
   ∀ (S T : Type) 
     ( t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_symmetric S rS  →  
      brel_transitive S rS  →  
      brel_reflexive T rT  → 
      bops_left_left_absorptive_decidable S rS addS mulS → 
      bops_left_left_absorptive_decidable T rT addT mulT → 
      bop_anti_left_decidable S rS mulS → 
         bops_left_left_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T t rS rT addS mulS addT mulT symS tranS refT laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_left_left_absorptive 
                          S T rS rT addS mulS addT mulT refT laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_left_left_absorptive 
                                    S T rS rT addS mulS addT mulT refT laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_left_left_absorptive_right
                            S T rS rT addS mulS addT mulT not_antilS symS tranS laS not_laT)
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_left_left_absorptive_left 
                          S T rS rT addS mulS addT mulT t not_laS ) 
end. 



Definition bops_llex_product_left_right_absorptive_decide : 
   ∀ (S T : Type) 
     ( t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_symmetric S rS  →  
      brel_transitive S rS  →  
      brel_reflexive T rT  → 
      bops_left_right_absorptive_decidable S rS addS mulS → 
      bops_left_right_absorptive_decidable T rT addT mulT → 
      bop_anti_right_decidable S rS mulS → 
         bops_left_right_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T t rS rT addS mulS addT mulT symS tranS refT laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_left_right_absorptive 
                          S T rS rT addS mulS addT mulT refT laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_left_right_absorptive 
                                    S T rS rT addS mulS addT mulT refT laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_left_right_absorptive_right
                            S T rS rT addS mulS addT mulT not_antilS symS tranS laS not_laT)
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_left_right_absorptive_left 
                          S T rS rT addS mulS addT mulT t not_laS ) 
end. 



Definition bops_llex_product_right_left_absorptive_decide : 
   ∀ (S T : Type) 
     ( t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_symmetric S rS  →  
      brel_transitive S rS  →  
      brel_reflexive T rT  → 
      bops_right_left_absorptive_decidable S rS addS mulS → 
      bops_right_left_absorptive_decidable T rT addT mulT → 
      bop_anti_left_decidable S rS mulS → 
         bops_right_left_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T t rS rT addS mulS addT mulT symS tranS refT laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_right_left_absorptive 
                          S T rS rT addS mulS addT mulT refT symS tranS laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_right_left_absorptive 
                                    S T rS rT addS mulS addT mulT refT symS tranS laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_right_left_absorptive_right
                            S T rS rT addS mulS addT mulT not_antilS symS tranS laS not_laT)
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_right_left_absorptive_left 
                          S T rS rT addS mulS addT mulT t not_laS ) 
end. 


Definition bops_llex_product_right_right_absorptive_decide : 
   ∀ (S T : Type) 
     ( t : T) 
     (rS : brel S) 
     (rT : brel T) 
     (addS mulS : binary_op S) 
     (addT mulT : binary_op T), 
      brel_symmetric S rS  →  
      brel_transitive S rS  →  
      brel_reflexive T rT  → 
      bops_right_right_absorptive_decidable S rS addS mulS → 
      bops_right_right_absorptive_decidable T rT addT mulT → 
      bop_anti_right_decidable S rS mulS → 
         bops_right_right_absorptive_decidable (S * T) 
             (brel_product _ _ rS rT) 
             (bop_llex  _ _ rS addS addT)
             (bop_product _ _ mulS mulT)
:= λ S T t rS rT addS mulS addT mulT symS tranS refT laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_right_right_absorptive 
                          S T rS rT addS mulS addT mulT refT laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_right_right_absorptive 
                                    S T rS rT addS mulS addT mulT refT laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_right_right_absorptive_right
                            S T rS rT addS mulS addT mulT not_antilS symS tranS laS not_laT)
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_right_right_absorptive_left 
                          S T rS rT addS mulS addT mulT t not_laS ) 
end. 





(* add zero *)


Definition bops_add_zero_ann_equals_id_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (s : S)
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bops_id_equals_ann_decidable S rS mulS addS -> 
     bops_id_equals_ann_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S mulS c) 
        (bop_add_id S addS c)
:= λ S rS s c addS mulS refS dS, 
   match dS with 
   | inl pS  => inl _ (bops_add_id_add_ann_ann_equals_id S rS c addS mulS refS pS)
   | inr npS => inr _ (bops_add_id_add_ann_not_ann_equals_id S rS s c addS mulS npS)
   end. 


Definition bops_add_zero_left_distributive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bop_left_distributive_decidable S rS addS mulS -> 
     bop_left_distributive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_id S addS c) 
        (bop_add_ann S mulS c)
:= λ S rS c addS mulS refS dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_distributive S rS c addS mulS refS ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_distributive S rS c addS mulS nldS)
   end. 

Definition bops_add_zero_right_distributive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bop_right_distributive_decidable S rS addS mulS -> 
     bop_right_distributive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_id S addS c) 
        (bop_add_ann S mulS c)
:= λ S rS c addS mulS refS dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_distributive S rS c addS mulS refS ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_distributive S rS c addS mulS nldS)
   end. 


Definition bops_add_zero_left_left_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S)  
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bops_left_left_absorptive_decidable S rS addS mulS -> 
     bops_left_left_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_id S addS c) 
        (bop_add_ann S mulS c)
:= λ S rS c addS mulS refS dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_left_absorptive S rS c addS mulS refS ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_left_absorptive S rS c addS mulS nldS)
   end. 


Definition bops_add_zero_left_right_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bops_left_right_absorptive_decidable S rS addS mulS -> 
     bops_left_right_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_id S addS c) 
        (bop_add_ann S mulS c)
:= λ S rS c addS mulS refS dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_left_right_absorptive S rS c addS mulS refS ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_left_right_absorptive S rS c addS mulS nldS)
   end. 


Definition bops_add_zero_right_left_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S)  
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bops_right_left_absorptive_decidable S rS addS mulS -> 
     bops_right_left_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_id S addS c) 
        (bop_add_ann S mulS c)
:= λ S rS c addS mulS refS dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_left_absorptive S rS c addS mulS refS ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_left_absorptive S rS c addS mulS nldS)
   end. 


Definition bops_add_zero_right_right_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S)  
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bops_right_right_absorptive_decidable S rS addS mulS -> 
     bops_right_right_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_id S addS c) 
        (bop_add_ann S mulS c)
:= λ S rS c addS mulS refS dS, 
   match dS with 
   | inl ldS  => inl _ (bops_add_id_add_ann_right_right_absorptive S rS c addS mulS refS ldS)
   | inr nldS => inr _ (bops_add_id_add_ann_not_right_right_absorptive S rS c addS mulS nldS)
   end. 



(* add one *) 

Definition bops_add_one_id_equals_ann_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (s : S)
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     bops_id_equals_ann_decidable S rS addS mulS -> 
     bops_id_equals_ann_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS s c addS mulS refS dS, 
   match dS with 
   | inl pS  => inl _ (bops_add_id_add_ann_ann_equals_id S rS c mulS addS refS pS)
   | inr npS => inr _ (bops_add_id_add_ann_not_ann_equals_id S rS s c mulS addS npS)
   end. 


Definition bops_add_one_left_distributive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     brel_symmetric S rS -> 
     bop_idempotent_decidable S rS addS -> 
     bops_left_left_absorptive_decidable S rS addS mulS -> 
     bops_right_left_absorptive_decidable S rS addS mulS -> 
     bop_left_distributive_decidable S rS addS mulS -> 
     bop_left_distributive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS c addS mulS refS symS idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | inl ldS  => 
    match llaS_d with 
    | inl llaS   => 
      match rlaS_d with 
      | inl rlaS   => 
         match idemS_d with 
         | inl idemS   => inl _ (bops_add_ann_add_id_left_distributive S rS c addS mulS 
                                 refS symS idemS llaS rlaS ldS)
         | inr nidemS  => inr _ (bops_add_ann_add_id_not_left_distributive_v2 S rS c addS mulS symS nidemS)
        end 
      | inr nrlaS   => inr _ (bops_add_ann_add_id_not_left_distributive_v4 S rS c addS mulS nrlaS)
      end 
    | inr nllaS  => inr _ (bops_add_ann_add_id_not_left_distributive_v3 S rS c addS mulS nllaS)
    end 
   | inr nldS => inr _ (bops_add_ann_add_id_not_left_distributive_v1 S rS c addS mulS nldS)
   end. 




Definition bops_add_one_right_distributive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_reflexive S rS -> 
     brel_symmetric S rS -> 
     bop_idempotent_decidable S rS addS -> 
     bops_left_right_absorptive_decidable S rS addS mulS -> 
     bops_right_right_absorptive_decidable S rS addS mulS -> 
     bop_right_distributive_decidable S rS addS mulS -> 
     bop_right_distributive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS c addS mulS refS symS idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | inl ldS  => 
    match llaS_d with 
    | inl llaS   => 
      match rlaS_d with 
      | inl rlaS   => 
         match idemS_d with 
         | inl idemS   => inl _ (bops_add_ann_add_id_right_distributive S rS c addS mulS 
                                 refS symS idemS llaS rlaS ldS)
         | inr nidemS  => inr _ (bops_add_ann_add_id_not_right_distributive_v2 S rS c addS mulS symS nidemS)
        end 
      | inr nrlaS   => inr _ (bops_add_ann_add_id_not_right_distributive_v4 S rS c addS mulS nrlaS)
      end 
    | inr nllaS  => inr _ (bops_add_ann_add_id_not_right_distributive_v3 S rS c addS mulS nllaS)
    end 
   | inr nldS => inr _ (bops_add_ann_add_id_not_right_distributive_v1 S rS c addS mulS nldS)
   end. 


Definition bops_add_one_left_left_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_symmetric S rS -> 
     bop_idempotent_decidable S rS addS -> 
     bops_left_left_absorptive_decidable S rS addS mulS -> 
     bops_left_left_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS c addS mulS symS idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_left_left_absorptive S rS c addS mulS symS idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_left_left_absorptive_v1 S rS c addS mulS 
                             symS nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_left_left_absorptive_v2 S rS c addS mulS nlaS)
   end. 


Definition bops_add_one_left_right_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_symmetric S rS -> 
     bop_idempotent_decidable S rS addS -> 
     bops_left_right_absorptive_decidable S rS addS mulS -> 
     bops_left_right_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS c addS mulS symS idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_left_right_absorptive S rS c addS mulS symS idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_left_right_absorptive_v1 S rS c addS mulS 
                             symS nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_left_right_absorptive_v2 S rS c addS mulS nlaS)
   end. 

Definition bops_add_one_right_left_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_symmetric S rS -> 
     bop_idempotent_decidable S rS addS -> 
     bops_right_left_absorptive_decidable S rS addS mulS -> 
     bops_right_left_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS c addS mulS symS idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_right_left_absorptive S rS c addS mulS symS idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_right_left_absorptive_v1 S rS c addS mulS 
                             symS nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_right_left_absorptive_v2 S rS c addS mulS nlaS)
   end. 


Definition bops_add_one_right_right_absorptive_decide : 
   ∀ (S : Type) 
     (rS : brel S) 
     (c : cas_constant)
     (addS mulS : binary_op S),  
     brel_symmetric S rS -> 
     bop_idempotent_decidable S rS addS -> 
     bops_right_right_absorptive_decidable S rS addS mulS -> 
     bops_right_right_absorptive_decidable 
        (with_constant S) 
        (brel_add_constant S rS c) 
        (bop_add_ann S addS c) 
        (bop_add_id S mulS c)
:= λ S rS c addS mulS symS idemS_d laS_d, 
   match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl _ (bops_add_ann_add_id_right_right_absorptive S rS c addS mulS symS idemS laS)
     | inr nidemS => inr _ (bops_add_ann_add_id_not_right_right_absorptive_v1 S rS c addS mulS 
                             symS nidemS)
     end 
   | inr nlaS => inr _ (bops_add_ann_add_id_not_right_right_absorptive_v2 S rS c addS mulS nlaS)
   end. 











