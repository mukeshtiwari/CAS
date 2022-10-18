Require Import List ListSet PeanoNat Utf8
  Mergesort.
From CAS Require Import 
  coq.po.from_sg
  coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory.


Import ListNotations.


(* Find a library with proofs *)
Section Priority_Queue_Def.


  Definition Node := nat.
  
  Context 
    {T : Type} (* Type *)
    {eqT : brel T}
    {add : binary_op T}.

  Definition lte (a b : T * Node) :=
    (brel_lte_left eqT add) (fst a) (fst b).


  Fixpoint find_min_node 
    (m : T * Node)
    (carry : list (T * Node))
    (l : list (T * Node)) : (T * Node) * list (T * Node) :=
    match l with 
    | [] => (m, carry)
    | h :: l' => 
      if lte h m then find_min_node h (m :: carry) l' 
      else find_min_node m (h :: carry) l' 
    end. 

 
  Definition remove_min_pq 
    (pq : list (T * Node)) :
    option ((T * Node) * list (T * Node)) :=
  match pq with 
  | [] => None
  | h :: t => Some (find_min_node h [] t)
  end. 

End Priority_Queue_Def. (* End of Definitions *)
  
Section Priority_Queue_Proofs.

  Context 
    {T : Type}
    {add : T -> T -> T}
    {eqT : brel T}
    {refT : brel_reflexive T eqT}
    {symT : brel_symmetric T eqT}
    {trnT : brel_transitive T eqT}
    {commutative : forall (a b : T), 
      (eqT (add a b) (add b a)) = true}
    {add_sel : forall (a b : T), 
      ((eqT (add a b) a) = true) + ((eqT (add a b) b) = true)}.


End Priority_Queue_Proofs.