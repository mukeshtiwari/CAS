Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.po.properties.

Close Scope nat. 
(* order, semigroup *) 

Definition os_left_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b s t) (b s u) = true. 

Definition os_not_left_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b s t) (b s u) = false) end }. 

Definition os_left_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_monotone lte b) + (os_not_left_monotone lte b). 


Definition os_right_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b t s) (b u s) = true. 

Definition os_not_right_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b t s) (b u s) = false) end }. 

Definition os_right_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_monotone lte b) + (os_not_right_monotone lte b). 


Definition os_left_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b s t) = true. 

Definition os_not_left_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b s t) = false end }. 

Definition os_left_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_increasing lte b) + (os_not_left_increasing lte b). 


Definition os_right_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b t s) = true. 

Definition os_not_right_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b t s) = false end }. 

Definition os_right_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_increasing lte b) + (os_not_right_increasing lte b). 


Definition os_left_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, (lte s (b s t) = true) * (lte (b s t) s = false). 

Definition os_not_left_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => (lte s (b s t) = false) + (lte (b s t) s = true)  end }. 

Definition os_left_strictly_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_strictly_increasing lte b) + (os_not_left_strictly_increasing lte b). 


Definition os_right_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, (lte s (b t s) = true) * (lte (b t s) s = false). 

Definition os_not_right_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => (lte s (b t s) = false) + (lte (b t s) s = true)  end }. 

Definition os_right_strictly_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
  := (os_right_strictly_increasing lte b) + (os_not_right_strictly_increasing lte b).


Definition os_left_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := ∀ s t u : S, lte t u = true -> lte u t = false ->
                  (lte (b s t) (b s u) = true) * (lte (b s u) (b s t) = false). 

Definition os_not_left_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := { z : S * (S * S) & match z with (s, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (b s t) (b s u) = false) + (lte (b s u) (b s t) = true))end }. 

Definition os_left_strictly_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_strictly_monotone lte b) + (os_not_left_strictly_monotone lte b). 


Definition os_right_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte u t = false -> (lte (b t s) (b u s) = true) * (lte (b u s) (b t s) = false). 

Definition os_not_right_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := { z : S * (S * S) & match z with (s, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (b t s) (b u s) = false) + (lte (b u s) (b t s) = true)) end }. 

Definition os_right_strictly_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_strictly_monotone lte b) + (os_not_right_strictly_monotone lte b). 


(* do the following belong in po/properties.v ? *) 
Definition is_lower_bound {S : Type} (lte : brel S) (a b c : S) :=  
     (lte c a = true) *  (lte c b = true). 

Definition is_upper_bound {S : Type} (lte : brel S) (a b c : S) :=  
     (lte a c = true) *  (lte b c = true). 

Definition is_glb {S : Type} (lte : brel S) (a b c : S) :=  
      (is_lower_bound lte a b c) *
          (∀ u : S, (is_lower_bound lte a b u) -> lte u c = true). 

Definition is_lub {S : Type} (lte : brel S) (a b c : S) :=  
      (is_upper_bound lte a b c) *
      (∀ u : S, (is_upper_bound lte a b u) -> lte c u = true).

Definition bop_is_glb {S : Type} (lte : brel S) (b : binary_op S) :=  ∀ s t : S,  is_glb lte s t (b s t).

Definition bop_is_lub {S : Type} (lte : brel S) (b : binary_op S) :=  ∀ s t : S,  is_lub lte s t (b s t).

Definition exists_glb {S : Type} (lte : brel S) := {b : binary_op S &  bop_is_glb lte b}.

Definition exists_lub {S : Type} (lte : brel S) := {b : binary_op S &  bop_is_lub lte b}.  


(********************** Top, bottom vs id ann *****************************************)

(* quasi ordered *) 

Definition os_qo_exists_bottom_id_equal {S : Type} (r lte : brel S) (b : binary_op S)
:= { i : S & (brel_is_qo_bottom S r lte i) * (bop_is_id S r b i)}. 

(* partially ordered *)

(********************** bottom vs id *****************************************)

Definition os_exists_bottom_id_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { bot : S & (brel_is_bottom S lte bot) * (bop_is_id S r b bot)}.

Definition os_exists_bottom_id_not_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { z : S * S & match z with (bot, id) => (brel_is_bottom S lte bot) * (bop_is_id S r b id) * (r bot id = false) end}.

Definition extract_exist_bottom_from_exists_bottom_id_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_bottom_id_equal r lte b) : brel_exists_bottom S lte := 
  existT (λ x : S, brel_is_bottom S lte x) (projT1 P) (fst (projT2 P)).

Definition extract_exist_id_from_exists_bottom_id_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_bottom_id_equal r lte b) : bop_exists_id S r b := 
  existT (λ x : S, bop_is_id S r b x) (projT1 P) (snd (projT2 P)).

Definition extract_exist_bottom_from_exists_bottom_id_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  os_exists_bottom_id_not_equal r lte b) : brel_exists_bottom S lte :=
  match P with
  existT _ (i, a) p =>     
     existT (λ x : S, brel_is_bottom S lte x) i (fst (fst p))
  end. 

Definition extract_exist_id_from_exists_bottom_id_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  os_exists_bottom_id_not_equal r lte b) : bop_exists_id S r b :=
  match P with
  existT _ (bot, id) ((_, p), _) =>     
     existT (λ x : S, bop_is_id S r b x) id p
  end. 


Inductive os_exists_bottom_id_decidable (S : Type) (eq lte : brel S) (b : binary_op S)  : Type :=
| Bottom_Id_Proof_None        : (brel_not_exists_bottom S lte) * (bop_not_exists_id S eq b) -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_Bottom_None : (brel_exists_bottom S lte) * (bop_not_exists_id S eq b)     -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_None_Id     : (brel_not_exists_bottom S lte) * (bop_exists_id S eq b)     -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_Equal       : os_exists_bottom_id_equal eq lte b                          -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_Not_Equal   : os_exists_bottom_id_not_equal eq lte b                      -> os_exists_bottom_id_decidable S eq lte b.

Definition extract_exists_bottom_decidable_from_exists_bottom_id_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_bottom_id_decidable S r lte b) : brel_exists_bottom_decidable S lte :=
match P with
| Bottom_Id_Proof_None _ _ _ _ (no_bot, _)             => inr no_bot 
| Bottom_Id_Proof_Bottom_None  _ _ _ _ (exists_bot, _) => inl exists_bot 
| Bottom_Id_Proof_None_Id _ _ _ _ (no_bot, _)          => inr no_bot
| Bottom_Id_Proof_Equal _ _ _ _ bot_id_eq              => inl (extract_exist_bottom_from_exists_bottom_id_equal S r lte b bot_id_eq) 
| Bottom_Id_Proof_Not_Equal _ _ _ _ bot_id_not_eq      => inl (extract_exist_bottom_from_exists_bottom_id_not_equal S r lte b bot_id_not_eq) 
end.

Definition extract_exists_id_decidable_from_exists_bottom_id_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_bottom_id_decidable S r lte b) : bop_exists_id_decidable S r b :=
match P with
| Bottom_Id_Proof_None _ _ _ _ (_, no_id)          => inr no_id
| Bottom_Id_Proof_Bottom_None  _ _ _ _ (_, no_id)  => inr no_id
| Bottom_Id_Proof_None_Id _ _ _ _ (_, exists_id)   => inl exists_id
| Bottom_Id_Proof_Equal _ _ _ _ bot_id_eq          => inl (extract_exist_id_from_exists_bottom_id_equal S r lte b bot_id_eq) 
| Bottom_Id_Proof_Not_Equal _ _ _ _ bot_id_not_eq  => inl (extract_exist_id_from_exists_bottom_id_not_equal S r lte b bot_id_not_eq) 
end.


(********************** Top vs ann *****************************************)

Definition os_exists_top_ann_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { top : S & (brel_is_top S lte top) * (bop_is_ann S r b top)}.

Definition os_exists_top_ann_not_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { z : S * S & match z with (top, ann) => (brel_is_top S lte top) * (bop_is_ann S r b ann) * (r top ann = false) end}.

Definition extract_exist_top_from_exists_top_ann_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_top_ann_equal r lte b) : brel_exists_top S lte := 
  existT (λ x : S, brel_is_top S lte x) (projT1 P) (fst (projT2 P)).

Definition extract_exist_ann_from_exists_top_ann_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_top_ann_equal r lte b) : bop_exists_ann S r b := 
  existT (λ x : S, bop_is_ann S r b x) (projT1 P) (snd (projT2 P)).

Definition extract_exist_top_from_exists_top_ann_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  os_exists_top_ann_not_equal r lte b) : brel_exists_top S lte :=
  match P with
  existT _ (top, _) p =>     
     existT (λ x : S, brel_is_top S lte x) top (fst (fst p))
  end. 

Definition extract_exist_ann_from_exists_top_ann_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  os_exists_top_ann_not_equal r lte b) : bop_exists_ann S r b :=
  match P with
  existT _ (_, ann) ((_, p), _) =>     
     existT (λ x : S, bop_is_ann S r b x) ann p
  end. 


Inductive os_exists_top_ann_decidable (S : Type) (eq lte : brel S) (b : binary_op S)  : Type :=
| Top_Ann_Proof_None      : (brel_not_exists_top S lte) * (bop_not_exists_ann S eq b) -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_Top_None  : (brel_exists_top S lte) * (bop_not_exists_ann S eq b)     -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_None_Ann  : (brel_not_exists_top S lte) * (bop_exists_ann S eq b)     -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_Equal     : os_exists_top_ann_equal eq lte b                          -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_Not_Equal : os_exists_top_ann_not_equal eq lte b                      -> os_exists_top_ann_decidable S eq lte b.

Definition extract_exists_top_decidable_from_exists_top_ann_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_top_ann_decidable S r lte b) : brel_exists_top_decidable S lte :=
match P with
| Top_Ann_Proof_None _ _ _ _ (no_top, _)             => inr no_top 
| Top_Ann_Proof_Top_None  _ _ _ _ (exists_top, _) => inl exists_top 
| Top_Ann_Proof_None_Ann _ _ _ _ (no_top, _)          => inr no_top
| Top_Ann_Proof_Equal _ _ _ _ top_ann_eq              => inl (extract_exist_top_from_exists_top_ann_equal S r lte b top_ann_eq) 
| Top_Ann_Proof_Not_Equal _ _ _ _ top_ann_not_eq      => inl (extract_exist_top_from_exists_top_ann_not_equal S r lte b top_ann_not_eq) 
end.

Definition pppextract_exists_ann_decannable_from_exists_top_ann_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_top_ann_decidable S r lte b) : bop_exists_ann_decidable S r b :=
match P with
| Top_Ann_Proof_None _ _ _ _ (_, no_ann)          => inr no_ann
| Top_Ann_Proof_Top_None  _ _ _ _ (_, no_ann)  => inr no_ann
| Top_Ann_Proof_None_Ann _ _ _ _ (_, exists_ann)   => inl exists_ann
| Top_Ann_Proof_Equal _ _ _ _ top_ann_eq          => inl (extract_exist_ann_from_exists_top_ann_equal S r lte b top_ann_eq) 
| Top_Ann_Proof_Not_Equal _ _ _ _ top_ann_not_eq  => inl (extract_exist_ann_from_exists_top_ann_not_equal S r lte b top_ann_not_eq) 
end.




