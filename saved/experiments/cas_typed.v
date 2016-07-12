Section Typed_CAS. 


Inductive NumberType :=
  | Nat 
  . 

Inductive te_base :=
  | te_bool : te_base
  | te_num  : NumberType → te_base 
  . 

Inductive te :=
  | te_from_base : te_base → te
  | te_list      : te → te
  | te_set       : te → te
  | te_prod      : te → te → te 
  | te_sum       : te → te → te 
  . 

Fixpoint NumberType_to_Type (x : NumberType) : Type :=
   match x with
   | Nat     => nat 
   end.

Fixpoint te_base_to_Type (x : te_base) : Type :=
   match x with
   | te_bool     => bool
   | te_num n    => NumberType_to_Type n 
   end.

Fixpoint te_to_Type (x : te) : Type :=
   match x with
   | te_from_base b => te_base_to_Type b
   | te_list x   => list (te_to_Type x)
   | te_set x   => finite_set (te_to_Type x)
   | te_sum x y  => sum (te_to_Type x) (te_to_Type y)
   | te_prod x y => prod (te_to_Type x) (te_to_Type y)
   end.


Inductive tEQV : te -> Type := 
   | eqvBase    : ∀ b : te_base, tEQV (te_from_base b) 
   | eqvList    : ∀ s : te, tEQV s→ tEQV (te_list s) 
   | eqvSet     : ∀ s : te, tEQV s→ tEQV (te_set s) 
   | eqvProduct : ∀ s t : te, tEQV s → tEQV t → tEQV (te_prod s t) 
   | eqvSum     : ∀ s t : te, tEQV s → tEQV t → tEQV (te_sum s t) 
   .

Inductive tSG : te → Type :=
   | stAnd            : tSG (te_from_base te_bool) 
   | stOr             : tSG (te_from_base te_bool) 
   | stMin            : ∀ n : NumberType, tSG (te_from_base (te_num n))
   | stMax            : ∀ n : NumberType, tSG (te_from_base (te_num n))
   | stPlus           : ∀ n : NumberType, tSG (te_from_base (te_num n))
   | stTimes          : ∀ n : NumberType, tSG (te_from_base (te_num n))
   | stLeftSum        : ∀ s t : te, tSG s → tSG t → tSG (te_sum s t) 
   | stRightSum       : ∀ s t : te, tSG s → tSG t → tSG (te_sum s t) 
   | stProduct        : ∀ s t : te, tSG s → tSG t → tSG (te_prod s t) 
   | stLeft           : ∀ s : te, tEQV s → tSG s
   | stRight          : ∀ s : te, tEQV s → tSG s
   | stConcat         : ∀ s : te, tEQV s → tSG (te_list s)
   | stUnion          : ∀ s : te, tEQV s → tSG (te_set s)
   .

Inductive tPOS : te → Type :=
   | tposFromSemigroupLeft : ∀ s : te, tSG s → tPOS s
   | tposFromSemigroupRight : ∀ s : te, tSG s → tPOS s
   . 

Inductive tTR : te → te → Type := 
   | trtFromSemigroup : ∀ s : te, tSG s→ tTR s s 
   | trtLeftSum       : ∀ s t u : te, tTR s t → tTR u t → tTR (te_sum s u) t
   | trtRightSum      : ∀ s t u : te, tTR s t → tTR s u → tTR s (te_sum t u)
   | trtProduct       : ∀ s t u v : te, tTR s t → tTR u v → tTR (te_prod s u) (te_prod t v) 
   . 


Definition eqv_base_sem (b : te_base) : brel (te_to_Type (te_from_base b)) :=
  match b with 
  | te_bool    => brel_eq_bool 
  | te_num Nat => brel_eq_nat 
  end. 


Fixpoint eqv_sem (t : te) (x : tEQV t) : brel (te_to_Type t):=
   match x in tEQV t return brel (te_to_Type t) with
   | eqvBase          b => eqv_base_sem b
   | eqvList        s x => brel_list (te_to_Type s) (eqv_sem s x)
   | eqvSet        s x => brel_set (te_to_Type s) (eqv_sem s x)
   | eqvSum     s t x y => brel_sum (te_to_Type s) (te_to_Type t) (eqv_sem s x) (eqv_sem t y)
   | eqvProduct s t x y => brel_product (te_to_Type s) (te_to_Type t) (eqv_sem s x) (eqv_sem t y)
   end. 

Fixpoint sg_sem (t : te) (x : tSG t) : Binary (te_to_Type t):=
   match x in tSG t return (Binary (te_to_Type t)) with
   | stAnd                => bool_and
   | stOr                 => bool_or 
   | stMin Nat            => nat_min 
   | stMax Nat            => nat_max 
   | stPlus Nat           => nat_plus 
   | stTimes Nat          => nat_times 
   | stLeftSum s t x y    => 
        semigroup_left_sum (te_to_Type s) (te_to_Type t) (sg_sem s x) (sg_sem t y)
   | stRightSum s t  x y   => 
        semigroup_right_sum (te_to_Type s) (te_to_Type t) (sg_sem s x) (sg_sem t y)
   | stProduct s t  x y    => 
        semigroup_product (te_to_Type s) (te_to_Type t) (sg_sem s x) (sg_sem t y)
   | stLeft s x => 
        semigroup_left (te_to_Type s) (eqv_sem s x)
   | stRight s x => 
        semigroup_right (te_to_Type s) (eqv_sem s x)
   | stConcat s x => 
        semigroup_concat (te_to_Type s) (eqv_sem s x)
   | stUnion s x => 
        semigroup_union (te_to_Type s) (eqv_sem s x)
   end. 

Fixpoint pos_sem (t : te) (x : tPOS t) : Relation (te_to_Type t):=
   match x with
   | tposFromSemigroupLeft t x  => pre_from_sgr_left (te_to_Type t) (sg_sem t x)
   | tposFromSemigroupRight t x => pre_from_sgr_right (te_to_Type t) (sg_sem t x)
   end. 


(*

UNION (LEX (S, LEFT T), LEX (RIGHT S, T))

BILT-to-LT (S LEX T, *_S x (left T), (right S) x *_T)

BILT-to-LT (LEX-PRODUCT (S, *_S, (right S)), (T, left T, *_T))

BILT-to-LT (LEX-PRODUCT (RIGHT-RIGHT (S, *_S),  LEFT-LEFT(T, *_T)))

*) 


(* 

Fixpoint tr_sem (s t : te) (x : tTR s t) : LeftTransform (te_to_Type s) (te_to_Type t) :=
   match x with
   | trtFromSemigroup s sg  => 
        left_transform_from_semigroup (te_to_Type s) (sg_sem s sg) 
   | trtLeftSum s t u l r   => 
        left_transform_left_sum (te_to_Type s) (te_to_Type t) (te_to_Type u) 
                                (tr_sem s t l) (tr_sem u t r)
   | trtRightSum s t u l r  => 
        left_transform_right_sum (te_to_Type s) (te_to_Type t) (te_to_Type u) 
                                 (tr_sem s t l) (tr_sem s u r)
   | trtProduct s t u v l r => 
        left_transform_product (te_to_Type s) (te_to_Type t) (te_to_Type u) (te_to_Type v) 
                               (tr_sem s t l) (tr_sem u v r)
   end.  
*) 
   
End Typed_CAS. 

