Definition uop_id : ∀ {S : Type}, (unary_op S) := λ {S} s, s.  


Definition uop_with_constant : ∀ {S : Type}, unary_op S → unary_op (with_constant S)
:= λ {S} g x ,  
      match x with
         | (inl _) => x 
         | (inr s) => inr _ (g s) 
      end.
