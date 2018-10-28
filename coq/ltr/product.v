Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.product.


Definition ltr_product :
   ∀ {S LS T LT: Type}, left_transform LS S → left_transform LT T → left_transform (LS * LT) (S * T)
   := λ {S LS T LT} U V x y,  
     match x, y with
     | (x1, x2), (y1, y2) => (U x1 y1, V x2 y2) 
     end.

Section Theory.

End Theory.

Section ACAS.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  