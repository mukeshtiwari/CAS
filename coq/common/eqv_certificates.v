Require Import CAS.coq.common.compute. 



Inductive assert_brel_congruence {S : Type} := 
| Assert_Brel_Congruence : assert_brel_congruence (S := S). 

Inductive assert_reflexive {S : Type} := 
| Assert_Reflexive : assert_reflexive (S := S). 

Inductive check_reflexive {S : Type} := 
| Certify_Reflexive : check_reflexive (S := S)
| Certify_Not_Reflexive : S → check_reflexive (S := S). 

Inductive assert_irreflexive {S : Type} := 
| Assert_Irreflexive : assert_irreflexive (S := S). 

Inductive check_irreflexive {S : Type} := 
| Certify_Irreflexive : check_irreflexive (S := S)
| Certify_Not_Irreflexive : S → check_irreflexive (S := S).  

Inductive assert_transitive {S : Type} := 
| Assert_Transitive : assert_transitive (S := S). 

Inductive check_transitive {S : Type} := 
| Certify_Transitive : check_transitive (S := S)
| Certify_Not_Transitive : (S * (S * S)) → check_transitive (S := S). 

Inductive assert_symmetric {S : Type} := 
| Assert_Symmetric : assert_symmetric (S := S). 

Inductive check_symmetric {S : Type} := 
| Certify_Symmetric : check_symmetric (S := S)
| Certify_Not_Symmetric : (S * S) → check_symmetric (S := S). 

Inductive assert_antisymmetric {S : Type} := 
| Assert_Antisymmetric : assert_antisymmetric (S := S). 

Inductive check_antisymmetric {S : Type} := 
| Certify_Antisymmetric : check_antisymmetric (S := S)
| Certify_Not_Antisymmetric : (S * S) → check_antisymmetric (S := S). 

Inductive assert_asymmetric {S : Type} := 
| Assert_Asymmetric : assert_asymmetric (S := S). 

Inductive check_asymmetric {S : Type} := 
| Certify_Asymmetric : check_asymmetric (S := S)
| Certify_Not_Asymmetric : (S * S) → check_asymmetric (S := S). 

Inductive assert_total {S : Type} := 
| Assert_Total : assert_total (S := S). 

Inductive check_total {S : Type} := 
| Certify_Total : check_total (S := S)
| Certify_Not_Total : (S * S) → check_total (S := S). 


Inductive check_exactly_two {S : Type} := 
| Certify_Exactly_Two : (S * S) → check_exactly_two (S := S)
| Certify_Not_Exactly_Two : (S -> (S -> S)) → check_exactly_two (S := S). 








