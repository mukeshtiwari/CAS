Require Import CAS.code.basic_types. 

Definition bProp_forall : forall (S : Type),  bProp S → bProp(finite_set S) := List.forallb. 

