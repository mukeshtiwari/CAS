Require Export Coq.Unicode.Utf8.
Require Import Coq.Strings.String. 

Close Scope nat_scope. 
Definition cas_constant : Type          := string. 
Definition with_constant (S : Type)     := cas_constant + S.  
Definition brel (S : Type)              := S → S → bool.  
Definition brel2 (S T : Type)           := S → T → bool.  
Definition bProp (S : Type)             := S → bool.  
Definition unary_op (S : Type)          := S → S. 
Definition binary_op (S : Type)         := S → S → S.  
Definition left_transform (S T : Type)  := S → T → T.  
Definition right_transform (S T : Type) := T → S → T. 
Definition finite_set (S : Type)        := list S.     (* improve someday ... *) 




