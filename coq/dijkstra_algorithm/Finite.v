Require Import Vector Fin List.
Import ListNotations.


Section Finite.

  Class Finite (A : Type) :=
  {
    l : list A; 
    Hfin : (forall x : A, List.In x l)
  }.


  Instance fin_finite : forall (n : nat), Finite (Fin.t n).
  Proof.
    induction n.
    + exists [].
      intros x.
      inversion x.
    + destruct IHn as (l, Hl).
      exists (Fin.F1 :: List.map Fin.FS l).
      intro a. 
      revert n a l Hl.
      refine (@Fin.caseS _ _ _); 
      intros; [left | right].
      - exact eq_refl.
      - now apply in_map.
  Qed.  


  (* 
    enum_fin 0 := []
    enum_fin 1 := [F1]
    enum_fin 2 := [F1; FS F1]
    enum_fin 3 := [F1; FS F1; FS (FS F1)]
  *)
  Fixpoint enum_fin {n : nat} : list (Fin.t n).
  Proof.
    induction n.
    + exact [].
    + exact (Fin.F1 :: List.map Fin.FS IHn).
  Defined.    


End Finite.
