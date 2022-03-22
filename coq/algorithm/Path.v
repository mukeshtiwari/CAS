From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties.
Import ListNotations.

Section Computation.
  Variables 
    (Node : Type)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN).

  (* carrier set and the operators *)
  Variables
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)
    (* equivalence relation on R *)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR).
    (* end of equivalence relation *)

    (* start of congruence relation *)
  Variables 
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)
      
  
  Declare Scope Mat_scope.
  Delimit Scope Mat_scope with R.
  Bind Scope Mat_scope with R.
  Local Open Scope Mat_scope.


  Local Notation "0" := zeroR : Mat_scope.
  Local Notation "1" := oneR : Mat_scope.
  Local Infix "+" := plusR : Mat_scope.
  Local Infix "*" := mulR : Mat_scope.
  Local Infix "=r=" := eqR (at level 70) : Mat_scope.
  Local Infix "=n=" := eqN (at level 70) : Mat_scope.


  (* a path is a triple *)
  Definition Path : Type := Node * Node * list (Node * Node * R). 


  Definition source (c : Node) (l : list (Node * Node * R)) : bool :=
    match l with 
    | [] => false
    | (x, _, _) :: _ => c =n= x 
    end.
  

  Definition target_alt (d : Node) (l : list (Node * Node * R)) := 
    match List.rev l with
    | [] => false
    | (x, y, r) :: t => d =n= y
    end. 


  Fixpoint target (d : Node) (l : list (Node * Node * R)) : bool :=
    match l with
    | [] => false
    | (x, y, r) :: t => match t with 
      | [] => d =n= y
      | hs :: ts => target d t
    end
    end.


    (* path strength between c and d *)
    Fixpoint measure_of_path (l : list (Node * Node * R)) : R :=
      match l with 
      | [] => 1
      | (_, _, v) :: t => v * measure_of_path t
      end.


    Fixpoint well_formed_path_aux (m : Node -> Node -> R) 
      (l : list (Node * Node * R)) : bool :=
      match l with 
      | [] => true
      | (c, x, v) :: tl => (m c x =r= v) && match tl with 
        | [] => true
        | (y, _, _) :: _ => (x =n= y) && well_formed_path_aux m tl
        end
      end.
  
  
    
    Definition fp (p : Path) : Node :=
      match p with
      |(a, _, _) => a
      end. 

    Definition sp (p : Path) : Node :=
      match p with
      |(_, b, _) => b
      end. 
    
    Definition tp (p : Path) : list (Node * Node * R):=
      match p with
      |(_, _, l) => l
      end.

     
    (* stick a node 'c' in all the paths, represented by l *)
    Fixpoint append_node_in_paths (m : Node -> Node -> R) 
      (c : Node) (l : list (list (Node * Node * R))) : 
      list (list (Node * Node * R)) := 
    match l with 
    | [] => []
    | h :: t => match h with 
      | [] => append_node_in_paths m c t
      | (x, _, _) :: ht => 
        ((c, x, m c x) :: h) :: append_node_in_paths m c t
      end 
    end.


    (* list of all paths of lenghth k from c to d. 
      xs is list of all candidates *)
    Fixpoint all_paths_klength (xs : list Node) 
      (m : Node -> Node -> R) (k : nat) 
      (c d : Node) : list (list (Node * Node * R)) :=
      match k with
      | O => if c =n= d then [[(c, d, 1)]] else []
      | S k' =>
          let lf := List.flat_map (fun x => all_paths_klength xs m k' x d) xs
          in append_node_in_paths m c lf
      end.

    
    Definition construct_all_paths (xs : list Node) 
      (m : Node -> Node -> R) (k : nat) 
      (c d : Node) : list Path :=
      let lp := all_paths_klength xs m k c d in 
      List.map (fun l => (c, d, l)) lp.

    (* get all the R values from path *)
    Definition get_all_rvalues (pl : list Path): list R :=
      List.map (fun '(_, _, l) => measure_of_path l) pl.

  
    Definition sum_all_rvalues (pl : list R) :=
      List.fold_right (fun b a => b + a) 0 pl.

    (* sum_fn using fold_right *)
    Definition sum_fn_fold (f : Node -> R) (l : list Node) : R :=
      List.fold_right (fun b a => f b + a) 0 l.

End Computation.





    
    
    

   