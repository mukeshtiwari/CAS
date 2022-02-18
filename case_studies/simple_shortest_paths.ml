
open Cas;;
open Describe;;
open Matrix_solver;; 


(* inspect the algebra mcas_min_plus ... *) 
  

(* we need to add a zero *) 
let simple_shortest_paths = mcas_bs_add_zero mcas_min_plus infinity;;

(* now, inspect this algebra *)

(* now, configure an adjacency matrix *)
let sq_mat = square_matrix_from_adj_list 4 [(1, [(2, Inr 10); (0, Inr 20)])] simple_shortest_paths

let _ =  List.map (fun (x, y) -> (x, y, sq_mat.mat x y)) (compute_pair [0; 1; 2])

(*
[(0, 0, Inr 0);
 (0, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (0, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 0, Inr 20); (1, 1, Inr 0); (1, 2, Inr 10);
 (2, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0)]
*)

(* now, run a few path finding algorithms *)
exception Msg of string 
let _ = match matrix_solver Matrix_power simple_shortest_paths with
  | Inl mf -> List.map (fun (x, y) -> (x, y, (mf sq_mat).mat x y)) (compute_pair (List.rev (list_enum 4))) 
  | Inr x -> raise (Msg "You algebra does not match with your algorithm")

(* 
[(0, 0, Inr 0);
 (0, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (0, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (0, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 0, Inr 20); (1, 1, Inr 0); (1, 2, Inr 10);
 (1, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0);
 (2, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 3, Inr 0)]
*)