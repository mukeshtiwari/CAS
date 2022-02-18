open Cas
open Describe


(* utility function *)
let rec compute_pair_gen (l : 'a list) (m : 'b list) : ('a * 'b) list = 
  match l with
  | [] -> []
  | h :: t -> (List.map (fun x -> (h, x)) m) @ (compute_pair_gen t m)


let compute_pair l = compute_pair_gen l l


let update_square_matrix (f : int -> int -> 'a) 
  ((u, v, w) : int * int * 'a) : int -> int -> 'a =
  fun c d -> if c = u && d = v then w else f c d



let rec massage_adj_list (l : (int * (int * 'a) list) list) 
  : (int * int * 'a) list = 
  match l with
  | [] -> []
  | (u, lu) :: ut -> (List.map (fun (x, y) -> (u, x, y)) lu) @  
    massage_adj_list ut

(* end of utility function *)

exception Msg of string
let fetch_zero_and_one_from_algebra (alg : 'a bs_mcas) = 
  let b = bs_mcas_cast_up alg in
  match b with
  | BS_Error l -> raise (Msg "something gone wrong")
  | BS_bs a ->
     let bsP = a.bs_certs in
     let id_annP = a.bs_id_ann_certs in
     (match id_annP.id_ann_plus_times_d with
     | Id_Ann_Cert_Equal zero -> 
        (match id_annP.id_ann_times_plus_d with
          | Id_Ann_Cert_Equal one -> (zero, one)
          | _ -> raise (Msg "something went wrong"))
     | _ -> raise (Msg "something went wrong")) 


let square_matrix_from_adj_list (n : int) (l : (int * (int * 'a) list) list) (alg : 'a bs_mcas)
  : 'a square_matrix =
  {
    size = n;
    mat = 
      (let (zero, one) = fetch_zero_and_one_from_algebra alg in 
      List.fold_left 
        update_square_matrix 
        (fun c d -> if c = d then zero else one)
        (massage_adj_list l));
    algebra = alg
  } 


type algorithm =  Matrix_power | Not_implemented_yet


let matrix_solver (algo : algorithm) (alge : 'a bs_mcas) :
('a Cas.square_matrix -> 'a Cas.square_matrix, char list list) Cas.sum =
  match algo with
  | Matrix_power -> call_instantiate_matrix_exp_unary_curry alge 
  | _ -> raise (Msg "algorithm not implemented yet")



