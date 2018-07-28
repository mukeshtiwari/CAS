
let upto k = let rec aux m = if k <= m then [] else m :: (aux (m +1)) in aux 0;;        
let explode s = List.map (fun i -> String.get s i) (upto (String.length s));; 

(* mbind : 'a option -> ('a -> 'b option) -> 'b option  *) 
let mbind m f = match m with Some a -> f a | None -> None;;

(* mreturn : 'a -> 'a option = <fun> *) 
let mreturn a = Some a;;

(* ommap : ('a -> 'b) -> 'a option -> 'b option *) 
let mmap f m = mbind m (fun a -> mreturn (f a));; 

(* liftM : ('a -> 'b -> 'c) -> 'a option -> 'b option -> 'c option *) 
let liftM f m n = 
    mbind m (fun a -> 
    mbind n (fun b -> mreturn (f a b)));;

(* liftN : ('a -> 'b -> 'c option) -> 'a option -> 'b option -> 'c option *) 
let liftN f m n = 
    mbind m (fun a -> 
    mbind n (fun b -> f a b));;


let sg_and   = Some (Cas.sg_from_sg_CS Cas.sg_CS_and);;   (* : bool sg option *) 
let sg_or    = Some (Cas.sg_from_sg_CS Cas.sg_CS_or);;    (* : bool sg option *) 
let sg_min   = Some (Cas.sg_from_sg_CS Cas.sg_CS_min);;   (* : int sg option *) 
let sg_max   = Some (Cas.sg_from_sg_CS Cas.sg_CS_max);;   (* : int sg option *) 
let sg_times = Some (Cas.sg_from_sg_C Cas.sg_C_times);;   (* : int sg option *) 
let sg_plus  = Some (Cas.sg_from_sg_CK Cas.sg_CK_plus);;  (* : int sg option *) 

let sg_concat eqv     = Some(Cas.sg_concat eqv);;
let sg_left eqv       = Some(Cas.sg_left eqv);;
let sg_right eqv      = Some(Cas.sg_right eqv);;

let sg_add_id id sg      = mmap (Cas.sg_add_id (explode id)) sg;;
let sg_add_ann ann sg    = mmap (Cas.sg_add_ann (explode ann)) sg;;

let sg_product m n  = liftM Cas.sg_product m n  ;; 
let sg_left_sum m n = liftM Cas.sg_left_sum m n ;;
let sg_right_sum m n = liftM Cas.sg_right_sum m n;;
let sg_llex m n = 
    let sg_llex_aux sg1 sg2 = 
        match (Cas.sg_CS_option_from_sg sg1) with 
       | None -> None 
       | Some sg1'-> Some(Cas.sg_llex sg1' sg2)
    in liftN sg_llex_aux m n ;; 

(*  
let sg_union c eqv     = Some (sg_union c eqv) 
let sg_intersect c eqv = Some (sg_intersect c eqv)
 *) 

(* bi-semigroup *) 

let bs_and_or   = Some Cas.bs_and_or;; 
let bs_or_and   = Some Cas.bs_or_and ;; 
let bs_min_max  = Some Cas.bs_min_max ;; 
let bs_max_min  = Some Cas.bs_max_min;; 
let bs_min_plus = Some Cas.bs_min_plus;; 
let bs_max_plus = Some Cas.bs_max_plus;; 

(*  
let bs_union_intersect c eqv = Some (bs_union_intersect (explode c) eqv);;
let bs_intersect_union c eqv = Some (bs_intersect_union (explode c) eqv);;
 *)
let bs_add_zero bs c   = mmap (fun b -> Cas.bs_add_zero b (explode c)) bs;; 
let bs_add_one bs c    = mmap (fun b -> Cas.bs_add_one b (explode c)) bs;;

let bs_product m n  = liftM Cas.bs_product m n  ;; 

let bs_llex_product m n = 
    let bs_llex_aux bs1 bs2 = 
        match Cas.bs_CS_option_from_bs bs1 with 
        | None -> None 
        | Some bs1'-> 
           (match Cas.bs_CS_option_from_bs bs2 with 
	   | None -> (match Cas.bs_C_option_from_bs bs2 with 
                     | None -> None 
		     | Some bs2'-> Some(Cas.bs_from_bs_C(Cas.bs_C_llex_product bs1' bs2'))
                     )
	   | Some bs2'-> Some(Cas.bs_from_bs_CS(Cas.bs_CS_llex_product bs1' bs2'))
           )
    in liftN bs_llex_aux m n ;;


let bs_describe bs = mmap Describe.bs_describe bs;;     
let sg_describe sg = mmap Describe.sg_describe sg;;     


(* Note: ocaml infix symbols must be made of 

    ! $ % & * + - . / : < = > ? @ ^ | ~

introduce an infix operators, 
  op : 'a sg option -> 'b sg option -> ('a * 'b) sg option
*) 
let (<*>)  m n  = sg_product m n  ;; 
let (<!+>) m n = sg_left_sum m n ;;
let (<+!>) m n = sg_right_sum m n;;
let (<!*>) m n = sg_llex m n ;;  
let (<**>) m n = bs_product m n  ;; 
let (<!**>) m n = bs_llex_product m n ;;   

