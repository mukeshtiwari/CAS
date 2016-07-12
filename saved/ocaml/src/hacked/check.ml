(* 
open Datatypes
open Basic_types
open Cef
open Certificates
*) 

(** val bop_add_ann_commutative_check :
    'a1 check_commutative -> 'a1 with_constant check_commutative **)

let bop_add_ann_commutative_check = function
| Certify_Commutative -> Certify_Commutative
| Certify_Not_Commutative p ->
  let s,t = p in Certify_Not_Commutative ((Coq_inr s),(Coq_inr t))

(** val bop_add_ann_selective_check :
    'a1 check_selective -> 'a1 with_constant check_selective **)

let bop_add_ann_selective_check = function
| Certify_Selective -> Certify_Selective
| Certify_Not_Selective p ->
  let s,t = p in Certify_Not_Selective ((Coq_inr s),(Coq_inr t))

(** val bop_add_ann_idempotent_check :
    'a1 check_idempotent -> 'a1 with_constant check_idempotent **)

let bop_add_ann_idempotent_check = function
| Certify_Idempotent -> Certify_Idempotent
| Certify_Not_Idempotent s -> Certify_Not_Idempotent (Coq_inr s)

(** val bop_add_ann_exists_id_check :
    'a1 check_exists_id -> 'a1 with_constant check_exists_id **)

let bop_add_ann_exists_id_check = function
| Certify_Exists_Id i -> Certify_Exists_Id (Coq_inr i)
| Certify_Not_Exists_Id -> Certify_Not_Exists_Id

(** val bop_add_ann_not_is_left_check :
    cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_left **)

let bop_add_ann_not_is_left_check c = function
| Certify_Witness s -> Certify_Not_Is_Left ((Coq_inr s),(Coq_inl c))

(** val bop_add_ann_not_is_right_check :
    cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_right **)

let bop_add_ann_not_is_right_check c = function
| Certify_Witness s -> Certify_Not_Is_Right ((Coq_inl c),(Coq_inr s))

(** val bop_add_id_commutative_check :
    'a1 check_commutative -> 'a1 with_constant check_commutative **)

let bop_add_id_commutative_check = function
| Certify_Commutative -> Certify_Commutative
| Certify_Not_Commutative p ->
  let s,t = p in Certify_Not_Commutative ((Coq_inr s),(Coq_inr t))

(** val bop_add_id_selective_check :
    'a1 check_selective -> 'a1 with_constant check_selective **)

let bop_add_id_selective_check = function
| Certify_Selective -> Certify_Selective
| Certify_Not_Selective p ->
  let s,t = p in Certify_Not_Selective ((Coq_inr s),(Coq_inr t))

(** val bop_add_id_idempotent_check :
    'a1 check_idempotent -> 'a1 with_constant check_idempotent **)

let bop_add_id_idempotent_check = function
| Certify_Idempotent -> Certify_Idempotent
| Certify_Not_Idempotent s -> Certify_Not_Idempotent (Coq_inr s)

(** val bop_add_id_exists_ann_check :
    'a1 check_exists_ann -> 'a1 with_constant check_exists_ann **)

let bop_add_id_exists_ann_check = function
| Certify_Exists_Ann a -> Certify_Exists_Ann (Coq_inr a)
| Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann

(** val bop_add_id_not_is_left_check :
    cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_left **)

let bop_add_id_not_is_left_check c = function
| Certify_Witness s -> Certify_Not_Is_Left ((Coq_inl c),(Coq_inr s))

(** val bop_add_id_not_is_right_check :
    cas_constant -> 'a1 certify_witness -> 'a1 with_constant check_is_right **)

let bop_add_id_not_is_right_check c = function
| Certify_Witness s -> Certify_Not_Is_Right ((Coq_inr s),(Coq_inl c))

(** val bop_add_id_left_cancellative_check :
    cas_constant -> 'a1 check_anti_left -> 'a1 check_left_cancellative -> 'a1
    with_constant check_left_cancellative **)

let bop_add_id_left_cancellative_check c ad lcd =
  match ad with
  | Certify_Anti_Left ->
    (match lcd with
     | Certify_Left_Cancellative -> Certify_Left_Cancellative
     | Certify_Not_Left_Cancellative p ->
       let s1,p0 = p in
       let s2,s3 = p0 in
       Certify_Not_Left_Cancellative ((Coq_inr s1),((Coq_inr s2),(Coq_inr
       s3))))
  | Certify_Not_Anti_Left p ->
    let s1,s2 = p in
    Certify_Not_Left_Cancellative ((Coq_inr s1),((Coq_inr s2),(Coq_inl c)))

(** val bop_add_id_right_cancellative_check :
    cas_constant -> 'a1 check_anti_right -> 'a1 check_right_cancellative ->
    'a1 with_constant check_right_cancellative **)

let bop_add_id_right_cancellative_check c ad lcd =
  match ad with
  | Certify_Anti_Right ->
    (match lcd with
     | Certify_Right_Cancellative -> Certify_Right_Cancellative
     | Certify_Not_Right_Cancellative p ->
       let s1,p0 = p in
       let s2,s3 = p0 in
       Certify_Not_Right_Cancellative ((Coq_inr s1),((Coq_inr s2),(Coq_inr
       s3))))
  | Certify_Not_Anti_Right p ->
    let s1,s2 = p in
    Certify_Not_Right_Cancellative ((Coq_inr s1),((Coq_inr s2),(Coq_inl c)))

(** val check_commutative_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_commutative
    -> 'a2 check_commutative -> ('a1*'a2) check_commutative **)

let check_commutative_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Commutative ->
     (match cT with
      | Certify_Commutative -> Certify_Commutative
      | Certify_Not_Commutative p ->
        let t1,t2 = p in Certify_Not_Commutative ((s,t1),(s,t2)))
   | Certify_Not_Commutative p ->
     let s1,s2 = p in Certify_Not_Commutative ((s1,t),(s2,t)))

(** val check_commutative_product_new :
    'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
    ('a1*'a2)*('a1*'a2)) sum **)

let check_commutative_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p -> let t1,t2 = p in Coq_inr ((s,t1),(s,t2)))
  | Coq_inr p -> let s1,s2 = p in Coq_inr ((s1,t),(s2,t))

(** val check_left_cancellative_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_left_cancellative -> 'a2 check_left_cancellative -> ('a1*'a2)
    check_left_cancellative **)

let check_left_cancellative_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Left_Cancellative ->
     (match cT with
      | Certify_Left_Cancellative -> Certify_Left_Cancellative
      | Certify_Not_Left_Cancellative p ->
        let t1,p0 = p in
        let t2,t3 = p0 in
        Certify_Not_Left_Cancellative ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Left_Cancellative p ->
     let s1,p0 = p in
     let s2,s3 = p0 in Certify_Not_Left_Cancellative ((s1,t),((s2,t),(s3,t))))

(** val check_left_cancellative_product_new :
    'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
    (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum **)

let check_left_cancellative_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p ->
       let t1,p0 = p in let t2,t3 = p0 in Coq_inr ((s,t1),((s,t2),(s,t3))))
  | Coq_inr p ->
    let s1,p0 = p in let s2,s3 = p0 in Coq_inr ((s1,t),((s2,t),(s3,t)))

(** val check_right_cancellative_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_right_cancellative -> 'a2 check_right_cancellative -> ('a1*'a2)
    check_right_cancellative **)

let check_right_cancellative_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Right_Cancellative ->
     (match cT with
      | Certify_Right_Cancellative -> Certify_Right_Cancellative
      | Certify_Not_Right_Cancellative p ->
        let t1,p0 = p in
        let t2,t3 = p0 in
        Certify_Not_Right_Cancellative ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Right_Cancellative p ->
     let s1,p0 = p in
     let s2,s3 = p0 in
     Certify_Not_Right_Cancellative ((s1,t),((s2,t),(s3,t))))

(** val check_right_cancellative_product_new :
    'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
    (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum **)

let check_right_cancellative_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p ->
       let t1,p0 = p in let t2,t3 = p0 in Coq_inr ((s,t1),((s,t2),(s,t3))))
  | Coq_inr p ->
    let s1,p0 = p in let s2,s3 = p0 in Coq_inr ((s1,t),((s2,t),(s3,t)))

(** val check_left_constant_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_left_constant
    -> 'a2 check_left_constant -> ('a1*'a2) check_left_constant **)

let check_left_constant_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Left_Constant ->
     (match cT with
      | Certify_Left_Constant -> Certify_Left_Constant
      | Certify_Not_Left_Constant p ->
        let t1,p0 = p in
        let t2,t3 = p0 in Certify_Not_Left_Constant ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Left_Constant p ->
     let s1,p0 = p in
     let s2,s3 = p0 in Certify_Not_Left_Constant ((s1,t),((s2,t),(s3,t))))

(** val check_left_constant_product_new :
    'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
    (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum **)

let check_left_constant_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p ->
       let t1,p0 = p in let t2,t3 = p0 in Coq_inr ((s,t1),((s,t2),(s,t3))))
  | Coq_inr p ->
    let s1,p0 = p in let s2,s3 = p0 in Coq_inr ((s1,t),((s2,t),(s3,t)))

(** val check_right_constant_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_right_constant -> 'a2 check_right_constant -> ('a1*'a2)
    check_right_constant **)

let check_right_constant_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Right_Constant ->
     (match cT with
      | Certify_Right_Constant -> Certify_Right_Constant
      | Certify_Not_Right_Constant p ->
        let t1,p0 = p in
        let t2,t3 = p0 in Certify_Not_Right_Constant ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Right_Constant p ->
     let s1,p0 = p in
     let s2,s3 = p0 in Certify_Not_Right_Constant ((s1,t),((s2,t),(s3,t))))

(** val check_right_constant_product_new :
    'a1 -> 'a2 -> (unit, 'a1*('a1*'a1)) sum -> (unit, 'a2*('a2*'a2)) sum ->
    (unit, ('a1*'a2)*(('a1*'a2)*('a1*'a2))) sum **)

let check_right_constant_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p ->
       let t1,p0 = p in let t2,t3 = p0 in Coq_inr ((s,t1),((s,t2),(s,t3))))
  | Coq_inr p ->
    let s1,p0 = p in let s2,s3 = p0 in Coq_inr ((s1,t),((s2,t),(s3,t)))

(** val check_anti_left_product :
    'a1 check_anti_left -> 'a2 check_anti_left -> ('a1*'a2) check_anti_left **)

let check_anti_left_product dS dT =
  match dS with
  | Certify_Anti_Left -> Certify_Anti_Left
  | Certify_Not_Anti_Left p ->
    let s1,s2 = p in
    (match dT with
     | Certify_Anti_Left -> Certify_Anti_Left
     | Certify_Not_Anti_Left p0 ->
       let t1,t2 = p0 in Certify_Not_Anti_Left ((s1,t1),(s2,t2)))

(** val check_anti_left_product_new :
    (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit, ('a1*'a2)*('a1*'a2))
    sum **)

let check_anti_left_product_new dS dT =
  match dS with
  | Coq_inl u -> Coq_inl ()
  | Coq_inr p ->
    let s1,s2 = p in
    (match dT with
     | Coq_inl u -> Coq_inl ()
     | Coq_inr p0 -> let t1,t2 = p0 in Coq_inr ((s1,t1),(s2,t2)))

(** val check_anti_right_product :
    'a1 check_anti_right -> 'a2 check_anti_right -> ('a1*'a2)
    check_anti_right **)

let check_anti_right_product dS dT =
  match dS with
  | Certify_Anti_Right -> Certify_Anti_Right
  | Certify_Not_Anti_Right p ->
    let s1,s2 = p in
    (match dT with
     | Certify_Anti_Right -> Certify_Anti_Right
     | Certify_Not_Anti_Right p0 ->
       let t1,t2 = p0 in Certify_Not_Anti_Right ((s1,t1),(s2,t2)))

(** val check_anti_right_product_new :
    (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit, ('a1*'a2)*('a1*'a2))
    sum **)

let check_anti_right_product_new dS dT =
  match dS with
  | Coq_inl u -> Coq_inl ()
  | Coq_inr p ->
    let s1,s2 = p in
    (match dT with
     | Coq_inl u -> Coq_inl ()
     | Coq_inr p0 -> let t1,t2 = p0 in Coq_inr ((s1,t1),(s2,t2)))

(** val check_idempotent_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_idempotent ->
    'a2 check_idempotent -> ('a1*'a2) check_idempotent **)

let check_idempotent_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Idempotent ->
     (match cT with
      | Certify_Idempotent -> Certify_Idempotent
      | Certify_Not_Idempotent t1 -> Certify_Not_Idempotent (s,t1))
   | Certify_Not_Idempotent s1 -> Certify_Not_Idempotent (s1,t))

(** val check_idempotent_product_new :
    'a1 -> 'a2 -> (unit, 'a1) sum -> (unit, 'a2) sum -> (unit, 'a1*'a2) sum **)

let check_idempotent_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr t1 -> Coq_inr (s,t1))
  | Coq_inr s1 -> Coq_inr (s1,t)

(** val check_is_left_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_is_left ->
    'a2 check_is_left -> ('a1*'a2) check_is_left **)

let check_is_left_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Is_Left ->
     (match cT with
      | Certify_Is_Left -> Certify_Is_Left
      | Certify_Not_Is_Left p ->
        let t1,t2 = p in Certify_Not_Is_Left ((s,t1),(s,t2)))
   | Certify_Not_Is_Left p ->
     let s1,s2 = p in Certify_Not_Is_Left ((s1,t),(s2,t)))

(** val check_is_left_product_new :
    'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
    ('a1*'a2)*('a1*'a2)) sum **)

let check_is_left_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p -> let t1,t2 = p in Coq_inr ((s,t1),(s,t2)))
  | Coq_inr p -> let s1,s2 = p in Coq_inr ((s1,t),(s2,t))

(** val check_is_right_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_is_right ->
    'a2 check_is_right -> ('a1*'a2) check_is_right **)

let check_is_right_product ntS ntT cS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match cS with
   | Certify_Is_Right ->
     (match cT with
      | Certify_Is_Right -> Certify_Is_Right
      | Certify_Not_Is_Right p ->
        let t1,t2 = p in Certify_Not_Is_Right ((s,t1),(s,t2)))
   | Certify_Not_Is_Right p ->
     let s1,s2 = p in Certify_Not_Is_Right ((s1,t),(s2,t)))

(** val check_is_right_product_new :
    'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
    ('a1*'a2)*('a1*'a2)) sum **)

let check_is_right_product_new s t cS cT =
  match cS with
  | Coq_inl u ->
    (match cT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p -> let t1,t2 = p in Coq_inr ((s,t1),(s,t2)))
  | Coq_inr p -> let s1,s2 = p in Coq_inr ((s1,t),(s2,t))

(** val check_selective_product :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1 check_is_left ->
    'a2 check_is_left -> 'a1 check_is_right -> 'a2 check_is_right ->
    ('a1*'a2) check_selective **)

let check_selective_product ntS ntT clS clT crS crT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match clS with
   | Certify_Is_Left ->
     (match clT with
      | Certify_Is_Left -> Certify_Selective
      | Certify_Not_Is_Left p ->
        let t1,t2 = p in
        (match crT with
         | Certify_Is_Right ->
           (match crS with
            | Certify_Is_Right -> Certify_Selective
            | Certify_Not_Is_Right p0 ->
              let s1,s2 = p0 in Certify_Not_Selective ((s1,t1),(s2,t2)))
         | Certify_Not_Is_Right p0 ->
           let t3,t4 = p0 in
           (match crS with
            | Certify_Is_Right ->
              (match clS with
               | Certify_Is_Left -> Certify_Selective
               | Certify_Not_Is_Left p1 ->
                 let s1,s2 = p1 in Certify_Not_Selective ((s1,t3),(s2,t4)))
            | Certify_Not_Is_Right p1 ->
              let s1,s2 = p1 in Certify_Not_Selective ((s1,t1),(s2,t2)))))
   | Certify_Not_Is_Left p ->
     let s1,s2 = p in
     (match crS with
      | Certify_Is_Right ->
        (match crT with
         | Certify_Is_Right -> Certify_Selective
         | Certify_Not_Is_Right p0 ->
           let t1,t2 = p0 in Certify_Not_Selective ((s1,t1),(s2,t2)))
      | Certify_Not_Is_Right p0 ->
        let s3,s4 = p0 in
        (match crT with
         | Certify_Is_Right ->
           (match clT with
            | Certify_Is_Left -> Certify_Selective
            | Certify_Not_Is_Left p1 ->
              let t1,t2 = p1 in Certify_Not_Selective ((s3,t1),(s4,t2)))
         | Certify_Not_Is_Right p1 ->
           let t1,t2 = p1 in
           (match clT with
            | Certify_Is_Left -> Certify_Not_Selective ((s1,t1),(s2,t2))
            | Certify_Not_Is_Left p2 ->
              let t3,t4 = p2 in Certify_Not_Selective ((s1,t1),(s2,t2))))))

(** val check_selective_product_new :
    'a1 -> 'a2 -> (unit, 'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit,
    'a1*'a1) sum -> (unit, 'a2*'a2) sum -> (unit, ('a1*'a2)*('a1*'a2)) sum **)

let check_selective_product_new s t clS clT crS crT =
  match clS with
  | Coq_inl u ->
    (match clT with
     | Coq_inl u0 -> Coq_inl ()
     | Coq_inr p ->
       let t1,t2 = p in
       (match crT with
        | Coq_inl u0 ->
          (match crS with
           | Coq_inl u1 -> Coq_inl ()
           | Coq_inr p0 -> let s1,s2 = p0 in Coq_inr ((s1,t1),(s2,t2)))
        | Coq_inr p0 ->
          let t3,t4 = p0 in
          (match crS with
           | Coq_inl u0 ->
             (match clS with
              | Coq_inl u1 -> Coq_inl ()
              | Coq_inr p1 -> let s1,s2 = p1 in Coq_inr ((s1,t3),(s2,t4)))
           | Coq_inr p1 -> let s1,s2 = p1 in Coq_inr ((s1,t1),(s2,t2)))))
  | Coq_inr p ->
    let s1,s2 = p in
    (match crS with
     | Coq_inl u ->
       (match crT with
        | Coq_inl u0 -> Coq_inl ()
        | Coq_inr p0 -> let t1,t2 = p0 in Coq_inr ((s1,t1),(s2,t2)))
     | Coq_inr p0 ->
       let s3,s4 = p0 in
       (match crT with
        | Coq_inl u ->
          (match clT with
           | Coq_inl u0 -> Coq_inl ()
           | Coq_inr p1 -> let t1,t2 = p1 in Coq_inr ((s3,t1),(s4,t2)))
        | Coq_inr p1 -> let t1,t2 = p1 in Coq_inr ((s1,t1),(s2,t2))))

(** val check_exists_id_product :
    'a1 check_exists_id -> 'a2 check_exists_id -> ('a1*'a2) check_exists_id **)

let check_exists_id_product cS cT =
  match cS with
  | Certify_Exists_Id s ->
    (match cT with
     | Certify_Exists_Id t -> Certify_Exists_Id (s,t)
     | Certify_Not_Exists_Id -> Certify_Not_Exists_Id)
  | Certify_Not_Exists_Id -> Certify_Not_Exists_Id

(** val check_exists_id_product_new :
    ('a1, unit) sum -> ('a2, unit) sum -> ('a1*'a2, unit) sum **)

let check_exists_id_product_new cS cT =
  match cS with
  | Coq_inl s ->
    (match cT with
     | Coq_inl t -> Coq_inl (s,t)
     | Coq_inr u -> Coq_inr ())
  | Coq_inr u -> Coq_inr ()

(** val check_exists_ann_product :
    'a1 check_exists_ann -> 'a2 check_exists_ann -> ('a1*'a2)
    check_exists_ann **)

let check_exists_ann_product cS cT =
  match cS with
  | Certify_Exists_Ann s ->
    (match cT with
     | Certify_Exists_Ann t -> Certify_Exists_Ann (s,t)
     | Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann)
  | Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann

(** val check_exists_ann_product_new :
    ('a1, unit) sum -> ('a2, unit) sum -> ('a1*'a2, unit) sum **)

let check_exists_ann_product_new cS cT =
  match cS with
  | Coq_inl s ->
    (match cT with
     | Coq_inl t -> Coq_inl (s,t)
     | Coq_inr u -> Coq_inr ())
  | Coq_inr u -> Coq_inr ()

(** val bop_product_left_distributive_check :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_left_distributive -> 'a2 check_left_distributive -> ('a1*'a2)
    check_left_distributive **)

let bop_product_left_distributive_check ntS ntT dS dT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match dS with
   | Certify_Left_Distributive ->
     (match dT with
      | Certify_Left_Distributive -> Certify_Left_Distributive
      | Certify_Not_Left_Distributive p ->
        let t1,p0 = p in
        let t2,t3 = p0 in
        Certify_Not_Left_Distributive ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Left_Distributive p ->
     let s1,p0 = p in
     let s2,s3 = p0 in Certify_Not_Left_Distributive ((s1,t),((s2,t),(s3,t))))

(** val bop_product_right_distributive_check :
    'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_right_distributive -> 'a2 check_right_distributive -> ('a1*'a2)
    check_right_distributive **)

let bop_product_right_distributive_check ntS ntT dS dT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match dS with
   | Certify_Right_Distributive ->
     (match dT with
      | Certify_Right_Distributive -> Certify_Right_Distributive
      | Certify_Not_Right_Distributive p ->
        let t1,p0 = p in
        let t2,t3 = p0 in
        Certify_Not_Right_Distributive ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Right_Distributive p ->
     let s1,p0 = p in
     let s2,s3 = p0 in
     Certify_Not_Right_Distributive ((s1,t),((s2,t),(s3,t))))

(** val bop_product_plus_id_is_times_ann_check :
    'a1 check_plus_id_equals_times_ann -> 'a2 check_plus_id_equals_times_ann
    -> ('a1*'a2) check_plus_id_equals_times_ann **)

let bop_product_plus_id_is_times_ann_check dS dT =
  match dS with
  | Certify_Plus_Id_Equals_Times_Ann ->
    (match dT with
     | Certify_Plus_Id_Equals_Times_Ann -> Certify_Plus_Id_Equals_Times_Ann
     | Certify_Not_Plus_Id_Equals_Times_Ann ->
       Certify_Not_Plus_Id_Equals_Times_Ann)
  | Certify_Not_Plus_Id_Equals_Times_Ann ->
    Certify_Not_Plus_Id_Equals_Times_Ann

(** val bop_product_times_id_equals_plus_ann_check :
    'a1 check_times_id_equals_plus_ann -> 'a2 check_times_id_equals_plus_ann
    -> ('a1*'a2) check_times_id_equals_plus_ann **)

let bop_product_times_id_equals_plus_ann_check dS dT =
  match dS with
  | Certify_Times_Id_Equals_Plus_Ann ->
    (match dT with
     | Certify_Times_Id_Equals_Plus_Ann -> Certify_Times_Id_Equals_Plus_Ann
     | Certify_Not_Times_Id_Equals_Plus_Ann ->
       Certify_Not_Times_Id_Equals_Plus_Ann)
  | Certify_Not_Times_Id_Equals_Plus_Ann ->
    Certify_Not_Times_Id_Equals_Plus_Ann

(** val bop_product_left_absorptive_check :
    'a1 -> 'a2 -> 'a1 check_left_absorptive -> 'a2 check_left_absorptive ->
    ('a1*'a2) check_left_absorptive **)

let bop_product_left_absorptive_check s t dS dT =
  match dS with
  | Certify_Left_Absorptive ->
    (match dT with
     | Certify_Left_Absorptive -> Certify_Left_Absorptive
     | Certify_Not_Left_Absorptive p ->
       let t1,t2 = p in Certify_Not_Left_Absorptive ((s,t1),(s,t2)))
  | Certify_Not_Left_Absorptive p ->
    let s1,s2 = p in Certify_Not_Left_Absorptive ((s1,t),(s2,t))

(** val bop_product_right_absorptive_check :
    'a1 -> 'a2 -> 'a1 check_right_absorptive -> 'a2 check_right_absorptive ->
    ('a1*'a2) check_right_absorptive **)

let bop_product_right_absorptive_check s t dS dT =
  match dS with
  | Certify_Right_Absorptive ->
    (match dT with
     | Certify_Right_Absorptive -> Certify_Right_Absorptive
     | Certify_Not_Right_Absorptive p ->
       let t1,t2 = p in Certify_Not_Right_Absorptive ((s,t1),(s,t2)))
  | Certify_Not_Right_Absorptive p ->
    let s1,s2 = p in Certify_Not_Right_Absorptive ((s1,t),(s2,t))

(** val check_commutative_llex :
    'a1 assert_nontrivial -> 'a2 check_commutative -> ('a1*'a2)
    check_commutative **)

let check_commutative_llex ntS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  (match cT with
   | Certify_Commutative -> Certify_Commutative
   | Certify_Not_Commutative p ->
     let t1,t2 = p in Certify_Not_Commutative ((s,t1),(s,t2)))

(** val check_idempotent_llex :
    'a1 assert_nontrivial -> 'a2 check_idempotent -> ('a1*'a2)
    check_idempotent **)

let check_idempotent_llex ntS cT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  (match cT with
   | Certify_Idempotent -> Certify_Idempotent
   | Certify_Not_Idempotent t1 -> Certify_Not_Idempotent (s,t1))

(** val check_selective_llex :
    'a1 assert_nontrivial -> 'a2 check_selective -> ('a1*'a2) check_selective **)

let check_selective_llex ntS dT =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  (match dT with
   | Certify_Selective -> Certify_Selective
   | Certify_Not_Selective p ->
     let t1,t2 = p in Certify_Not_Selective ((s,t1),(s,t2)))

(** val check_exists_id_llex :
    'a1 check_exists_id -> 'a2 check_exists_id -> ('a1*'a2) check_exists_id **)

let check_exists_id_llex cS cT =
  match cS with
  | Certify_Exists_Id s ->
    (match cT with
     | Certify_Exists_Id t -> Certify_Exists_Id (s,t)
     | Certify_Not_Exists_Id -> Certify_Not_Exists_Id)
  | Certify_Not_Exists_Id -> Certify_Not_Exists_Id

(** val check_exists_ann_llex :
    'a1 check_exists_ann -> 'a2 check_exists_ann -> ('a1*'a2)
    check_exists_ann **)

let check_exists_ann_llex cS cT =
  match cS with
  | Certify_Exists_Ann s ->
    (match cT with
     | Certify_Exists_Ann t -> Certify_Exists_Ann (s,t)
     | Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann)
  | Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann

(** val bops_llex_product_left_distributive_check :
    'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a2 binary_op
    -> 'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_left_cancellative -> 'a2 check_left_constant -> 'a1
    check_left_distributive -> 'a2 check_left_distributive -> ('a1*'a2)
    check_left_distributive **)

let bops_llex_product_left_distributive_check rS rT addS addT mulT ntS ntT lcS_d lkT_d ldS_d ldT_d =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match ldS_d with
   | Certify_Left_Distributive ->
     (match ldT_d with
      | Certify_Left_Distributive ->
        (match lcS_d with
         | Certify_Left_Cancellative -> Certify_Left_Distributive
         | Certify_Not_Left_Cancellative p ->
           let s1,p0 = p in
           let s2,s3 = p0 in
           (match lkT_d with
            | Certify_Left_Constant -> Certify_Left_Distributive
            | Certify_Not_Left_Constant p1 ->
              let t1,p2 = p1 in
              let t2,t3 = p2 in
              Certify_Not_Left_Distributive
              (cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3
                addS addT mulT)))
      | Certify_Not_Left_Distributive p ->
        let t1,p0 = p in
        let t2,t3 = p0 in
        Certify_Not_Left_Distributive ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Left_Distributive p ->
     let s1,p0 = p in
     let s2,s3 = p0 in Certify_Not_Left_Distributive ((s1,t),((s2,t),(s3,t))))

(** val bops_llex_product_right_distributive_check :
    'a1 brel -> 'a2 brel -> 'a1 binary_op -> 'a2 binary_op -> 'a2 binary_op
    -> 'a1 assert_nontrivial -> 'a2 assert_nontrivial -> 'a1
    check_right_cancellative -> 'a2 check_right_constant -> 'a1
    check_right_distributive -> 'a2 check_right_distributive -> ('a1*'a2)
    check_right_distributive **)

let bops_llex_product_right_distributive_check rS rT addS addT mulT ntS ntT lcS_d lkT_d ldS_d ldT_d =
  let Certify_Witness s = ntS.certify_nontrivial_witness in
  let Certify_Witness t = ntT.certify_nontrivial_witness in
  (match ldS_d with
   | Certify_Right_Distributive ->
     (match ldT_d with
      | Certify_Right_Distributive ->
        (match lcS_d with
         | Certify_Right_Cancellative -> Certify_Right_Distributive
         | Certify_Not_Right_Cancellative p ->
           let s1,p0 = p in
           let s2,s3 = p0 in
           (match lkT_d with
            | Certify_Right_Constant -> Certify_Right_Distributive
            | Certify_Not_Right_Constant p1 ->
              let t1,p2 = p1 in
              let t2,t3 = p2 in
              Certify_Not_Right_Distributive
              (cef_llex_product_not_right_distributive rS rT s1 s2 s3 t1 t2
                t3 addS addT mulT)))
      | Certify_Not_Right_Distributive p ->
        let t1,p0 = p in
        let t2,t3 = p0 in
        Certify_Not_Right_Distributive ((s,t1),((s,t2),(s,t3))))
   | Certify_Not_Right_Distributive p ->
     let s1,p0 = p in
     let s2,s3 = p0 in
     Certify_Not_Right_Distributive ((s1,t),((s2,t),(s3,t))))

(** val bops_llex_product_plus_id_is_times_ann_check :
    'a1 check_plus_id_equals_times_ann -> 'a2 check_plus_id_equals_times_ann
    -> ('a1*'a2) check_plus_id_equals_times_ann **)

let bops_llex_product_plus_id_is_times_ann_check dS dT =
  match dS with
  | Certify_Plus_Id_Equals_Times_Ann ->
    (match dT with
     | Certify_Plus_Id_Equals_Times_Ann -> Certify_Plus_Id_Equals_Times_Ann
     | Certify_Not_Plus_Id_Equals_Times_Ann ->
       Certify_Not_Plus_Id_Equals_Times_Ann)
  | Certify_Not_Plus_Id_Equals_Times_Ann ->
    Certify_Not_Plus_Id_Equals_Times_Ann

(** val bops_llex_product_times_id_equals_plus_ann_check :
    'a1 check_times_id_equals_plus_ann -> 'a2 check_times_id_equals_plus_ann
    -> ('a1*'a2) check_times_id_equals_plus_ann **)

let bops_llex_product_times_id_equals_plus_ann_check dS dT =
  match dS with
  | Certify_Times_Id_Equals_Plus_Ann ->
    (match dT with
     | Certify_Times_Id_Equals_Plus_Ann -> Certify_Times_Id_Equals_Plus_Ann
     | Certify_Not_Times_Id_Equals_Plus_Ann ->
       Certify_Not_Times_Id_Equals_Plus_Ann)
  | Certify_Not_Times_Id_Equals_Plus_Ann ->
    Certify_Not_Times_Id_Equals_Plus_Ann

(** val bops_llex_product_left_absorptive_check :
    'a2 -> 'a1 check_left_absorptive -> 'a2 check_left_absorptive -> 'a1
    check_anti_left -> ('a1*'a2) check_left_absorptive **)

let bops_llex_product_left_absorptive_check t dS dT alS =
  match dS with
  | Certify_Left_Absorptive ->
    (match dT with
     | Certify_Left_Absorptive -> Certify_Left_Absorptive
     | Certify_Not_Left_Absorptive p ->
       let t1,t2 = p in
       (match alS with
        | Certify_Anti_Left -> Certify_Left_Absorptive
        | Certify_Not_Anti_Left p0 ->
          let s1,s2 = p0 in Certify_Not_Left_Absorptive ((s1,t1),(s2,t2))))
  | Certify_Not_Left_Absorptive p ->
    let s1,s2 = p in Certify_Not_Left_Absorptive ((s1,t),(s2,t))

(** val bops_llex_product_right_absorptive_check :
    'a2 -> 'a1 check_right_absorptive -> 'a2 check_right_absorptive -> 'a1
    check_anti_right -> ('a1*'a2) check_right_absorptive **)

let bops_llex_product_right_absorptive_check t dS dT alS =
  match dS with
  | Certify_Right_Absorptive ->
    (match dT with
     | Certify_Right_Absorptive -> Certify_Right_Absorptive
     | Certify_Not_Right_Absorptive p ->
       let t1,t2 = p in
       (match alS with
        | Certify_Anti_Right -> Certify_Right_Absorptive
        | Certify_Not_Anti_Right p0 ->
          let s1,s2 = p0 in Certify_Not_Right_Absorptive ((s1,t1),(s2,t2))))
  | Certify_Not_Right_Absorptive p ->
    let s1,s2 = p in Certify_Not_Right_Absorptive ((s1,t),(s2,t))

(** val bops_add_zero_left_distributive_check :
    'a1 check_left_distributive -> 'a1 with_constant check_left_distributive **)

let bops_add_zero_left_distributive_check = function
| Certify_Left_Distributive -> Certify_Left_Distributive
| Certify_Not_Left_Distributive p ->
  let s1,p0 = p in
  let s2,s3 = p0 in
  Certify_Not_Left_Distributive ((Coq_inr s1),((Coq_inr s2),(Coq_inr s3)))

(** val bops_add_zero_right_distributive_check :
    'a1 check_right_distributive -> 'a1 with_constant
    check_right_distributive **)

let bops_add_zero_right_distributive_check = function
| Certify_Right_Distributive -> Certify_Right_Distributive
| Certify_Not_Right_Distributive p ->
  let s1,p0 = p in
  let s2,s3 = p0 in
  Certify_Not_Right_Distributive ((Coq_inr s1),((Coq_inr s2),(Coq_inr s3)))

(** val bops_add_zero_left_absorptive_check :
    'a1 -> 'a1 check_left_absorptive -> 'a1 with_constant
    check_left_absorptive **)

let bops_add_zero_left_absorptive_check s = function
| Certify_Left_Absorptive -> Certify_Left_Absorptive
| Certify_Not_Left_Absorptive p ->
  let s1,s2 = p in Certify_Not_Left_Absorptive ((Coq_inr s1),(Coq_inr s2))

(** val bops_add_zero_right_absorptive_check :
    'a1 -> 'a1 check_right_absorptive -> 'a1 with_constant
    check_right_absorptive **)

let bops_add_zero_right_absorptive_check s = function
| Certify_Right_Absorptive -> Certify_Right_Absorptive
| Certify_Not_Right_Absorptive p ->
  let s1,s2 = p in Certify_Not_Right_Absorptive ((Coq_inr s1),(Coq_inr s2))

(** val check_commutative_sum :
    'a1 check_commutative -> 'a2 check_commutative -> ('a1, 'a2) sum
    check_commutative **)

let check_commutative_sum cS cT =
  match cS with
  | Certify_Commutative ->
    (match cT with
     | Certify_Commutative -> Certify_Commutative
     | Certify_Not_Commutative p ->
       let t1,t2 = p in Certify_Not_Commutative ((Coq_inr t1),(Coq_inr t2)))
  | Certify_Not_Commutative p ->
    let s1,s2 = p in Certify_Not_Commutative ((Coq_inl s1),(Coq_inl s2))

(** val check_idempotent_sum :
    'a1 check_idempotent -> 'a2 check_idempotent -> ('a1, 'a2) sum
    check_idempotent **)

let check_idempotent_sum cS cT =
  match cS with
  | Certify_Idempotent ->
    (match cT with
     | Certify_Idempotent -> Certify_Idempotent
     | Certify_Not_Idempotent t1 -> Certify_Not_Idempotent (Coq_inr t1))
  | Certify_Not_Idempotent s1 -> Certify_Not_Idempotent (Coq_inl s1)

(** val check_selective_sum :
    'a1 check_selective -> 'a2 check_selective -> ('a1, 'a2) sum
    check_selective **)

let check_selective_sum cS cT =
  match cS with
  | Certify_Selective ->
    (match cT with
     | Certify_Selective -> Certify_Selective
     | Certify_Not_Selective p ->
       let t1,t2 = p in Certify_Not_Selective ((Coq_inr t1),(Coq_inr t2)))
  | Certify_Not_Selective p ->
    let s1,s2 = p in Certify_Not_Selective ((Coq_inl s1),(Coq_inl s2))

(** val check_exists_id_left_sum :
    'a2 check_exists_id -> ('a1, 'a2) sum check_exists_id **)

let check_exists_id_left_sum = function
| Certify_Exists_Id t -> Certify_Exists_Id (Coq_inr t)
| Certify_Not_Exists_Id -> Certify_Not_Exists_Id

(** val check_exists_id_right_sum :
    'a1 check_exists_id -> ('a1, 'a2) sum check_exists_id **)

let check_exists_id_right_sum = function
| Certify_Exists_Id s -> Certify_Exists_Id (Coq_inl s)
| Certify_Not_Exists_Id -> Certify_Not_Exists_Id

(** val check_exists_ann_left_sum :
    'a1 check_exists_ann -> ('a1, 'a2) sum check_exists_ann **)

let check_exists_ann_left_sum = function
| Certify_Exists_Ann s -> Certify_Exists_Ann (Coq_inl s)
| Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann

(** val check_exists_ann_right_sum :
    'a2 check_exists_ann -> ('a1, 'a2) sum check_exists_ann **)

let check_exists_ann_right_sum = function
| Certify_Exists_Ann t -> Certify_Exists_Ann (Coq_inr t)
| Certify_Not_Exists_Ann -> Certify_Not_Exists_Ann

