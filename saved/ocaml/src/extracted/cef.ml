open Basic_types
open Brel

(** val cef_commutative_implies_not_is_left :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*'a1 **)

let cef_commutative_implies_not_is_left r b s f =
  if r (b (f s) s) s then (f s),s else s,(f s)

(** val cef_commutative_implies_not_is_right :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*'a1 **)

let cef_commutative_implies_not_is_right r b s f =
  if r (b (f s) s) s then s,(f s) else (f s),s

(** val cef_selective_and_commutative_imply_not_left_cancellative :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1) **)

let cef_selective_and_commutative_imply_not_left_cancellative r b s f =
  if r (b s (f s)) s then s,(s,(f s)) else (f s),((f s),s)

(** val cef_selective_and_commutative_imply_not_right_cancellative :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1) **)

let cef_selective_and_commutative_imply_not_right_cancellative r b s f =
  if r (b s (f s)) s then s,(s,(f s)) else (f s),((f s),s)

(** val cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative :
    'a1 binary_op -> 'a1 -> 'a1 -> 'a1*('a1*'a1) **)

let cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative b s1 s2 =
  (b s1 s2),(s1,s2)

(** val cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative :
    'a1 binary_op -> 'a1 -> 'a1 -> 'a1*('a1*'a1) **)

let cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative b s1 s2 =
  (b s1 s2),(s1,s2)

(** val cef_not_idempotent_implies_not_selective : 'a1 -> 'a1*'a1 **)

let cef_not_idempotent_implies_not_selective s =
  s,s

(** val cef_left_cancellative_implies_not_left_constant :
    'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1) **)

let cef_left_cancellative_implies_not_left_constant s f =
  s,(s,(f s))

(** val cef_right_cancellative_implies_not_right_constant :
    'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1) **)

let cef_right_cancellative_implies_not_right_constant s f =
  s,(s,(f s))

(** val cef_cancellative_and_exists_id_imply_not_idempotent :
    'a1 brel -> 'a1 -> 'a1 -> ('a1 -> 'a1) -> 'a1 **)

let cef_cancellative_and_exists_id_imply_not_idempotent r s i f =
  if r s i then f s else s

(** val cef_idempotent_and_commutative_imply_not_left_constant :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1) **)

let cef_idempotent_and_commutative_imply_not_left_constant r b s f =
  if r (b (f s) s) s then (f s),(s,(f s)) else s,((f s),s)

(** val cef_idempotent_and_commutative_imply_not_right_constant :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a1*('a1*'a1) **)

let cef_idempotent_and_commutative_imply_not_right_constant r b s f =
  if r (b (f s) s) s then (f s),(s,(f s)) else s,((f s),s)

(** val cef_idempotent_implies_not_anti_left : 'a1 -> 'a1*'a1 **)

let cef_idempotent_implies_not_anti_left s =
  s,s

(** val cef_idempotent_implies_not_anti_right : 'a1 -> 'a1*'a1 **)

let cef_idempotent_implies_not_anti_right s =
  s,s

(** val cef_bop_llex_not_cancellative :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2)
    -> ('a1*'a2)*(('a1*'a2)*('a1*'a2)) **)

let cef_bop_llex_not_cancellative rS bS s f t g =
  if brel_llt rS bS s (f s)
  then (s,t),(((f s),t),((f s),(g t)))
  else ((f s),t),((s,t),(s,(g t)))

(** val cef_bop_llex_not_anti_left :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
    ('a1*'a2)*('a1*'a2) **)

let cef_bop_llex_not_anti_left rS bS s f t =
  if rS (bS s (f s)) s then (s,t),((f s),t) else ((f s),t),(s,t)

(** val cef_bop_llex_not_anti_right :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
    ('a1*'a2)*('a1*'a2) **)

let cef_bop_llex_not_anti_right rS bS s f t =
  if rS (bS s (f s)) s then (s,t),((f s),t) else ((f s),t),(s,t)

(** val cef_bop_llex_not_constant :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 -> ('a2 -> 'a2)
    -> ('a1*'a2)*(('a1*'a2)*('a1*'a2)) **)

let cef_bop_llex_not_constant rS bS s f t g =
  if brel_llt rS bS s (f s)
  then ((f s),t),((s,t),(s,(g t)))
  else (s,t),(((f s),t),((f s),(g t)))

(** val cef_bop_llex_not_is_left :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
    ('a1*'a2)*('a1*'a2) **)

let cef_bop_llex_not_is_left r b s f t =
  if r (b s (f s)) s then ((f s),t),(s,t) else (s,t),((f s),t)

(** val cef_bop_llex_not_is_right :
    'a1 brel -> 'a1 binary_op -> 'a1 -> ('a1 -> 'a1) -> 'a2 ->
    ('a1*'a2)*('a1*'a2) **)

let cef_bop_llex_not_is_right r b s f t =
  if r (b s (f s)) s then (s,t),((f s),t) else ((f s),t),(s,t)

(** val cef_llex_product_not_left_distributive :
    'a1 brel -> 'a2 brel -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1
    binary_op -> 'a2 binary_op -> 'a2 binary_op ->
    ('a1*'a2)*(('a1*'a2)*('a1*'a2)) **)

let cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3 addS addT mulT =
  if rS (addS s2 s3) s2
  then if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
       then (s1,t1),((s2,t3),(s3,t2))
       else (s1,t1),((s2,t2),(s3,t3))
  else if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
       then (s1,t1),((s3,t3),(s2,t2))
       else (s1,t1),((s2,t3),(s3,t2))

(** val cef_llex_product_not_right_distributive :
    'a1 brel -> 'a2 brel -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1
    binary_op -> 'a2 binary_op -> 'a2 binary_op ->
    ('a1*'a2)*(('a1*'a2)*('a1*'a2)) **)

let cef_llex_product_not_right_distributive rS rT s1 s2 s3 t1 t2 t3 addS addT mulT =
  if rS (addS s2 s3) s2
  then if rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))
       then (s1,t1),((s2,t3),(s3,t2))
       else (s1,t1),((s2,t2),(s3,t3))
  else if rT (mulT t2 t1) (addT (mulT t2 t1) (mulT t3 t1))
       then (s1,t1),((s3,t3),(s2,t2))
       else (s1,t1),((s2,t3),(s3,t2))

