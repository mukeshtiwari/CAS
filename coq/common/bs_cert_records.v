Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.bs_certificates.

Set Implicit Arguments.
Unset Strict Implicit.


Record id_ann_certificates {S: Type} := 
{
  id_ann_exists_plus_id_d       : @check_exists_id S 
; id_ann_exists_plus_ann_d      : @check_exists_ann S 
; id_ann_exists_times_id_d      : @check_exists_id S 
; id_ann_exists_times_ann_d     : @check_exists_ann S 
; id_ann_plus_id_is_times_ann_d : @check_plus_id_equals_times_ann S
; id_ann_times_id_is_plus_ann_d : @check_times_id_equals_plus_ann S
}.

Record zero_one_certificates {S: Type} := 
{
  zero_one_exists_plus_ann_d      : @check_exists_ann S 
; zero_one_exists_times_id        : @assert_exists_id S 
; zero_one_plus_id_is_times_ann   : @assert_plus_id_equals_times_ann S
; zero_one_times_id_is_plus_ann_d : @check_times_id_equals_plus_ann S
}.

Record bounded_certificates {S: Type} := 
{
  bounded_plus_id_is_times_ann : @assert_plus_id_equals_times_ann S
; bounded_times_id_is_plus_ann : @assert_times_id_equals_plus_ann S
}.


Record bs_certificates {S: Type} := 
{
  bs_left_distributive_d      : check_left_distributive (S := S) 
; bs_right_distributive_d     : check_right_distributive (S := S) 
; bs_left_left_absorptive_d   : check_left_left_absorptive (S := S) 
; bs_left_right_absorptive_d  : check_left_right_absorptive (S := S) 
; bs_right_left_absorptive_d  : check_right_left_absorptive (S := S) 
; bs_right_right_absorptive_d : check_right_right_absorptive (S := S) 
}. 


Record semiring_certificates {S: Type} := 
{
  semiring_left_distributive      : @assert_left_distributive S
; semiring_right_distributive     : @assert_right_distributive S

; semiring_left_left_absorptive_d   : @check_left_left_absorptive S
; semiring_left_right_absorptive_d  : @check_left_right_absorptive S 
}.

Record lattice_certificates {S: Type} := 
{
  lattice_absorptive           : @assert_left_left_absorptive S 
; lattice_absorptive_dual      : @assert_left_left_absorptive_dual S 
 
; lattice_distributive_d       : @check_left_distributive S 
; lattice_distributive_dual_d  : @check_left_distributive_dual S 
}. 

Record distributive_lattice_certificates {S: Type} := 
{
  distributive_lattice_absorptive        : @assert_left_left_absorptive S 
; distributive_lattice_absorptive_dual   : @assert_left_left_absorptive_dual S 
; distributive_lattice_distributive      : @assert_left_distributive S 
}. 


