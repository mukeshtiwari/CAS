open Ast
open Basic_types
open Cas_records
open Cef
open Cert_records
open Certificates

val sg_certs_from_sg_C_certs :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a1 sg_C_certificates
  -> 'a1 sg_certificates

val sg_from_sg_C : 'a1 sg_C -> 'a1 sg

val sg_C_certs_from_sg_CI_certs :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a1 sg_CI_certificates
  -> 'a1 sg_C_certificates

val sg_C_from_sg_CI : 'a1 sg_CI -> 'a1 sg_C

val sg_CI_certs_from_sg_CS_certs :
  'a1 sg_CS_certificates -> 'a1 sg_CI_certificates

val sg_CI_from_sg_CS : 'a1 sg_CS -> 'a1 sg_CI

val sg_C_certs_from_sg_CK_certs :
  'a1 brel -> 'a1 binary_op -> 'a1 eqv_certificates -> 'a1 sg_CK_certificates
  -> 'a1 sg_C_certificates

val sg_C_from_sg_CK : 'a1 sg_CK -> 'a1 sg_C

val sg_from_sg_CI : 'a1 sg_CI -> 'a1 sg

val sg_from_sg_CK : 'a1 sg_CK -> 'a1 sg

val sg_C_from_sg_CS : 'a1 sg_CS -> 'a1 sg_C

val sg_from_sg_CS : 'a1 sg_CS -> 'a1 sg

val sg_C_certs_option_from_sg_certs :
  'a1 sg_certificates -> 'a1 sg_C_certificates option

val sg_C_option_from_sg : 'a1 sg -> 'a1 sg_C option

val sg_CI_certs_option_from_sg_C_certs :
  'a1 sg_C_certificates -> 'a1 sg_CI_certificates option

val sg_CI_option_from_sg_C : 'a1 sg_C -> 'a1 sg_CI option

val sg_CS_certs_option_from_sg_CI_certs :
  'a1 sg_CI_certificates -> 'a1 sg_CS_certificates option

val sg_CS_option_from_sg_CI : 'a1 sg_CI -> 'a1 sg_CS option

val sg_CK_certs_option_from_sg_C_certs :
  'a1 sg_C_certificates -> 'a1 sg_CK_certificates option

val sg_CK_option_from_sg_C : 'a1 sg_C -> 'a1 sg_CK option

val sg_CI_option_from_sg : 'a1 sg -> 'a1 sg_CI option

val sg_CK_option_from_sg : 'a1 sg -> 'a1 sg_CK option

val sg_CS_option_from_sg_C : 'a1 sg_C -> 'a1 sg_CS option

val sg_CS_option_from_sg : 'a1 sg -> 'a1 sg_CS option

