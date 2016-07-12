open Ast
open Basic_types
open Cert_records

type 's eqv = { eqv_eq : 's brel; eqv_certs : 's eqv_certificates;
                eqv_ast : ast_eqv }

val eqv_eq : 'a1 eqv -> 'a1 brel

val eqv_certs : 'a1 eqv -> 'a1 eqv_certificates

val eqv_ast : 'a1 eqv -> ast_eqv

type 's sg = { sg_eq : 's eqv; sg_bop : 's binary_op;
               sg_certs : 's sg_certificates; sg_ast : ast_sg }

val sg_eq : 'a1 sg -> 'a1 eqv

val sg_bop : 'a1 sg -> 'a1 binary_op

val sg_certs : 'a1 sg -> 'a1 sg_certificates

val sg_ast : 'a1 sg -> ast_sg

type 's sg_new = { sgn_eq : 's eqv; sgn_bop : 's binary_op;
                   sgn_certs : 's sg_certificates_new; sgn_ast : ast_sg }

val sgn_eq : 'a1 sg_new -> 'a1 eqv

val sgn_bop : 'a1 sg_new -> 'a1 binary_op

val sgn_certs : 'a1 sg_new -> 'a1 sg_certificates_new

val sgn_ast : 'a1 sg_new -> ast_sg

type 's sg_C = { sg_C_eqv : 's eqv; sg_C_bop : 's binary_op;
                 sg_C_certs : 's sg_C_certificates; sg_C_ast : ast_sg_C }

val sg_C_eqv : 'a1 sg_C -> 'a1 eqv

val sg_C_bop : 'a1 sg_C -> 'a1 binary_op

val sg_C_certs : 'a1 sg_C -> 'a1 sg_C_certificates

val sg_C_ast : 'a1 sg_C -> ast_sg_C

type 's sg_CI = { sg_CI_eqv : 's eqv; sg_CI_bop : 's binary_op;
                  sg_CI_certs : 's sg_CI_certificates; sg_CI_ast : ast_sg_CI }

val sg_CI_eqv : 'a1 sg_CI -> 'a1 eqv

val sg_CI_bop : 'a1 sg_CI -> 'a1 binary_op

val sg_CI_certs : 'a1 sg_CI -> 'a1 sg_CI_certificates

val sg_CI_ast : 'a1 sg_CI -> ast_sg_CI

type 's sg_CS = { sg_CS_eqv : 's eqv; sg_CS_bop : 's binary_op;
                  sg_CS_certs : 's sg_CS_certificates; sg_CS_ast : ast_sg_CS }

val sg_CS_eqv : 'a1 sg_CS -> 'a1 eqv

val sg_CS_bop : 'a1 sg_CS -> 'a1 binary_op

val sg_CS_certs : 'a1 sg_CS -> 'a1 sg_CS_certificates

val sg_CS_ast : 'a1 sg_CS -> ast_sg_CS

type 's sg_CK = { sg_CK_eqv : 's eqv; sg_CK_bop : 's binary_op;
                  sg_CK_certs : 's sg_CK_certificates; sg_CK_ast : ast_sg_CK }

val sg_CK_eqv : 'a1 sg_CK -> 'a1 eqv

val sg_CK_bop : 'a1 sg_CK -> 'a1 binary_op

val sg_CK_certs : 'a1 sg_CK -> 'a1 sg_CK_certificates

val sg_CK_ast : 'a1 sg_CK -> ast_sg_CK

type 's sg_sg = { sg_sg_eqv : 's eqv; sg_sg_plus : 's binary_op;
                  sg_sg_times : 's binary_op;
                  sg_sg_plus_certs : 's sg_certificates;
                  sg_sg_times_certs : 's sg_certificates;
                  sg_sg_certs : 's sg_sg_certificates; sg_sg_ast : ast_sg_sg }

val sg_sg_eqv : 'a1 sg_sg -> 'a1 eqv

val sg_sg_plus : 'a1 sg_sg -> 'a1 binary_op

val sg_sg_times : 'a1 sg_sg -> 'a1 binary_op

val sg_sg_plus_certs : 'a1 sg_sg -> 'a1 sg_certificates

val sg_sg_times_certs : 'a1 sg_sg -> 'a1 sg_certificates

val sg_sg_certs : 'a1 sg_sg -> 'a1 sg_sg_certificates

val sg_sg_ast : 'a1 sg_sg -> ast_sg_sg

type 's sg_C_sg = { sg_C_sg_eqv : 's eqv; sg_C_sg_plus : 's binary_op;
                    sg_C_sg_times : 's binary_op;
                    sg_C_sg_plus_certs : 's sg_C_certificates;
                    sg_C_sg_times_certs : 's sg_certificates;
                    sg_C_sg_certs : 's sg_sg_certificates;
                    sg_C_sg_ast : ast_sg_C_sg }

val sg_C_sg_eqv : 'a1 sg_C_sg -> 'a1 eqv

val sg_C_sg_plus : 'a1 sg_C_sg -> 'a1 binary_op

val sg_C_sg_times : 'a1 sg_C_sg -> 'a1 binary_op

val sg_C_sg_plus_certs : 'a1 sg_C_sg -> 'a1 sg_C_certificates

val sg_C_sg_times_certs : 'a1 sg_C_sg -> 'a1 sg_certificates

val sg_C_sg_certs : 'a1 sg_C_sg -> 'a1 sg_sg_certificates

val sg_C_sg_ast : 'a1 sg_C_sg -> ast_sg_C_sg

type 's sg_CI_sg = { sg_CI_sg_eqv : 's eqv; sg_CI_sg_plus : 's binary_op;
                     sg_CI_sg_times : 's binary_op;
                     sg_CI_sg_plus_certs : 's sg_CI_certificates;
                     sg_CI_sg_times_certs : 's sg_certificates;
                     sg_CI_sg_certs : 's sg_sg_certificates;
                     sg_CI_sg_ast : ast_sg_CI_sg }

val sg_CI_sg_eqv : 'a1 sg_CI_sg -> 'a1 eqv

val sg_CI_sg_plus : 'a1 sg_CI_sg -> 'a1 binary_op

val sg_CI_sg_times : 'a1 sg_CI_sg -> 'a1 binary_op

val sg_CI_sg_plus_certs : 'a1 sg_CI_sg -> 'a1 sg_CI_certificates

val sg_CI_sg_times_certs : 'a1 sg_CI_sg -> 'a1 sg_certificates

val sg_CI_sg_certs : 'a1 sg_CI_sg -> 'a1 sg_sg_certificates

val sg_CI_sg_ast : 'a1 sg_CI_sg -> ast_sg_CI_sg

type 's sg_CS_sg = { sg_CS_sg_eqv : 's eqv; sg_CS_sg_plus : 's binary_op;
                     sg_CS_sg_times : 's binary_op;
                     sg_CS_sg_plus_certs : 's sg_CS_certificates;
                     sg_CS_sg_times_certs : 's sg_certificates;
                     sg_CS_sg_certs : 's sg_sg_certificates;
                     sg_CS_sg_ast : ast_sg_CS_sg }

val sg_CS_sg_eqv : 'a1 sg_CS_sg -> 'a1 eqv

val sg_CS_sg_plus : 'a1 sg_CS_sg -> 'a1 binary_op

val sg_CS_sg_times : 'a1 sg_CS_sg -> 'a1 binary_op

val sg_CS_sg_plus_certs : 'a1 sg_CS_sg -> 'a1 sg_CS_certificates

val sg_CS_sg_times_certs : 'a1 sg_CS_sg -> 'a1 sg_certificates

val sg_CS_sg_certs : 'a1 sg_CS_sg -> 'a1 sg_sg_certificates

val sg_CS_sg_ast : 'a1 sg_CS_sg -> ast_sg_CS_sg

