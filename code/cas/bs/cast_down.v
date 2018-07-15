Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.  
Require Import CAS.code.cef.  
Require Import CAS.code.ast.
Require Import CAS.code.eqv_certificates.
Require Import CAS.code.eqv_cert_records. 
Require Import CAS.code.eqv_records. 
Require Import CAS.code.bs_certificates.
Require Import CAS.code.bs_cert_records. 
Require Import CAS.code.bs_records. 
Require Import CAS.code.cas.sg.cast_down. 



Definition bs_C_option_from_bs : ∀ {S : Type},  bs (S := S) -> option (bs_C (S := S)) 
:= λ {S} s, 
   match sg_C_certs_option_from_sg_certs (bs_plus_certs s) with 
   | None => None
   | Some sg_C_p => Some (
     {| 
         bs_C_eqv          := bs_eqv s
       ; bs_C_plus         := bs_plus s
       ; bs_C_times        := bs_times s
       ; bs_C_plus_certs  := sg_C_p
       ; bs_C_times_certs := bs_times_certs s
       ; bs_C_certs       := bs_certs  s 
       ; bs_C_ast          := Ast_bs_C_from_bs (bs_ast  s)
    |})
   end. 

Definition bs_CS_option_from_bs : ∀ {S : Type},  bs (S := S) -> option (bs_CS (S := S)) 
:= λ {S} s, 
   match sg_CS_certs_option_from_sg_certs (bs_plus_certs s) with 
   | None => None
   | Some sg_CS_p => Some (
     {| 
         bs_CS_eqv          := bs_eqv s
       ; bs_CS_plus         := bs_plus s
       ; bs_CS_times        := bs_times s
       ; bs_CS_plus_certs  := sg_CS_p
       ; bs_CS_times_certs := bs_times_certs s
       ; bs_CS_certs       := bs_certs s 
       ; bs_CS_ast          := Ast_bs_CS_from_bs (bs_ast s)
    |})
   end. 

