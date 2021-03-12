Require Import CAS.coq.common.base. 
Require Import CAS.coq.sg.cast_down.

Section Theory.

End Theory.

Section ACAS.


Definition A_bs_CS_option_from_bs : ∀ (S : Type),  A_bs S -> option (A_bs_CS S) 
:= λ S s, 
   match A_sg_CS_proofs_option_from_asg_proofs _ _ _ (A_bs_plus_proofs S s) with 
   | None => None
   | Some sg_CS_p => Some (
     {| 
         A_bs_CS_eqv          := A_bs_eqv S s
       ; A_bs_CS_plus         := A_bs_plus S s
       ; A_bs_CS_times        := A_bs_times S s
       ; A_bs_CS_plus_proofs  := sg_CS_p
       ; A_bs_CS_times_proofs := A_bs_times_proofs S s
       ; A_bs_CS_id_ann_proofs := A_bs_id_ann_proofs S s 
       ; A_bs_CS_proofs       := A_bs_proofs S s
       ; A_bs_CS_ast          := Ast_bs_CS_from_bs (A_bs_ast S s)
    |})
   end. 


End ACAS.

Section CAS.


Definition bs_CS_option_from_bs : ∀ {S : Type},  @bs S -> option (@bs_CS S) 
:= λ {S} s, 
   match sg_CS_certs_option_from_asg_certs S (bs_plus_certs s) with 
   | None => None
   | Some sg_CS_p => Some (
     {| 
         bs_CS_eqv          := bs_eqv s
       ; bs_CS_plus         := bs_plus s
       ; bs_CS_times        := bs_times s
       ; bs_CS_plus_certs  := sg_CS_p
       ; bs_CS_times_certs := bs_times_certs s
       ; bs_CS_id_ann_certs := bs_id_ann_certs s                                                
       ; bs_CS_certs       := bs_certs s
       ; bs_CS_ast         := Ast_bs_CS_from_bs (bs_ast s)
    |})
   end. 


End CAS.

Section Verify.
 
End Verify.     