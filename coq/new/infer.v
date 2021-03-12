Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.data.
Require Import CAS.coq.new.ast.
Require Import CAS.coq.new.signatures.
Require Import CAS.coq.new.sg_constructions.
Require Import CAS.coq.new.sg_proofs. 
Require Import CAS.coq.common.sg_certificates.
Require Import CAS.coq.common.bop_properties. 
Require Import CAS.coq.new.min.
Require Import CAS.coq.new.max.

Open Scope string.
Open Scope list. 

Fixpoint sg_ast_type (sg : ast_sg) : Type := 
match sg with
   | Ast_sg_times  =>              nat
   | Ast_sg_plus  =>               nat
   | Ast_sg_min  =>                nat
   | Ast_sg_max  =>                nat                                                                       
   | Ast_sg_add_id (c, sg) =>      cas_constant + (sg_ast_type sg)
   | Ast_sg_add_ann (c, sg) =>     cas_constant + (sg_ast_type sg)
   | Ast_sg_product (sg1, sg2) =>  (sg_ast_type sg1) * (sg_ast_type sg2)
   | Ast_sg_llex (sg1, sg2) =>     (sg_ast_type sg1) * (sg_ast_type sg2)                                                         
   | _ => nat                                                     
   end.


Fixpoint sg_gen (sgAST : ast_sg) : (@sg (sg_ast_type sgAST)) + (list string) :=
  match sgAST with
(*    
   | Ast_sg_times  =>              inl sg_times 
   | Ast_sg_plus =>                inl sg_plus
 *)
   | Ast_sg_min  =>                inl sg_min
   | Ast_sg_max =>                 inl sg_max
   | Ast_sg_concat eqv =>          inr ("" ::nil)
   | Ast_sg_left   eqv =>          inr ("" :: nil)
   | Ast_sg_right  eqv =>          inr ("" :: nil)
   | Ast_sg_left_sum(sg1, sg2) =>  inr ("" :: nil)
   | Ast_sg_right_sum(sg1, sg2) => inr ("" :: nil)
   | Ast_sg_product(sg1, sg2) =>   (match sg_gen sg1, sg_gen sg2 with
                                    | inl sg1', inl sg2'  => inl (sg_product sg1' sg2')
                                    | inl _   , inr sl    => inr sl
                                    | inr sl, inl _       => inr sl
                                    | inr sl1, inr sl2    => inr(sl1 ++ sl2)
                                    end) 
   | Ast_sg_llex(sg1, sg2) =>      (match sg_gen sg1, sg_gen sg2 with
                                    | inl sg1', inl sg2'  => inl (sg_llex sg1' sg2')
                                    | inl _   , inr sl    => inr sl
                                    | inr sl, inl _       => inr sl
                                    | inr sl1, inr sl2    => inr(sl1 ++ sl2)
                                    end) 
   | Ast_sg_add_id (c, sg) =>      (match sg_gen sg with | inl sg' => inl (sg_add_id c sg')  | inr sl => inr sl end)
   | Ast_sg_add_ann (c, sg) =>     (match sg_gen sg with | inl sg' => inl (sg_add_ann c sg') | inr sl => inr sl end)
   | Ast_sg_lift sg =>             inr ("" :: nil)
   | _ =>                          inr ("" :: nil)
   end. 



Fixpoint sg_proofs_gen_additive (sgAST : ast_sg) :
                                          (match sg_gen sgAST with
                                            | inl sg => sg_proofs (sg_ast_type sgAST) (eqv_eq (sg_eq sg)) (sg_bop sg)
                                            | inr sl => list string 
                                           end) :=
match sgAST with
   | Ast_sg_plus =>                 ("" ::nil)
   | Ast_sg_concat eqv =>           ("" ::nil)
   | Ast_sg_left   eqv =>           ("" :: nil)
   | Ast_sg_right  eqv =>           ("" :: nil)
   | Ast_sg_left_sum(sg1, sg2) =>   ("" :: nil)
   | Ast_sg_right_sum(sg1, sg2) =>  ("" :: nil)
   | _ =>                           ("" :: nil)
   end. 
