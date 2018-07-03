
Combinators for Algebraic Structures (CAS) 
==========================================
     http://www.cl.cam.ac.uk/~tgg22
             tgg22@cam.ac.uk
==========================================

This is a Coq/Ocaml project to develop a set 
of combinators for constructing algebraic
structures such as semigroups, ordered semigroups, 
semirings, and even more exotic constructions. 

The Coq development has one goal and only one goal: 
to prove that the Ocaml code extracted is correct. 

KEY IDEA 
========
The key idea is as follows. Every class of 
structures (semigroup, bi-semigroup, and so on) 
is associated with a fixed set of properties 
(commutative, idempotent, and so on). 
The combinators are designed so that for any instance 
of a class constructed, the instance automatically contains
an assertion of the truth or falsity of each of the class' 
properties.  In the Coq world these assertions are 
associated with actual proofs, while in the OCaml world
the are just "certificates" in an OCaml datatype. 

BUILD
=====
A "make all" will 
   (1) compile coq code,
   (2) extract Ocaml code (into extraction/),
   (3) compile Ocaml code (into _build/). 

The shell script ./casml then runs a custom Ocaml toplevel
with all of the CAS modules loaded. See documentation [TODO]. 

For a very short demo, enter this toplevel and do a 

     #use "tests/demo.ml";; 


CORRECTNESS
===========

CURRENT LIMITATIONS
===================

HISTORY
=======



