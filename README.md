
Combinators for Algebraic Structures (CAS) 
==========================================
     http://www.cl.cam.ac.uk/~tgg22 (tgg22@cam.ac.uk)
  Mukesh Tiwari (https://mukeshtiwari.github.io/)

==========================================

This is a Coq/Ocaml project to develop a set 
of combinators for algebraic structures used to
solve path problems.  Such structures include
semirings/dioids and their generalisations. 

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


DEMO
=====
For a very short demo, enter this toplevel and do a 

     #use "tests/demo.ml";;

explain CAS vs MCAS .... 

GOALS
=====
The main goal is to produce the OCaml libraries that
can be distributed, documented, and used without Coq.
The intent is that this library should be useful to
communities that do not know theorem proving and
do not want to know theorem proving.

STYLE
=====
The are several ways in which the Coq portion of this
project differs from typical Coq developments.

1) Tactics are used very infrequently. This is for three main
   reasons.  First, as the system has undergone many rewrites
   and modifications to all of the basic definitions, it was found that
   when using tactics this development churn often broke tactics in ways that 
   where difficult to debug. It was found that avoiding them
   often saved time in the end.  Second, Tactics often 
   obscured the proof structure. The proofs here serve 
   as a guide to their manual translation to standard
   mathematics (see [???]). This is important for documentation and
   the desire that the algorithms/results here outlive this
   Coq implementation.  Finally, the very nature of this
   development pays special attention to exactly
   which properties are used in each proof, thus
   allowing some (often unexpected) generalisations
   when properties are *not* used (for example, see the genralisations
   of partial orders to pre-orders lacking anti-symmetry).
   In proofs using complex tactics it is often difficult and time-consuming to
   determine which properties were used actually.

   It must be admitted that this aversion to tactics may have
   gone too far in this development, but there were good
   reasons for it. One might then ask "Why not Agda?"
   The answer is simple: Agda does not (currently) have anything like
   Coq's extraction mechanism (altough it must be said that
   Agda's equational reasoning facility was sorely missed). 

2) The Coq library itself is not the main goal of the project.
   The extracted OCaml library is.  


CORRECTNESS
===========

CURRENT LIMITATIONS
===================

HISTORY
=======

REFERENCES
==========



