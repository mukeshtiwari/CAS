open Datatypes

type cas_constant = char list

type 's with_constant = (cas_constant, 's) sum

type 's brel = 's -> 's -> bool

type ('s, 't) brel2 = 's -> 't -> bool

type 's bProp = 's -> bool

type 's unary_op = 's -> 's

type 's binary_op = 's -> 's -> 's

type 's finite_set = 's list

