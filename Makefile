
COQINCLUDES= -R . CAS 
COQC=coqc -q $(COQINCLUDES)
COQDOC=coqdoc $(COQINCLUDES)
COQDEP=coqdep -c
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
OCAMLBUILD=ocamlbuild
CAMLINCLUDES= -I extraction -I src 
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  $(CAMLINCLUDES)

CODE=\
   code/basic_types.v \
   code/ast.v \
   code/data.v \
   code/brel.v \
   code/bop.v \
   code/trans.v \
   code/cef.v \
   code/uop.v \
   code/bprop.v \
   code/combined.v \
   code/eqv_certificates.v \
   code/sg_certificates.v \
   code/bs_certificates.v \
   code/eqv_cert_records.v \
   code/sg_cert_records.v \
   code/bs_cert_records.v \
   code/eqv_records.v \
   code/sg_records.v \
   code/bs_records.v \
   code/cas/eqv/add_constant.v \
   code/cas/eqv/bool.v \
   code/cas/eqv/list.v \
   code/cas/eqv/nat.v \
   code/cas/eqv/product.v \
   code/cas/eqv/sum.v \
   code/cas/eqv/set.v \
   code/cas/sg/cast_up.v \
   code/cas/sg/cast_down.v \
   code/cas/sg/and.v \
   code/cas/sg/or.v \
   code/cas/sg/max.v \
   code/cas/sg/min.v \
   code/cas/sg/plus.v \
   code/cas/sg/add_ann.v \
   code/cas/sg/add_id.v \
   code/cas/sg/left.v \
   code/cas/sg/right.v \
   code/cas/sg/concat.v \
   code/cas/sg/product.v \
   code/cas/sg/left_sum.v \
   code/cas/sg/right_sum.v \
   code/cas/sg/llex.v \
   code/cas/sg/intersect.v \
   code/cas/sg/union.v \
   code/cas/bs/add_one.v \
   code/cas/bs/add_zero.v \
   code/cas/bs/and_or.v \
   code/cas/bs/cast_up.v \
   code/cas/bs/cast_down.v \
   code/cas/bs/or_and.v \
   code/cas/bs/max_min.v \
   code/cas/bs/min_max.v \
   code/cas/bs/min_plus.v \
   code/cas/bs/max_plus.v \
   code/cas/bs/product.v \
   code/cas/bs/llex_product.v \
   code/cas/bs/dual.v 

ACODE=\
   a_code/proof_records.v \
   a_code/a_cas_records.v \
   a_code/a_cas/eqv/bool.v \
   a_code/a_cas/eqv/nat.v \
   a_code/a_cas/eqv/add_constant.v \
   a_code/a_cas/eqv/list.v \
   a_code/a_cas/eqv/sum.v \
   a_code/a_cas/eqv/sum.v \
   a_code/a_cas/eqv/product.v \
   a_code/a_cas/eqv/set.v \
   a_code/a_cas/sg/cast_up.v \
   a_code/a_cas/sg/and.v \
   a_code/a_cas/sg/or.v \
   a_code/a_cas/sg/min.v \
   a_code/a_cas/sg/max.v \
   a_code/a_cas/sg/times.v \
   a_code/a_cas/sg/plus.v \
   a_code/a_cas/sg/concat.v \
   a_code/a_cas/sg/left.v \
   a_code/a_cas/sg/right.v \
   a_code/a_cas/sg/add_id.v \
   a_code/a_cas/sg/add_ann.v \
   a_code/a_cas/sg/left_sum.v \
   a_code/a_cas/sg/right_sum.v \
   a_code/a_cas/sg/product.v \
   a_code/a_cas/sg/llex.v \
   a_code/a_cas/sg/union.v \
   a_code/a_cas/sg/intersect.v \
   a_code/a_cas/bs/dual.v \
   a_code/a_cas/bs/and_or.v \
   a_code/a_cas/bs/or_and.v \
   a_code/a_cas/bs/min_max.v \
   a_code/a_cas/bs/max_min.v \
   a_code/a_cas/bs/min_plus.v \
   a_code/a_cas/bs/max_plus.v \
   a_code/a_cas/bs/add_one.v \
   a_code/a_cas/bs/add_zero.v \
   a_code/a_cas/bs/product.v \
   a_code/a_cas/bs/left_sum.v \
   a_code/a_cas/bs/right_sum.v \
   a_code/a_cas/bs/llex_product.v \
   a_code/a_cas/bs/union_intersect.v \
   a_code/a_cas/bs/intersect_union.v \


THEORY=\
   theory/brel_properties.v \
   theory/uop_properties.v \
   theory/bop_properties.v \
   theory/lt_properties.v \
   theory/bs_properties.v \
   theory/os_properties.v \
   theory/facts.v \
   theory/brel/eq_bool.v \
   theory/brel/eq_nat.v \
   theory/brel/eq_list.v \
   theory/brel/product.v \
   theory/brel/sum.v \
   theory/brel/dual.v \
   theory/brel/complement.v \
   theory/brel/conjunction.v \
   theory/brel/llte.v \
   theory/brel/rlte.v \
   theory/brel/add_constant.v \
   theory/brel/strictify.v \
   theory/brel/to_bool.v \
   theory/brel/to_nat.v \
   theory/brel/reduce.v \
   theory/brel/in_set.v \
   theory/brel/subset.v \
   theory/brel/set.v \
   theory/bop/and.v \
   theory/bop/or.v \
   theory/bop/min.v \
   theory/bop/max.v \
   theory/bop/plus.v \
   theory/bop/times.v \
   theory/bop/concat.v \
   theory/bop/left.v \
   theory/bop/right.v \
   theory/bop/product.v \
   theory/bop/left_sum.v \
   theory/bop/right_sum.v \
   theory/bop/llex.v \
   theory/bop/add_id.v \
   theory/bop/add_ann.v \
   theory/bop/union.v \
   theory/bop/lift.v \
   theory/bop/intersect.v \
   theory/bop/reduction_theory.v \
   theory/bop/full_reduce.v \
   theory/bop/predicate_reduce.v \
   theory/bop/reduce_annihilators.v \
   theory/lt/cons.v \
   theory/bs/and_or.v \
   theory/bs/or_and.v \
   theory/bs/min_max.v \
   theory/bs/max_min.v \
   theory/bs/min_plus.v \
   theory/bs/max_plus.v \
   theory/bs/product_product.v \
   theory/bs/llex_product.v \
   theory/bs/add_ann_add_id.v \
   theory/bs/add_id_add_ann.v \
   theory/bs/left_sum_right_sum.v \
   theory/bs/right_sum_left_sum.v \
   theory/bs/union_intersect.v \
   theory/bs/intersect_union.v \
   theory/bs/union_lift.v \
   theory/bs/reduction_theory.v \
   theory/structures/semilattice.v \
   theory/structures/lattice.v \

VERIFY=\
   verify/eqv_proofs_to_certs.v \
   verify/eqv/add_constant.v \
   verify/eqv/bool.v \
   verify/eqv/list.v \
   verify/eqv/nat.v \
   verify/eqv/product.v \
   verify/eqv/sum.v \
   verify/eqv/set.v \
   verify/sg_proofs_to_certs.v \
   verify/sg/and.v \
   verify/sg/or.v \
   verify/sg/max.v \
   verify/sg/min.v \
   verify/sg/plus.v \
   verify/sg/times.v \
   verify/sg/add_ann.v \
   verify/sg/add_id.v \
   verify/sg/concat.v \
   verify/sg/left.v \
   verify/sg/right.v \
   verify/sg/product.v \
   verify/sg/left_sum.v \
   verify/sg/right_sum.v \
   verify/sg/llex.v \
   verify/sg/union.v \
   verify/sg/intersect.v \
   verify/bs_proofs_to_certs.v \
   verify/bs/add_one.v \
   verify/bs/add_zero.v \
   verify/bs/dual.v \

FILES=$(CODE) $(ACODE) $(THEORY) $(VERIFY) 

-include $(addsuffix .d,$(FILES))
.SECONDARY: $(addsuffix .d,$(FILES))


# is there a better way? 
CMOFILES=\
Cas.cmo \
../src/Describe.cmo
# 

.PHONY: all casml html clean

clean:
	rm -f  */*.glob  */*/*.glob */*/*/*.glob 
	rm -f  */*.vo  */*/*.vo */*/*/*.vo 
	rm -f  */*.d  */*/*.d */*/*/*.d 
	rm -f  */.*.aux  */*/.*.aux */*/*/.*.aux 
	rm -rf _build
	rm -rf extraction/*.ml extraction/*.mli extraction/STAMP

cleancasml:
	rm -rf _build


all:
	$(MAKE) coq
	$(MAKE) extraction
	$(MAKE) casml


depend: $(FILES:.v=.v.d)

coq: $(FILES:.v=.vo) depend

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

casml: extraction/STAMP src/Mcas.ml src/Describe.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.byte
	cd _build/extraction && ocamlmktop -o casml $(CMOFILES)

html: $(FILES:.v=.glob)
	$(COQDOC) --html --toc --utf8 --charset utf8 --interpolate -d doc/html $(FILES)

%.vo: %.v
	$(COQC) $*.v

%.v.d: %.v
	$(COQDEP) $(COQINCLUDES) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )


