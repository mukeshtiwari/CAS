
DIRS=code a_code theory verify 
#COQINCLUDES=$(foreach d, $(DIRS), -R $(d))
COQINCLUDES= -R . CAS 

COQC=coqc -q $(COQINCLUDES)
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
   code/cef.v \
   code/uop.v \
   code/bprop.v \
   code/certificates.v \
   code/cert_records.v \
   code/cast.v \
   code/check.v \
   code/construct_certs.v \
   code/cas_records.v \
   code/cas.v

ACODE=\
   a_code/proof_records.v \
   a_code/decide.v \
   a_code/construct_proofs.v \
   a_code/a_cas_records.v \
   a_code/a_cast.v \
   a_code/a_cas.v 

THEORY=\
   theory/brel_properties.v \
   theory/uop_properties.v \
   theory/bop_properties.v \
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
   theory/brel/reduce.v \
   theory/brel/add_constant.v \
   theory/brel/add_bottom.v \
   theory/brel/add_top.v \
   theory/brel/and_sym.v \
   theory/brel/reduce.v \
   theory/brel/reduce.v \
   theory/brel/strictify.v \
   theory/brel/to_bool.v \
   theory/brel/to_nat.v \
   theory/bop/and.v \
   theory/bop/or.v \
   theory/bop/min.v \
   theory/bop/max.v \
   theory/bop/plus.v \
   theory/bop/times.v \
   theory/bop/concat.v \
   theory/bop/list_product.v \
   theory/bop/left.v \
   theory/bop/right.v \
   theory/bop/product.v \
   theory/bop/left_sum.v \
   theory/bop/right_sum.v \
   theory/bop/llex.v \
   theory/bop/then_unary.v \
   theory/bop/union.v \
   theory/bop/intersect.v \
   theory/bop/add_id.v \
   theory/bop/add_ann.v \
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
   theory/bs/union_intersect.v \
   theory/bs/intersect_union.v \
   theory/bs/left_sum_right_sum.v \
   theory/brel/in_list.v \
   theory/brel/in_set.v \
   theory/brel/is_minimal_in.v \
   theory/brel/subset.v \
   theory/brel/set.v \
   theory/uop/duplicate_elim.v \
   theory/uop/filter.v \
   theory/bop/reduction.v

VERIFY=\
   verify/proofs_to_certs.v \
   verify/check_correct.v \
   verify/construct_correct.v \
   verify/cas_correct.v \
   verify/cast_correct.v \


FILES=$(CODE) $(ACODE) $(THEORY) $(VERIFY) 

-include $(addsuffix .d,$(FILES))
.SECONDARY: $(addsuffix .d,$(FILES))


# is there a better way? 
CMOFILES=\
   Bool.cmo \
   Compare_dec.cmo \
   Datatypes.cmo \
   EqNat.cmo \
   List0.cmo \
   Peano.cmo \
   basic_types.cmo \
   ast.cmo \
   data.cmo \
   brel.cmo \
   uop.cmo \
   bop.cmo \
   certificates.cmo \
   cef.cmo \
   cert_records.cmo \
   cas_records.cmo \
   cast.cmo \
   check.cmo \
   construct_certs.cmo \
   cas.cmo \
   ../src/Describe.cmo
# 


all:
	$(MAKE) coq
	$(MAKE) extraction
	$(MAKE) casml

theory: $(THEORY:.v=.vo)

coq: $(FILES:.v=.vo)

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

casml: extraction/STAMP src/Driver.ml src/Describe.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.byte
	cd _build/extraction && ocamlmktop -o casml $(CMOFILES)

.PHONY: coq extraction src 

%.vo: %.v
	$(COQC) $*.v

%.v.d: %.v
	$(COQDEP) -slash $(COQINCLUDES) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

cleancoq:
	rm -f  code/*.glob  a_code/*.glob  theory/*.glob  theory/*/*.glob verify/*.glob
	rm -f  code/*.vo  a_code/*.vo  theory/*.vo theory/*/*.vo  verify/*.vo
	rm -f  code/*.d  a_code/*.d  theory/*.d theory/*/*.d  verify/*.d

cleancasml:
	rm -rf _build
	rm -rf extraction/*.ml extraction/*.mli extraction/STAMP

clean:
	$(MAKE) cleancoq
	$(MAKE) cleancasml



