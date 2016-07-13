
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
   theory/properties.v \
   theory/facts.v \
   theory/brel_eq_bool.v \
   theory/brel_eq_nat.v \
   theory/brel_eq_list.v \
   theory/brel_product.v \
   theory/brel_sum.v \
   theory/brel_dual.v \
   theory/brel_conjunction.v \
   theory/brel_llte_llt.v \
   theory/brel_reduce.v \
   theory/brel_add_constant.v \
   theory/brel_and_sym.v \
   theory/brel_reduce.v \
   theory/brel_reduce.v \
   theory/brel_reverse.v \
   theory/brel_strictify.v \
   theory/bop_and.v \
   theory/bop_or.v \
   theory/bop_min.v \
   theory/bop_max.v \
   theory/bop_plus.v \
   theory/bop_times.v \
   theory/bop_concat.v \
   theory/bop_list_product.v \
   theory/bop_left.v \
   theory/bop_right.v \
   theory/bop_product.v \
   theory/bop_left_sum.v \
   theory/bop_right_sum.v \
   theory/bop_llex.v \
   theory/bop_then_unary.v \
   theory/bop_union.v \
   theory/bop_intersect.v \
   theory/bop_add_id.v \
   theory/bop_add_ann.v \
   theory/bops_and_or.v \
   theory/bops_or_and.v \
   theory/bops_min_max.v \
   theory/bops_max_min.v \
   theory/bops_min_plus.v \
   theory/bops_max_plus.v \
   theory/bops_product_product.v \
   theory/bops_llex_product.v \
   theory/bops_add_ann_add_id.v \
   theory/bops_add_id_add_ann.v \
   theory/bops_union_intersect.v \
   theory/bops_intersect_union.v \
   theory/bops_left_sum_right_sum.v \
   theory/brel2_in_list.v \
   theory/brel2_in_set.v \
   theory/brel2_is_minimal_in.v \
   theory/brel_subset.v \
   theory/brel_set.v \
   theory/uop_duplicate_elim.v \
   theory/uop_filter.v \
   theory/bop_reduction.v

VERIFY=\
   verify/proofs_to_certs.v \
   verify/check_correct.v \
   verify/construct_correct.v \
   verify/cas_correct.v \
   verify/cast_correct.v \


FILES=$(CODE) $(ACODE) $(THEORY) $(VERIFY) 

-include $(addsuffix .d,$(FILES))
.SECONDARY: $(addsuffix .d,$(FILES))


all:
	$(MAKE) coq
	$(MAKE) extraction
	$(MAKE) src

theory: $(THEORY:.v=.vo)

coq: $(FILES:.v=.vo)

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

src: extraction/STAMP src/Driver.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.byte

.PHONY: coq extraction src 

%.vo: %.v
	$(COQC) $*.v

%.v.d: %.v
	$(COQDEP) -slash $(COQINCLUDES) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )


cleanocaml:
	rm -rf _build
	rm -rf extraction/*.ml extraction/*.mli

cleancoq:
	rm -f  code/*.glob  a_code/*.glob  theory/*.glob  verify/*.glob
	rm -f  code/*.vo  a_code/*.vo  theory/*.vo  verify/*.vo
	rm -f  code/*.d  a_code/*.d  theory/*.d  verify/*.d
	rm -f extraction/STAMP 

clean:
	$(MAKE) cleancoq
	$(MAKE) cleanocaml

# hard coded. FIX THIS 
cma:
	ocamlc.opt -a -I _build/extraction -o _build/extraction/cas.cma EqNat.cmo Bool.cmo Datatypes.cmo Peano.cmo List0.cmo basic_types.cmo brel.cmo uop.cmo bop.cmo ast.cmo cef.cmo certificates.cmo check.cmo cert_records.cmo construct_certs.cmo cas_records.cmo cas.cmo


