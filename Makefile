
COQINCLUDES= -R . CAS 
COQC=coqc -q $(COQINCLUDES)
COQDOC=coqdoc $(COQINCLUDES)
COQDEP=coqdep -c
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
OCAMLBUILD=ocamlbuild
CAMLINCLUDES= -I extraction -I ocaml
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  $(CAMLINCLUDES)

BASE=\
   coq/common/compute.v \
   coq/common/brel_properties.v \
   coq/common/uop_properties.v \
   coq/common/bop_properties.v \
   coq/common/lt_properties.v \
   coq/common/bs_properties.v \
   coq/common/os_properties.v \
   coq/common/ast.v \
   coq/common/data.v \
   coq/common/proof_records.v \
   coq/common/a_cas_records.v \
   coq/common/eqv_certificates.v \
   coq/common/eqv_cert_records.v \
   coq/common/eqv_records.v \
   coq/common/sg_certificates.v \
   coq/common/sg_cert_records.v \
   coq/common/sg_records.v \
   coq/common/bs_certificates.v \
   coq/common/bs_cert_records.v \
   coq/common/bs_records.v \
   coq/common/eqv_proofs_to_certs.v \
   coq/common/sg_proofs_to_certs.v \
   coq/common/bs_proofs_to_certs.v \
   coq/common/base.v \
   coq/theory/conjunction.v \
   coq/theory/complement.v\
   coq/theory/llte.v \
   coq/theory/in_set.v\
   coq/theory/subset.v\
   coq/theory/facts.v

CAS=\
   coq/eqv/nat.v \
   coq/eqv/bool.v \
   coq/eqv/list.v \
   coq/eqv/set.v \
   coq/eqv/sum.v \
   coq/eqv/product.v \
   coq/eqv/add_constant.v \
   coq/sg/cast_up.v \
   coq/sg/cast_down.v \
   coq/sg/plus.v \
   coq/sg/times.v \
   coq/sg/and.v \
   coq/sg/or.v \
   coq/sg/max.v \
   coq/sg/min.v \
   coq/sg/times.v \
   coq/sg/left.v \
   coq/sg/right.v \
   coq/sg/concat.v \
   coq/sg/left_sum.v \
   coq/sg/right_sum.v \
   coq/sg/product.v \
   coq/sg/llex.v \
   coq/sg/add_id.v \
   coq/sg/add_ann.v \
   coq/sg/union.v \
   coq/sg/intersect.v \
   coq/sg/lift.v \
   coq/bs/cast_up.v \
   coq/bs/cast_down.v \
   coq/bs/min_plus.v \
   coq/bs/max_plus.v \
   coq/bs/dual.v \
   coq/bs/and_or.v \
   coq/bs/or_and.v \
   coq/bs/product_product.v \
   coq/bs/llex_product.v \
   coq/bs/left_sum.v \
   coq/bs/right_sum.v \
   coq/bs/min_max.v \
   coq/bs/max_min.v \
   coq/bs/union_intersect.v \
   coq/bs/intersect_union.v \
   coq/bs/add_id_add_ann.v \
   coq/bs/add_ann_add_id.v \


FILES=$(BASE) $(CAS)

-include $(addsuffix .d,$(FILES))
.SECONDARY: $(addsuffix .d,$(FILES))

# is there a better way? 
CMOFILES=\
Cas.cmo \
../ocaml/Describe.cmo \
../ocaml/Mcas.cmo
# 

.PHONY: all casml html clean

clean:
	rm casml
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

casml: casml extraction/STAMP ocaml/Mcas.ml ocaml/Describe.ml
	mk_casml.sh
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.byte
	cd _build/extraction && ocamlmktop -o casml $(CMOFILES)

html: $(FILES:.v=.glob)
	$(COQDOC) --html --toc --utf8 --charset utf8 --interpolate -d doc/html $(FILES)

%.vo: %.v
	$(COQC) $*.v

%.v.d: %.v
	$(COQDEP) $(COQINCLUDES) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )


