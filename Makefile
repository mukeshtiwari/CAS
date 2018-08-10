
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

BASE=\
   code/basic_types.v \
   code/ast.v \
   code/data.v \
   code/brel.v \
   code/bop.v \
   code/cef.v \
   code/uop.v \
   code/bprop.v \
   code/combined.v \
   theory/brel_properties.v \
   theory/uop_properties.v \
   theory/bop_properties.v \
   theory/lt_properties.v \
   theory/bs_properties.v \
   theory/os_properties.v \
   a_code/proof_records.v \
   a_code/a_cas_records.v \
   code/eqv_certificates.v \
   code/eqv_cert_records.v \
   code/eqv_records.v \
   code/sg_certificates.v \
   code/sg_cert_records.v \
   code/sg_records.v \
   code/bs_certificates.v \
   code/bs_cert_records.v \
   code/bs_records.v \
   verify/eqv_proofs_to_certs.v \
   verify/sg_proofs_to_certs.v \
   verify/bs_proofs_to_certs.v \
   theory/facts.v

CAS=\
   coq/eqv/nat.v \
   coq/sg/cast_up.v \
   coq/sg/plus.v \
   coq/sg/times.v \
   coq/sg/max.v \
   coq/sg/min.v \
   coq/sg/times.v \
   coq/bs/min_plus.v \
   coq/bs/max_plus.v \
   coq/bs/dual.v \
   coq/bs/min_max.v \
   coq/bs/max_min.v \

FILES=$(BASE) $(CAS)

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


