# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find theories \( -name "*.v.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete
	rm -f Makefile.coq
.PHONY: clean

# Create Coq Makefile. POSIX awk can't do in-place editing, but coq_makefile wants the real
# filename, so we do some file gymnastics.
Makefile.coq: _CoqProject Makefile awk.Makefile
	coq_makefile -f _CoqProject -o Makefile.coq
	mv Makefile.coq Makefile.coq.tmp && awk -f awk.Makefile Makefile.coq.tmp > Makefile.coq && rm Makefile.coq.tmp

build-dep: phony
	opam install . --deps-only

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
awk.Makefile: ;
opam: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
