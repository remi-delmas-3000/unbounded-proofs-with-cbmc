lseg_lemma:
	cbmc lseg.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat

list_append:
	cbmc list_append.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat

all: lseg_lemma list_append

.PHONY = all
