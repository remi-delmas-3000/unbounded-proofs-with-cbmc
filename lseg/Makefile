lseg_lemma:
	cbmc lseg.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_lemma

list_append:
	cbmc -DCBMC=1 list.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_list_append

all: lseg_lemma list_append

.PHONY = all
