original:
	cbmc --unwind 10 --pointer-check --bounds-check --signed-overflow-check --function original abstract_dynamic_objects.c

loop_elim:
	cbmc --nondet-static --pointer-check --bounds-check --signed-overflow-check --function loop_elimination abstract_dynamic_objects.c

lemmas:
	cbmc --nondet-static --pointer-check --bounds-check --signed-overflow-check --function lemma_inference abstract_dynamic_objects.c

bug:
	cbmc --nondet-static --function main abstract_dynamic_objects_havoc_bug.c
