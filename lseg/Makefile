lseg_lemma:
	cbmc lseg.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_lemma

list_append:
	cbmc -DCBMC=1 list.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_list_append

list_abstract_objects:
	cbmc list_abstract_objects.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_list_append

list_abstract_objects_bug1:
	cbmc -DBUG1 list_abstract_objects.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_list_append

list_abstract_objects_bug2:
	cbmc -DBUG2 list_abstract_objects.c --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check --slice-formula --external-sat-solver kissat 2>&1 | tee log_list_append

indirect_heap:
	cbmc indirect_heap.c --external-sat-solver cadical --slice-formula  --arrays-uf-always --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check  2>&1 | tee log_list_append

indirect_heap_bug1:
	cbmc indirect_heap.c -DBUG1 --external-sat-solver cadical --slice-formula  --arrays-uf-always --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check  2>&1 | tee log_list_append

indirect_heap_bug2:
	cbmc indirect_heap.c -DBUG2 --external-sat-solver cadical --slice-formula  --arrays-uf-always --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check  2>&1 | tee log_list_append

indirect_heap_bug3:
	cbmc indirect_heap.c -DBUG3 --external-sat-solver cadical --slice-formula  --arrays-uf-always --pointer-check --bounds-check --pointer-overflow-check --signed-overflow-check --unsigned-overflow-check --conversion-check  2>&1 | tee log_list_append

indirect_heap_bug4:
	cbmc indirect_heap.c -DBUG4 --external-sat-solver cadical --slice-formula  --arrays-uf-always --pointer-check  2>&1 | tee log_list_append

indirect_heap_bug5:
	cbmc indirect_heap.c -DBUG5 --external-sat-solver cadical --slice-formula  --arrays-uf-always --pointer-check  2>&1 | tee log_list_append

all: lseg_lemma list_append list_abstract_objects list_abstract_objects_bug1 list_abstract_objects_bug2 indirect_heap indirect_heap_bug1 indirect_heap_bug2 indirect_heap_bug3 indirect_heap_bug4 indirect_heap_bug5

.PHONY = lseg_lemma list_append list_abstract_objects list_abstract_objects_bug1 list_abstract_objects_bug2 indirect_heap indirect_heap_bug1 indirect_heap_bug2 indirect_heap_bug3 indirect_heap_bug4 indirect_heap_bug5 all
