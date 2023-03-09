list_init_unbounded:
	cbmc --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat list_init_unbounded.c

list_init_unbounded_hidden_fail:
	cbmc -DASSIGN_HIDDEN --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat list_init_unbounded.c

list_init_unbounded_hidden_fix:
	cbmc -DASSIGN_HIDDEN -DFIX_ASSIGN_HIDDEN --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat list_init_unbounded.c

list_search_bounded:
	goto-cc list_search_bounded.c -o a.out
	goto-instrument --dfcc main --enforce-contract-rec list_search a.out b.out
	cbmc --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat b.out
	rm a.out b.out

list_search_unbounded:
	cbmc --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat list_search_unbounded.c

list_insert_before:
	cbmc --function list_insert_before_harness --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat doubly_linked_list_unbounded.c

list_is_valid:
	cbmc --function list_is_valid_harness --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat doubly_linked_list_unbounded.c

maybe_list:
	cbmc --function maybe_list_harness --bounds-check --pointer-check --pointer-overflow-check --external-sat-solver kissat doubly_linked_list_unbounded.c
