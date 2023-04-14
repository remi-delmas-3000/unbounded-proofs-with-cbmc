list_init_unbounded:
	time cbmc --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula list_init_unbounded.c

list_init_unbounded_hidden_fail:
	time cbmc -DASSIGN_HIDDEN --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula list_init_unbounded.c

list_init_unbounded_hidden_fix:
	time cbmc -DASSIGN_HIDDEN -DFIX_ASSIGN_HIDDEN --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula list_init_unbounded.c

list_search_bounded:
	goto-cc list_search_bounded.c -o a.out
	goto-instrument --dfcc main --enforce-contract-rec list_search a.out b.out
	time cbmc --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula b.out
	rm a.out b.out

list_search_unbounded:
	time cbmc --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula list_search_unbounded.c

list_insert_before:
	time cbmc --function list_insert_before_harness --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula doubly_linked_list_unbounded.c

list_is_valid:
	time cbmc --function list_is_valid_harness --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula doubly_linked_list_unbounded.c

maybe_list:
	time cbmc --function maybe_list_harness --bounds-check --pointer-check --pointer-overflow-check --sat-solver cadical --slice-formula doubly_linked_list_unbounded.c
