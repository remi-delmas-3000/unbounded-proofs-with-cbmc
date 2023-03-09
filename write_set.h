/* FUNCTION: __CPROVER_contracts_library */
#ifndef __CPROVER_write_set_defined
#define __CPROVER_write_set_defined

/// dynamic frames/write set macros
#define CHECK_ASSIGN(EXPR)                                                     \
  do {                                                                         \
    if (__write_set) {                                                         \
      assert(__CPROVER_contracts_write_set_check_assignment(                   \
          __write_set, &(EXPR), sizeof(EXPR)));                                \
    }                                                                          \
  } while (0)

#define RECORD_DECL(EXPR)                                                      \
  do {                                                                         \
    if (__write_set) {                                                         \
      __CPROVER_contracts_write_set_add_decl(__write_set, &(EXPR));            \
    }                                                                          \
  } while (0)

#define RECORD_DEAD(EXPR)                                                      \
  do {                                                                         \
    if (__write_set) {                                                         \
      __CPROVER_contracts_write_set_record_dead(__write_set, &(EXPR));         \
    }                                                                          \
  } while (0)

// TEMPORARY ADDITION
#define __CPROVER_malloc_failure_mode 0
#define __CPROVER_malloc_failure_mode_return_null 0
#define __CPROVER_malloc_failure_mode_assert_then_assume 0
#define __CPROVER_malloc_may_fail 0

// external dependencies
extern __CPROVER_size_t __CPROVER_max_malloc_size;
const void *__CPROVER_alloca_object = 0;
extern const void *__CPROVER_deallocated;
const void *__CPROVER_new_object = 0;
extern const void *__CPROVER_memory_leak;
__CPROVER_bool __CPROVER_malloc_is_new_array = 0;
int __builtin_clzll(unsigned long long);
__CPROVER_bool __VERIFIER_nondet___CPROVER_bool(void);
__CPROVER_size_t __VERIFIER_nondet_size(void);

/// \brief A conditionally writable range of bytes.
typedef struct {
  /// \brief  True iff __CPROVER_w_ok(lb, size) holds at creation
  __CPROVER_bool is_writable;
  /// \brief Size of the range in bytes
  __CPROVER_size_t size;
  /// \brief Lower bound address of the range
  void *lb;
  /// \brief Upper bound address of the range
  void *ub;
} __CPROVER_contracts_car_t;

/// \brief A set of \ref __CPROVER_contracts_car_t.
typedef struct {
  /// \brief Maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  /// \brief next usable index in elems if less than max_elems
  /// (1 + greatest used index in elems)
  __CPROVER_size_t watermark;
  /// \brief An array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

/// \brief Type of pointers to \ref __CPROVER_contracts_car_set_t.
typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

/// \brief A set of pointers.
typedef struct {
  /// \brief Maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  /// \brief next usable index in elems if less than max_elems
  /// (1 + greatest used index in elems)
  __CPROVER_size_t watermark;
  /// \brief Number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  /// \brief True iff nof_elems is 0
  __CPROVER_bool is_empty;
  /// \brief True iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  /// \brief Array of void *pointers, indexed by their object ID
  /// or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

/// \brief Type of pointers to \ref __CPROVER_contracts_car_set_t.
typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

/// \brief Runtime representation of a write set.
typedef struct {
  /// \brief Set of car derived from the contract
  __CPROVER_contracts_car_set_t contract_assigns;
  /// \brief Set of freeable pointers derived from the contract (indexed mode)
  __CPROVER_contracts_obj_set_t contract_frees;
  /// \brief Set of freeable pointers derived from the contract (append mode)
  __CPROVER_contracts_obj_set_t contract_frees_append;
  /// \brief Set of objects allocated by the function under analysis
  /// (indexed mode)
  __CPROVER_contracts_obj_set_t allocated;
  /// \brief Set of objects deallocated by the function under analysis
  /// (indexed mode)
  __CPROVER_contracts_obj_set_t deallocated;
  /// \brief Pointer to object set supporting the is_fresh predicate checks
  /// (indexed mode)
  __CPROVER_contracts_obj_set_ptr_t linked_is_fresh;
  /// \brief Object set recording the is_fresh allocations in post conditions
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  /// \brief Object set recording the deallocations (used by was_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  /// \brief True iff the write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  /// \brief True iff the write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  /// \brief True iff the write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  /// \brief True iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
  /// \brief True iff dynamic allocation is allowed (default: true)
  __CPROVER_bool allow_allocate;
  /// \brief True iff dynamic deallocation is allowed (default: true)
  __CPROVER_bool allow_deallocate;
} __CPROVER_contracts_write_set_t;

/// \brief Type of pointers to \ref __CPROVER_contracts_write_set_t.
typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;

/// \brief Creates a __CPROVER_car_t struct from \p ptr and  \p size
/// \param[in] ptr Start address of the range
/// \param[in] size Size in bytes
/// \return A \ref __CPROVER_contracts_car_t value
__CPROVER_contracts_car_t
__CPROVER_contracts_car_create(void *ptr, __CPROVER_size_t size) {
__CPROVER_HIDE:;
  __CPROVER_assert(((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
                   "ptr NULL or writable up to size");
  __CPROVER_assert(size <= __CPROVER_max_malloc_size,
                   "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(!(offset > 0) | (offset + size <= __CPROVER_max_malloc_size),
                   "no offset bits overflow on CAR upper bound computation");
  return (__CPROVER_contracts_car_t){.is_writable = ptr != 0,
                                     .size = size,
                                     .lb = ptr,
                                     .ub = (char *)ptr + size};
}

/// \brief Initialises a __CPROVER_contracts_car_set_ptr_t object
/// \param[inout] set Pointer to the object to initialise
/// \param[in] max_elems Max number of elements to store in the set
void __CPROVER_contracts_car_set_create(__CPROVER_contracts_car_set_ptr_t set,
                                        __CPROVER_size_t max_elems) {
__CPROVER_HIDE:;
  set->max_elems = max_elems;
  set->watermark = 0;
  set->elems =
      __CPROVER_allocate(max_elems * sizeof(__CPROVER_contracts_car_t), 1);
}

/// TODO add to actal library
/// \brief Appends a \ref __CPROVER_contracts_car_t snapshotted from \p ptr
/// and \p size into \p set.
/// \param[inout] set Set to insert into
/// \param[in] ptr Pointer to the range of bytes
/// \param[in] size Size of the range in number of bytes
void __CPROVER_contracts_car_set_append(__CPROVER_contracts_car_set_ptr_t set,
                                        void *ptr, __CPROVER_size_t size) {
__CPROVER_HIDE:;
  __CPROVER_assert(((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
                   "ptr NULL or writable up to size");
  __CPROVER_assert(size <= __CPROVER_max_malloc_size,
                   "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(!(offset > 0) | (offset + size <= __CPROVER_max_malloc_size),
                   "no offset bits overflow on CAR upper bound computation");
  __CPROVER_assert(set->watermark < set->max_elems, "set is not full");
  __CPROVER_contracts_car_t *elem = set->elems + set->watermark;
  set->watermark += 1;
  *elem = (__CPROVER_contracts_car_t){.is_writable = ptr != 0,
                                      .size = size,
                                      .lb = ptr,
                                      .ub = (char *)ptr + size};
}

/// \brief Invalidates all cars in the \p set that point into the same object
/// as the given \p ptr.
/// \param[inout] set Set to update
/// \param[in] ptr Pointer to the object to invalidate
void __CPROVER_contracts_car_set_remove(__CPROVER_contracts_car_set_ptr_t set,
                                        void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  __CPROVER_size_t idx = set->max_elems;
  __CPROVER_contracts_car_t *elem = set->elems;
CAR_SET_REMOVE_LOOP:
  while (idx != 0) {
    if (object_id == __CPROVER_POINTER_OBJECT(elem->lb))
      elem->is_writable = 0;
    ++elem;
    --idx;
  }
}

/// \brief Checks if \p candidate is included in one of \p set 's elements.
/// \param[in] set Set to check inclusion in
/// \param[in] candidate A candidate \ref __CPROVER_contracts_car_t
/// \return True iff an element of \p set contains \p candidate
__CPROVER_bool
__CPROVER_contracts_car_set_contains(__CPROVER_contracts_car_set_ptr_t set,
                                     __CPROVER_contracts_car_t candidate) {
__CPROVER_HIDE:;
  __CPROVER_bool incl = 0;
  __CPROVER_size_t idx = set->max_elems;
  __CPROVER_contracts_car_t *elem = set->elems;
CAR_SET_CONTAINS_LOOP:
  while (idx != 0) {
    incl |= (int)candidate.is_writable & (int)elem->is_writable &
            (int)__CPROVER_same_object(elem->lb, candidate.lb) &
            (__CPROVER_POINTER_OFFSET(elem->lb) <=
             __CPROVER_POINTER_OFFSET(candidate.lb)) &
            (__CPROVER_POINTER_OFFSET(candidate.ub) <=
             __CPROVER_POINTER_OFFSET(elem->ub));
    ++elem;
    --idx;
  }

  return incl;
}

/// \brief Initialises a \ref __CPROVER_contracts_obj_set_t object to use it
/// in "indexed by object id" mode.
///
/// The elements array is allocated to `2^OBJECT_BITS`, where object bits is
/// calculated as the number of leading zeroes in the `__CPROVER_max_alloc_size`
/// constant.
///
/// \param[inout] set Pointer to the object to initialise
void __CPROVER_contracts_obj_set_create_indexed_by_object_id(
    __CPROVER_contracts_obj_set_ptr_t set) {
__CPROVER_HIDE:;
  // compute the maximum number of objects that can exist in the
  // symex state from the number of object_bits/offset_bits
  // the number of object bits is determined by counting the number of leading
  // zeroes of the built-in constant __CPROVER_max_malloc_size;
  int object_bits = __builtin_clzll(__CPROVER_max_malloc_size);
  __CPROVER_size_t nof_objects = 1ULL << object_bits;
  *set = (__CPROVER_contracts_obj_set_t){
      .max_elems = nof_objects,
      .watermark = 0,
      .nof_elems = 0,
      .is_empty = 1,
      .indexed_by_object_id = 1,
      .elems = __CPROVER_allocate(nof_objects * sizeof(*(set->elems)), 1)};
}

/// \brief Initialises a \ref __CPROVER_contracts_obj_set_t object to use it
/// in "append" mode for at most \p max_elems elements.
///
/// \param[inout] set Pointer to the object to initialise
/// \param[inout] max_elems Maximum number of objects in the set.
void __CPROVER_contracts_obj_set_create_append(
    __CPROVER_contracts_obj_set_ptr_t set, __CPROVER_size_t max_elems) {
__CPROVER_HIDE:;
  *set = (__CPROVER_contracts_obj_set_t){
      .max_elems = max_elems,
      .watermark = 0,
      .nof_elems = 0,
      .is_empty = 1,
      .indexed_by_object_id = 0,
      .elems = __CPROVER_allocate(max_elems * sizeof(*(set->elems)), 1)};
}

/// @brief Releases resources used by \p set.
void __CPROVER_contracts_obj_set_release(
    __CPROVER_contracts_obj_set_ptr_t set) {
__CPROVER_HIDE:;
  __CPROVER_deallocate(set->elems);
}

/// \brief Adds the \p ptr to \p set.
/// \pre \p set->indexed_by_object_id must be true.
/// \param[inout] set Set to add the pointer to
/// \param[in] ptr The pointer to add
void __CPROVER_contracts_obj_set_add(__CPROVER_contracts_obj_set_ptr_t set,
                                     void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->nof_elems = set->elems[object_id] ? set->nof_elems : set->nof_elems + 1;
  set->elems[object_id] = ptr;
  set->is_empty = 0;
}

/// \brief Appends \p ptr to \p set.
/// \pre \p set->indexed_by_object_id must be false.
/// \param[inout] set The set to append to
/// \param[in] ptr The pointer to append
void __CPROVER_contracts_obj_set_append(__CPROVER_contracts_obj_set_ptr_t set,
                                        void *ptr) {
__CPROVER_HIDE:;
  set->nof_elems = set->watermark;
  set->elems[set->watermark] = ptr;
  set->watermark += 1;
  set->is_empty = 0;
}

/// \brief Removes \p ptr form \p set if \p ptr exists in \p set,
/// no-op otherwise.
/// \param[inout] set Set to update
/// \param[in] ptr Pointer to remove
void __CPROVER_contracts_obj_set_remove(__CPROVER_contracts_obj_set_ptr_t set,
                                        void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->nof_elems = set->elems[object_id] ? set->nof_elems - 1 : set->nof_elems;
  set->is_empty = set->nof_elems == 0;
  set->elems[object_id] = 0;
}

/// \brief Checks if a pointer with the same object id as \p ptr is contained in
/// \p set.
/// \param[inout] set The set to check membership in
/// \param ptr The pointer to check
/// \return True iff a pointer with the same object id exists in \p set
__CPROVER_bool
__CPROVER_contracts_obj_set_contains(__CPROVER_contracts_obj_set_ptr_t set,
                                     void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  return set->elems[object_id] != 0;
}

/// \brief Checks if \p ptr is contained in \p set.
/// \param[inout] set The set to check membership in
/// \param ptr The pointer to check
/// \return True iff \p ptr exists in \p set
__CPROVER_bool __CPROVER_contracts_obj_set_contains_exact(
    __CPROVER_contracts_obj_set_ptr_t set, void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  return set->elems[object_id] == ptr;
}

/// \brief Initialises a \ref __CPROVER_contracts_write_set_t object.
/// \param[inout] set Pointer to the object to initialise
/// \param[in] contract_assigns_size Max size of the assigns clause
/// \param[in] contract_frees_size Max size of the frees clause
/// \param[in] assume_requires_ctx True iff this write set is used to check side
/// effects in a requires clause in contract checking mode
/// \param[in] assert_requires_ctx True iff this write set is used to check side
/// effects in a requires clause in contract replacement mode
/// \param[in] assume_ensures_ctx True iff this write set is used to check for
/// side effects in an ensures clause in contract replacement mode
/// \param[in] assert_ensures_ctx True iff this write set is used to check for
/// side effects in an ensures clause in contract checking mode
/// \param[in] allow_allocate True iff the context gobally allows dynamic
/// allocation.
/// \param[in] allow_deallocate True iff the context gobally allows dynamic
/// deallocation.
void __CPROVER_contracts_write_set_create(
    __CPROVER_contracts_write_set_ptr_t set,
    __CPROVER_size_t contract_assigns_size,
    __CPROVER_size_t contract_frees_size, __CPROVER_bool assume_requires_ctx,
    __CPROVER_bool assert_requires_ctx, __CPROVER_bool assume_ensures_ctx,
    __CPROVER_bool assert_ensures_ctx, __CPROVER_bool allow_allocate,
    __CPROVER_bool allow_deallocate) {
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_create(&(set->contract_assigns),
                                     contract_assigns_size);
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(
      &(set->contract_frees));
  __CPROVER_contracts_obj_set_create_append(&(set->contract_frees_append),
                                            contract_frees_size);
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(&(set->allocated));
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(&(set->deallocated));
  set->linked_is_fresh = 0;
  set->linked_allocated = 0;
  set->linked_deallocated = 0;
  set->assume_requires_ctx = assume_requires_ctx;
  set->assert_requires_ctx = assert_requires_ctx;
  set->assume_ensures_ctx = assume_ensures_ctx;
  set->assert_ensures_ctx = assert_ensures_ctx;
  set->allow_allocate = allow_allocate;
  set->allow_deallocate = allow_deallocate;
}

/// \brief Releases resources used by \p set.
void __CPROVER_contracts_write_set_release(
    __CPROVER_contracts_write_set_ptr_t set) {
__CPROVER_HIDE:;
  __CPROVER_deallocate(set->contract_assigns.elems);
  __CPROVER_deallocate(set->contract_frees.elems);
  __CPROVER_deallocate(set->contract_frees_append.elems);
  __CPROVER_deallocate(set->allocated.elems);
  __CPROVER_deallocate(set->deallocated.elems);
  // do not free set->linked_is_fresh->elems or set->deallocated_linked->elems
  // since they are owned by someone else.
}

/// TODO add to actual library
/// \brief Appends a snapshot of the range starting at \p ptr of size \p size
/// to \p set->contract_assigns.
/// \param[inout] set The set to update
/// \param[in] ptr Start of the range of bytes
/// \param[in] size Size of the range in bytes
void __CPROVER_contracts_write_set_append_assignable(
    __CPROVER_contracts_write_set_ptr_t set, void *ptr, __CPROVER_size_t size) {
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_append(&(set->contract_assigns), ptr, size);
}

/// \brief Adds the dynamically allocated pointer \p ptr to \p set->allocated.
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to a dynamic object `x = __CPROVER_allocate(...)`.
void __CPROVER_contracts_write_set_add_allocated(
    __CPROVER_contracts_write_set_ptr_t set, void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_assert(set->allow_allocate, "dynamic allocation is allowed");
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->allocated.nof_elems = (set->allocated.elems[object_id] != 0)
                                 ? set->allocated.nof_elems
                                 : set->allocated.nof_elems + 1;
  set->allocated.elems[object_id] = ptr;
  set->allocated.is_empty = 0;
}

/// \brief Adds the pointer \p ptr to \p set->allocated.
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to an object declared using `DECL x`.
void __CPROVER_contracts_write_set_add_decl(
    __CPROVER_contracts_write_set_ptr_t set, void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->allocated.nof_elems = (set->allocated.elems[object_id] != 0)
                                 ? set->allocated.nof_elems
                                 : set->allocated.nof_elems + 1;
  set->allocated.elems[object_id] = ptr;
  set->allocated.is_empty = 0;
}

/// \brief Records that an object is dead by removing the pointer \p ptr from
/// \p set->allocated.
///
/// \pre \p ptr is the start address `&x` of an object declared as 'DEAD x'.
///
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to the dead object
void __CPROVER_contracts_write_set_record_dead(
    __CPROVER_contracts_write_set_ptr_t set, void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->allocated.nof_elems = set->allocated.elems[object_id]
                                 ? set->allocated.nof_elems - 1
                                 : set->allocated.nof_elems;
  set->allocated.is_empty = set->allocated.nof_elems == 0;
  set->allocated.elems[object_id] = 0;
}

/// \brief Records that an object is deallocated by adding the pointer \p ptr to
/// \p set->deallocated.
///
/// \pre \p ptr was deallocated with a call to `__CPROVER_deallocate(ptr)`.
///
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to the deallocated object
void __CPROVER_contracts_write_set_record_deallocated(
    __CPROVER_contracts_write_set_ptr_t set, void *ptr) {
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);

  // __CPROVER_contracts_obj_set_add
  set->deallocated.nof_elems = set->deallocated.elems[object_id]
                                   ? set->deallocated.nof_elems
                                   : set->deallocated.nof_elems + 1;
  set->deallocated.elems[object_id] = ptr;
  set->deallocated.is_empty = 0;

  // __CPROVER_contracts_obj_set_remove
  set->allocated.nof_elems = set->allocated.elems[object_id]
                                 ? set->allocated.nof_elems - 1
                                 : set->allocated.nof_elems;
  set->allocated.is_empty = set->allocated.nof_elems == 0;
  set->allocated.elems[object_id] = 0;

  // __CPROVER_contracts_obj_set_remove
  set->contract_frees.nof_elems = set->contract_frees.elems[object_id]
                                      ? set->contract_frees.nof_elems - 1
                                      : set->contract_frees.nof_elems;
  set->contract_frees.is_empty = set->contract_frees.nof_elems == 0;
  set->contract_frees.elems[object_id] = 0;

  // __CPROVER_contracts_car_set_remove
  __CPROVER_size_t idx = set->contract_assigns.max_elems;
  __CPROVER_contracts_car_t *elem = set->contract_assigns.elems;
  while (idx != 0) {
    if (object_id == __CPROVER_POINTER_OBJECT(elem->lb))
      elem->is_writable = 0;
    ++elem;
    --idx;
  }
}

/// \brief Checks if an assignment to the range of bytes starting at \p ptr and
/// of \p size bytes is allowed according to \p set.
///
/// \param[in] set Write set to check the assignment against
/// \param[in] ptr Start address of the assigned range
/// \param[in] size Size of the assigned range in bytes
/// \return True iff the range of bytes starting at \p ptr of \p size bytes is
/// contained in \p set->allocated or \p set->contract_assigns.
__CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
    __CPROVER_contracts_write_set_ptr_t set, void *ptr, __CPROVER_size_t size) {
__CPROVER_HIDE:;
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "pointer-primitive"
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check disable "signed-overflow"
#pragma CPROVER check disable "undefined-shift"
#pragma CPROVER check disable "conversion"
  __CPROVER_assert(((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
                   "ptr NULL or writable up to size");

  // the range is not writable
  if (ptr == 0)
    return 0;

  // is ptr pointing within some a locally allocated object ?
  if (set->allocated.elems[__CPROVER_POINTER_OBJECT(ptr)] != 0)
    return 1;

  // don't even drive symex into the rest of the function if the set is emtpy
  if (set->contract_assigns.max_elems == 0)
    return 0;

  // Compute the upper bound, perform inclusion check against contract-assigns
  __CPROVER_assert(size <= __CPROVER_max_malloc_size,
                   "CAR size is less than __CPROVER_max_malloc_size");

  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);

  __CPROVER_assert(!(offset > 0) | (offset + size <= __CPROVER_max_malloc_size),
                   "no offset bits overflow on CAR upper bound computation");
  void *ub = (void *)((char *)ptr + size);
  __CPROVER_contracts_car_t *elem = set->contract_assigns.elems;
  __CPROVER_size_t idx = set->contract_assigns.max_elems;
  __CPROVER_bool incl = 0;

SET_CHECK_ASSIGNMENT_LOOP:
  while (idx != 0) {
    incl |=
        (int)elem->is_writable & (int)__CPROVER_same_object(elem->lb, ptr) &
        (__CPROVER_POINTER_OFFSET(elem->lb) <= offset) &
        (__CPROVER_POINTER_OFFSET(ub) <= __CPROVER_POINTER_OFFSET(elem->ub));
    ++elem;
    --idx;
  }
  return incl;
#pragma CPROVER check pop
}
#endif // __CPROVER_write_set_defined
