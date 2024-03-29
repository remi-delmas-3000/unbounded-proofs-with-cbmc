/// \file cprover_contracts.c
/// \brief Types and functions for dynamic frames instrumentation in contracts.

/* FUNCTION: __CPROVER_contracts_library */

#ifndef __CPROVER_contracts_library_defined
#define __CPROVER_contracts_library_defined

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
typedef struct
{
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
typedef struct
{
  /// \brief Maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  /// \brief An array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

/// \brief Type of pointers to \ref __CPROVER_contracts_car_set_t.
typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

/// \brief A set of pointers.
typedef struct
{
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
typedef struct
{
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
__CPROVER_contracts_car_create(void *ptr, __CPROVER_size_t size)
{
__CPROVER_HIDE:;
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");
  __CPROVER_assert(
    size <= __CPROVER_max_malloc_size,
    "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(
    !(offset > 0) | (offset + size <= __CPROVER_max_malloc_size),
    "no offset bits overflow on CAR upper bound computation");
  return (__CPROVER_contracts_car_t){
    .is_writable = ptr != 0, .size = size, .lb = ptr, .ub = (char *)ptr + size};
}

/// \brief Initialises a __CPROVER_contracts_car_set_ptr_t object
/// \param[inout] set Pointer to the object to initialise
/// \param[in] max_elems Max number of elements to store in the set
void __CPROVER_contracts_car_set_create(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t max_elems)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_car_set_t)),
    "set writable");
#endif
  set->max_elems = max_elems;
  set->elems =
    __CPROVER_allocate(max_elems * sizeof(__CPROVER_contracts_car_t), 1);
}

/// \brief Inserts a \ref __CPROVER_contracts_car_t snapshotted from \p ptr
/// and \p size into \p set at index \p idx.
/// \param[inout] set Set to insert into
/// \param[in] idx Insertion index
/// \param[in] ptr Pointer to the range of bytes
/// \param[in] size Size of the range in number of bytes
void __CPROVER_contracts_car_set_insert(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert((set != 0) & (idx < set->max_elems), "no OOB access");
#endif
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");
  __CPROVER_assert(
    size <= __CPROVER_max_malloc_size,
    "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(
    !(offset > 0) | (offset + size <= __CPROVER_max_malloc_size),
    "no offset bits overflow on CAR upper bound computation");
  __CPROVER_contracts_car_t *elem = set->elems + idx;
  *elem = (__CPROVER_contracts_car_t){
    .is_writable = ptr != 0, .size = size, .lb = ptr, .ub = (char *)ptr + size};
}

/// \brief Invalidates all cars in the \p set that point into the same object
/// as the given \p ptr.
/// \param[inout] set Set to update
/// \param[in] ptr Pointer to the object to invalidate
void __CPROVER_contracts_car_set_remove(
  __CPROVER_contracts_car_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  __CPROVER_size_t idx = set->max_elems;
  __CPROVER_contracts_car_t *elem = set->elems;
CAR_SET_REMOVE_LOOP:
  while(idx != 0)
  {
    if(object_id == __CPROVER_POINTER_OBJECT(elem->lb))
      elem->is_writable = 0;
    ++elem;
    --idx;
  }
}

/// \brief Checks if \p candidate is included in one of \p set 's elements.
/// \param[in] set Set to check inclusion in
/// \param[in] candidate A candidate \ref __CPROVER_contracts_car_t
/// \return True iff an element of \p set contains \p candidate
__CPROVER_bool __CPROVER_contracts_car_set_contains(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_contracts_car_t candidate)
{
__CPROVER_HIDE:;
  __CPROVER_bool incl = 0;
  __CPROVER_size_t idx = set->max_elems;
  __CPROVER_contracts_car_t *elem = set->elems;
CAR_SET_CONTAINS_LOOP:
  while(idx != 0)
  {
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
  __CPROVER_contracts_obj_set_ptr_t set)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_obj_set_t)),
    "set writable");
#endif
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
  __CPROVER_contracts_obj_set_ptr_t set,
  __CPROVER_size_t max_elems)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_obj_set_t)),
    "set writable");
#endif
  *set = (__CPROVER_contracts_obj_set_t){
    .max_elems = max_elems,
    .watermark = 0,
    .nof_elems = 0,
    .is_empty = 1,
    .indexed_by_object_id = 0,
    .elems = __CPROVER_allocate(max_elems * sizeof(*(set->elems)), 1)};
}

/// @brief Releases resources used by \p set.
void __CPROVER_contracts_obj_set_release(__CPROVER_contracts_obj_set_ptr_t set)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_obj_set_t)),
    "set readable");
  __CPROVER_assert(__CPROVER_rw_ok(&(set->elems), 0), "set->elems writable");
#endif
  __CPROVER_deallocate(set->elems);
}

/// \brief Adds the \p ptr to \p set.
/// \pre \p set->indexed_by_object_id must be true.
/// \param[inout] set Set to add the pointer to
/// \param[in] ptr The pointer to add
void __CPROVER_contracts_obj_set_add(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
#ifdef DFCC_DEBUG
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(object_id < set->max_elems, "no OOB access");
#endif
  set->nof_elems = set->elems[object_id] ? set->nof_elems : set->nof_elems + 1;
  set->elems[object_id] = ptr;
  set->is_empty = 0;
}

/// \brief Appends \p ptr to \p set.
/// \pre \p set->indexed_by_object_id must be false.
/// \param[inout] set The set to append to
/// \param[in] ptr The pointer to append
void __CPROVER_contracts_obj_set_append(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(!(set->indexed_by_object_id), "not indexed by object id");
  __CPROVER_assert(set->watermark < set->max_elems, "no OOB access");
#endif
  set->nof_elems = set->watermark;
  set->elems[set->watermark] = ptr;
  set->watermark += 1;
  set->is_empty = 0;
}

/// \brief Removes \p ptr form \p set if \p ptr exists in \p set,
/// no-op otherwise.
/// \param[inout] set Set to update
/// \param[in] ptr Pointer to remove
void __CPROVER_contracts_obj_set_remove(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
#ifdef DFCC_DEBUG
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(object_id < set->max_elems, "no OOB access");
#endif
  set->nof_elems = set->elems[object_id] ? set->nof_elems - 1 : set->nof_elems;
  set->is_empty = set->nof_elems == 0;
  set->elems[object_id] = 0;
}

/// \brief Checks if a pointer with the same object id as \p ptr is contained in
/// \p set.
/// \param[inout] set The set to check membership in
/// \param ptr The pointer to check
/// \return True iff a pointer with the same object id exists in \p set
__CPROVER_bool __CPROVER_contracts_obj_set_contains(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
#ifdef DFCC_DEBUG
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(object_id < set->max_elems, "no OOB access");
#endif
  return set->elems[object_id] != 0;
}

/// \brief Checks if \p ptr is contained in \p set.
/// \param[inout] set The set to check membership in
/// \param ptr The pointer to check
/// \return True iff \p ptr exists in \p set
__CPROVER_bool __CPROVER_contracts_obj_set_contains_exact(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
#ifdef DFCC_DEBUG
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(object_id < set->max_elems, "no OOB access");
#endif
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
  __CPROVER_size_t contract_frees_size,
  __CPROVER_bool assume_requires_ctx,
  __CPROVER_bool assert_requires_ctx,
  __CPROVER_bool assume_ensures_ctx,
  __CPROVER_bool assert_ensures_ctx,
  __CPROVER_bool allow_allocate,
  __CPROVER_bool allow_deallocate)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    __CPROVER_w_ok(set, sizeof(__CPROVER_contracts_write_set_t)),
    "set writable");
#endif
  __CPROVER_contracts_car_set_create(
    &(set->contract_assigns), contract_assigns_size);
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(
    &(set->contract_frees));
  __CPROVER_contracts_obj_set_create_append(
    &(set->contract_frees_append), contract_frees_size);
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
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_write_set_t)),
    "set readable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->contract_assigns.elems), 0),
    "contract_assigns writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->contract_frees.elems), 0),
    "contract_frees writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->contract_frees_append.elems), 0),
    "contract_frees_append writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->allocated.elems), 0), "allocated writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->deallocated.elems), 0), "deallocated writable");
#endif
  __CPROVER_deallocate(set->contract_assigns.elems);
  __CPROVER_deallocate(set->contract_frees.elems);
  __CPROVER_deallocate(set->contract_frees_append.elems);
  __CPROVER_deallocate(set->allocated.elems);
  __CPROVER_deallocate(set->deallocated.elems);
  // do not free set->linked_is_fresh->elems or set->deallocated_linked->elems
  // since they are owned by someone else.
}

/// \brief Inserts a snapshot of the range starting at \p ptr of size \p size
/// at index \p idx in \p set->contract_assigns.
/// \param[inout] set The set to update
/// \param[in] idx Insertion index
/// \param[in] ptr Start of the range of bytes
/// \param[in] size Size of the range in bytes
void __CPROVER_contracts_write_set_insert_assignable(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_insert(&(set->contract_assigns), idx, ptr, size);
}

/// \brief Inserts a snapshot of the range of bytes covering the whole object
/// pointed to by \p ptr in \p set->contact_assigns at index \p idx.
///
/// - The start address is `ptr - __CPROVER_POINTER_OFFSET(ptr)`
/// - The size in bytes is `__CPROVER_OBJECT_SIZE(ptr)`
///
/// at index \p idx in \p set.
/// \param[inout] set The set to update
/// \param[in] idx Insertion index
/// \param[in] ptr Pointer to the object
void __CPROVER_contracts_write_set_insert_object_whole(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_insert(
    &(set->contract_assigns),
    idx,
    ((char *)ptr) - __CPROVER_POINTER_OFFSET(ptr),
    __CPROVER_OBJECT_SIZE(ptr));
}

/// \brief Inserts a snapshot of the range of bytes starting at \p ptr and
/// extending to the end of the object in \p set->contact_assigns at index
/// \p idx.
///
/// - The start address is `ptr`
/// - The size in bytes is
///  `__CPROVER_OBJECT_SIZE(ptr) - __CPROVER_POINTER_OFFSET(ptr)`
///
/// \param[inout] set The set to update
/// \param[in] idx Insertion index
/// \param[in] ptr Pointer to the start of the range
void __CPROVER_contracts_write_set_insert_object_from(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr)
{
  __CPROVER_contracts_car_set_insert(
    &(set->contract_assigns),
    idx,
    ptr,
    __CPROVER_OBJECT_SIZE(ptr) - __CPROVER_POINTER_OFFSET(ptr));
}

/// \brief Inserts a snapshot of the range of bytes starting at \p ptr of
/// \p size bytes in \p set->contact_assigns at index \p idx.
///
/// - The start address is `ptr`
/// - The size in bytes is `size`
///
/// \param[inout] set The set to update
/// \param[in] idx Insertion index
/// \param[in] ptr Pointer to the start of the range
/// \param[in] size Size of the range in bytes
void __CPROVER_contracts_write_set_insert_object_upto(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_insert(&(set->contract_assigns), idx, ptr, size);
}

/// \brief Adds the freeable pointer \p ptr to \p set->contract_frees.
/// \param[inout] set The set to update
/// \param[in] ptr The pointer to add
void __CPROVER_contracts_write_set_add_freeable(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  // we don't check yet that the pointer satisfies
  // the __CPROVER_contracts_is_freeable as precondition.
  // preconditions will be checked if there is an actual attempt
  // to free the pointer.

  // store pointer
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
#ifdef DFCC_DEBUG
  // manually inlined below
  __CPROVER_contracts_obj_set_add(&(set->contract_frees), ptr);
  __CPROVER_assert(object_id < set->contract_frees.max_elems, "no OOB access");
#else
  set->contract_frees.nof_elems = (set->contract_frees.elems[object_id] != 0)
                                    ? set->contract_frees.nof_elems
                                    : set->contract_frees.nof_elems + 1;
  set->contract_frees.elems[object_id] = ptr;
  set->contract_frees.is_empty = 0;
#endif

  // append pointer if available
#ifdef DFCC_DEBUG
  __CPROVER_contracts_obj_set_append(&(set->contract_frees_append), ptr);
#else
  set->contract_frees_append.nof_elems = set->contract_frees_append.watermark;
  set->contract_frees_append.elems[set->contract_frees_append.watermark] = ptr;
  set->contract_frees_append.watermark += 1;
  set->contract_frees_append.is_empty = 0;
#endif
}

/// \brief Adds the dynamically allocated pointer \p ptr to \p set->allocated.
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to a dynamic object `x = __CPROVER_allocate(...)`.
void __CPROVER_contracts_write_set_add_allocated(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_assert(set->allow_allocate, "dynamic allocation is allowed");
#if DFCC_DEBUG
  // call inlined below
  __CPROVER_contracts_obj_set_add(&(set->allocated), ptr);
#else
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->allocated.nof_elems = (set->allocated.elems[object_id] != 0)
                               ? set->allocated.nof_elems
                               : set->allocated.nof_elems + 1;
  set->allocated.elems[object_id] = ptr;
  set->allocated.is_empty = 0;
#endif
}

/// \brief Adds the pointer \p ptr to \p set->allocated.
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to an object declared using `DECL x`.
void __CPROVER_contracts_write_set_add_decl(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#if DFCC_DEBUG
  // call inlined below
  __CPROVER_contracts_obj_set_add(&(set->allocated), ptr);
#else
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->allocated.nof_elems = (set->allocated.elems[object_id] != 0)
                               ? set->allocated.nof_elems
                               : set->allocated.nof_elems + 1;
  set->allocated.elems[object_id] = ptr;
  set->allocated.is_empty = 0;
#endif
}

/// \brief Records that an object is dead by removing the pointer \p ptr from
/// \p set->allocated.
///
/// \pre \p ptr is the start address `&x` of an object declared as 'DEAD x'.
///
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to the dead object
void __CPROVER_contracts_write_set_record_dead(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  // manually inlined below
  __CPROVER_contracts_obj_set_remove(&(set->allocated), ptr);
#else
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->allocated.nof_elems = set->allocated.elems[object_id]
                               ? set->allocated.nof_elems - 1
                               : set->allocated.nof_elems;
  set->allocated.is_empty = set->allocated.nof_elems == 0;
  set->allocated.elems[object_id] = 0;
#endif
}

/// \brief Records that an object is deallocated by adding the pointer \p ptr to
/// \p set->deallocated.
///
/// \pre \p ptr was deallocated with a call to `__CPROVER_deallocate(ptr)`.
///
/// \param[inout] set The set to update
/// \param[in] ptr Pointer to the deallocated object
void __CPROVER_contracts_write_set_record_deallocated(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#if DFCC_DEBUG
  // we record the deallocation to be able to evaluate was_freed post conditions
  __CPROVER_contracts_obj_set_add(&(set->deallocated), ptr);
  __CPROVER_contracts_obj_set_remove(&(set->allocated), ptr);
  __CPROVER_contracts_obj_set_remove(&(set->contract_frees), ptr);
  __CPROVER_contracts_car_set_remove(&(set->contract_assigns), ptr);
  // Manually inlined below
#else
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
  while(idx != 0)
  {
    if(object_id == __CPROVER_POINTER_OBJECT(elem->lb))
      elem->is_writable = 0;
    ++elem;
    --idx;
  }
#endif
}

/// \brief Returns true iff \p set->deallocated is empty.
///
/// \param[in] set The set to be checked for emptiness
/// \returns True iff \p set->deallocated is empty
__CPROVER_bool
__CPROVER_contracts_write_set_check_allocated_deallocated_is_empty(
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
  return set->allocated.is_empty & set->deallocated.is_empty;
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
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr,
  __CPROVER_size_t size)
#if DFCC_DEBUG
// manually inlined below
{
__CPROVER_HIDE:;
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");

  __CPROVER_assert(
    (ptr == 0) | (__CPROVER_POINTER_OBJECT(ptr) < set->allocated.max_elems),
    "no OOB access");

  __CPROVER_contracts_car_t car = __CPROVER_contracts_car_create(ptr, size);
  if(!car.is_writable)
    return 0;

  if(set->allocated.elems[__CPROVER_POINTER_OBJECT(ptr)] != 0)
    return 1;

  return __CPROVER_contracts_car_set_contains(&(set->contract_assigns), car);
}
#else
{
__CPROVER_HIDE:;
#  pragma CPROVER check push
#  pragma CPROVER check disable "pointer"
#  pragma CPROVER check disable "pointer-primitive"
#  pragma CPROVER check disable "unsigned-overflow"
#  pragma CPROVER check disable "signed-overflow"
#  pragma CPROVER check disable "undefined-shift"
#  pragma CPROVER check disable "conversion"
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");

  // the range is not writable
  if(ptr == 0)
    return 0;

  // is ptr pointing within some a locally allocated object ?
  if(set->allocated.elems[__CPROVER_POINTER_OBJECT(ptr)] != 0)
    return 1;

  // don't even drive symex into the rest of the function if the set is emtpy
  if(set->contract_assigns.max_elems == 0)
    return 0;

  // Compute the upper bound, perform inclusion check against contract-assigns
  __CPROVER_assert(
    size <= __CPROVER_max_malloc_size,
    "CAR size is less than __CPROVER_max_malloc_size");

  __CPROVER_size_t offset = __CPROVER_POINTER_OFFSET(ptr);

  __CPROVER_assert(
    !(offset > 0) | (offset + size <= __CPROVER_max_malloc_size),
    "no offset bits overflow on CAR upper bound computation");
  void *ub = (void *)((char *)ptr + size);
  __CPROVER_contracts_car_t *elem = set->contract_assigns.elems;
  __CPROVER_size_t idx = set->contract_assigns.max_elems;
  __CPROVER_bool incl = 0;

SET_CHECK_ASSIGNMENT_LOOP:
  while(idx != 0)
  {
    incl |=
      (int)elem->is_writable & (int)__CPROVER_same_object(elem->lb, ptr) &
      (__CPROVER_POINTER_OFFSET(elem->lb) <= offset) &
      (__CPROVER_POINTER_OFFSET(ub) <= __CPROVER_POINTER_OFFSET(elem->ub));
    ++elem;
    --idx;
  }
  return incl;
#  pragma CPROVER check pop
}
#endif

/// \brief Checks if the operation `array_set(dest, ...)` is allowed according
/// to \p set.
///
/// \remark The `array_set` operation updates all bytes of the object starting
/// from \p dest.
///
/// \param[in] set Write set to check the array_set operation against
/// \param[in] dest The destination pointer
/// \return True iff the range of bytes starting at \p dest and of
/// `__CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest)` bytes is
/// contained in \p set->allocated or \p set->contract_assigns.
__CPROVER_bool __CPROVER_contracts_write_set_check_array_set(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest)
{
__CPROVER_HIDE:;
  return __CPROVER_contracts_write_set_check_assignment(
    set, dest, __CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest));
}

/// \brief Checks if the operation `array_copy(dest, ...)` is allowed according
/// to \p set.
///
/// \remark The `array_copy` operation updates all of `*dest` (possibly using
/// nondet values), even when `*src` is smaller.
///
/// \param[in] set Write set to check the `array_copy` operation against
/// \param[in] dest The destination pointer
/// \return True iff the range of bytes starting at \p dest and of
/// `__CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest)` bytes is
/// contained in \p set->allocated or \p set->contract_assigns.
__CPROVER_bool __CPROVER_contracts_write_set_check_array_copy(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest)
{
__CPROVER_HIDE:;
  return __CPROVER_contracts_write_set_check_assignment(
    set, dest, __CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest));
}

/// \brief Checks if the operation `array_replace(dest, src)` is allowed
/// according to \p set.
///
/// \remark The `array_replace` operation updates at most `size-of-*src` bytes
/// in \p *dest, i.e. it replaces `MIN(size-of-*dest, size-of-*src)` bytes in
/// \p *dest.
///
/// \param[in] set Write set to check the `array_replace` operation against
/// \param[in] dest The destination pointer
/// \param[in] src The source pointer
/// \return True iff the range of bytes starting at \p dest and extending for
/// `MIN(__CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest),
/// __CPROVER_OBJECT_SIZE(src) - __CPROVER_POINTER_OFFSET(src))` bytes is
/// contained in \p set->allocated or \p set->contract_assigns.
__CPROVER_bool __CPROVER_contracts_write_set_check_array_replace(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest,
  void *src)
{
__CPROVER_HIDE:;
  __CPROVER_size_t src_size =
    __CPROVER_OBJECT_SIZE(src) - __CPROVER_POINTER_OFFSET(src);
  __CPROVER_size_t dest_size =
    __CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest);
  __CPROVER_size_t size = dest_size < src_size ? dest_size : src_size;
  return __CPROVER_contracts_write_set_check_assignment(set, dest, size);
}

/// \brief Checks if a `havoc_object(ptr)` is allowed according to \p set.
///
/// \param[in] set The write set to check the operation against
/// \param[in] ptr Pointer to the havoced object
/// \return True iff the range of bytes starting at
/// `(char *)ptr - __CPROVER_POINTER_OFFSET(ptr)` and of size
/// `__CPROVER_OBJECT_SIZE(ptr)` is contained in `set->contract_assigns` or
/// `set->allocated`.
__CPROVER_bool __CPROVER_contracts_write_set_check_havoc_object(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  return __CPROVER_contracts_write_set_check_assignment(
    set,
    (char *)ptr - __CPROVER_POINTER_OFFSET(ptr),
    __CPROVER_OBJECT_SIZE(ptr));
}

/// \brief Checks if the deallocation of \p ptr is allowed according to \p set.
///
/// \pre The pointer \p ptr is involved in the GOTO instruction
/// `CALL __CPROVER_deallocate(ptr);`
///
/// \param[in] set Write set to check the deallocation against
/// \param[in] ptr Deallocated pointer to check set to check the deallocation
/// against
/// \return True iff deallocation is allowed and \p ptr is contained in
/// \p set->contract_frees or \p set->allocated.
__CPROVER_bool __CPROVER_contracts_write_set_check_deallocate(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);

#ifdef DFCC_DEBUG
  __CPROVER_assert(
    set->contract_frees.indexed_by_object_id,
    "set->contract_frees is indexed by object id");
  __CPROVER_assert(
    set->allocated.indexed_by_object_id,
    "set->allocated is indexed by object id");
#endif
  return (set->allow_deallocate) &
         ((ptr == 0) | (set->contract_frees.elems[object_id] == ptr) |
          (set->allocated.elems[object_id] == ptr));
}

/// \brief Checks the inclusion of the \p candidate->contract_assigns elements
/// in \p reference->contract_assigns or \p reference->allocated.
///
/// \pre \p candidate->allocated must be empty.
///
/// \param[in] reference Reference write set from a caller
/// \param[in] candidate Candidate write set from a contract being replaced
/// \return True iff all elements of \p candidate->contract_assigns are included
/// in some element of \p reference->contract_assigns or \p reference->allocated
__CPROVER_bool __CPROVER_contracts_write_set_check_assigns_clause_inclusion(
  __CPROVER_contracts_write_set_ptr_t reference,
  __CPROVER_contracts_write_set_ptr_t candidate)
{
__CPROVER_HIDE:;
  __CPROVER_bool incl = 1;
  __CPROVER_contracts_car_t *current = candidate->contract_assigns.elems;
  __CPROVER_size_t idx = candidate->contract_assigns.max_elems;
SET_CHECK_ASSIGNS_CLAUSE_INCLUSION_LOOP:
  while(idx != 0)
  {
    if(current->is_writable)
    {
      incl &= __CPROVER_contracts_write_set_check_assignment(
        reference, current->lb, current->size);
    }
    --idx;
    ++current;
  }
  return incl;
}

/// \brief Checks the inclusion of the \p candidate->contract_frees elements
/// in \p reference->contract_frees or \p reference->allocated.
///
/// \pre \p candidate->allocated must be empty.
///
/// \param[in] reference Reference write set from a caller
/// \param[in] candidate Candidate write set from a contract being replaced
/// \return True iff all elements of \p candidate->contract_frees are included
/// in some element of \p reference->contract_frees or \p reference->allocated
__CPROVER_bool __CPROVER_contracts_write_set_check_frees_clause_inclusion(
  __CPROVER_contracts_write_set_ptr_t reference,
  __CPROVER_contracts_write_set_ptr_t candidate)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    reference->contract_frees.indexed_by_object_id,
    "reference->contract_frees is indexed by object id");
  __CPROVER_assert(
    reference->allocated.indexed_by_object_id,
    "reference->allocated is indexed by object id");
#endif
  __CPROVER_bool all_incl = 1;
  void **current = candidate->contract_frees_append.elems;
  __CPROVER_size_t idx = candidate->contract_frees_append.max_elems;

SET_CHECK_FREES_CLAUSE_INCLUSION_LOOP:
  while(idx != 0)
  {
    void *ptr = *current;
    __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
    all_incl &= (ptr == 0) |
                (reference->contract_frees.elems[object_id] == ptr) |
                (reference->allocated.elems[object_id] == ptr);
    --idx;
    ++current;
  }

  return all_incl;
}

/// \brief Models the instrumented version of the free function.
///
/// \remark Uses of this function will be remapped to the instrumented version
/// of the `free` found in the goto model.
__CPROVER_bool
__CPROVER_contracts_free(void *, __CPROVER_contracts_write_set_ptr_t);

/// \brief Non-deterministically call \ref __CPROVER_contracts_free on all
/// elements of \p set->contract_frees, and records the freed pointers in
/// \p target->deallocated.
///
/// \param[in] set Write set to free
/// \param[out] target Write set to record deallocations in
void __CPROVER_contracts_write_set_deallocate_freeable(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_contracts_write_set_ptr_t target)
{
__CPROVER_HIDE:;
  void **current = set->contract_frees_append.elems;
  __CPROVER_size_t idx = set->contract_frees_append.max_elems;
SET_DEALLOCATE_FREEABLE_LOOP:
  while(idx != 0)
  {
    void *ptr = *current;

    // call free only iff the pointer is valid preconditions are met
    // skip checks on r_ok, dynamic_object and pointer_offset
    __CPROVER_bool preconditions =
      (ptr == 0) |
      ((int)__CPROVER_r_ok(ptr, 0) & (int)__CPROVER_DYNAMIC_OBJECT(ptr) &
       (__CPROVER_POINTER_OFFSET(ptr) == 0));
    // If there is aliasing between the pointers in the freeable set,
    // and we attempt to free again one of the already freed pointers,
    // the r_ok condition above will fail, preventing us to deallocate
    // the same pointer twice
    if((ptr != 0) & preconditions & __VERIFIER_nondet___CPROVER_bool())
    {
      __CPROVER_contracts_free(ptr, 0);
      __CPROVER_contracts_write_set_record_deallocated(set, ptr);
      // also record effects in the caller write set
      if(target != 0)
        __CPROVER_contracts_write_set_record_deallocated(target, ptr);
    }
    --idx;
    ++current;
  }
}

/// \brief Links \p is_fresh_set to
/// \p write_set->linked_is_fresh so that the is_fresh predicates
/// can be evaluated in requires and ensures clauses.
void __CPROVER_contracts_link_is_fresh(
  __CPROVER_contracts_write_set_ptr_t write_set,
  __CPROVER_contracts_obj_set_ptr_t is_fresh_set)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(write_set != 0, "write_set not NULL");
#endif
  if((is_fresh_set != 0))
  {
    write_set->linked_is_fresh = is_fresh_set;
  }
  else
  {
    write_set->linked_is_fresh = 0;
  }
}

/// \brief Links \p write_set_to_link->allocated to
/// \p write_set_postconditions->linked_allocated so that allocations performed
/// by \ref __CPROVER_contracts_is_fresh when evaluating ensures clauses are
/// recorded in \p write_set_to_link.
void __CPROVER_contracts_link_allocated(
  __CPROVER_contracts_write_set_ptr_t write_set_postconditions,
  __CPROVER_contracts_write_set_ptr_t write_set_to_link)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    write_set_postconditions != 0, "write_set_postconditions not NULL");
#endif
  if((write_set_to_link != 0))
  {
    write_set_postconditions->linked_allocated =
      &(write_set_to_link->allocated);
  }
  else
  {
    write_set_postconditions->linked_allocated = 0;
  }
}

/// \brief Links \p write_set_to_link->deallocated to
/// \p write_set_postconditions->linked_deallocated so that deallocations
/// performed by the function get recorded in \p write_set_to_link->deallocated
/// and are later available  to  \ref __CPROVER_contracts_was_freed predicate
/// when evaluating ensures clauses.
void __CPROVER_contracts_link_deallocated(
  __CPROVER_contracts_write_set_ptr_t write_set_postconditions,
  __CPROVER_contracts_write_set_ptr_t write_set_to_link)
{
__CPROVER_HIDE:;
#ifdef DFCC_DEBUG
  __CPROVER_assert(
    write_set_postconditions != 0, "write_set_postconditions not NULL");
#endif
  if((write_set_to_link != 0))
  {
    write_set_postconditions->linked_deallocated =
      &(write_set_to_link->deallocated);
  }
  else
  {
    write_set_postconditions->linked_deallocated = 0;
  }
}
#endif // __CPROVER_contracts_library_defined
