#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

 // if enabled, checks that serialised and deserialised results are equal
#define CHECK_RESULT 0

#define KEY_BYTES 4
#define DATA_BYTES 1
#define MAX_ENTRY_SIZE (KEY_BYTES + 1 + DATA_BYTES)

// A entry to serialize
// If the tag is non-zero, then data is serialized, otherwise,
// just the key is serialized.
// As a result the serialization is variable-length, each entry can take either
// KEY_BYTES + 1 or KEY_BYTES + 1 + DATA_BYTES bytes.
typedef struct {
  uint8_t key[KEY_BYTES];
  uint8_t tag;
  uint8_t data[DATA_BYTES];
} entry_t;

size_t nondet_size_t();

int main() {
  bool force_write = false;
  size_t nof_entries = nondet_size_t();
  __CPROVER_assume(0 < nof_entries && nof_entries <= 1000000);

  entry_t *entries_in = malloc(nof_entries * sizeof(entry_t));
  __CPROVER_assume(entries_in);

  size_t *nof_tags = malloc(nof_entries * sizeof(size_t));
  __CPROVER_assume(nof_tags);

  size_t cap = nof_entries * MAX_ENTRY_SIZE;
  uint8_t *buffer = malloc(cap);
  __CPROVER_assume(buffer);

  // write
  size_t written = 0;
  nof_tags[0] = 0;
  bool write_error = false;
  for (size_t i = 0; i < nof_entries && written < cap; i++)
    // clang-format off
    __CPROVER_assigns(__CPROVER_object_whole(buffer), __CPROVER_object_whole(nof_tags), i, written)
    __CPROVER_loop_invariant(i <= nof_entries)
    __CPROVER_loop_invariant(!(i == 0) || (nof_tags[i] == 0))
    __CPROVER_loop_invariant(!(i < nof_entries) || (nof_tags[i] <= i))
    __CPROVER_loop_invariant(!(0 < i && i < nof_entries) || (nof_tags[i-1] <= i-1))
    __CPROVER_loop_invariant(!(i < nof_entries) || (written == nof_tags[i] * (MAX_ENTRY_SIZE) + (i - nof_tags[i]) * (KEY_BYTES + 1)))
    #if 0
    // invariant that maps entry_in bytes to buffer bytes
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> nof_tags[i] >= 1)
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> (buffer[written-1] == entries_in[i-1].data[0]))
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> (buffer[written-2] == entries_in[i-1].tag))
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> (buffer[written-3] == entries_in[i-1].key[3]))
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> (buffer[written-4] == entries_in[i-1].key[2]))
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> (buffer[written-5] == entries_in[i-1].key[1]))
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && entries_in[i-1].tag ==> (buffer[written-6] == entries_in[i-1].key[0]))
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && !(entries_in[i-1].tag) ==> buffer[written-1] == entries_in[i-1].tag)
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && !(entries_in[i-1].tag) ==> buffer[written-2] == entries_in[i-1].key[3])
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && !(entries_in[i-1].tag) ==> buffer[written-3] == entries_in[i-1].key[2])
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && !(entries_in[i-1].tag) ==> buffer[written-4] == entries_in[i-1].key[1])
    // __CPROVER_loop_invariant((0 < i && i < nof_entries) && !(entries_in[i-1].tag) ==> buffer[written-5] == entries_in[i-1].key[0])
    __CPROVER_decreases(nof_entries - i)
    #endif
    // clang-format on
    {
      entry_t *entry = &entries_in[i];
      // key
      if (written > cap - KEY_BYTES) {
        write_error = true;
        break;
      }
      memcpy(&buffer[written], entry->key, KEY_BYTES);
      written += KEY_BYTES;
      assert(written <= cap);

      if (written >= cap) {
        write_error = true;
        break;
      }

      // tag
      if (i < nof_entries - 1) {
        if (entry->tag) {
          nof_tags[i + 1] = nof_tags[i] + 1;
        } else {
          nof_tags[i + 1] = nof_tags[i];
        }
      }

      buffer[written] = entry->tag;
      written++;
      assert(written <= cap);

      // data
      if (force_write || entry->tag) {
        if (written > cap - DATA_BYTES) {
          write_error = true;
          break;
        }
        memcpy(&buffer[written], entry->data, DATA_BYTES);
        written += DATA_BYTES;
        assert(written <= cap);
      }
    }

  assert(!write_error);

  // read
  entry_t *entries_out = malloc(nof_entries * sizeof(entry_t));
  __CPROVER_assume(entries_out);

  size_t *nof_tags_out = malloc(nof_entries * sizeof(size_t));
  __CPROVER_assume(nof_tags_out);

  size_t read = 0;
  nof_tags_out[0] = 0;
  bool read_error = false;
  for (size_t i = 0; i < nof_entries && read < cap; i++)
    // clang-format off
    __CPROVER_assigns(__CPROVER_object_whole(entries_out), __CPROVER_object_whole(nof_tags_out), i, read)
    __CPROVER_loop_invariant(i <= nof_entries)
    __CPROVER_loop_invariant(!(i == 0) || (nof_tags_out[i] == 0))
    __CPROVER_loop_invariant(!(i < nof_entries) || (nof_tags_out[i] <= i))
    __CPROVER_loop_invariant(!(0 < i && i < nof_entries) || (nof_tags_out[i-1] <= i-1))
    __CPROVER_loop_invariant(!(i < nof_entries) || (read == nof_tags_out[i] * (MAX_ENTRY_SIZE) + (i - nof_tags_out[i]) * (KEY_BYTES + 1)))
    // clang-format on
    {
      entry_t *entry = &entries_out[i];

      if (read > cap - KEY_BYTES) {
        read_error = true;
        break;
      }
      memcpy(entry->key, &buffer[read], KEY_BYTES);
      read += KEY_BYTES;

      // tag
      if (read >= cap) {
        read_error = true;
        break;
      }
      entry->tag = buffer[read];

      // tag
      if (i < nof_entries - 1) {
        if (entry->tag) {
          nof_tags_out[i + 1] = nof_tags_out[i] + 1;
        } else {
          nof_tags_out[i + 1] = nof_tags_out[i];
        }
      }

      read++;
      assert(read <= cap);

      // data
      if (force_write || entry->tag) {
        if (read > cap - DATA_BYTES) {
          read_error = true;
          break;
        }
        memcpy(entry->data, &buffer[read], DATA_BYTES);
        read += DATA_BYTES;
      }
    }
  assert(!read_error);
#if 0
  // compare
  for (size_t i = 0; i < nof_entries; i++)
    // clang-format off
__CPROVER_assigns(i)
__CPROVER_loop_invariant(i <= nof_entries)
__CPROVER_decreases(nof_entries - i)
    // clang-format on
    {
      entry_t *in = &entries_in[i];
      entry_t *out = &entries_out[i];
      //assert(0 == memcmp(in->key, out->key, KEY_BYTES));
      //assert(in->tag == out->tag);
      if (force_write || in->tag) {
        //assert(0 == memcmp(in->data, out->data, DATA_BYTES));
      }
    }
#endif
}

// goto-cc serde.c
// goto-instrument --dfcc main --apply-loop-contracts a.out b.out

// does not terminate
// cbmc --external-sat-solver kissat --bounds-check --pointer-check --pointer-overflow-check --unsigned-overflow-check --signed-overflow-check a.out

// 2 mins
// cbmc --external-sat-solver kissat --bounds-check --pointer-check --pointer-overflow-check --unsigned-overflow-check --signed-overflow-check b.out

// 4 mins
// cbmc --external-sat-solver kissat --bounds-check --pointer-check --pointer-overflow-check --unsigned-overflow-check --signed-overflow-check b.out
