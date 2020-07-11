/** A simple parametised dynamic array in an X-Macro. */

#include <stddef.h> /* size_t */
#include <stdlib.h> /* realloc */
#include <errno.h>  /* errno, ERANGE */
#include <assert.h> /* assert */

/* Inclomplete initialisers are a `C99` feature. */
#ifndef MIN_ARRAY_H
#define MIN_ARRAY_H
#define ARRAY_IDLE { 0, 0, 0 }
#endif

/* Definition of type; useful when splitting .c/.h. */
#define MIN_ARRAY_DEF(Name, type) \
struct Name##Array { type *data; size_t size, capacity; };

/* `MIN_ARRAY_DEF` must be defined first. */
#define MIN_ARRAY_FNS(name, Name, type) \
/* Initialises `a` to idle. */ \
static void name##_array(struct Name##Array *const a) \
	{ assert(a), a->data = 0, a->capacity = a->size = 0; } \
/* Destroys `a` and returns it to idle. */ \
static void name##_array_(struct Name##Array *const a) \
	{ assert(a), free(a->data), name##_array(a); } \
/* Ensures `min_capacity` of `a`. @param[min_capacity] If zero, does nothing.
@return Success; otherwise, `errno` will be set.
@throws[ERANGE] Tried allocating more then can fit in `size_t` or `realloc`
doesn't follow POSIX. @throws[realloc, ERANGE] */ \
static int name##_array_reserve(struct Name##Array *const a, \
	const size_t min_capacity) { \
	size_t c0; \
	type *data; \
	const size_t max_size = (size_t)-1 / sizeof *a->data; \
	assert(a); \
	if(a->data) { \
		if(min_capacity <= a->capacity) return 1; \
		c0 = a->capacity; \
		if(c0 < 8) c0 = 8; \
	} else { /* Idle. */ \
		if(!min_capacity) return 1; \
		c0 = 8; \
	} \
	if(min_capacity > max_size) return errno = ERANGE, 0; \
	/* `c_n = a1.625^n`, approximation golden ratio `\phi ~ 1.618`. */ \
	while(c0 < min_capacity) { \
		size_t c1 = c0 + (c0 >> 1) + (c0 >> 3); \
		if(c0 >= c1) { c0 = max_size; break; } \
		c0 = c1; \
	} \
	if(!(data = realloc(a->data, sizeof *a->data * c0))) \
		{ if(!errno) errno = ERANGE; return 0; } \
	a->data = data, a->capacity = c0; \
	return 1; \
} \
/* @return Push back a new un-initialized datum of `a`.
 @throws[realloc, ERANGE] */ \
static type *name##_array_new(struct Name##Array *const a) { \
	assert(a); \
	return name##_array_reserve(a, a->size + 1) ? a->data + a->size++ : 0; \
} \
/* Clears `a` but leaves the memory. @order \O(1) */ \
static void name##_array_clear(struct Name##Array *const a) \
	{ assert(a); a->size = 0; } \
/* These don't need to be used; should not generate a warning. */ \
static void name##_array_unused_coda(void); \
static void name##_array_unused(void) { \
name##_array_new(0); name##_array_clear(0); name##_array_unused_coda(); } \
static void name##_array_unused_coda(void) { name##_array_unused(); }

/* Both together. */
#define MIN_ARRAY(name, Name, type) \
MIN_ARRAY_DEF(Name, type) MIN_ARRAY_FNS(name, Name, type)
