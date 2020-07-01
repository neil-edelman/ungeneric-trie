/** @license 2020 Neil Edelman,
 [MIT License](https://opensource.org/licenses/MIT).
 @subtitle Prefix Tree

 @fixme Don't put two strings side-by-side or delete one that causes two
 strings to be side-by-side that have more than 512 matching characters in the
 same bit-positions, it will trip an `assert`. (Genomic data, perhaps?) */

#include <stdlib.h> /* EXIT malloc free qsort */
#include <stdio.h>  /* printf */
#include <string.h> /* memmove memcpy */
#include <assert.h> /* assert */
#include <errno.h>  /* errno */
#include <limits.h> /* INT_MAX */
/* Added in `C99` and doesn't guarantee `uint64_t`; can be replaced with
 `typedef` these machine-dependant types. */
#include <stdint.h> /* uint8_t uint64_t */

#define DICT_MAX_WORD_LENGTH 64

#define DEFINE_MIN_ARRAY(name, Name, type) \
/* A dynamic array. */ \
struct Name##Array { type *data; size_t size, capacity; }; \
/* Initialises `a` to idle. */ \
static void name##_array(struct Name##Array *const a) \
	{ assert(a), a->data = 0, a->capacity = a->size = 0; } \
/* Destroys `a` and returns it to idle. */ \
static void name##_array_(struct Name##Array *const a) \
	{ assert(a), free(a->data), name##_array(a); } \
/* Ensures `min_capacity` of `a`. @param[min_capacity] If zero, does nothing. \
@return Success; otherwise, `errno` will be set. \
@throws[ERANGE] Tried allocating more then can fit in `size_t` or `realloc` \
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
/* @return A new un-initialized datum of `a`. @throws[realloc, ERANGE] */ \
static type *name##_array_new(struct Name##Array *const a) { \
	assert(a); \
	return name##_array_reserve(a, a->size + 1) ? a->data + a->size++ : 0; \
} \
/* Clears `a` but leaves the memory. @order \O(1) */ \
static void name##_array_clear(struct Name##Array *const a) \
	{ assert(a); a->size = 0; } \
static void name##_array_unused_coda(void); \
static void name##_array_unused(void) { \
name##_array_new(0); name##_array_clear(0); name##_array_unused_coda(); } \
static void name##_array_unused_coda(void) { name##_array_unused(); }
#define ARRAY_IDLE { 0, 0, 0 }


/** Leaves are string constants; `typedef` because it could be more complex. */
typedef const char *Leaf;

/** Returns a boolean given two `Leaf`. */
typedef int (*TrieBipredicate)(Leaf, Leaf);

/** Orders `a` and `b`. @implements qsort bsearch */
static int vstrcmp(const void *const a, const void *const b)
	{ return strcmp(*(char **)a, *(char **)b); }

DEFINE_MIN_ARRAY(leaf, Leaf, Leaf)

/** For each consecutive pair of equal elements in `a`, surjects two one
 according to `merge`.
 @param[merge] If null, discards all but the first. @order \O(`a.size`) */
static void leaf_compactify(struct LeafArray *const a,
	const TrieBipredicate merge) {
	size_t target, from, cursor, choice, next, move;
	const size_t last = a->size;
	int is_first, is_last;
	assert(a);
	for(target = from = cursor = 0; cursor < last; cursor += next) {
		/* Bijective `[from, cursor)` is moved lazily. */
		for(choice = 0, next = 1; cursor + next < last &&
			!strcmp(a->data[cursor + choice], a->data[cursor + next]); next++)
			if(merge && merge(a->data[cursor + choice], a->data[cursor + next]))
			choice = next;
		if(next == 1) continue;
		/* Must move injective `cursor + choice \in [cursor, cursor + next)`. */
		is_first = !choice;
		is_last  = (choice == next - 1);
		move = cursor - from + is_first;
		memmove(a->data + target, a->data + from, sizeof *a->data * move),
		target += move;
		if(!is_first && !is_last) memcpy(a->data + target,
			a->data + cursor + choice, sizeof *a->data), target++;
		from = cursor + next - is_last;
	}
	/* Last differed move. */
	move = last - from;
	memmove(a->data + target, a->data + from, sizeof *a->data * move),
	target += move, assert(a->size >= target);
	a->size = target;
}


/* Trie pre-order internal nodes in the style of <Morrison, 1968 PATRICiA>
 semi-implicitly. Each contains two items of information in a `size_t`: left
 children branches are <fn:trie_left> immediately following, right children are
 the rest, and <fn:trie_skip>, the length in bits of the don't care values
 preceding this branch in the string. */
DEFINE_MIN_ARRAY(size, Size, size_t)

/* 12 makes the maximum skip length 512 bytes and the maximum size of a trie is
 `size_t` 64-bits: 4503599627370495, 32-bits: 1048575, and 16-bits: 15. */
#define TRIE_SKIP 12
#define TRIE_SKIP_MAX ((1 << TRIE_SKIP) - 1)
#define TRIE_LEFT_MAX (((size_t)1 << ((sizeof(size_t) << 3) - TRIE_SKIP)) - 1)

/** @return Packs `skip` and `left` into a branch. */
static size_t trie_branch(const size_t skip, const size_t left) {
	assert(skip <= TRIE_SKIP_MAX && left <= TRIE_LEFT_MAX);
	return skip + (left << TRIE_SKIP);
}

/** @return Unpacks skip from `branch`. */
static size_t trie_skip(const size_t branch)
	{ return branch & TRIE_SKIP_MAX; }

/** @return Unpacks left descendent branches from `branch`. */
static size_t trie_left(const size_t branch) { return branch >> TRIE_SKIP; }

/** Overwrites `skip` in `branch`. */
static void trie_skip_set(size_t *const branch, size_t skip) {
	assert(branch && skip <= TRIE_SKIP_MAX);
	*branch &= ~TRIE_SKIP_MAX;
	*branch += skip;
}

/** Increments the left descendants `branch` count. */
static void trie_left_inc(size_t *const branch) {
	assert(branch && *branch < ~(size_t)TRIE_SKIP_MAX);
	*branch += TRIE_SKIP_MAX + 1;
}

/** Decrements the left descendants `branch` count. */
static void trie_left_dec(size_t *const branch) {
	assert(branch && *branch > TRIE_SKIP_MAX);
	*branch -= TRIE_SKIP_MAX + 1;
}

/** Compares `bit` from the string `a` against `b`.
 @return In the `bit` position, positive if `a` is after `b`, negative if `a`
 is before `b`, or zero if `a` is equal to `b`. */
static int trie_strcmp_bit(const char *const a, const char *const b,
	const size_t bit) {
	const size_t byte = bit >> 3, mask = 128 >> (bit & 7);
	return !(b[byte] & mask) - !(a[byte] & mask);
}

/** From string `a`, extract `bit`, either 0 or 1. */
static int trie_is_bit(const char *const a, const size_t bit) {
	const size_t byte = bit >> 3, mask = 128 >> (bit & 7);
	return !!(a[byte] & mask);
}

/** @return Whether `a` and `b` are equal up to the minimum of their lengths'.
 Used in <fn:prefix>. */
static int trie_is_prefix(const char *a, const char *b) {
	for( ; ; a++, b++) {
		if(*a == '\0') return 1;
		if(*a != *b) return *b == '\0';
	}
}


/** Trie is a full binary tree, it's either empty or
 `|branches| + 1 = |leaves|`. */
struct Trie { struct SizeArray branches; struct LeafArray leaves; };

/** Initialises `t` to idle. */
static void trie(struct Trie *const t)
	{ assert(t); size_array(&t->branches), leaf_array(&t->leaves); }

/** Returns an initialised `t` to idle. */
static void trie_(struct Trie *const t)
	{ assert(t); size_array_(&t->branches), leaf_array_(&t->leaves); }

/** Recursive function used for <fn:trie_init>. Initialise branches of `t`
 up to `bit` with `a` to `a_size` array of sorted leaves.
 @order Speed \O(`a_size` log E(`a.length`))?; memory \O(E(`a.length`)). */
static void trie_init_branches_r(struct Trie *const t, size_t bit,
	const size_t a, const size_t a_size) {
	size_t b = a, b_size = a_size, half;
	size_t skip = 0;
	size_t *branch;
	assert(t && a_size && a_size <= t->leaves.size && t->leaves.size
		&& t->branches.capacity >= t->leaves.size - 1);
	if(a_size <= 1) return;
	/* Endpoints of sorted range: skip [_1_111...] or [...000_0_] don't care.
	 fixme: UINT_MAX overflow. */
	while(trie_is_bit(t->leaves.data[a], bit)
		|| !trie_is_bit(t->leaves.data[a + a_size - 1], bit)) bit++, skip++;
	/* Do a binary search for the first `leaves[a+half_s]#bit == 1`. */
	while(b_size) half = b_size >> 1,
		trie_is_bit(t->leaves.data[b + half], bit)
		? b_size = half : (half++, b += half, b_size -= half);
	b_size = b - a;
	/* Should have space for all branches pre-allocated in <fn:<PN>init>. */
	branch = size_array_new(&t->branches), assert(branch);
	*branch = trie_branch(skip, b_size - 1);
	bit++;
	trie_init_branches_r(t, bit, a, b_size);
	trie_init_branches_r(t, bit, b, a_size - b_size);
}

/** Initialises `t` to `a` of size `a_size`, which cannot be zero.
 @param[merge] Called with any duplicate entries and replaces if true; if
 null, doesn't replace. @return Success. @throws[ERANGE, malloc]
 @fixme There's a better way to do this in the literature? */
static int trie_init(struct Trie *const t, const Leaf *const a,
	const size_t a_size, const TrieBipredicate merge) {
	Leaf *leaves;
	assert(t && a && a_size);
	trie(t);
	/* This will store space for all of the duplicates, as well. */
	if(!leaf_array_reserve(&t->leaves, a_size)
		|| !size_array_reserve(&t->branches, a_size - 1)) return 0;
	leaves = t->leaves.data;
	memcpy(leaves, a, sizeof *a * a_size);
	t->leaves.size = a_size;
	/* Sort, get rid of duplicates, and initialise branches. */
	qsort(leaves, a_size, sizeof *a, &vstrcmp);
	leaf_compactify(&t->leaves, merge);
	trie_init_branches_r(t, 0, 0, t->leaves.size);
	assert(t->branches.size + 1 == t->leaves.size);
	return 1;
}

/** Looks at only the index for potential matches.
 @param[result] A index pointer to leaves that matches `key` when true.
 @return True if `key` in `trie` has matched, otherwise `key` is definitely is
 not in `trie`. @order \O(`key.length`) */
static int param_index_get(const struct Trie *const t, const char *const key,
	size_t *const result) {
	/* `(n0, n1]` is the index of pre-order `ancestor` (`n0`) and all
	 descendant branches. `i` is the leaf index. `left` is all ancestor's left
	 branches. */
	size_t n0 = 0, n1 = t->branches.size, i = 0, left;
	size_t ancestor;
	size_t byte, key_byte = 0, bit = 0;
	assert(t && key && result);
	if(!t->leaves.size) return assert(!n1), 0; /* Empty tree. */
	assert(n1 + 1 == t->leaves.size); /* Full binary tree. */
	while(n0 < n1) {
		ancestor = t->branches.data[n0];
		bit += trie_skip(ancestor);
		/* `key` ends at an internal branch; '\0' is part of `key`. */
		for(byte = bit >> 3; key_byte < byte; key_byte++)
			if(key[key_byte] == '\0') return 0;
		left = trie_left(ancestor);
		if(!trie_is_bit(key, bit++)) n1 = ++n0 + left;
		else n0 += left + 1, i += left + 1;
	}
	assert(n0 == n1 && i < t->leaves.size);
	*result = i;
	return 1;
}

/** @return True if found the exact `key` in `t` and stored it's index in
 `result`. */
static int param_get(const struct Trie *const t,
	const char *const key, size_t *const result) {
	return param_index_get(t, key, result)
		&& !strcmp(t->leaves.data[*result], key);
}

/** @return `t` entry that matches trie bits of `key`, (ignoring the don't care
 bits,) or null if either `key` didn't have the length to fully differentiate
 more then one entry or the `trie` is empty. */
static Leaf index_get(const struct Trie *const t, const char *const key) {
	size_t i;
	return param_index_get(t, key, &i) ? t->leaves.data[i] : 0;
}

/** @return Exact match for `key` in `t` or null. */
static Leaf trie_get(const struct Trie *const t, const char *const key) {
	size_t i;
	return param_get(t, key, &i) ? t->leaves.data[i] : 0;
}

/** In `t`, which must be non-empty, given a partial `prefix`, stores all leaf
 prefix matches between `low`, `high`, only given the index, ignoring don't
 care bits. @order \O(`prefix.length`) */
static void index_prefix(const struct Trie *const t, const char *const prefix,
	size_t *const low, size_t *const high) {
	size_t n0 = 0, n1 = t->branches.size, i = 0, left;
	size_t branch;
	size_t byte, key_byte = 0, bit = 0;
	assert(t && prefix && low && high);
	assert(n1 + 1 == t->leaves.size); /* Full binary tree. */
	while(n0 < n1) {
		branch = t->branches.data[n0];
		bit += trie_skip(branch);
		/* '\0' is not included for partial match. */
		for(byte = bit >> 3; key_byte <= byte; key_byte++)
			if(prefix[key_byte] == '\0') goto finally;
		left = trie_left(branch);
		if(!trie_is_bit(prefix, bit++)) n1 = ++n0 + left;
		else n0 += left + 1, i += left + 1;
	}
	assert(n0 == n1);
finally:
	assert(n0 <= n1 && i - n0 + n1 < t->leaves.size);
	*low = i, *high = i - n0 + n1;
}

/** @return Whether, in `t`, given a partial `prefix`, it has found `low`,
 `high` prefix matches. */
static int trie_prefix(const struct Trie *const t, const char *const prefix,
	size_t *const low, size_t *const high) {
	assert(t && prefix && low && high);
	return t->leaves.size ? (index_prefix(t, prefix, low, high),
		trie_is_prefix(prefix, t->leaves.data[*low])) : 0;
}

/** Add `datum` to `t`. Must not be the same as any key of trie; _ie_ it
 does not check for the end of the string. @return Success. @order \O(|`t`|)
 @throws[ERANGE] Trie reached it's conservative maximum, which on machines
 where the pointer is 64-bits, is 4.5T. On 32-bits, it's 1M.
 @throws[realloc, ERANGE] @fixme Throw EILSEQ if two strings have subsequences
 that are equal in more than 2^12 bits. */
static int trie_add_unique(struct Trie *const t, Leaf datum) {
	const size_t leaf_size = t->leaves.size, branch_size = leaf_size - 1;
	size_t n0 = 0, n1 = branch_size, i = 0, left, bit = 0, bit0 = 0, bit1;
	size_t *branch = 0;
	const char *n0_key;
	Leaf *leaf;
	int cmp;
	assert(t && datum);
	/* Empty special case. */
	if(!leaf_size) return assert(!t->branches.size),
		(leaf = leaf_array_new(&t->leaves)) ? *leaf = datum, 1 : 0;
	/* Redundant `size_t`, but maybe we will use it like Judy. */
	assert(leaf_size == branch_size + 1);
	/* Conservative maximally unbalanced trie. Reserve one more. */
	if(leaf_size > TRIE_LEFT_MAX) return errno = ERANGE, 0;
	if(!leaf_array_reserve(&t->leaves, leaf_size + 1)
		|| !size_array_reserve(&t->branches, branch_size + 1)) return 0;
	/* Branch from internal node. */
	while(branch = t->branches.data + n0, n0_key = t->leaves.data[i], n0 < n1) {
		/* fixme: Detect overflow 12 bits between. */
		for(bit1 = bit + trie_skip(*branch); bit < bit1; bit++)
			if((cmp = trie_strcmp_bit(datum, n0_key, bit)) != 0) goto insert;
		bit0 = bit1;
		left = trie_left(*branch) + 1; /* Leaves. */
		if(!trie_is_bit(datum, bit++)) trie_left_inc(branch), n1 = n0++ + left;
		else n0 += left, i += left;
	}
	/* Branch from leaf. */
	while((cmp = trie_strcmp_bit(datum, n0_key, bit)) == 0) bit++;
insert:
	assert(n0 <= n1 && n1 <= t->branches.size && n0_key && i <= t->leaves.size
		&& !n0 == !bit0);
	/* How many left entries are there to move. */
	if(cmp < 0) left = 0;
	else left = n1 - n0, i += left + 1;
	/* Insert leaf. */
	leaf = t->leaves.data + i;
	memmove(leaf + 1, leaf, sizeof *leaf * (leaf_size - i));
	*leaf = datum, t->leaves.size++;
	/* Insert branch. */
	branch = t->branches.data + n0;
	if(n0 != n1) { /* Split the skip value with the existing branch. */
		const size_t branch_skip = trie_skip(*branch);
		assert(branch_skip + bit0 >= bit + !n0);
		trie_skip_set(branch, branch_skip + bit0 - bit - !n0);
	}
	memmove(branch + 1, branch, sizeof *branch * (branch_size - n0));
	*branch = trie_branch(bit - bit0 - !!n0, left), t->branches.size++;
	return 1;
}

/** Adds `datum` to `t` and, if `eject` is non-null, stores the collided
 element, if any, as long as `replace` is null or returns true.
 @param[eject] If not-null, the ejected datum. If `replace` returns false, then
 `*eject == datum`, but it will still return true.
 @return Success. @throws[realloc, ERANGE] */
static int trie_put(struct Trie *const t, Leaf datum,
	Leaf *const eject, const TrieBipredicate replace) {
	Leaf *match;
	size_t i;
	assert(t && datum);
	/* Add if absent. */
	if(!param_get(t, datum, &i)) {
		if(eject) *eject = 0;
		return trie_add_unique(t, datum);
	}
	assert(i < t->leaves.size), match = t->leaves.data + i;
	/* Collision policy. */
	if(replace && !replace(*match, datum)) {
		if(eject) *eject = datum;
	} else {
		if(eject) *eject = *match;
		*match = datum;
	}
	return 1;
}

/** @return Whether leaf index `i` has been removed from `t`.
 @fixme There is nothing stopping an `assert` from being triggered. */
static int index_remove(struct Trie *const t, size_t i) {
	size_t n0 = 0, n1 = t->branches.size, parent_n0, left;
	size_t *parent, *twin; /* Branches. */
	assert(t && i < t->leaves.size && n1 + 1 == t->leaves.size);
	/* Remove leaf. */
	if(!--t->leaves.size) return 1; /* Phase transition to empty. */
	memmove(t->leaves.data + i, t->leaves.data + i + 1,
		sizeof t->leaves.data * (n1 - i));
	/* Traverse trie getting `parent` and `twin`. */
	for( ; ; ) {
		left = trie_left(*(parent = t->branches.data + (parent_n0 = n0)));
		if(i <= left) { /* Pre-order binary search. */
			if(!left) { twin = n0 + 1 < n1 ? t->branches.data + n0 + 1 : 0;
				break; }
			n1 = ++n0 + left;
			trie_left_dec(parent);
		} else {
			if((n0 += left + 1) >= n1)
				{ twin = left ? t->branches.data + n0 - left : 0; break; }
			i -= left + 1;
		}
	}
	/* Merge `parent` with `twin` before deleting `parent` branch. */
	if(twin)
		/* fixme: There is nothing to guarantee this. */
		assert(trie_skip(*twin) < TRIE_SKIP_MAX - trie_skip(*parent)),
		trie_skip_set(twin, trie_skip(*twin) + 1 + trie_skip(*parent));
	memmove(parent, parent + 1,
		sizeof *t->branches.data * (--t->branches.size - parent_n0));
	return 1;
}

/** @return Whether `key` has been removed from `t`. */
static int trie_remove(struct Trie *const t, const char *const key) {
	size_t i;
	assert(t && key);
	return param_get(t, key, &i) && index_remove(t, i);
}


/** This saves the position in the trie, bit-by-bit. */
struct Node { size_t bit, n0, n1, i; enum { LEFT, RIGHT, LEAF } choice; };

DEFINE_MIN_ARRAY(node, Node, struct Node)

struct TriePath {
	const struct Trie trie; /* Pointers to words in order and branches. */
	struct NodeArray nodes; /* Path to currently selected word. */
	struct SizeArray byte;  /* Bytes in `nodes`. */
};

static void path_(struct TriePath *const path) {
	assert(path);
	node_array_(&path->nodes);
	size_array_(&path->byte);
}

static void path_clear(struct TriePath *const path) {
	assert(path);
	node_array_clear(&path->nodes);
	size_array_clear(&path->byte);
}

/** Add to `path`, `bit`, which must be strictly monotonic with other bits,
 `n0` >= `n1`, branch indices, and `i`, leaf index. */
static struct Node *path_new(struct TriePath *const path, const size_t bit,
	const size_t n0, const size_t n1, const size_t i) {
	struct Node *node;
	const size_t byte = bit >> 3;
	printf("path_new bit %lu byte %lu: [%lu, %lu], leaf %lu.\n",
		bit, byte, n0, n1, i);
	assert(path && (!path->byte.size
		|| path->byte.data[path->byte.size - 1] <= byte) && n0 <= n1);
	node = node_array_new(&path->nodes);
	node->bit = bit;
	node->n0  = n0;
	node->n1  = n1;
	node->i   = i;
	node->choice = LEAF;
	/* Expand `byte` to include `bit`. Is sort of a hash, bits in bytes. */
	if(path->byte.size == byte + 1) goto finally;
	assert(path->byte.size < byte + 1);
	if(!size_array_reserve(&path->byte, byte + 1)) return 0;
	while(byte >= path->byte.size) path->byte.data[path->byte.size++] = byte;
finally:
	return node;
}


/** In `t`, which must be non-empty, given a `key`, stores every choice made,
 only given the index, ignoring don't care bits. If given `key` in `t`, it will
 find the path to it, and `key` not in `t`, it will find a path to some element
 in `t`. @order \O(`key.length`) @return Success. */
static int path_key(const struct Trie *const t, const char *const key,
	struct TriePath *const path) {
	size_t n0 = 0, n1 = t->branches.size, i = 0, left, right;
	size_t branch;
	size_t byte, key_byte = 0, bit = 0;
	struct Node *node;
	printf("node_key %s\n", key);
	assert(t && key && path);
	path_clear(path);
	assert(n1 + 1 == t->leaves.size); /* Full binary tree. */
	/* Descend the trie normally, storing the nodes. */
	while((node = path_new(path, bit, n0, n1, i))
		&& (printf("node_key1 [%lu,%lu]\n", n0, n1),
		n0 < n1)) {
		branch = t->branches.data[n0];
		bit += trie_skip(branch);
		left = trie_left(branch);
		/* '\0' is not included for partial match. */
		for(byte = bit >> 3; key_byte <= byte; key_byte++)
			if(key[key_byte] == '\0') goto end_key;
		if(!(node->choice = trie_is_bit(key, bit++))) n1 = ++n0 + left;
		else n0 += left + 1, i += left + 1;
	}
	if(n0 != n1) goto catch;
	goto finally;
	/* End of `key` and still in the internal nodes. Instead of calculating all
	 the paths to find the shortest, greedily take the one with the least
	 children, (statistically the best choice without looking at them.) */
	while((node = path_new(path, bit, n0, n1, i))
		&& (printf("node_key2 [%lu,%lu]\n", n0, n1),
		n0 < n1)) {
		branch = t->branches.data[n0];
		bit += trie_skip(branch);
		left = trie_left(branch);
end_key:
		assert(n1 > n0 + 1 + left);
		right = n1 - n0 - 1 - left;
		if(!(node->choice = right < left)) n1 = ++n0 + left;
		else n0 += left + 1, i += left + 1;
	}
	if(n0 != n1) goto catch;
	goto finally;
catch:
	return assert(n0 < n1 && errno), 0;
finally:
	return assert(n0 == n1), 1;
}


/* Memory for dynamic programming. */
DEFINE_MIN_ARRAY(byte, Byte, uint8_t)


/** `table.size` == `entries.size` * `query_length`. */
static struct {
	const char *query;
	size_t query_length, closest_length, common;
	struct LeafArray closest; /* Current suggestions with `closest_length`. */
	struct ByteArray table; /* DP matrix `query_length` columns. */
	struct TriePath path;
} wf;

static void path_print(void) {
	size_t byte, max, i = 0;
	struct Node *n;
	for(byte = 0; byte < wf.path.byte.size; byte++) {
		max = wf.path.byte.data[byte], assert(max <= wf.path.nodes.size);
		printf("__ byte %lu (bits %lu--%lu) __\n",
			byte, byte << 3, (byte << 3) + 7);
		while(i < max) {
			n = wf.path.nodes.data + i++;
			printf(" [%lu,%lu], leaf %lu, choice %u\n",
				n->n0, n->n1, n->i, n->choice);
		}
	}
	printf("__ the rest __\n");
	while(i < wf.path.nodes.size) {
		n = wf.path.nodes.data + i++;
		printf(" [%lu,%lu], leaf %lu, choice %u\n",
			n->n0, n->n1, n->i, n->choice);
	}
}

/** Destroy memory associated to Wagner-Fisher. */
static void wagner_fischer_(void) {
	leaf_array_(&wf.closest);
	byte_array_(&wf.table);
	path_(&wf.path);
}

/** Initialise Wagner-Fisher with `query`. */
static void wagner_fischer(const char *const query) {
	assert(query);
	wf.query = query;
	wf.query_length = strlen(query), assert(wf.query_length < 256); /* Bytes. */
	leaf_array_clear(&wf.closest);
	byte_array_clear(&wf.table);
	path_clear(&wf.path);
}

static void wf_print(const char *const candidate) {
	size_t candidate_length = strlen(candidate);
	size_t q, q_end, c;
	assert(candidate && wf.table.size
		== (wf.query_length + 1) * (candidate_length + 1));
	printf("   ");
	for(q = 0, q_end = wf.query_length; q < q_end; q++)
		assert(wf.query[q] != '\0'), printf(" %c", wf.query[q]);
	printf("\n ");
	for(q = 0, q_end = wf.query_length + 1; q < q_end; q++)
		printf(" %u", wf.table.data[q]);
	printf("\n");
	for(c = 0; c < candidate_length; c++) {
		assert(candidate[c] != '\0'), printf("%c", candidate[c]);
		for(q_end = (c + 2) * (wf.query_length + 1);
			q < q_end; q++) printf(" %u", wf.table.data[q]);
		if(c >= wf.query_length) printf("--");
		printf("\n");
	}
}

static int wagner_fischer_word(const char *const candidate) {
	const size_t candidate_length = strlen(candidate); /* Vertical. */
	size_t table_size, i, c, q;
	/* Contains excepts from 2019 Fujimoto Seiji <fujimoto@ceptord.net>. Can We
	 Optimize the Wagner-Fischer Algorithm? placed in public domain. */
	uint8_t u, v;
	assert(wf.path.trie
		&& candidate && candidate_length < 256
		&& wf.query  && wf.query_length  < 256);
	printf("wagner fischer word: %s(%lu), %s(%lu)\n",
		wf.query, wf.query_length, candidate, candidate_length);
	/* Horizontal \times vertical. */
	table_size = (wf.query_length + 1) * (candidate_length + 1);
	byte_array_clear(&wf.table);
	if(!byte_array_reserve(&wf.table, table_size)) return 0;
	wf.table.size = table_size;
	/* debug: fill. */
	for(i = 0; i < table_size; i++) wf.table.data[i] = 42;
	wf.common = 0;
	/* Fill the first row. */
	for(i = 0; i <= wf.query_length; i++) wf.table.data[i] = i;
	/* Fill all others. */
	for(c = 0; c < candidate_length; c++) {
		/* Fill the first of the row. */
		wf.table.data[i++] = c + 1;
		for(q = 0; q < wf.query_length; q++) {
			/* @fixme Implement Ukkonen's optimisation?
			 @fixme Abs min at right, done? */
			if(wf.query[q] == candidate[c]) {
				u = wf.table.data[i - wf.query_length - 2]; /* Diagonal. */
				wf.table.data[i++] = u;
				if(!u) wf.common++;
			} else {
				u = wf.table.data[i - 1]; /* Left. */
				v = wf.table.data[i - wf.query_length - 1]; /* Top. */
				if(u > v) u = v;
				v = wf.table.data[i - wf.query_length - 2]; /* Diagonal. */
				if(u > v) u = v;
				wf.table.data[i++] = u + 1;
			}
		}
		if(c + 2 > wf.query_length);
	}
	wf_print(candidate);
	return 1;
}

/* Wagner-Fischer (Memory Reduction + Branch Pruning.) From 2019 Fujimoto Seiji
 <fujimoto@ceptord.net>: Can We Optimize the Wagner-Fischer Algorithm? placed
 in public domain. `a_str` is length `a_len` and `b_str` is length `b_len`.
 `a_len` >= `b_len` and within `INT_MAX`. Should be called from
 <fn:wagner_fischer_do>. @fixme Take advantage of existing structure. */
static unsigned wagner_fischer_o2(const char *const a_str, const unsigned a_len,
	const char *const b_str, const unsigned b_len) {
	int min;
	unsigned max, min_clip, max_clip;
	unsigned a, b, dia, top, left;
	unsigned buf[DICT_MAX_WORD_LENGTH];

	/* Greedy special lengths. */
	assert(0 <= b_len && b_len <= a_len
		&& b_len < sizeof buf / sizeof *buf - 1);
	if(b_len == 0) return a_len;
	if(b_len == 1) return a_len - !!memchr(a_str, b_str[0], a_len);
	if(b_len == 2) {
		const char *const match = memchr(a_str, b_str[0], a_len - 1);
		return a_len - !!index((match ? match : a_str) + 1, b_str[1]) - !!match;
	}

	/* Branch pruning initial values. */
	max = (b_len - 1) >> 1;
	min = 1 - max - (a_len - b_len);

	/* Fill first row. */
	for(b = 0; b <= max; b++) buf[b] = b;

	/* DP. */
	for(a = 1; a <= a_len; a++) {
		buf[0] = a - 1;
		min_clip = min > 1 ? min : 1,         min++;
		max_clip = max < b_len ? max : b_len, max++;
		dia = buf[min_clip - 1];
		top = buf[min_clip];
		if(a_str[a - 1] != b_str[min_clip - 1])
			dia = (dia < top ? dia : top) + 1;
		buf[min_clip] = dia;
		left = dia;
		dia  = top;
		for(b = min_clip + 1; b <= max_clip; b++) {
			top = buf[b];
			if(a_str[a - 1] != b_str[b - 1]) {
				if(dia > top)  dia = top;
				if(dia > left) dia = left;
				dia++;
			}
			buf[b] = dia;
			left = dia;
			dia = top;
		}
		if(b_len == max_clip) continue;
		if(a_str[a - 1] != b_str[max_clip])
			dia = (dia < left ? dia : left) + 1;
		buf[max_clip + 1] = dia;
	}
	dia = buf[b_len];
	return dia;
}

/* Calls <fn:wagner_fisher_o2> with the order correct. */
static int wagner_fischer_do(const char *const a, const char *const b,
	unsigned *const result) {
	const size_t a_length = strlen(a), b_length = strlen(b);
	assert(a && b && result);
	if(a_length < b_length) {
		if(a_length >= DICT_MAX_WORD_LENGTH || b_length >= UINT_MAX) return 0;
		*result
			= wagner_fischer_o2(b, (unsigned)b_length, a, (unsigned)a_length);
	} else {
		if(a_length >= UINT_MAX || b_length >= DICT_MAX_WORD_LENGTH) return 0;
		*result
			= wagner_fischer_o2(a, (unsigned)a_length, b, (unsigned)b_length);
	}
	return 1;
}

/** Suggest Levenshtein geodesics for `word` in `t` and output them to
 `wagner_fischer.suggest` or `!wagner_fischer.suggest.size` if spelt
 correctly. This may allocate space which is freed by <wagner_fischer_>.
 @return Success. */
static int geodesics(const char *const query, const struct Trie *const t) {
	Leaf *leaf;
	unsigned lev;

	printf("geodesics %s.\n", query);
	/* Initialise suggestions. */
	assert(query && t && t->leaves.size);
	leaf_array_clear(&wf.closest);

	/* Easy-out to see if `t` actually contains `query`. */
	if(trie_get(t, query)) return 1;

	/* Greedy educated guess to serve as the starting point. */
	wagner_fischer(query, t);
	if(!path_key(t, query, &wf.path)
		|| !(leaf = leaf_array_new(&wf.closest))) return 0;
	path_print();
	assert(wf.path.nodes.size && wf.path.nodes.data[wf.path.nodes.size - 1].n0
		== wf.path.nodes.data[wf.path.nodes.size - 1].n1);
	*leaf = t->leaves.data[wf.path.nodes.data[wf.path.nodes.size - 1].i];
	if(!wagner_fischer_word(*leaf)) return 0;
	printf("common: %lu\n", wf.common);

	if(wagner_fischer_do(query, *leaf, &lev))
		printf("wf do: %u\n", lev);
	else
		printf("overflow\n");

	/*for(i = prefix.low + 1; i <= prefix.high; i++) { *s = t->leaves.data[i]; }*/
	/*........*/
	return 1;
}


/* Testing. */


/** Prints `t` on `stdout`. */
static void trie_print(const struct Trie *const t) {
	size_t i, n;
	printf("Trie: ");
	if(!t) { printf("null.\n"); return; }
	printf("{");
	for(i = 0; i < t->leaves.size; i++)
		printf("%s%s", i ? ", " : "", t->leaves.data[i]);
	printf("}; {");
	for(n = 0; n < t->branches.size; n++)
		printf("%s%lu:%lu", n ? ", " : "", trie_skip(t->branches.data[n]),
		(unsigned long)trie_left(t->branches.data[n]));
	printf("}.\n");
}

/** Given `n` in `t` branches, calculate the right child branches. Used in
 <fn:trie_graph>. @order \O(log `size`) */
static size_t trie_right(const struct Trie *const t, const size_t n) {
	size_t remaining = t->branches.size, n0 = 0, left, right;
	assert(t && n < remaining);
	for( ; ; ) {
		left = trie_left(t->branches.data[n0]);
		right = remaining - left - 1;
		assert(left < remaining && right < remaining);
		if(n0 >= n) break;
		if(n <= n0 + left) remaining = left, n0++;
		else remaining = right, n0 += left + 1;
	}
	assert(n0 == n);
	return right;
}

/** @return Given `n` in `t` branches, follows the internal nodes left until
 it hits a branch. Used in <fn:trie_graph>. */
static size_t trie_left_leaf(const struct Trie *const t, const size_t n) {
	size_t remaining = t->branches.size, n0 = 0, left, right, i = 0;
	assert(t && n < remaining);
	for( ; ; ) {
		left = trie_left(t->branches.data[n0]);
		right = remaining - left - 1;
		assert(left < remaining && right < remaining);
		if(n0 >= n) break;
		if(n <= n0 + left) remaining = left, n0++;
		else remaining = right, n0 += left + 1, i += left + 1;
	}
	assert(n0 == n);
	return i;
}

/** Draw a graph of `t` to `fn` in Graphviz format. */
static void trie_graph(const struct Trie *const t, const char *const fn) {
	FILE *fp;
	size_t i, n;
	assert(t && fn);
	if(!(fp = fopen(fn, "w"))) { perror(fn); return; }
	fprintf(fp, "digraph {\n"
		"\trankdir = TB;\n"
		"\tnode [shape = record, style = filled];\n"
		"\tTrie [label = \"{\\Trie"
		"\\l|size: %lu\\l}\"];\n", (unsigned long)t->leaves.size);
	fprintf(fp, "\tnode [shape = none, fillcolor = none];\n");
	for(n = 0; n < t->branches.size; n++) {
		const size_t branch = t->branches.data[n];
		const size_t left = trie_left(branch), right = trie_right(t, n);
		fprintf(fp, "\tbranch%lu [label = \"%lu\"];\n"
			"\tbranch%lu -> ", (unsigned long)n, trie_skip(branch),
			(unsigned long)n);
		if(left) fprintf(fp, "branch%lu [style = dashed]; // left branch\n",
			(unsigned long)n + 1);
		else fprintf(fp, "leaf%lu [style = dashed]; // left leaf\n",
			(unsigned long)trie_left_leaf(t, n));
		fprintf(fp, "\tbranch%lu -> ", (unsigned long)n);
		if(right) fprintf(fp, "branch%lu; // right branch\n",
			(unsigned long)n + left + 1);
		else fprintf(fp, "leaf%lu; // right leaf\n",
			(unsigned long)trie_left_leaf(t, n) + left + 1);
	}
	/* This must be after the branches, or it will mix up the order. Since they
	 have been referenced, one needs explicit formatting? */
	for(i = 0; i < t->leaves.size; i++)
		fprintf(fp, "\tleaf%lu [label = \"%s\", shape = box, "
		"fillcolor = lightsteelblue, style = filled];\n", (unsigned long)i,
		t->leaves.data[i]);
	fprintf(fp, "\tnode [color = red];\n"
		"}\n");
	fclose(fp);
}

int main(void) {
	const char *const words[] = {
"wryer","posturists","nonanswers","collations","renovating","view","kiddingly",
"lineman","elating","convocate","tonically","steradians","disdained",
"hypervigilance","annexational","scabiosas","pinfishes","disinhibited",
"coryphenes","omohyoid","mongoes","tarries","oestrin","decillion","tutorships",
"marriers","photocomposer","finesse","kosmos","jipyapa","nortenos","laminator",
"outgives","lampshades","inhumation","syringes","deiced","herpetologists",
"granulomata","footgear","stemless","lallygagging","expectation","ecus",
"jetplane","pusher","whiffings","bouffes","majorships","unintellectual",
"unhouses","pumy","convalesces","anticodon","rubicelle","simmering","suborned",
"guacharo","cassata","shedlike","chelating","limbering","detect","dandiacal",
"reedify","pegmatite","undignifies","jawbox","feudatories","opticist",
"overmany","synthon","dehisce","volens","nonself","drams","deluded","heisting",
"embosoms","lambda","growthiest","graphing","conepatl","disinclining",
"diffraction","phytotron","klezmorim","greenmailer","kyogens","daydreaming",
"canephors","uncleanlinesses","absinths","headmost","persists","sexiness",
"unanchoring","colickier","aquatinter","absentee","excimer","snakeskin",
"outtook","sybil","aldolizations","boundaries","hypochondrias","whitewashers",
"noninterests","evacuant","fogbow","bemean","nontaxable","bleacheries",
"preserve","puisny","pyrheliometers","peytrals","clypeus","joists","oxygenized",
"plyer","satinwoods","tashed","retailoring","micropuncture","chyle",
"overruffing","allots","pyrosises","squinched","misrelies","rheophil",
"tracheostomy","mischoices","boogymen","manyattas","honestly","indicters",
"cragginesses","epitaphing","tribulate","dishable","concealed","amis","annats",
"trompes","witchetties","napped","pusled","harewoods","napless","deadener",
"besat","overprescribing","liberates","summability","rumrunner","kamichi",
"lymphomas","wellborn","choughs","pudendous","petrochemistry","baboonish",
"hideousness","chanfron","tinnituses","mousts","drill","harborage","bogey",
"trabeated","choofing","utmosts","hypocentral","imidazoles","demology",
"evictees","rotal","axiological","ectozoans","teazes","taleful",
"interchangeable","helmsmanships","unhattings","overruff","playwear","tripart",
"neuropils","conspirers","outthrown","leucotomy","engilt","declarers","pandura",
"agony","saltnesses","saucy","begalling","misinter","regularize","zidovudines",
"ripsaw","hydrogenations","chivvying","disreputability","twirler","germaine",
"bullishnesses","crural","dognapped","flatmate","triceratopses","sighlike",
"heirdoms","maturities","frigged","zoechrome","snottinesses","arefy","bingled",
"scission","byrl","joky","insatiatenesses","tituped","latchets","streaky",
"dualin","perceptible","almudes","reproachfulness","seclude","quintes",
"lawbreakers","odalique","hosepipes","sulfadiazines","spool","chironomies",
"untillable","foreword","marly","cytometries","oxer","carbazoles","adventives",
"epigeic","appropriative","squeezabilities","pomposity","amorists","peplum",
"biogeographical","insertion","neonatal","fleers","omegas","preens","reshaven",
"chevy","gubbah","cachexy","syncope","skewed","hospitalities","cinematic",
"worrels","dispursed","tainted","divinator","impedance","intertexts","whiss",
"synonymical","chromize","lumpiest","hyalonema","entender","itinerates",
"saccharums","exclusives","jo","resurfaced","pompousness","doctrine","dropped",
"jaygees","deputised","appealed","complain","ancientry","otalgy","ferryboats",
"frowzier","allegiance","encalmed","fattens","plasmin","literalized",
"insupportable","approbations","lenity","coexerts","fascinators","medullae",
"taborers","phylloxera","wadings","apostatize","fippences","anecdotes",
"speechifies","impassible","superstrike","unrifled","runbacks","shampoos",
"quinoidal","preformatted","honchos","gigawatt","triodes","lophophores",
"gargarising","hydrological","undeifying","distinctness","cravening",
"phagocytosing","leopardesses","careless","baetyl","showmanship","lankiness",
"racketers","engrossed","hakes","treatment","abstractedly","wirinesses",
"unnilquadiums","greasier","mynas","inexpertness","mooner","digesting",
"rhabdoms","actioners","lauans","semanteme","trapesings","rabatments","maimers",
"heathier","amebean","gainer","diktat","redsear","spoilages","kitties",
"procaryotes","labroids","antiobscenities","stanchels","enjoiner","notoriety",
"pumicating","stupendousness","fidgeters","fecklessly","cawk","boraces",
"technologizing","cycloliths","biffy","penduline","tepefied","infernally",
"subdorsal","confectionary","slenderize","unearthed","camorrista","outpressing",
"unworldly","frankpledges","leveeing","polysyndetons","aguizing","semantra",
"neutralization","hypopharynges","multiwall","spellbinder","parenchymal",
"waiving","happily","anklebones","obligees","monoecies","blindage","bodyshells",
"asperse","cotyledons","forekings","fico","subclaim","chorus","homesteaders",
"prometals","transudates","glamourless","sphygmographs","traversal",
"thimbleriggers","shaken","undefaced","jeopardy","enheartening","dentural",
"fluorides","loganias","gladsomeness","locule","oestrones","militantnesses",
"skrieghs","smouldry","crower","pellicles","sapucaias","underuses","reexplored",
"chlamydia","tragediennes","levator","accipiter","esquisses","intentnesses",
"julienning","tetched","creeshing","anaphrodisiacs","insecurities","tarpons",
"lipotropins","sinkage","slooshes","homoplastic","feateous"},
		*const extra[] = { "foo", "bar", "baz", "qux", "quxx", "a" };
	const size_t words_size = sizeof words / sizeof *words,
		extra_size = sizeof extra / sizeof *extra;
	size_t start, end, i;
	struct Trie t;
	Leaf leaf, eject;
	Leaf word;
	int success = EXIT_FAILURE;
	if(!trie_init(&t, words, words_size, 0)) goto catch;

	/* Test initialistion. */
	trie_print(&t);
	trie_graph(&t, "graph/trie-all-at-once.gv");

	/* Test get. */
	word = "lambda";
	leaf = index_get(&t, word);
	printf("index get: %s --> %s\n", word, leaf);
	leaf = trie_get(&t, word);
	printf("exact get: %s --> %s\n", word, leaf);
	word = "slithern";
	leaf = index_get(&t, word);
	printf("index get: %s --> %s\n", word, leaf);
	leaf = trie_get(&t, word);
	printf("exact get: %s --> %s\n", word, leaf);
	word = "pe";
	index_prefix(&t, word, &start, &end);
	printf("index prefix: %s --> { ", word);
	for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");
	printf("exact prefix: %s --> { ", word);
	if(trie_prefix(&t, word, &start, &end)) for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");
	word = "qz";
	index_prefix(&t, word, &start, &end);
	printf("index prefix: %s --> { ", word);
	for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");
	printf("exact prefix: %s --> { ", word);
	if(trie_prefix(&t, word, &start, &end)) for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");

	/* Test put. */
	assert(t.leaves.size == words_size);
	for(i = 0; i < extra_size; i++) {
		char fn[64];
		if(!trie_put(&t, extra[i], &eject, 0)) goto catch;
		sprintf(fn, "graph/trie-extra%02lu.gv", (unsigned long)i);
		trie_graph(&t, fn);
	}
	assert(t.leaves.size == words_size + extra_size);
	for(i = 0; i < words_size; i++) {
		leaf = trie_get(&t, words[i]);
		assert(leaf && leaf == words[i]);
	}
	for(i = 0; i < extra_size; i++) {
		leaf = trie_get(&t, extra[i]);
		assert(leaf && leaf == extra[i]);
	}
	for(i = 0; i < extra_size; i++) {
		const int is = trie_remove(&t, extra[i]);
		assert(is);
	}
	trie_graph(&t, "graph/trie-removed.gv");
	assert(t.leaves.size == words_size);
	for(i = 0; i < words_size; i++) {
		leaf = trie_get(&t, words[i]);
		assert(leaf && leaf == words[i]);
	}
	for(i = 0; i < extra_size; i++) {
		leaf = trie_get(&t, extra[i]);
		assert(!leaf);
	}

	/* Test spelling. */
	word = "trie";
	if(!geodesics(word, &t)) goto catch;
	if(!wf.closest.size) {
		printf("%s spelt correctly.\n", word);
	} else {
		printf("Dictionary words closest to %s:", word);
		for(i = 0; i < wf.closest.size; i++)
			printf(" %s", wf.closest.data[i]);
		printf(".\n");
	}

	success = EXIT_SUCCESS;
	goto finally;
catch:
	perror("trie");
finally:
	trie_(&t);
	wagner_fischer_();
	return success;
}






#if 0
/*printf("delete found %s --> %s\n",
 words[i], leaf ? leaf : "nothing");*/
/*printf("delete found %s --> %s\n",
 extra[i], leaf ? leaf : "nothing");*/
/*printf("found %s --> %s\n", words[i], leaf ? leaf : "nothing");*/
/*printf("found %s --> %s\n", extra[i], leaf ? leaf : "nothing");*/

/*word = "ainsertion", edit = 1;
 if(!trie_suggest(&t, word, edit, &lsuggest)) goto catch;
 printf("suggest(\"%s\", %u):", word, edit);
 for(i = 0; i < lsuggest.size; i++) printf(" %s", lsuggest.data[i]);
 leaf_array_clear(&lsuggest);
 printf("\n");
 printf("Subset of?\n");
 printf("%s\n", index_get(&t, "insertion"));
 printf("%s\n", index_get(&t, "ansertion"));
 printf("%s\n", index_get(&t, "aisertion"));
 printf("%s\n", index_get(&t, "ainertion"));
 printf("%s\n", index_get(&t, "ainsrtion"));
 printf("%s\n", index_get(&t, "ainsetion"));
 printf("%s\n", index_get(&t, "ainserion"));
 printf("%s\n", index_get(&t, "ainserton"));
 printf("%s\n", index_get(&t, "ainsertin"));
 printf("%s\n", index_get(&t, "ainsertio"));
 printf("%s\n", index_get(&t, "ainsertion"));*/

/*
 trie_(&t);
 if(!trie_init(&t, extra, extra_size, 0)) goto catch;
 trie_print(&t);
 trie_graph(&t, "graph/trie-extra.gv");

 word = "fbar", edit = 2;
 if(!trie_suggest(&t, word, edit, &lsuggest)) goto catch;
 printf("suggest(\"%s\", %u):", word, edit);
 for(i = 0; i < lsuggest.size; i++) printf(" %s", lsuggest.data[i]);
 leaf_array_clear(&lsuggest);
 printf("\n");
 printf("Subset of?\n");
 printf("%s\n", index_get(&t, "ar"));
 printf("%s\n", index_get(&t, "br"));
 printf("%s\n", index_get(&t, "ba"));
 printf("%s\n", index_get(&t, "bar"));
 printf("%s\n", index_get(&t, "ar"));
 printf("%s\n", index_get(&t, "fr"));
 printf("%s\n", index_get(&t, "fa"));
 printf("%s\n", index_get(&t, "far"));
 printf("%s\n", index_get(&t, "br"));
 printf("%s\n", index_get(&t, "fr"));
 printf("%s\n", index_get(&t, "fb"));
 printf("%s\n", index_get(&t, "fbr"));
 printf("%s\n", index_get(&t, "ba"));
 printf("%s\n", index_get(&t, "fa"));
 printf("%s\n", index_get(&t, "fb"));
 printf("%s\n", index_get(&t, "fba"));
 printf("%s\n", index_get(&t, "fbar"));
 */

/* <Levenshtein>:
 - Insertion: -> b;
 - Deletion: a ->;
 - Substitution: a -> b
 <Damerau>:
 - transpositions: ab -> ba */
static int bfs_r(const struct Trie *const t, struct LeafArray *const output,
				 const char *const key, const unsigned remaining_edits,
				 size_t n0, size_t n1, size_t i) {
	Branch branch;
	assert(t && output && key
		   && n0 <= n1 && n1 < t->leaves.size && i < t->leaves.size);
	while(n0 < n1) {
		size_t future_bit;
		branch = t->branches.data[n0];
		future_bit = bit + trie_skip(branch);
		for(byte = future_bit >> 3; key_byte < byte; key_byte++)
			if(key[key_byte] == '\0') { printf("%sinternal node\n", depth2str(edit)); return 1; }

		/* Delete BFS, subsequent edits only if we are on the next byte. */
		if(edit && delete_byte < key_byte) delete_byte = key_byte,
			suggest_r(t, key + 1, output, edit - 1, n0, n1, i, bit);

		bit = future_bit;
		left = trie_left(branch);
		left_child = n0 + 1;
		right_child = left_child + left;
		if(!trie_is_bit(key, bit++)) {
			int is_already = subs_byte == key_byte;
			printf("%sleft at %lu\n", depth2str(edit), bit);
			if(edit || is_already) suggest_r(t, key, output, edit - !is_already, right_child, n1, i, bit), subs_byte = key_byte;
			n0 = left_child, n1 = right_child;
		} else {
			int is_already = subs_byte == key_byte;
			printf("%sright at %lu\n", depth2str(edit), bit);
			if(edit || is_already) suggest_r(t, key, output, edit - !is_already, right_child, n1, i, bit), subs_byte = key_byte;
			n0 = right_child, i += left + 1;
		}
	}
	assert(n0 == n1 && i < t->leaves.size);
	if(!(new_key = leaf_new(output))) return 0;
	*new_key = t->leaves.data[i];
	printf("%sfound \"%s\" }\n", depth2str(edit), *new_key);
	return 1;
}

/*struct TriePosition {
 const struct Trie *t;
 const char *key;
 size_t n0, n1, i, bit;
 unsigned edit;
 struct LeafArray *output;
 };*/

static unsigned max_edit;

static const char *depth2str(const unsigned edit) {
	static char buffer[64];
	unsigned depth, d;
	assert(max_edit < sizeof buffer - 1 && edit <= max_edit);
	depth = max_edit - edit;
	for(d = 0; d < depth; d++) buffer[d] = '\t';
	buffer[depth] = '\0';
	return buffer;
}

/** Breath-first-search `t` for `edit` Levenshtein edits away from `key` and
 appends `output`. @order I don't know. */
static int suggest_r(const struct Trie *const t, const char *key,
	struct LeafArray *const output, const unsigned edit,
	size_t n0, size_t n1, size_t i, size_t bit) {
	Branch branch;
	size_t byte, key_byte = bit >> 3, delete_byte = key_byte, subs_byte = (size_t)-1, future_bit;
	size_t left, left_child, right_child;
	Leaf *new_key;
	assert(t && key && output && n0 <= n1 && n1 < t->leaves.size);
	printf("%s{ \"%s\" edit %u, n=[%lu, %lu], i=%lu, bit=%lu\n",
		depth2str(edit), key, edit, n0, n1, i, bit);

	/* BFS limit of `edit`; first edit. */
	if(edit && key[0] != '\0') /* Deletion. */
		suggest_r(t, key + 1, output, edit - 1, n0, n1, i, bit);

	while(n0 < n1) {
		branch = t->branches.data[n0];
		future_bit = bit + trie_skip(branch);
		/* `key` ends at an internal branch; NUL-terminator is part of `key`. */
		for(byte = future_bit >> 3; key_byte < byte; key_byte++)
			if(key[key_byte] == '\0') { printf("%sinternal node\n", depth2str(edit)); return 1; }

		/* Delete BFS, subsequent edits only if we are on the next byte. */
		if(edit && delete_byte < key_byte) delete_byte = key_byte,
			suggest_r(t, key + 1, output, edit - 1, n0, n1, i, bit);

		bit = future_bit;
		left = trie_left(branch);
		left_child = n0 + 1;
		right_child = left_child + left;
		if(!trie_is_bit(key, bit++)) {
			int is_already = subs_byte == key_byte;
			printf("%sleft at %lu\n", depth2str(edit), bit);
			if(edit || is_already) suggest_r(t, key, output, edit - !is_already, right_child, n1, i, bit), subs_byte = key_byte;
			n0 = left_child, n1 = right_child;
		} else {
			int is_already = subs_byte == key_byte;
			printf("%sright at %lu\n", depth2str(edit), bit);
			if(edit || is_already) suggest_r(t, key, output, edit - !is_already, right_child, n1, i, bit), subs_byte = key_byte;
			n0 = right_child, i += left + 1;
		}
	}
	assert(n0 == n1 && i < t->leaves.size);
	if(!(new_key = leaf_array_new(output))) return 0;
	*new_key = t->leaves.data[i];
	printf("%sfound \"%s\" }\n", depth2str(edit), *new_key);
	return 1;
}

/** @return True unless error. */
static int trie_suggest(const struct Trie *const t, const char *const key,
	unsigned edit_limit, struct LeafArray *const output) {
	assert(t && key && output);
	if(!t->leaves.size) return 1;
	max_edit = edit_limit; /* Debug print global. */
	suggest_r(t, key, output, edit_limit, 0, t->leaves.size - 1, 0, 0);
	return 1;
}

#endif
