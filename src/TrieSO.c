#include <stdlib.h> /* EXIT malloc free qsort */
#include <stdio.h>  /* printf */
#include <string.h> /* memmove memcpy */
#include <assert.h> /* assert */
#include <errno.h>  /* errno */
#include <limits.h> /* INT_MAX */


/* X-macro for a minimal dynamic array. */
#define MIN_ARRAY(name, Name, type) \
struct Name##Array { type *data; size_t size, capacity; }; \
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
}


/* Trie pre-order internal nodes in the style of <Morrison, 1968 PATRICiA>. */
MIN_ARRAY(size, Size, size_t)

/* 12 makes the maximum skip length 512 bytes and the maximum size of a trie is
 `size_t` 64-bits: 4503599627370495, 32-bits: 1048575, 16-bits: 15, 8-bits: not
 supported at all, sorry, (unlikely since `C++` has additional constraints.) */
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

/** Increments the left descendants `branch` count. @fixme This will trip an
 `assert` if two strings have subsequences that are equal in more than 2^12
 bits and then different. */
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


/** Leaves are string constants necessarily in lexicographic order; `typedef`
 because it could be a more complex structure like an associative array. */
typedef const char *Leaf;

MIN_ARRAY(leaf, Leaf, Leaf)


/** Trie is a full binary tree; it's either empty or
 `|branches| + 1 = |leaves|`. The reason we spilt branches and leaves is it's
 `O(1)` to check the leftmost leaf of a branch, which we do on insertion. */
struct Trie { struct SizeArray branches; struct LeafArray leaves; };

/** Initialises `t` to idle. */
static void trie(struct Trie *const t)
	{ assert(t); size_array(&t->branches), leaf_array(&t->leaves); }

/** Returns an initialised `t` to idle. */
static void trie_(struct Trie *const t)
	{ assert(t); size_array_(&t->branches), leaf_array_(&t->leaves); }

/** Orders `a` and `b` used in <fn:trie_init>. @implements qsort bsearch */
static int vstrcmp(const void *const a, const void *const b)
	{ return strcmp(*(const char *const*const)a, *(const char *const*)b); }

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

/** Initialises `t` to `a` of size `a_size`, which cannot be zero. For code
 brevity, all entries of `a` have to be unique. If this is not the case, the
 strings will happily go past the null and cause undefined behaviour.
 @return Success. @throws[ERANGE, malloc]
 @fixme There's a better way to do this somewhere in the literature? */
static int trie_init(struct Trie *const t, const Leaf *const a,
	const size_t a_size) {
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
	/* fixme: this is where we de-duplicate `t->leaves`; left out. */
	trie_init_branches_r(t, 0, 0, t->leaves.size);
	assert(t->branches.size + 1 == t->leaves.size);
	return 1;
}

/** Looks at only the index for potential matches.
 @param[result] A index pointer to leaves that matches `key` when true.
 @return True if `key` in `trie` may have matched, otherwise `key` is
 definitely is not in `trie`. @order \O(`key.length`) */
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

/** Add `datum` to `t`. Must not be the same as any key of trie; it does not
 check for the end of the string. @return Success. @order \O(`t.size`)
 @throws[ERANGE] Trie reached it's conservative maximum, which on machines
 where the pointer is 64-bits, is 4.5T. On 32-bits, it's 1M.
 @throws[realloc, ERANGE] */
static int trie_add_unique(struct Trie *const t, Leaf key) {
	const size_t leaf_size = t->leaves.size, branch_size = leaf_size - 1;
	size_t n0 = 0, n1 = branch_size, i = 0, left, bit = 0, bit0 = 0, bit1;
	size_t *branch = 0;
	const char *n0_key;
	Leaf *leaf;
	int cmp;
	assert(t && key);
	/* Empty special case. */
	if(!leaf_size) return assert(!t->branches.size),
		(leaf = leaf_array_new(&t->leaves)) ? *leaf = key, 1 : 0;
	/* Redundant `size_t`, but maybe we will use it like Judy compression? */
	assert(leaf_size == branch_size + 1);
	/* Conservative maximally unbalanced trie. Reserve one more. */
	if(leaf_size > TRIE_LEFT_MAX) return errno = ERANGE, 0;
	if(!leaf_array_reserve(&t->leaves, leaf_size + 1)
		|| !size_array_reserve(&t->branches, branch_size + 1)) return 0;
	/* Branch from internal node. */
	while(branch = t->branches.data + n0, n0_key = t->leaves.data[i], n0 < n1) {
		for(bit1 = bit + trie_skip(*branch); bit < bit1; bit++)
			if((cmp = trie_strcmp_bit(key, n0_key, bit)) != 0) goto insert;
		bit0 = bit1;
		left = trie_left(*branch) + 1; /* Leaves. */
		if(!trie_is_bit(key, bit++)) trie_left_inc(branch), n1 = n0++ + left;
		else n0 += left, i += left;
	}
	/* Branch from leaf. */
	while((cmp = trie_strcmp_bit(key, n0_key, bit)) == 0) bit++;
insert:
	assert(n0 <= n1 && n1 <= t->branches.size && n0_key && i <= t->leaves.size
		&& !n0 == !bit0);
	/* How many left entries are there to move. */
	if(cmp < 0) left = 0;
	else left = n1 - n0, i += left + 1;
	/* Insert leaf. */
	leaf = t->leaves.data + i;
	memmove(leaf + 1, leaf, sizeof *leaf * (leaf_size - i));
	*leaf = key, t->leaves.size++;
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

/** Returns a boolean given two `Leaf`. Used for <fn:trie_put>. */
typedef int (*TrieBipredicate)(Leaf, Leaf);

/** Adds `key` to `t` and, if `eject` is non-null, stores the collided element,
 if any, as long as `replace` is null or returns true.
 @param[eject] If not-null, the ejected datum. If `replace` returns false, then
 `*eject == datum`, but it will still return true.
 @return Success. @throws[realloc, ERANGE] */
static int trie_put(struct Trie *const t, Leaf key,
	Leaf *const eject, const TrieBipredicate replace) {
	Leaf *match;
	size_t i;
	assert(t && key);
	/* Add if absent. */
	if(!param_get(t, key, &i)) {
		if(eject) *eject = 0;
		return trie_add_unique(t, key);
	}
	assert(i < t->leaves.size), match = t->leaves.data + i;
	/* Collision policy. */
	if(replace && !replace(*match, key)) {
		if(eject) *eject = key;
	} else {
		if(eject) *eject = *match;
		*match = key;
	}
	return 1;
}

/** @return Whether leaf index `i` has been removed from `t`. */
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
	if(twin) /* fixme: There is nothing to guarantee this. */
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


/* Testing. */


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
static void trie_graph_fp(const struct Trie *const t, FILE *fp) {
	size_t i, n;
	assert(t && fp);
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
}

/** Graphs `t` in `Graphviz` format in the file `fn`.
 @return Success. @throws[fopen, EDOM] */
static int trie_graph(const struct Trie *const t, const char *const fn) {
	FILE *fp;
	assert(t && fn);
	if(!(fp = fopen(fn, "w"))) return 0;
	trie_graph_fp(t, fp);
	return fclose(fp) ? errno ? 0 : (errno = EDOM, 0) : 1;
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
	const char *leaf, *eject;
	const char *word, *res0, *res1;
	int success = EXIT_FAILURE;

	if(!trie_init(&t, words, words_size)) goto catch;

	trie_graph(&t, "graph/trie0.gv");

	word = "lambda";
	res0 = index_get(&t, word);
	res1 = trie_get(&t, word);
	printf("index get: %s --> %s\n"
		"exact get: %s --> %s\n", word, res0, word, res1);

	word = "slithern";
	res0 = index_get(&t, word);
	res1 = trie_get(&t, word);
	printf("index get: %s --> %s\n"
		"exact get: %s --> %s\n", word, res0, word, res1);

	word = "pe";
	printf("index prefix: %s --> { ", word);
	index_prefix(&t, word, &start, &end);
	for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n"
		"exact prefix: %s --> { ", word);
	if(trie_prefix(&t, word, &start, &end)) for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");

	word = "qz";
	index_prefix(&t, word, &start, &end);
	printf("index prefix: %s --> { ", word);
	for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n"
		"exact prefix: %s --> { ", word);
	if(trie_prefix(&t, word, &start, &end)) for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");

	assert(t.leaves.size == words_size);
	for(i = 0; i < extra_size; i++)
		if(!trie_put(&t, extra[i], &eject, 0)) goto catch;
	trie_graph(&t, "graph/trie1.gv");
	assert(t.leaves.size == words_size + extra_size);
	for(i = 0; i < words_size; i++)
		leaf = trie_get(&t, words[i]), assert(leaf && leaf == words[i]);
	for(i = 0; i < extra_size; i++)
		leaf = trie_get(&t, extra[i]), assert(leaf && leaf == extra[i]);

	for(i = 0; i < extra_size; i++) {
		const int is = trie_remove(&t, extra[i]);
		assert(is);
	}
	trie_graph(&t, "graph/trie2.gv");
	assert(t.leaves.size == words_size);
	for(i = 0; i < words_size; i++)
		leaf = trie_get(&t, words[i]), assert(leaf && leaf == words[i]);
	for(i = 0; i < extra_size; i++)
		leaf = trie_get(&t, extra[i]), assert(!leaf);

	success = EXIT_SUCCESS;
	goto finally;
catch:
	perror("trie");
finally:
	trie_(&t);
	return success;
}

/*
 
 [trie]

 Can we speed-up lookup by only storing the difference between the strings in a dynamic hash function, like [HAMT](https://infoscience.epfl.ch/record/64398)? Taking this idea to it's end, I ended up with a binary [PATRICiA][https://dl.acm.org/doi/abs/10.1145/321479.321481] prefix-tree data-structure. There is a great example of PATRICiA trees in [Crochemore, Lecroq, 2009](https://hal.archives-ouvertes.fr/hal-00470103/document), (except they have the byte-order flipped.)

// Bagwell, 2001, Ideal
// Morrison1968PATRICIA
// Crochemore, Lecroq, 2009 Trie
 
 ** Code **
 
 This is a lot to review, but certain parts are more important:
 
 - 9-53: A minimal `C` vector-like-type in an X-Macro.
 - 56-122: Branches array. Each entry represents an internal node, storing two items of information that it needs to represent a tree semi-implicitly in a `size_t`.
 - 125-129: A lexicographically sorted array of words, which are trie leaves. Branches can be seen as an index to this array.
 - 137-199: Initialisation code for a trie.
 - 201-251: `param_index_get`, supplied with a `key`, looks up the position in the index branches, and wrappers.
 - 253-286: `index_prefix`, supplied with a `prefix`, returns a [`low`, `high`] for the index branches matching that prefix, and `trie_prefix` wrapper.
 - 288-370: `trie_add_unique`, insert `key`, and `trie_put` wrapper.
 - 132-409: `index_remove`, removes a path from the root to a leaf, and wrapper `trie_remove`.
 - 415-493: `trie_graph` and supporting functions that make a GraphViz out of a trie.
 - 495-644: `main` that runs some tests and outputs GraphViz files in `graph/` if you have it.

 [code -- run valgrind]

 ** Analysis **

 [compare]
 Random garbage words of a maximum of 64 bytes.

 - Size per element is numerically unstable on low numbers. X-axis is a log scale.
 - Usually a trie is a state machine of independently allocated nodes, but I've set it to be an array. This means it's in-order and contiguous, but dominated by `O(n)` modifications at large `n`.
 - A trie performs okay up to a point, especially when modification is done rarely. This has almost no effect with the length of a string. 
 - Hash table speed is `O(1)`, but that is not including the hash function and not including cache effects. In this case, that's the limiting factor. On English words with have an average of 5 letters, it's even faster, becoming faster then the trie at about 10-20 elements.
 - The `ARRAYINIT` and `TRIEINIT` lines are very close and `TRIEINIT` is always above. This is entirely expected because they both do `qsort` and then the trie does more stuff.
 - `ARRAYLOOK` is `bsearch`.

 ** Questions **
 
 Adding one-at-a-time is way less efficient than initialising it all at once. What is the run-time? How could we improving memory access and speed for initialisation?

 Before I had a fixed 512-byte limit on `bit`. Now I use `skip`, which can expand to the limits of the computer, but only 512 bytes between levels on the tree. I assert that this holds, but really I should check and not allow it to get in an inconsistent state. This is a worry, for instance, [Ziv-Lempel compression tree](Naverro2004), or [Genomic data](WilliamsZobel??). What if I merge two `skip` values on delete and it overflows the 12-bits?
 
 Judy?
 
 */
