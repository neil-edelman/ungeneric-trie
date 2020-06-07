#include <stdlib.h> /* EXIT malloc free qsort */
#include <stdio.h>  /* printf */
#include <string.h> /* memmove memcpy */
#include <assert.h> /* assert */
#include <errno.h>  /* errno */


/** Leaves are strings, (for example.) */
typedef const char *TrieLeaf;

/** Returns a boolean given two `TrieLeaf`. */
typedef int (*TrieBipredicate)(TrieLeaf, TrieLeaf);

/** @implements qsort bsearch */
static int vstrcmp(const void *const a, const void *const b)
	{ return strcmp(*(char **)a, *(char **)b); }

struct LeafArray { TrieLeaf *data; size_t size, capacity; };

/** Initialises `a` to idle. */
static void leaf_array(struct LeafArray *const a)
	{ assert(a), a->data = 0, a->capacity = a->size = 0; }

/** Destroys `a` and returns it to idle. */
static void leaf_array_(struct LeafArray *const a)
	{ assert(a), free(a->data), leaf_array(a); }

/** Ensures `min_capacity` of `a`.
 @param[min_capacity] If zero, does nothing.
 @return Success; otherwise, `errno` will be set.
 @throws[ERANGE] Tried allocating more then can fit in `size_t` or `realloc`
 doesn't follow POSIX. @throws[realloc] */
static int leaf_reserve(struct LeafArray *const a, const size_t min_capacity) {
	size_t c0;
	TrieLeaf *data;
	const size_t max_size = (size_t)-1 / sizeof *a->data;
	assert(a);
	if(a->data) {
		if(min_capacity <= a->capacity) return 1;
		c0 = a->capacity;
		if(c0 < 8) c0 = 8;
	} else { /* Idle. */
		if(!min_capacity) return 1;
		c0 = 8;
	}
	if(min_capacity > max_size) return errno = ERANGE, 0;
	/* `c_n = a1.625^n`, approximation golden ratio `\phi ~ 1.618`. */
	while(c0 < min_capacity) {
		size_t c1 = c0 + (c0 >> 1) + (c0 >> 3);
		if(c0 >= c1) { c0 = max_size; break; } /* Overflow; very unlikely. */
		c0 = c1;
	}
	if(!(data = realloc(a->data, sizeof *a->data * c0)))
		{ if(!errno) errno = ERANGE; return 0; }
	a->data = data, a->capacity = c0;
	return 1;
}

/** Returns a new un-initialized datum of `a`. */
static TrieLeaf *leaf_new(struct LeafArray *const a) {
	assert(a); return leaf_reserve(a, a->size + 1) ? a->data + a->size++ : 0;
}

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


/* Trie internal nodes are semi-implicit. Each contains two items of
 information in a `size_t`: left children branches are <fn:trie_left>
 immediately following, right children are the rest, and <fn:trie_bit>, the
 bit at which the all the branches on the left differ from that on the right. */
typedef size_t TrieBranch;

struct BranchArray { TrieBranch *data; size_t size, capacity; };

/** Initialises `a` to idle. */
static void branch_array(struct BranchArray *const a)
	{ assert(a), a->data = 0, a->capacity = a->size = 0; }

/** Destroys `a` and returns it to idle. */
static void branch_array_(struct BranchArray *const a)
	{ assert(a), free(a->data), branch_array(a); }

/** Ensures `min_capacity` of `a`. */
static int branch_reserve(struct BranchArray *const a,
	const size_t min_capacity) {
	size_t c0;
	TrieBranch *data;
	const size_t max_size = (size_t)-1 / sizeof *a->data;
	assert(a);
	if(a->data) {
		if(min_capacity <= a->capacity) return 1;
		c0 = a->capacity;
		if(c0 < 8) c0 = 8;
	} else {
		if(!min_capacity) return 1;
		c0 = 8;
	}
	if(min_capacity > max_size) return errno = ERANGE, 0;
	while(c0 < min_capacity) {
		size_t c1 = c0 + (c0 >> 1) + (c0 >> 3);
		if(c0 >= c1) { c0 = max_size; break; }
		c0 = c1;
	}
	if(!(data = realloc(a->data, sizeof *a->data * c0)))
		{ if(!errno) errno = ERANGE; return 0; }
	a->data = data, a->capacity = c0;
	return 1;
}

/** Returns a new un-initialized datum of `a`. */
static TrieBranch *branch_new(struct BranchArray *const a) {
	assert(a); return branch_reserve(a, a->size + 1) ? a->data + a->size++ : 0;
}

/* 12 makes the maximum skip length 512 bytes and the maximum size of a trie is
 `size_t` 64-bits: 4503599627370495, 32-bits: 1048575, and 16-bits: 15. */
#define TRIE_SKIP 12
#define TRIE_SKIP_MAX ((1 << TRIE_SKIP) - 1)
#define TRIE_LEFT_MAX (((size_t)1 << ((sizeof(size_t) << 3) - TRIE_SKIP)) - 1)

/** @return Packs `bit` and `left` into a branch. */
static TrieBranch trie_branch(const unsigned skip, const size_t left) {
	assert(skip <= TRIE_SKIP_MAX && left <= TRIE_LEFT_MAX);
	return skip + (left << TRIE_SKIP);
}

/** @return Unpacks skip from `branch`. */
static unsigned trie_skip(const TrieBranch branch)
	{ return (unsigned)branch & TRIE_SKIP_MAX; }

/** @return Unpacks left sub-branches from `branch`. */
static size_t trie_left(const TrieBranch branch) { return branch >> TRIE_SKIP; }

/** Increments the left `branch` count. */
static void trie_left_inc(size_t *const branch)
	{ assert(*branch < ~(size_t)TRIE_SKIP_MAX), *branch += TRIE_SKIP_MAX + 1; }

/** Decrements the left `branch` count. */
static void trie_left_dec(size_t *const branch)
	{ assert(*branch > TRIE_SKIP_MAX), *branch -= TRIE_SKIP_MAX + 1; }

/** Compares `bit` from the string `a` against `b`.
 @return In the `bit` position, positive if `a` is after `b`, negative if `a`
 is before `b`, or zero if `a` is equal to `b`. */
static int trie_strcmp_bit(const char *const a, const char *const b,
	const unsigned bit) {
	const unsigned byte = bit >> 3, mask = 128 >> (bit & 7);
	return (a[byte] & mask) - (b[byte] & mask);
}

/** From string `a`, extract `bit` and return zero or non-zero if one. */
static unsigned trie_is_bit(const char *const a, const unsigned bit) {
	const unsigned byte = bit >> 3, mask = 128 >> (bit & 7);
	return a[byte] & mask;
}


struct Trie { struct BranchArray branches; struct LeafArray leaves; };

/** Initialises `t` to idle. */
static void trie(struct Trie *const t) {
	assert(t);
	branch_array(&t->branches), leaf_array(&t->leaves);
}

/** Returns an initialised `t` to idle. */
static void trie_(struct Trie *const t) {
	assert(t);
	branch_array_(&t->branches), leaf_array_(&t->leaves);
}

/** Recursive function used for <fn:trie_init>. Initialise branches of `t`
 up to `bit` with `a` to `a_size` array of sorted leaves.
 @order Speed \O(`leaves`), memory \O(`longest string`). */
static void trie_init_branches_r(struct Trie *const t, unsigned bit,
	const size_t a, const size_t a_size) {
	size_t b = a, b_size = a_size, half;
	unsigned skip = 0;
	TrieBranch *branch;
	assert(t && a_size && a_size <= t->leaves.size && t->leaves.size
		&& t->branches.capacity >= t->leaves.size - 1);
	if(a_size <= 1) return;
	/* Endpoints of sorted range: skip [_1_111...] or [...000_0_].
	 fixme: UINT_MAX overflow. */
	while(trie_is_bit(t->leaves.data[a], bit)
		|| !trie_is_bit(t->leaves.data[a + a_size - 1], bit)) bit++, skip++;
	/* Do a binary search for the first `leaves[a+half_s]#bit == 1`. */
	while(b_size) half = b_size >> 1,
		trie_is_bit(t->leaves.data[b + half], bit)
		? b_size = half : (half++, b += half, b_size -= half);
	b_size = b - a;
	/* Should have space for all branches pre-allocated, (right?) */
	branch = branch_new(&t->branches), assert(branch);
	*branch = trie_branch(skip, b_size - 1);
	bit++;
	trie_init_branches_r(t, bit, a, b_size);
	trie_init_branches_r(t, bit, b, a_size - b_size);
}

/** Initialises `t` to `array`.
 @param[t] An idle or uninitalised trie.
 @param[a_size] The size of the array, cannot be zero.
 @param[merge] Called with any duplicate entries and replaces if true; if
 null, doesn't replace.
 @return Success initialising `t` with `a` of size `a_size`, (non-zero.) */
static int trie_init(struct Trie *const t, const TrieLeaf *const a,
	const size_t a_size, const TrieBipredicate merge) {
	TrieLeaf *leaves;
	assert(t && a && a_size);
	trie(t);
	if(!leaf_reserve(&t->leaves, a_size)
		|| !branch_reserve(&t->branches, a_size - 1)) return 0;
	leaves = t->leaves.data;
	memcpy(leaves, a, sizeof *a * a_size);
	t->leaves.size = a_size;
	qsort(leaves, a_size, sizeof *a, &vstrcmp);
	leaf_compactify(&t->leaves, merge);
	trie_init_branches_r(t, 0, 0, t->leaves.size);
	assert(t->branches.size + 1 == t->leaves.size);
	return 1;
}

/** Add `datum` to `t`. Must not be the same as any key of trie; _ie_ it
 does not check for the end of the string. @return Success. @order \O(|`t`|)
 @throws[ERANGE] At capacity or string too long.? @throws[realloc] */
static int trie_add(struct Trie *const t, TrieLeaf datum) {
	const size_t leaf_size = t->leaves.size, branch_size = leaf_size - 1;
	size_t n0 = 0, n1 = branch_size, i = 0, left;
	TrieBranch *branch;
	const char *n0_key;
	unsigned bit = 0, n0_bit;
	TrieLeaf *leaf;
	int cmp; /* fixme: has not changed with skip bits. */

	/* Verify string length and empty short circuit. */
	assert(t && datum);
	if(strlen(datum) > (TRIE_SKIP_MAX >> 3) - 1/* null */)
		return errno = ERANGE, 0;
	if(!leaf_size) return assert(!t->branches.size),
		(leaf = leaf_new(&t->leaves)) ? *leaf = datum, 1 : 0;

	/* Non-empty; verify conservative maximally unbalanced trie. */
	assert(leaf_size == branch_size + 1); /* Waste `size_t`. */
	if(leaf_size >= TRIE_LEFT_MAX) return errno = ERANGE, 0; /* EILSEQ */
	if(!leaf_reserve(&t->leaves, leaf_size + 1)
		|| !branch_reserve(&t->branches, branch_size + 1)) return 0;

	/* Internal nodes. */
	while(branch = t->branches.data + n0, n0_key = t->leaves.data[i], n0 < n1) {
		assert(0);
		/*for(n0_bit = trie_bit(*branch); bit < n0_bit; bit++)
			if((cmp = trie_strcmp_bit(datum, n0_key, bit)) != 0) goto insert;*/
		left = trie_left(*branch) + 1;
		if(!trie_is_bit(datum, bit)) trie_left_inc(branch), n1 = n0++ + left;
		else n0 += left, i += left;
	}

	/* Leaf. */
	while((cmp = trie_strcmp_bit(datum, n0_key, bit)) == 0) bit++;

insert:
	assert(n0 <= n1 && n1 <= t->branches.size && n0_key && i <= t->leaves.size);
	if(cmp < 0) left = 0;
	else left = n1 - n0, i += left + 1;

	leaf = t->leaves.data + i;
	memmove(leaf + 1, leaf, sizeof *leaf * (leaf_size - i));
	*leaf = datum;
	t->leaves.size++;

	branch = t->branches.data + n0;
	memmove(branch + 1, branch, sizeof *branch * (branch_size - n0));
	*branch = trie_branch(bit, left);
	t->branches.size++;

	return 1;
}

/** Don't care bits of `key` are not tested, those that aren't involved in
 making a decision, and are not stored in the trie. @return `t` leaf that
 potentially matches `key` or null if it definitely is not in `t`.
 @order \O(`key.length`) */
static TrieLeaf trie_match(const struct Trie *const t, const char *const key) {
	size_t n0 = 0, n1 = t->leaves.size, i = 0, left;
	TrieBranch branch;
	unsigned n0_byte, str_byte = 0, bit = 0; /* `bit` should be size_t */
	assert(t && key);
	if(!n1) return 0; /* Special case: empty has no matches. */
	n1--, assert(n1 == t->branches.size);
	while(n0 < n1) {
		branch = t->branches.data[n0];
		bit += trie_skip(branch);
		for(n0_byte = bit >> 3; str_byte < n0_byte; str_byte++)
			if(key[str_byte] == '\0') return 0;
		left = trie_left(branch);
		if(!trie_is_bit(key, bit)) n1 = ++n0 + left;
		else n0 += left + 1, i += left + 1;
		bit++;
	}
	assert(n0 == n1 && i < t->leaves.size);
	return t->leaves.data[i];
}

/** In `t` that must be non-empty, given a partial `key`, stores the leaf
 [`low`, `high`] descision bits prefix matches. @order \O(`key.length`) */
static void trie_prefix(const struct Trie *const t, const char *const key,
	size_t *const low, size_t *const high) {
	size_t n0 = 0, n1 = t->leaves.size, i = 0, left;
	TrieBranch branch;
	unsigned n0_byte, str_byte = 0, bit = 0;
	assert(t && key && low && high && n1);
	n1--, assert(n1 == t->branches.size);
	while(n0 < n1) {
		branch = t->branches.data[n0];
		bit += trie_skip(branch);
		/* _Sic_; `\0` is _not_ included for partial match. */
		for(n0_byte = bit >> 3; str_byte <= n0_byte; str_byte++)
			if(key[str_byte] == '\0') goto finally;
		left = trie_left(branch);
		if(!trie_is_bit(key, bit)) n1 = ++n0 + left;
		else n0 += left + 1, i += left + 1;
		bit++;
	}
	assert(n0 == n1);
finally:
	assert(n0 <= n1 && i - n0 + n1 < t->leaves.size);
	*low = i, *high = i - n0 + n1;
}

/** Remove leaf index `i` from `t`. */
static void trie_remove(struct Trie *const t, size_t i) {
	size_t n0 = 0, n1 = t->branches.size, last_n0, left;
	size_t *branch;
	assert(t && i < t->leaves.size && t->branches.size + 1 == t->leaves.size);
	/* fixme: make sure that we could combine siblings' and parents' skips. */
	/* Remove leaf. */
	if(!--t->leaves.size) return; /* Special case of one leaf. */
	memmove(t->leaves.data + i, t->leaves.data + i + 1,
			sizeof t->leaves.data * (n1 - i));
	/* Remove branch. */
	for( ; ; ) {
		left = trie_left(*(branch = t->branches.data + (last_n0 = n0)));
		if(i <= left) {
			if(!left) break;
			n1 = ++n0 + left;
			trie_left_dec(branch);
		} else {
			if((n0 += ++left) >= n1) break;
			i -= left;
		}
	}
	memmove(branch, branch + 1, sizeof n0 * (--t->branches.size - last_n0));
}

/** @return `key` is an element of `t` that is an exact match or null. */
static TrieLeaf trie_get(const struct Trie *const t, const char *const key) {
	TrieLeaf match;
	assert(t && key);
	return (match = trie_match(t, key)) && !strcmp(match, key) ? match : 0;
}

/** Adds `data` to `t` and, if `eject` is non-null, stores the collided
 element, if any, as long as `replace` is null or returns true.
 @param[eject] If not-null, the ejected datum. If `replace` returns false, then
 `*eject == datum`.
 @return Success. @throws[realloc, ERANGE] */
static int trie_put(struct Trie *const t, TrieLeaf datum,
	TrieLeaf *const eject, const TrieBipredicate replace) {
	TrieLeaf match;
	assert(t && datum);
	/* Add. */
	if(!(match = trie_get(t, datum))) {
		if(eject) *eject = 0;
		return trie_add(t, datum);
	}
	/* Collision policy. */
	if(replace && !replace(match, datum)) {
		if(eject) *eject = datum;
	} else {
		if(eject) *eject = match;
		match = datum;
	}
	return 1;
}

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
		printf("%s%u:%lu", n ? ", " : "", trie_skip(t->branches.data[n]),
		(unsigned long)trie_left(t->branches.data[n]));
	printf("}.\n");
}

/** Given `n` in `t` branches, caluculate the right child branches. Used in
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
		fprintf(fp, "\tbranch%lu [label = \"%u\"];\n"
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
"lipotropins","sinkage","slooshes","homoplastic","feateous"
	}, *const extra[] = { "foo", "bar", "baz", "qux", "quxx" };
	const size_t words_size = sizeof words / sizeof *words,
		extra_size = sizeof extra / sizeof *extra;
	size_t start, end, i;
	struct Trie t;
	TrieLeaf leaf, eject;
	const TrieLeaf word = "slithern", prefix = "pe";
	int success = EXIT_FAILURE;
	if(!trie_init(&t, words, words_size, 0)) goto catch;
	trie_print(&t);
	trie_graph(&t, "graph/trie-words.gv");
	leaf = trie_match(&t, word);
	printf("match: %s --> %s\n", word, leaf);
	trie_prefix(&t, prefix, &start, &end);
	printf("match prefix: %s --> { ", prefix);
	for(i = start; i <= end; i++)
		printf("%s%s", i == start ? "" : ", ", t.leaves.data[i]);
	printf(" }.\n");
	assert(t.leaves.size == words_size);
	for(i = 0; i < extra_size; i++)
		if(!trie_put(&t, extra[i], &eject, 0)) goto catch;
	trie_graph(&t, "graph/trie-words-extra.gv");
	assert(t.leaves.size == words_size + extra_size);
	success = EXIT_SUCCESS;
	goto finally;
catch:
	perror("trie");
finally:
	trie_(&t);
	return success;
}
