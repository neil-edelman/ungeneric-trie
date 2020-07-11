/** @license 2020 Neil Edelman,
 [MIT License](https://opensource.org/licenses/MIT). */

#include <stdlib.h> /* EXIT malloc free qsort */
#include <stdio.h>  /* printf */
#include <string.h> /* memmove memcpy */
#include <assert.h> /* assert */
#include <errno.h>  /* errno */
#include <limits.h> /* INT_MAX */
/* Added in `C99` and doesn't guarantee `uint64_t`; can be replaced with
 `typedef` these machine-dependant types. */
#include <stdint.h> /* uint8_t uint64_t */
#include "Trie.h"
#include "MinArray.h" /* DEFINE_MIN_ARRAY */

#define DICT_MAX_WORD_LENGTH 64

/** This saves the position in the trie, bit-by-bit. */
struct Node { size_t bit, n0, n1, i; enum { LEFT, RIGHT, LEAF } choice; };

MIN_ARRAY(node, Node, struct Node)

MIN_ARRAY(byte, Byte, uint8_t)

/* Already defined in Trie.h. */
MIN_ARRAY_FNS(size, Size, size_t)
MIN_ARRAY_FNS(leaf, Leaf, Leaf)

struct Path {
	struct Trie dict; /* Pointers to in-order words as leaves and branches. */
	/* <fn:path_dfs>. */
	struct NodeArray nodes; /* Temporary path to an entry in `trie`. */
	struct SizeArray next; /* Index in `nodes` of each byte. */
	/* <fn:path_wagner_fisher>. */
	const char *row, *column;
	size_t row_length, column_length;
	unsigned ld, common; /* Levenshtein, common bytes. */
	struct LeafArray closest; /* Current suggestions with `ld`. */
	struct ByteArray table; /* DP matrix with width `query_length`. */
};

/** Initialise `p` with dictionary `a` of `a_size`. */
static int path(struct Path *const p, const Leaf *const a,
	const size_t a_size) {
	assert(p && a && a_size);
	/* <fn:path_dfs>. */
	node_array(&p->nodes);
	size_array(&p->next);
	/* <fn:path_wagner_fisher>. */
	p->row = p->column = 0;
	p->row_length = p->column_length = 0;
	p->ld = p->common = 0;
	leaf_array(&p->closest);
	byte_array(&p->table);
	return Trie(&p->dict, a, a_size);
}

/** Destroy `p`. */
static void path_(struct Path *const p) {
	assert(p);
	Trie_(&p->dict);
	node_array_(&p->nodes);
	size_array_(&p->next);
	leaf_array_(&p->closest);
	byte_array_(&p->table);
}
/** Print `p`. */
static void path_print(const struct Path *const p) {
	size_t next, max, i = 0;
	struct Node *n;
	assert(p);
	printf("Path byte:");
	for(next = 0; next < p->next.size; next++)
		printf(" %lu:%lu", next, p->next.data[next]);
	printf(" looks like:\n");
	for(next = 0; next < p->next.size; next++) {
		max = p->next.data[next], assert(max <= p->nodes.size);
		printf("__ byte %lu (bits %lu--%lu) max %lu __\n",
			   next, next << 3, (next << 3) + 7, max);
		while(i < max) {
			n = p->nodes.data + i++;
			printf(" Bit %lu: [%lu,%lu], leaf %lu, choice %u\n",
				n->bit, n->n0, n->n1, n->i, n->choice);
		}
	}
	printf("__ the rest __\n");
	while(i < p->nodes.size) {
		n = p->nodes.data + i++;
		printf(" Bit %lu: [%lu,%lu], leaf %lu, choice %u\n",
			   n->bit, n->n0, n->n1, n->i, n->choice);
	}
}
/** Called from <fn:path_dfs>. Add to `path`, `bit`, which must be strictly
 monotonic with other bits, `n0` >= `n1`, branch indices, and `i`, leaf
 index. @fixme Only return choice. */
static struct Node *path_new_node(struct Path *const p, const size_t bit,
	const size_t n0, const size_t n1, const size_t i) {
	struct Node *node;
	const size_t byte = bit >> 3;
	/*printf("path_new bit %lu byte %lu: [%lu, %lu], leaf %lu.\n",
		bit, byte, n0, n1, i);*/
	assert(p && (!p->next.size
		|| p->next.data[p->next.size - 1] < p->nodes.size) && n0 <= n1);
	node = node_array_new(&p->nodes);
	node->bit = bit;
	node->n0  = n0;
	node->n1  = n1;
	node->i   = i;
	node->choice = LEAF;
	/* Expand `next` to include `byte`. Is sort of a hash. */
	if(p->next.size == byte) goto finally;
	assert(p->next.size < byte);
	if(!size_array_reserve(&p->next, byte)) return 0;
	while(p->next.size < byte) p->next.data[p->next.size++]
		= node - p->nodes.data;
finally:
	return node;
}
static int path_dfs_from(struct Path *const p, const char *const key) {
	assert(p && p->nodes.size);
	return 0;
}
/** Consumes `p.nodes` and `p.byte` and requires that `p.trie` is be non-empty.
 Given a `key`, stores every choice made, only given the index, ignoring don't
 care bits. If given `key` in `p`, it will find the path to it; `key` not in
 `p`, it will find a path to some element in `p`. The stored entry is at
 `p.dict.leaves.data[p.nodes.data[p.nodes.size - 1].i]`.
 @order \O(`key.length`) @return Success. */
static int path_dfs(struct Path *const p, const char *const key) {
	size_t n0 = 0, n1 = p->dict.branches.size, i = 0, left, right;
	size_t branch;
	size_t byte, key_byte = 0, bit = 0;
	struct Node *node;
	assert(key && p && n1 + 1 == p->dict.leaves.size); /* Full binary tree. */
	/* Clear temp nodes and bytes. (fixme: don't have to clear all.) */
	node_array_clear(&p->nodes);
	size_array_clear(&p->next);
	/* Descend the trie normally, storing the nodes. */
	while((node = path_new_node(p, bit, n0, n1, i)) && n0 < n1) {
		branch = p->dict.branches.data[n0];
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
	 children. Statistically the best choice without looking at them, though
	 is a poor guess practically in most dictionaries because words have a lot
	 of redundant information; otoh, this is probably mot the closest anyway.
	 fixme: nodes don't have to be inserted if they are not going to be used? */
	while((node = path_new_node(p, bit, n0, n1, i)) && n0 < n1) {
		branch = p->dict.branches.data[n0];
		bit += trie_skip(branch);
		left = trie_left(branch);
end_key:
		assert(n1 > n0 + left);
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
static void path_wf_print(const struct Path *const p) {
	size_t r, r_end, c;
	assert(p->row && p->column && p->table.size
		== (p->row_length + 1) * (p->column_length + 1));
	printf("   ");
	for(r = 0, r_end = p->row_length; r < r_end; r++)
		assert(p->row[r] != '\0'), printf(" %c", p->row[r]);
	printf("\n ");
	for(r = 0, r_end = p->row_length + 1; r < r_end; r++)
		printf(" %u", p->table.data[r]);
	printf("\n");
	for(c = 0; c < p->column_length; c++) {
		assert(p->column[c] != '\0'), printf("%c", p->column[c]);
		for(r_end = (c + 2) * (p->row_length + 1); r < r_end; r++)
			printf(" %u", p->table.data[r]);
		printf("\n");
	}
}
static int path_wagner_fischer(struct Path *const p) {
	size_t table_size, i, c, q;
	/* Contains excepts from 2019 Fujimoto Seiji <fujimoto@ceptord.net>. Can We
	 Optimize the Wagner-Fischer Algorithm? placed in public domain. */
	uint8_t u, v;
	/* @fixme This is not enough to guarantee bounds. */
	assert(p->dict.leaves.size
		&& p->row && p->row_length < 256
		&& p->column && p->column_length < 256);
	printf("path wagner fischer, row: %s(%lu), column: %s(%lu)\n",
		p->row, p->row_length, p->column, p->column_length);
	/* Horizontal \times vertical. */
	table_size = (p->row_length + 1) * (p->column_length + 1);
	byte_array_clear(&p->table);
	if(!byte_array_reserve(&p->table, table_size)) return 0;
	p->table.size = table_size;
	/* debug: fill. */
	for(i = 0; i < table_size; i++) p->table.data[i] = 42;
	p->common = 0;
	/* Fill the first row. */
	for(i = 0; i <= p->row_length; i++) p->table.data[i] = i;
	/* Fill all others. */
	for(c = 0; c < p->column_length; c++) {
		/* Fill the first of the row. */
		p->table.data[i++] = c + 1;
		for(q = 0; q < p->row_length; q++) {
			/* @fixme Implement Ukkonen's optimisation?
			 @fixme Abs min at right, done? */
			if(p->row[q] == p->column[c]) {
				u = p->table.data[i - p->row_length - 2]; /* Diagonal. */
				p->table.data[i++] = u;
				if(!u) p->common++;
			} else {
				u = p->table.data[i - 1]; /* Left. */
				v = p->table.data[i - p->row_length - 1]; /* Top. */
				if(u > v) u = v;
				v = p->table.data[i - p->row_length - 2]; /* Diagonal. */
				if(u > v) u = v;
				p->table.data[i++] = u + 1;
			}
		}
		/*if(c + 2 > p->row_length); ... */
	}
	p->ld = i ? p->table.data[i - 1] : 0;
	return 1;
}




#if 1
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
#endif








/** Suggest Levenshtein geodesics for `query` in `p` and output them to
 `p.closest` or `!p.closest.size` if `query` was actually in `p`.
 @return Success. */
static int path_geodesics(struct Path *const p, const char *const query) {
	Leaf *leaf, candidate;
	unsigned lev;

	printf("geodesics(%s).\n", query);
	/* Initialise suggestions. */
	assert(query && p && p->dict.leaves.size);
	leaf_array_clear(&p->closest);

	/* If the dictionary actually contains `query`, then skip the path. */
	if(trie_get(&p->dict, query)) return 1;

	/* Greedy educated guess to serve as the starting point. */
	if(!path_dfs(p, query)) return 0;
	candidate = p->dict.leaves.data[p->nodes.data[p->nodes.size - 1].i];
	path_print(p);
	if(!(leaf = leaf_array_new(&p->closest))) return 0;
	*leaf = candidate;

	/* Do Wagner-Fisher. */
	p->row = query;
	if((p->row_length = strlen(query)) > 255) return 1;
	{
		p->column = candidate;
		if((p->column_length = strlen(candidate)) > 255) return 1;
		if(!path_wagner_fischer(p)) return 0;
		path_wf_print(p);
		printf("ld: %u, common: %u.\n", p->ld, p->common);
	}

#if 1
	/* Just to be certain. */
	if(wagner_fischer_do(query, candidate, &lev))
		printf("wf do: %u\n", lev), assert(lev == p->ld);
	else
		printf("overflow\n");
#endif

	return 1;
}


/* Testing. */

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
		*const look[] = { "trie", "a", "substitute" };
	const size_t words_size = sizeof words / sizeof *words,
		look_size = sizeof look / sizeof *look;
	size_t i;
	struct Path p;
	Leaf word;
	int success = EXIT_FAILURE;

	if(!path(&p, words, words_size)) goto catch;
	trie_print(&p.dict);
	trie_graph(&p.dict, "graph/dictionary.gv");
	for(i = 0; i < look_size; i++) {
		word = look[i];
		if(!path_geodesics(&p, word)) goto catch;
		if(!p.closest.size) {
			printf("%s spelt correctly.\n", word);
		} else {
			size_t j;
			printf("Dictionary words closest to %s:", word);
			for(j = 0; j < p.closest.size; j++)
				printf(" %s", p.closest.data[j]);
			printf(".\n");
		}
	}
	success = EXIT_SUCCESS;
	goto finally;
catch:
	perror("trie");
finally:
	path_(&p);
	return success;
}
