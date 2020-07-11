#include <stddef.h> /* size_t */
#include "MinArray.h"

/** Leaves are string constants; `typedef` because it could be a more complex
 structure like an associative array; this defines the minimum usable Trie. */
typedef const char *Leaf;

MIN_ARRAY_DEF(Leaf, Leaf)

MIN_ARRAY_DEF(Size, size_t)

/** Trie is a full binary tree; it's either empty or
 `|branches| + 1 = |leaves|`, (something of a phase transition happens at the
 interface.) */
struct Trie { struct SizeArray branches; struct LeafArray leaves; };

#define TRIE_IDLE { ARRAY_IDLE, ARRAY_IDLE }

int Trie(struct Trie *, const char *const*, size_t);
void Trie_(struct Trie *);
const char *TrieGet(const struct Trie *, const char *);
void TriePrefix(const struct Trie *, const char *,
	const char **, const char **);
int TriePut(struct Trie *, const char *);
int TrieRemove(struct Trie *, const char *);
int TrieGraph(const struct Trie *, const char *);
