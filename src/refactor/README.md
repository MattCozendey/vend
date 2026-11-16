# Refactor

This folder holds a rewrite of Vend in two layers. The lower layer is a generic decentralized
system that knows nothing about versioning. Vend is a small set of hooks on top of it.

This folder stands on its own, and this file is its canon: what it must do, and how it is built.

## Rules of the work

- Laws first. Each module gets its `spec.bend`, with every law stated and approved, before any
  implementation is written.
- Layout: the same onion as the rest of `src/`. Each layer has one `shared.bend` file or one
  `shared/` folder, and what is more general goes deeper. The generic decentralized system lives in
  the `shared` tree of this folder. Vend-specific modules live at the top level of `src/refactor/`.
- Placeholders: when a spec must name, inside a def, an operation that is still an open law (the
  record-set type, for example), that law gets a `?TODO` body in its own spec, with a comment. Its
  implementation later replaces that body in the spec; `impl.bend` holds only proofs for it.
- Self-sufficient: no file in `src/refactor/` imports a file outside it, except Bend's Base. Code
  from elsewhere in the repository is avoided. When it is needed, its file is copied into the layer
  of `src/refactor/` where it belongs (domain-agnostic code goes into the `shared` tree, at the
  depth its generality calls for) and adjusted there; the copy then follows every rule of this
  folder.

## Requirements

Trust

1. Only Bend's checker, the hash and signature functions, and the operating system are trusted.
   Everything else is proven.
2. Each law states exactly what is meant, never less.
3. Group members are trusted for one thing only: they never sign two votes that contradict each
   other. Nobody else is trusted at all.
4. Nodes can be offline, slow or lost, and there is still one history.

Shape

1. All nodes are equal. A "server" is a node that does more.
2. The generic layer comes first and knows nothing about versioning. Versioning is a small set of
   hooks on top of it.
3. Hooks can bring their own data and storage, so speed work happens in the hook, proven equal to
   the plain version.
4. Groups can contain groups, and they can change over time. A change reaches each line at the
   first slot decided from a proposal made after the change was known.

Behavior

1. Nodes with the same records give the same answers, in whatever order they got them. Catching up
   never creates a conflict.
2. A node can hold only part of the data and still never give a wrong answer. It answers "unknown",
   or "within this range", until it knows.
3. No data is ever lost, because enough nodes keep each piece.
4. A request counts once, however often and wherever it is sent. A writer always sees their own
   changes, on any node, even before they are decided.

Cost

1. Cost does not grow with history. A small edit costs about its own size, even in huge files.
2. Caching is safe, now and for any cache added later.
3. The design is simpler and stronger than the current one: fewer separate things to prove, more
   guaranteed behavior.
4. It keeps room for everything planned (formats, nested languages, mounts,
   submodules).

## Design

### Signed records

The state of a node is a set of records, kept as a `patricia_map` from the key of each record to
nothing. A record is an author's public key, words, and the author's signature of the words. Its key
reads back as the record and as nothing else, so correctness never depends on a hash; the
implementation puts a hash in front of the encoding to keep the map balanced. A record enters the set
only if its signature checks. What a record refers to is checked by the queries that read it: a
missing record or part makes their answer Unknown, never wrong. A Sync is a merge of two maps. Two
maps with the same entries are the same map, so the order in which a node receives records cannot
change anything. The summary of each part is a Merkle hash, so two nodes find where their records
differ by trusting SHA-256 alone; `record_sync` exchanges those summaries, then the records of the
parts that differ.

### Queries

A hook is a query over the set. There are two kinds.

- A **monotone** query answers Unknown, Known, or Contradicted. A known answer can also be a range that only
  narrows (for example "at least 3 versions"); Unknown is the widest range. Each monotone query proves
  that more records never change a known answer, except to Contradicted. A known answer can therefore be
  cached forever.
- A **live** query is a function of the set too, so the same records give the same answer. But its
  answer may change when records arrive. A writer's view of a branch with their pending changes is a
  live query. A live query is never cached.

A query that always answers Unknown is monotone and useless. So each monotone query also states when it
must know: if the set holds these records, the answer is known.

A hook may keep its own state, in any data structure, and update it one record at a time. It then
proves that its state gives the same answer as the plain query over the set, whatever the order in
which the records arrived.

### Slot consensus

Consensus is a hook, not the base. It is used only where one choice must win over another, for
example "which request is version 5 of this branch". Everything that only adds (a request exists, a
part exists, a node keeps a part) needs no consensus.

"Slot k is decided" is a monotone query over vote records. It counts only the votes of members of the
group of that slot. Voting is the one act that is not monotone: a node must never sign two votes for
one step. If a member does, the slot's answer becomes Contradicted, with both votes as proof. The damage
stays in the groups that contain the liar. A stranger's votes count nowhere, so a stranger cannot
break anything.

### Groups

One line, the root, holds the configuration: its decided choices set the members of groups and the
owner group of every line, as a hook reads them. A member is a node or another group; the nodes of
a group are the names reached through it that are not groups. The voters of a root slot are the
nodes of the root's owner group after all earlier root slots. The voters of a slot of any other
line are the nodes of that line's owner group in the configuration of the slot's era: at first the
configuration right after the root slot that gave the line an owner, then the era that the line's
previous decided choice names, never lower than the one before. An honest voter accepts a choice
only when the era it names is one whose configuration it already knows, and an honest leader names
the latest such era. So no line waits on an era that the root never reaches, and a change of a
group reaches each line at the first slot decided from a proposal made after the change was known.

### Time

The program reads the clock and gives the core a `Tick` deed when a round takes too long. On a
Tick, a voter moves to the round after its highest one. A voter also catches up to the highest
round that at least half of the voters reached; strangers and faulty voters are fewer than that, so
they cannot drag honest voters into rounds of their own. The core holds no clock value. Safety does
not depend on Ticks; only progress does: a good phase (honest voters in sync and an honest next
leader) decides a slot, and the network and the clock make good phases happen.

### Keeping data

Content lives in a part store: each part under its SHA-256, so a part from any node is right or
absent, never wrong. A node keeps the parts it needs and the parts it signed a claim to keep; it may
drop any other part only once enough trusted keepers, other than itself, signed claims to keep it.
A node that lacks a part asks a peer for it by hash. How many copies are enough, and who the
trusted keepers are, are parameters.

### Records are never forgotten

Records are the history: ballots prove each version, and requests say what it did. They cost a
constant amount per version, and the time of each operation does not grow with them. Forgetting
them would also lose proof: a lie about a forgotten slot could no longer show as Contradicted. So
only parts (the bulk of the data) are ever dropped, and no checkpoint is needed.

## Modules

Each module is stated as laws (`spec.bend`) and approved before its `impl.bend` is written. A
module never imports a sibling, so each module sits one layer above everything it uses:

```
src/refactor/                       Vend (top level)
  shared/                           node
    shared/                         owner_groups, record_views
      shared/                       slot_consensus, record_sync
        shared/                     signed_records, monotone_queries
          shared/                   patricia_map, exact_word_encoding, signatures, part_store
            shared/                 sha256, association_list, word_list_sets, item_merge
              shared/               shared.bend, word_list_order, list_append
```

No layer is created before a module needs it. When a generic module is written above `node`, the tree below it moves down one layer; imports are relative, so they do
not change.

| Module | What it states | Status |
| --- | --- | --- |
| `list_append` | Joining lists (Base's `List.append`) is associative, and joining an empty list changes nothing. | Laws stated |
| `word_list_order` | Comparing lists of words: equal only when the same, flips when swapped, "below" is transitive; the split key of two lists lies above the first and at or below the second. | Laws stated |
| `word_list_sets` | Lists of words as sets: equal, contains, and dedupe, which keeps each list once (1 law). | Laws stated |
| `item_merge` | Three-way merge of lists of items (lines, functions, blocks): a diff is an edit script over the base. Laws: a diff applies; a diff keeps a longest common list of items; changes that are apart are both applied; changes that touch and differ clash. So a merge never loses a change made on only one side. | Laws stated |
| `shared.bend` | Helpers with no laws: combining comparisons, optional values, fixed-length lists. | Stated |
| `association_list` | Lists of key-value pairs, which the `patricia_map` laws compare a map with. No laws. | Stated |
| `sha256` | SHA-256 of words. No law: a test against the standard's examples checks it. | Stated; test written |
| `patricia_map` | A map from keys (lists of words) to values: made from a list, merge, keep, split, list, "same entries, same map", and a summary that combines the summaries of two halves split where the keys part (a Merkle hash when the combine hashes). | Laws stated |
| `exact_word_encoding` | Exact encodings as words (each value has one encoding, read back with the words after it) for a word, a number, a dependent pair, a fixed-length list, and a conversion; every other type's encoding comes from these. | Laws stated |
| `signatures` | A signer (never copied, so never signs twice from one state): every signature it makes checks with its public key, which never changes; it makes at least 2^20. | Laws stated |
| `signed_records` | A signed record (author, words, signature); its key reads back as it and as nothing else; it checks exactly when its signature does; the record set (`SignedRecordSet`, a `patricia_map`) whose summaries are Merkle hashes. That a node holds only records that check is a law of the node, where records are added. | Laws stated |
| `monotone_queries` | A monotone answer (Unknown, Known, or Contradicted with proof) and when one knows more; number ranges that only narrow; a monotone query (it knows more on a grown state); "q1, then q2" of monotone queries is monotone (1 law); a hook's incremental state matches its plain query. | Laws stated |
| `slot_consensus` | Paxos with chained ballots, with the voters as a parameter. Deciding: the rule (definitions) and 2 laws: a decision only knows more with more ballots, and a judged ballot keeps its judgment. Casting: what an honest voter signs next, voting only for choices that a validity hook accepts (a vote, a lead, a catch-up join of a round that at least half of the voters reached, a first join of round 0, or on a Tick a join of the round after its own), with 3 laws: it never contradicts its own ballots, it leads and votes only for its proposal or accepted choices, and its leads and votes are judged sound. Progress: a good phase (honest voters in sync, an honest next leader) decides the slot within one Tick and two exchanges, whatever the other voters send. | Laws stated |
| `owner_groups` | The voters of each step: a root line whose decided choices set group members and line owners (read by a decode hook); groups of groups; eras that never go back; what an honest voter accepts (a choice naming an era it already knows) and the era an honest leader names (the latest known). Laws: nodes are exactly the names reached through a group; voters only become known; eras grow; acceptance lasts; after a decided accepted slot the next slot's voters are known; an honest proposal is accepted and names every known era. | Laws stated |
| `record_sync` | Two nodes exchange messages until one has nothing more to say. Laws: taking in a message never loses a record and adds only records that check; every sync ends; a sync between nodes that follow it, with no SHA-256 collision on their parts, ends with both holding the records of both. What the messages say is the implementation's choice; that a sync costs what differs is measured. | Laws stated |
| `part_store` | Parts of content under their SHA-256; keep claims; dropping; fetching from a peer. Laws: a part is the words of its hash; the empty store holds nothing; put adds a part under its hash and changes nothing else; the hashes are exactly those held, once; a drop keeps what the node needs or claimed and drops a part only once enough other trusted keepers claimed it; a fetch gives every asked part that the peer holds; taking in any message loses no part. | Laws stated |
| `record_views` | The ballots and keep claims among a record set's records, read by hooks; a ballot or claim counts only as its record's author's. Laws: ballots and claims are exactly those the records are. | Laws stated |
| `node` | The whole non-IO program: one pure step from a node's state and a deed to its next state and outputs. Hooks (from Vend): how ballots and claims are written, how choices name eras, the plan of steps and payloads, the needed parts, the answers to questions. Laws: start and resume are sound; every step keeps the invariant (records check, own ballots never contradict, name is the key); no record is lost; a step persists exactly what it adds, before any message; clients and the stop rule; each deed does what it asks and outputs nothing else; submits, syncs and part answers take in what they should; Work and Tick cast exactly what slot consensus says; keepers claim and drop parts as part store says; a node signs nothing else. | Laws stated |
| Vend | The versioning hooks, at the top level of `src/refactor/`. | Not started |

Slot consensus takes the voters of a slot as a parameter, and groups (above it) say who they are,
from slots that slot consensus decided before. So the two do not depend on each other in a cycle.

## Requirement coverage

| Requirement | How |
| --- | --- |
| Trust 1 | Signatures and hashes are the only assumptions. |
| Trust 2 | Each monotone query has two laws: it never changes a known answer, and it knows when it must. |
| Trust 3 | Votes count only for members. A lying member makes only the groups that contain it Contradicted. |
| Trust 4 | One history: two majorities of a group always share a member. Progress: see Limits. |
| Shape 1, 2 | Nodes are one type; Vend is hooks. |
| Shape 3 | A hook's own state, proven equal to its plain query. |
| Shape 4 | Groups are a monotone query over decided records. |
| Behavior 1 | Answers are functions of the set; Sync is a merge; equal entries make equal maps. |
| Behavior 2 | Monotone queries answer Unknown or a range until they know. |
| Behavior 3 | Keeping data. See Limits. |
| Behavior 4 | A request is one record, and slot consensus puts it in at most one slot. A writer's view is a live query. |
| Cost 1 | Content is split into parts by hash, stored once; Sync compares the summaries of parts; the time of each operation does not grow with the history. |
| Cost 2 | Known answers never change, so caches never need invalidation. Live queries are not cached. |
| Cost 3 | Agreement, validity and groups are proven once, for every hook. |
| Cost 4 | Formats, languages, mounts and submodules are hooks. |

## Limits

No design removes these. They are stated so that no law claims more.

- Progress needs a majority of each group to be reachable, and a round that lasts long enough for
  that majority to sync with its leader.
- Data is kept only as long as enough of the nodes that signed that they keep it are not lost.
- A Sync by hashes of subtrees can miss records when two inputs have one hash. A missed record makes
  answers less known, never wrong.
- Records from strangers cost storage. The program limits them; the core has no rule for them.
- A change of a group cannot reach a line at the very next slot when that slot already has votes from
  before the change: consensus must finish it with its old choice, or two nodes could decide two
  different ones. The era is part of the chosen value for the same reason: if it could change after
  the choice is made, two nodes could disagree on who votes next. So the slot after it takes the
  change.

## Sources

Read from abstracts and summaries only, not the full papers.

- Hellerstein and Alvaro, [Keeping CALM: when distributed consistency is easy](https://arxiv.org/abs/1901.01930)
  (2019): what needs no coordination is exactly what is monotone.
- Kuper and Newton, LVars ([POPL 2014 paper](https://www.cl.cam.ac.uk/~nk480/lvish-popl.pdf)):
  values that only move up a lattice, with reads that wait for a lower bound; an error state when
  two writes cannot join.
- Kleppmann and Howard, [Byzantine Eventual Consistency](https://arxiv.org/abs/2012.00472) (2020):
  what a peer-to-peer database can do with any number of faulty nodes and no consensus.
- Sanjuán et al., [Merkle-CRDTs](https://arxiv.org/abs/2004.00107) (2020): records in a Merkle DAG as
  transport and storage for merging data types.
- Auvolat and Taïani, [Merkle Search Trees](https://g-trees.github.io/g_trees/assets/references/auvolat2019merkle.pdf)
  (SRDS 2019): a tree whose shape depends only on its content, so two nodes find their differences
  by comparing hashes.
